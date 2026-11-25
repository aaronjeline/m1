//! Verification target for the M1 model: a Cedar type-soundness check.
//!
//! [`check`] takes the text of an arbitrary Cedar expression and
//!
//! 1. parses it (a parse error is an ordinary outcome: [`Outcome::ParseError`]);
//! 2. typechecks it with Cedar's validator in strict mode against [`SCHEMA`]
//!    (an ill-typed expression is an ordinary outcome: [`Outcome::IllTyped`]);
//! 3. evaluates it against a fixed request and entity store that conform to
//!    [`SCHEMA`];
//! 4. if evaluation fails with a *type error*, that contradicts the soundness
//!    of the typechecker, so that path is asserted unreachable
//!    ([`type_soundness_violation`]).
//!
//! The C entry point for the compiled dylib is [`cedar_check`].

use std::str::FromStr;
use std::sync::OnceLock;

use cedar_policy::{
    eval_expression, Context, Entities, EntityUid, EvalResult, EvaluationError, Expression,
    Request, Schema,
};
use cedar_policy_core::ast;
use cedar_policy_core::validator::{ValidationMode, Validator};

/// Schema the expression is typechecked against. `principal`, `action`,
/// `resource` and `context` have the types given by the single action.
pub const SCHEMA: &str = r#"
entity Group;
entity User in [Group] = { name: String, age: Long };
entity Doc = { owner: User, tags: Set<String>, public: Bool };
action read appliesTo {
  principal: User,
  resource: Doc,
  context: { n: Long, ip: ipaddr }
};
"#;

/// Entity store the expression is evaluated against (conforms to [`SCHEMA`]).
pub const ENTITIES: &str = r#"[
  { "uid": { "type": "Group", "id": "admins" }, "attrs": {}, "parents": [] },
  { "uid": { "type": "User", "id": "alice" },
    "attrs": { "name": "alice", "age": 30 },
    "parents": [ { "type": "Group", "id": "admins" } ] },
  { "uid": { "type": "Doc", "id": "d" },
    "attrs": { "owner": { "__entity": { "type": "User", "id": "alice" } },
               "tags": ["a", "b"], "public": false },
    "parents": [] }
]"#;

/// Request the expression is evaluated in (conforms to [`SCHEMA`]).
pub const PRINCIPAL: &str = r#"User::"alice""#;
pub const ACTION: &str = r#"Action::"read""#;
pub const RESOURCE: &str = r#"Doc::"d""#;
pub const CONTEXT: &str = r#"{ "n": 1, "ip": { "__extn": { "fn": "ip", "arg": "10.0.0.1" } } }"#;

/// Result of [`check`]. The discriminants are what [`cedar_check`] returns.
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(i32)]
pub enum Outcome {
    /// The input is not valid UTF-8 or not a Cedar expression.
    ParseError = 0,
    /// The expression does not typecheck.
    IllTyped = 1,
    /// The expression typechecks and evaluates to a value.
    Value(EvalResult) = 2,
    /// The expression typechecks and evaluation fails with an error the
    /// typechecker does not rule out (entity does not exist, integer
    /// overflow, extension function failure, ...). Never a type error.
    EvalError(EvaluationError) = 3,
}

impl Outcome {
    pub fn code(&self) -> i32 {
        match self {
            Outcome::ParseError => 0,
            Outcome::IllTyped => 1,
            Outcome::Value(_) => 2,
            Outcome::EvalError(_) => 3,
        }
    }
}

/// The fixed typing and evaluation environment.
pub struct Env {
    validator: Validator,
    entities: Entities,
    request: Request,
}

#[expect(clippy::expect_used, reason = "fixed inputs; failure is a bug in this file")]
fn env() -> &'static Env {
    static ENV: OnceLock<Env> = OnceLock::new();
    ENV.get_or_init(|| {
        let (schema, _warnings) = Schema::from_cedarschema_str(SCHEMA).expect("SCHEMA parses");
        // Both constructors check the data against the schema, so the
        // request and entities are well-typed: soundness applies to them.
        let entities =
            Entities::from_json_str(ENTITIES, Some(&schema)).expect("ENTITIES conform to SCHEMA");
        let uid = |s: &str| EntityUid::from_str(s).expect("valid entity uid");
        let action = uid(ACTION);
        let context =
            Context::from_json_str(CONTEXT, Some((&schema, &action))).expect("CONTEXT conforms");
        let request = Request::new(uid(PRINCIPAL), action, uid(RESOURCE), context, Some(&schema))
            .expect("request conforms to SCHEMA");
        let validator = cedar_policy::Validator::new(schema).as_ref().clone();
        Env { validator, entities, request }
    })
}

/// Does `e` typecheck (strict mode) against [`SCHEMA`]?
///
/// The validator checks policies, whose condition must be a `Bool`, so the
/// expression is checked as the policy
/// `permit(principal, action, resource) when { e == e };`
/// which typechecks exactly when `e` has some type. The policy is built as an
/// AST, not by pasting `e` into policy text, so the input cannot escape it.
pub fn typechecks(e: &ast::Expr) -> bool {
    typechecks_in(env(), e)
}

/// [`typechecks`] in the given environment.
#[inline(never)]
fn typechecks_in(env: &Env, e: &ast::Expr) -> bool {
    let cond = ast::Expr::is_eq(e.clone(), e.clone());
    let policy = ast::Policy::from_when_clause(
        ast::Effect::Permit,
        cond,
        ast::PolicyID::from_string("target"),
        None,
    );
    let mut pset = ast::PolicySet::new();
    if pset.add(policy).is_err() {
        return false;
    }
    env.validator.validate(&pset, ValidationMode::Strict).validation_passed()
}

/// Parse, typecheck and evaluate `src`.
pub fn check(src: &str) -> Outcome {
    let parsed = Expression::from_str(src);
    match &parsed {
        Ok(expr) => verdict(env(), expr),
        Err(_) => Outcome::ParseError,
    }
}

/// Typecheck and evaluate a parsed expression: the part of [`check`] that
/// decides whether the assertion is reached, and the only caller of
/// [`type_soundness_violation`].
///
/// Kept out of line, borrowing its inputs and moving the evaluation result
/// into its own result, so that its machine code is small and self-contained:
/// it is verified in the M1 model (`Examples/Cedar`).
#[inline(never)]
pub fn verdict(env: &Env, expr: &Expression) -> Outcome {
    if !typechecks_in(env, expr.as_ref()) {
        return Outcome::IllTyped;
    }
    match eval_expression(&env.request, &env.entities, expr) {
        Ok(v) => Outcome::Value(v),
        Err(EvaluationError::TypeError(_)) => type_soundness_violation(),
        Err(e) => Outcome::EvalError(e),
    }
}

/// The assertion: a well-typed expression raised a type error at run time.
///
/// On AArch64 this is a single `brk #0xc0de`, which stops the M1 model with
/// status `.brk 0xc0de` (and raises `SIGTRAP` on hardware), so the property
/// to prove about the compiled code is that it never reaches this
/// instruction. Elsewhere (host tests) it is `unreachable!()`.
#[cold]
#[inline(never)]
pub fn type_soundness_violation() -> ! {
    #[cfg(target_arch = "aarch64")]
    // SAFETY: `brk` only traps; it reads and writes no memory.
    unsafe {
        core::arch::asm!("brk #0xc0de", options(noreturn, nomem, nostack))
    }
    #[cfg(not(target_arch = "aarch64"))]
    unreachable!("well-typed Cedar expression raised a type error at run time")
}

/// C entry point: check the `len` bytes at `src`.
///
/// Returns 0 (parse error or invalid UTF-8), 1 (ill-typed), 2 (value) or
/// 3 (evaluation error that is not a type error); see [`Outcome`].
///
/// # Safety
/// `src` must point to `len` readable bytes (it may be null when `len` is 0).
#[no_mangle]
pub unsafe extern "C" fn cedar_check(src: *const u8, len: usize) -> i32 {
    let bytes = if len == 0 { &[][..] } else { std::slice::from_raw_parts(src, len) };
    match std::str::from_utf8(bytes) {
        Ok(s) => check(s).code(),
        Err(_) => Outcome::ParseError.code(),
    }
}
