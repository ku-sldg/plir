# Programming Languages in Rocq: TFun Module (Typed Functions)

A complete teaching scaffold for the **"Typed Functions"** unit of the
PLIH course, ported to the Rocq Prover.

Source chapter (Haskell):
<https://ku-sldg.github.io/plih//types/1-Function-Types.html>

## The idea

Func and Rec built an **untyped**, Turing-powerful language: it can loop
(`omega`) and it can get **stuck** — `Plus (Boolean true) (Num 1)` is
nonsense the interpreter only rejects (as `None`) *at run time*, after it
has already started evaluating. This chapter adds a **static type
system** that rejects such programs *before* evaluation.

Two things drive the chapter.

### 1. `typeof` is an interpreter that returns types

We add a type language and a type checker:

```
Inductive Ty : Type :=
| TNum  : Ty
| TBool : Ty
| TArr  : Ty -> Ty -> Ty.        (* function type: d -> r *)

Fixpoint typeof (ctx : Ctx) (e : TFBAEC) : option Ty := ...
Definition typecheck (e : TFBAEC) : option Ty := typeof nil e.
```

`typeof` has the **same shape** as the evaluator `evalM` — it recurses
over the term and carries an identifier→type **context** (`Ctx = Env Ty`)
exactly as `evalM` carries a value environment — but it returns *types*
instead of *values*, and needs no fuel because type checking always
terminates. The interesting rules:

- **`App f a`**: `f` must have a function type `D → R` and `a` must have
  type `D`; the application then has type `R`.
- **`If c t f`**: `c` must be `TBool`, and **both branches must have the
  same type** (a static term cannot know which branch will run).
- **`Lambda x T b`**: the parameter type is **ascribed** — you cannot
  infer a domain type from a function that has not yet been applied — so
  with `x : T` in scope, if `b : R` then the lambda has type `T → R`.

The checker accepts good programs and rejects every classic stuck term:

```
typecheck (Plus (Boolean true) (Num 1))          = None   (* bad arithmetic *)
typecheck (If (Boolean true) (Num 1) (Boolean false)) = None (* branches disagree *)
typecheck (App (Num 1) (Num 2))                  = None   (* number is not a function *)
typecheck (App inc (Boolean true))               = None   (* argument type mismatch *)
```

### 2. Self-application no longer type-checks — so `omega` is gone

Rec's `omega = selfApp selfApp` with `selfApp = \x. x x` is exactly what
made the untyped language diverge. For `x x` to type-check, `x` would
need type `D` **and** `D → R` at the same time — `D = D → R` — which no
finite `Ty` satisfies:

```
typecheck (selfApp TNum)              = None
typecheck (selfApp (TArr TNum TNum))  = None   (* rejected at ANY parameter type *)
```

Types rule out the very term at the heart of `omega` and the Y/Z
combinators. The payoff — **type soundness**, "well-typed programs do not
get stuck" — is stated and witnessed on examples (a well-typed term and
its value side by side), with the base-type canonical-forms slices
proved; the fully general proof needs a logical-relations development and
is left as advanced material, exactly as PLIH states it here.

### Design decision: strict evaluation only

Func and Rec each carried **two** interpreters (a strict `evalM` and a
lazy `evalL`). From this chapter on we keep **only** the strict,
call-by-value `evalM`: the typed language pairs one evaluator with a type
checker, and the headline metatheorem shifts from *fuel monotonicity* to
*type soundness*. (Fuel monotonicity is still re-proved — `evalM` is
defined on all terms, well-typed or not, so the fuel stays.)

## What you get

| File | Purpose |
|------|---------|
| `plih_rocq_tfun_shared.v` | Re-exports the Func/IDs/AE infrastructure (`Env`, `lookup`, `extend`, string lemmas) |
| `plih_tfun_lecture.v` | `Ty` + `Ty_eqb`, typed `TFBAEC`, `typeof`/`typecheck`, strict `evalM`/`eval`, `evalM_mono`, accept/reject examples, soundness witnesses |
| `plih_tfun_exercises.v` | 12 exercises + 3 challenge parts (`Admitted` stubs) |
| `plih_tfun_solutions.v` | Complete, machine-checked solutions |
| `plih_tfun_instructor_guide.v` | Lesson plan, common mistakes, transition notes |
| `plih_tfun_summary.v` | Module organization and concept map |

## Exercise highlights

- **Type checking** — accept arithmetic and a lambda, reject a
  non-Boolean condition, an argument-type mismatch, and self-application
- **Strict evaluation** — an application, a conditional, and a lambda's
  closure under positive fuel
- **Metatheory** — `Ty_eqb` soundness (cite `Ty_eqb_eq`), fuel
  monotonicity (cite `evalM_mono`, fuel kept a *variable*), a
  canonical-forms proof for `Mult`, and determinism
- **Challenge** — `twice`: its function type, and *soundness in
  miniature* (`twice inc 5` type-checks at `TNum` and evaluates to
  `NumV 7`)

## Building

From the repository root:

```bash
make
```

`TFun/` is mapped to the empty logical path in the root `_CoqProject`
(`-Q TFun ""`) and depends on the `Func/` chapter (its shared file
re-exports `plih_rocq_func_shared`). Editing `_CoqProject` and re-running
`make` regenerates the Makefile.

## What's different from PLIH (Haskell)

| Aspect | PLIH (Haskell) | PLIH (Rocq) |
|--------|----------------|-------------|
| `typeof` | `Maybe`-returning, `do`-notation | fuel-free `option`-returning `Fixpoint` over the same context |
| type equality | Haskell `==` | `Ty_eqb`, proved to reflect equality (`Ty_eqb_eq`) |
| interpreter | one evaluator | one **strict** `evalM` (lazy dropped by design) with fuel monotonicity |
| type soundness | stated informally | stated + witnessed on examples; base-type canonical forms proved |

## Where this is heading

Typing is now strict enough that **recursion is gone** — Y/Z relied on
self-application, which no longer type-checks. The next chapter, **Typed
Recursion** (`TRec/`), adds a primitive typed `fix` to put recursion back
deliberately, with the striking payoff that every well-typed term
**normalizes** (terminates).
