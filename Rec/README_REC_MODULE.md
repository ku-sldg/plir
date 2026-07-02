# Programming Languages in Rocq: Rec Module (Untyped Recursion)

A complete teaching scaffold for the **"Untyped Recursion"** unit of the
PLIH course, ported to the Rocq Prover.

Source chapter (Haskell):
<https://ku-sldg.github.io/plih//funs/7-Untyped-Recursion.html>

## The idea

The `Func` chapter could only *tease* recursion: FBAE has no
conditional, so a recursive call has no way to stop, and
self-terminating recursion is inexpressible. This chapter adds a
conditional and delivers **productive** recursion — computing real
answers — **without** a primitive `fix`, exactly as the original PLIH
chapter does: recursion is built from the **Y** and **Z** fixpoint
combinators.

FBAEC ("FBAE + Conditionals") extends FBAE with `Mult`, booleans,
`IsZero`, and `If`:

```
Inductive FBAEC : Type :=
| Num     : nat -> FBAEC        | If     : FBAEC -> FBAEC -> FBAEC -> FBAEC
| Plus    : FBAEC -> FBAEC -> FBAEC | Bind   : string -> FBAEC -> FBAEC -> FBAEC
| Minus   : FBAEC -> FBAEC -> FBAEC | Lambda : string -> FBAEC -> FBAEC
| Mult    : FBAEC -> FBAEC -> FBAEC | App    : FBAEC -> FBAEC -> FBAEC
| Boolean : bool -> FBAEC        | Id     : string -> FBAEC
| IsZero  : FBAEC -> FBAEC.
```

Two ideas carry the chapter.

### 1. `If` evaluates only the taken branch — that is what lets recursion stop

The conditional evaluates its guard, then runs **only** the selected
branch. A generator like

```
sumGen = \g. \z. if z = 0 then z else z + (g (z-1))
```

recurses through `g` in the *else* branch; once `z` reaches `0` the
*then* branch is taken and the branch still containing the recursive
call is **never evaluated**. That is precisely how the recursion bottoms
out.

The language is still Turing-powerful and partial, so — as in `Func` —
evaluation is driven by an explicit **fuel** counter, and running out of
fuel yields `None`:

```
Fixpoint evalM (fuel : nat) (env : Env RVal) (e : FBAEC) : option RVal
Definition eval (e : FBAEC) : option RVal := evalM 1000 nil e.
```

The metatheorem carried over from `Func` is **fuel monotonicity**:

```
Lemma evalM_mono : forall f1 f2 env e v,
  f1 <= f2 -> evalM f1 env e = Some v -> evalM f2 env e = Some v.
```

*more fuel never changes a definite answer.* (A terminating concrete
term stops early at its value, so fuel `1000` is plenty — cost is the
actual number of steps, not the cap.)

### 2. Two evaluation strategies — and Y vs Z depends on which you pick

The chapter ships **two** fuel-driven interpreters, deliberately parallel:

| Interpreter | Strategy | Values |
|-------------|----------|--------|
| `evalM` | strict, call-by-value | `RVal = NumV \| BoolV \| ClosureV` |
| `evalL` | lazy, call-by-name (thunks) | `LVal = LNumV \| LBoolV \| LCloV`; `LThunk = Thk FBAEC env` |

The two recursion combinators are `omega` parameterised by a generator:

```
Yc = \f. (\x. f (x x)) (\x. f (x x))
Zc = \f. (\x. f (\v. x x v)) (\x. f (\v. x x v))   (* eta-guarded *)
```

Which one works depends on the strategy:

- **`Zc` under strict `eval`.** `Zc`'s eta-guard delays the
  self-application, so the strict interpreter makes progress:
  `eval (App (App Zc sumGen) (Num 5)) = Some (NumV 15)` and
  `eval (App (App Zc factGen) (Num 5)) = Some (NumV 120)`.
- **`Yc` under lazy `evalLazy`.** Plain `Yc` needs non-strict argument
  handling: `evalLazy (App (App Yc factGen) (Num 5)) = Some (LNumV 120)`.
- **`Yc` under strict evaluation is just parameterised `omega`** — it
  diverges: `evalM 100 nil (App (App Yc sumGen) (Num 5)) = None`.

All the productive results are `reflexivity` on concrete terms.

## What you get

| File | Purpose |
|------|---------|
| `plih_rocq_rec_shared.v` | Re-exports the `Func`/IDs infrastructure (`Env`, `lookup`, `extend`, string lemmas) via `Require Export plih_rocq_func_shared` |
| `plih_rec_lecture.v` | FBAEC, strict `evalM` + `eval`, lazy `evalL` + `evalLazy`, `evalM_mono`, `omega`, `Yc`/`Zc`, `sumGen`/`factGen`, productive summation & factorial |
| `plih_rec_exercises.v` | 10 exercises (`Admitted` stubs) |
| `plih_rec_solutions.v` | Complete, machine-checked solutions |
| `plih_rec_instructor_guide.v` | Lesson plan, common mistakes, transition notes |
| `plih_rec_summary.v` | Module organization and concept map |

## Exercise highlights

- **Productive recursion** — sum and factorial via `Zc` under strict
  `eval` (`ex3`, `ex4`), factorial via `Yc` under `evalLazy` (`ex5`)
- **Strict Y diverges** — `Yc` under strict evaluation is `omega`
  parameterised, and runs out of fuel (`ex6`)
- **Fuel monotonicity & determinism** — `ex9` cites `evalM_mono` (fuel
  kept a *variable*); `ex10` proves the answer is unique
- **The new evaluator cases** — booleans and the two-branch `If`
  (`ex7`, `ex8`)

## Building

From the repository root:

```bash
make
```

`Rec/` is mapped to the empty logical path in the root `_CoqProject`
(`-Q Rec ""`) and depends on the `Func/` chapter (its shared file
re-exports `plih_rocq_func_shared`). Editing `_CoqProject` and re-running
`make` regenerates the Makefile. A full clean build of all six chapters
(AE → Rec) takes roughly 5.5s.

## What's different from PLIH (Haskell)

| Aspect | PLIH (Haskell) | PLIH (Rocq) |
|--------|----------------|-------------|
| `evalM` / `evalL` | `Maybe`-returning, general recursion | fuel-indexed `option`, since the language can diverge |
| "eval is well defined" | (implicit) | `evalM_mono` — fuel monotonicity, proved |
| Y vs Z / strict vs lazy | prose + examples | two interpreters, with `Zc`-strict, `Yc`-lazy, and `Yc`-strict-diverges all proved |
| Productive sum & factorial | evaluated by hand | machine-checked `reflexivity` on concrete terms |

## Where this is heading

The untyped language stays Turing-powerful and partial. A type system
will reject `Yc`/`Zc`'s self-application (`x x` cannot be typed), so
recursion has to be re-introduced as a **typed `fix`** — the subject of
the upcoming *Typed Recursion* chapter (`types/`).
