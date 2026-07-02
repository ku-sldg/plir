# Programming Languages in Rocq: Func Module (Adding Functions)

A complete teaching scaffold for the **"Functions"** unit of the PLIH
course, ported to the Rocq Prover.

Source chapters (Haskell):
<https://ku-sldg.github.io/plih//funs/1-Adding-Functions.html>,
<https://ku-sldg.github.io/plih//funs/2-Scoping.html>

## The idea

FBAE extends the BAE language with first-class functions — `Lambda` and
`App`:

```
Inductive FBAE : Type :=
| Num  : nat -> FBAE       | Bind   : string -> FBAE -> FBAE -> FBAE
| Plus : FBAE -> FBAE -> FBAE | Lambda : string -> FBAE -> FBAE
| Minus: FBAE -> FBAE -> FBAE | App    : FBAE -> FBAE -> FBAE
| Id   : string -> FBAE.
```

Two things change fundamentally from the earlier chapters.

### 1. The language can diverge — so fuel is unavoidable

In IDs/Env we only ever substituted a *number*, so `size` was preserved
and `size e` was always enough fuel (and Env's interpreter was even a
clean structural `Fixpoint`). Now we substitute whole *functions*, so a
substitution can make a term **grow**, and self-application

```
Definition omega := App (Lambda "x" (App (Id "x") (Id "x")))
                        (Lambda "x" (App (Id "x") (Id "x"))).
```

loops forever. No measure bounds evaluation, so **both** interpreters —
the substitution `evalS` and the environment/closure `evalM` — are driven
by an explicit **fuel** counter, and running out yields `None`.

The metatheorem that replaces "size is enough fuel" is **fuel
monotonicity**:

```
Lemma evalM_mono : forall f1 f2 env e v,
  f1 <= f2 -> evalM f1 env e = Some v -> evalM f2 env e = Some v.
```

*more fuel never changes a definite answer.*

### 2. Scoping becomes a choice — closures give static scoping

A function returned from its defining scope must remember the bindings
in force **where it was defined**. That bundle is a **closure**:

```
Inductive FBAEVal : Type :=
| NumV     : nat -> FBAEVal
| ClosureV : string -> FBAE -> list (string * FBAEVal) -> FBAEVal.
```

The environment interpreter `evalM` runs a called function's body in the
closure's captured environment (static scoping). A deliberately
different interpreter `evalDyn` uses the **caller's** environment
(dynamic scoping). They disagree on the classic term

```
bind n = 1 in bind f = (lambda x in x + n) in bind n = 2 in (f 3)
```

— `evalM` (and the substitution interpreter `evalS`) answer **4**;
`evalDyn` answers **5**.

## What you get

| File | Purpose |
|------|---------|
| `plih_rocq_func_shared.v` | Re-exports the IDs/AE infrastructure (`Env`, `lookup`, `extend`, string lemmas) |
| `plih_func_lecture.v` | FBAE, `evalS`, closures + `evalM`, monotonicity, static-vs-dynamic scoping, currying, divergence |
| `plih_func_exercises.v` | 22 exercises + 2 challenges (`Admitted` stubs) |
| `plih_func_solutions.v` | Complete, machine-checked solutions |
| `plih_func_instructor_guide.v` | Lesson plan, common mistakes, transition notes |
| `plih_func_summary.v` | Module organization and concept map |

## Exercise highlights

- **Fuel monotonicity & determinism** — cite `evalM_mono`; then re-prove
  monotonicity for the dynamic interpreter `evalDyn` from scratch
- **Static vs dynamic scoping** — the 4-vs-5 witness
- **Currying** — partial application returns a closure capturing the
  first argument
- **Divergence** — `omega`, and strict binding of a divergent expression
- **An error interpreter** — `evalErr : nat -> Env FBAEVal -> FBAE ->
  string + FBAEVal` distinguishing *out of gas* from *stuck*, proved to
  *refine* `evalM` via `forget (evalErr f env e) = evalM f env e`

## Building

From the repository root:

```bash
make
```

`Func/` is mapped to the empty logical path in the root `_CoqProject`,
and depends on the `IDs/` chapter. Tested on The Rocq Prover 9.1.

## What's different from PLIH (Haskell)

| Aspect | PLIH (Haskell) | PLIH (Rocq) |
|--------|----------------|-------------|
| `evalS` / `evalM` | `Maybe`-returning, general recursion | fuel-indexed `option`, since the language can diverge |
| "eval is well defined" | (implicit) | `evalM_mono` — fuel monotonicity, proved |
| Static vs dynamic scoping | prose + examples | two interpreters + a proved 4-vs-5 witness |
| `evalErr` (Either) | suggested exercise | implemented + proved to refine `evalM` |
