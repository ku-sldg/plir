# Programming Languages in Rocq: Env Module (Adding Environments)

A complete teaching scaffold for the **"Adding Environments"** section
of the PLIH course, ported to the Rocq Prover.

Source chapter (Haskell):
<https://ku-sldg.github.io/plih//ids/2-Adding-Environments.html>

## The idea

This chapter keeps the **same BAE language** from *Adding Identifiers*
but replaces eager substitution with a deferred **environment** — a
table of identifier/value bindings consulted on demand:

```
Fixpoint evalE (env : Env nat) (e : BAE) : option nat :=
  match e with
  | Num n      => Some n
  | Plus  l r  => (* ... a + b ... *)
  | Minus l r  => (* ... a - b ... *)
  | Bind i v b => match evalE env v with
                  | Some n => evalE (extend i n env) b
                  | None => None
                  end
  | Id x       => lookup x env
  end.
```

Unlike the substitution interpreter (which needed **fuel** because
substitution is not structurally recursive), `evalE` is a clean
structural `Fixpoint`: the environment is just an extra parameter.

## The headline theorem

The chapter's claim is that environments change *how* we evaluate, not
*what* we compute. We prove exactly that:

```
Theorem evalE_agrees_eval : forall e, evalE nil e = eval e.
```

where `eval` is the substitution interpreter from the IDs chapter. The
Haskell course validates this with QuickCheck
(`\t -> eval [] t == evals t`); here it is proved for **all** terms.

The proof rests on one key lemma — *an environment binding is a
deferred substitution*:

```
Lemma evalE_extend_subst : forall e env i n,
  evalE (extend i n env) e = evalE env (subst i (Num n) e).
```

whose `Bind` case is handled with environment extensionality
(`evalE_ext`) plus the shadowing/swapping lookup lemmas.

## What you get

| File | Purpose |
|------|---------|
| `plih_rocq_env_shared.v` | Re-exports the IDs chapter and the `Env` operations |
| `plih_env_lecture.v` | `evalE`, extensionality, the key lemma, the agreement theorem |
| `plih_env_exercises.v` | 22 exercises + 2 challenges (`Admitted` stubs) |
| `plih_env_solutions.v` | Complete, machine-checked solutions |
| `plih_env_instructor_guide.v` | Lesson plan, common mistakes, transition notes |
| `plih_env_summary.v` | Module organization and concept map |

## Exercise highlights

- **Environment algebra** — extensionality, shadowing, swapping
- **Agreement** — `evalE nil e = eval e`, and PROGRESS transferred to
  the environment interpreter for free
- **A prelude** — an initial environment of always-available globals
- **An error interpreter** — `evalErr : Env nat -> BAE -> string + nat`
  (the course's `Either` exercise), proved to *refine* `evalE` via
  `forget (evalErr env e) = evalE env e`

## Building

From the repository root:

```bash
make
```

`Env/` is mapped to the empty logical path in the root `_CoqProject`,
and depends on the `IDs/` chapter. Tested on The Rocq Prover 9.1.

## What's different from PLIH (Haskell)

| Aspect | PLIH (Haskell) | PLIH (Rocq) |
|--------|----------------|-------------|
| `eval` | `eval :: Env -> BAE -> Maybe BAE` | `evalE : Env nat -> BAE -> option nat` (clean `Fixpoint`) |
| Two interpreters agree | QuickCheck property | `evalE_agrees_eval`, proved for all terms |
| `evalErr` (Either) | suggested exercise | implemented + proved to refine `evalE` |
| Prelude | suggested exercise | implemented with worked examples |
