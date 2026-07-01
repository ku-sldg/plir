# Programming Languages in Rocq: IDs Module (Adding Identifiers)

A complete teaching scaffold for the **"Adding Identifiers"** section of
the PLIH course, ported to the Rocq Prover.

Source chapter (Haskell):
<https://ku-sldg.github.io/plih//ids/1-Adding-IDs.html>

## The language: BAE

BAE ("Bind and Arithmetic Expressions") is AE plus identifiers and a
local binding form:

```
Inductive BAE : Type :=
| Num   : nat -> BAE
| Plus  : BAE -> BAE -> BAE
| Minus : BAE -> BAE -> BAE
| Bind  : string -> BAE -> BAE -> BAE   (* bind x = v in b *)
| Id    : string -> BAE.
```

The meaning of a binding is given by **substitution**: `bind x = v in b`
evaluates `v` to a number, then replaces every free `x` in `b` with it.

## What you get

| File | Purpose |
|------|---------|
| `plih_rocq_ids_shared.v` | Shared infra; re-exports the AE library, adds name-comparison lemmas |
| `plih_ids_lecture.v` | 9 sections: syntax, free/closed, substitution, the fuel interpreter, properties |
| `plih_ids_exercises.v` | 24 exercises + 2 challenges (`Admitted` stubs) |
| `plih_ids_solutions.v` | Complete, machine-checked solutions |
| `plih_ids_instructor_guide.v` | Lesson plan, common mistakes, transition notes |
| `plih_ids_summary.v` | Module organization and concept map |

## The Rocq-specific twist

A substitution interpreter is **not structurally recursive**: the
`Bind` case would recurse on `subst i (Num n) b`, a brand-new term that
Rocq's termination checker cannot see is smaller. The naive `Fixpoint`
is therefore rejected.

The fix is to recurse on a decreasing **fuel** counter. Because
substituting a number preserves `size`
(`size (subst i (Num n) e) = size e`), starting with `fuel = size e` is
always enough. A monotonicity lemma (`evalF_mono`) then yields clean
recursive equations (`eval_Num`, `eval_Plus`, `eval_Minus`,
`eval_Bind`) so downstream proofs never mention fuel.

This friction is exactly what the next chapter, **Adding
Environments**, removes.

## Highlights proved

- `subst_not_free` / `subst_closed` — substitution ignores non-free vars
- `free_in_subst_num` — how substitution reshapes the free-variable set
- `closed_after_subst` — substituting the last free variable closes a term
- **Progress** (challenge) — every *closed* BAE evaluates to a number;
  closed programs never get stuck (the substitution-semantics analogue
  of type safety)

## Building

From the repository root:

```bash
make
```

The root `_CoqProject` maps `IDs/` to the empty logical path, so files
cross-reference by short module name (e.g.
`Require Import plih_ids_lecture`). Tested on The Rocq Prover 9.1.

## What's different from PLIH (Haskell)

| Aspect | PLIH (Haskell) | PLIH (Rocq) |
|--------|----------------|-------------|
| `eval` | `evals :: BAE -> Maybe BAE` (general recursion) | `eval : BAE -> option nat` via `size`-bounded fuel (proved total) |
| Free ids | runtime `Nothing` | `option`; plus a proved **progress** theorem for closed terms |
| Correctness | QuickCheck | machine-checked lemmas |
