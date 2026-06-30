---
name: plir-abe-design-decisions
description: "ABE chapter design choices in the plir Rocq port (constructors, eval semantics, type caveats)"
metadata: 
  node_type: memory
  type: project
  originSessionId: d30c277d-435f-43de-8a3b-ef776a2ebbb5
---

The ABE Rocq scaffold (in `ABE/`) deliberately diverges from the original PLIH Haskell `ABE` type. The Haskell course uses `Num | Plus | Minus | Boolean | And | Leq | IsZero | If`; the Rocq scaffold instead uses `Num | Plus | Minus | BTrue | BFalse | And | Or | Not | LessThan | Equal | IfThenElse` (kept because the whole scaffold was already written around these). Values are a dedicated type `Value := NumV nat | BoolV bool` (in `plih_rocq_abe_shared.v`), and `eval : ABE -> option Value` with **eager, type-checked** semantics: both operands are always evaluated, and a type mismatch yields `None`.

Consequence: several "obvious" untyped identities are FALSE under these semantics and were restated with hypotheses — e.g. `And BTrue e = e` needs `eval e = Some (BoolV b)`; `IfThenElse cond (Num 5)(Num 5) = Some (NumV 5)` needs the condition to be boolean; naive double-negation elimination `Not(Not e) -> e` is unsound (so the optimization exercise folds `Not` of a boolean literal instead); And short-circuit needs the second operand to be boolean. These caveats are documented inline and are good teaching points about why static typing matters.

`plih_abe_lecture.v` defines `ABE`/`eval` and re-exports the shared infra; `plih_abe_exercises.v` and `plih_abe_solutions.v` import the lecture. Exercises use `Admitted` placeholders (Rocq's analog of Lean's `sorry`); solutions are fully proved. See [[plir-pending-work]].