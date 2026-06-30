---
name: plir-feedback-no-lean-tactics
description: "User requires Rocq tactics only, never Lean 4, in the plir project"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: d30c277d-435f-43de-8a3b-ef776a2ebbb5
---

In the plir project the user explicitly instructed: "DO NOT USE LEAN 4 TACTICS." The initial generated files were riddled with Lean 4 syntax (`simp [...]`, `rw [...]`, `cases x`, `·` bullets, `sorry`, `obtain ⟨⟩`, `Inductive T := eq_refl` stubs).

**Why:** the course is being ported to the Rocq Prover; Lean syntax does not compile and is misleading to students.

**How to apply:** use only Rocq/Coq tactics — `simpl`/`cbn`, `rewrite`, `destruct`, `induction`, `reflexivity`, `lia`, bullets `- + *`, and `Admitted` (not `sorry`) for unfinished proofs. Verify every `.v` file with `coqc`/`make` before claiming it's done. See [[plir-abe-design-decisions]].