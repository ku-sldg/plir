---
name: plir-pending-work
description: Known incomplete/WIP files in the plir Rocq port as of 2026-06-30
metadata: 
  node_type: memory
  type: project
  originSessionId: d30c277d-435f-43de-8a3b-ef776a2ebbb5
---

As of 2026-06-30, the ABE chapter is complete and builds clean. Still outstanding (not yet done, the user will iterate interactively):

- `AE/plih_ae_exercises.v`, `AE/plih_ae_solutions.v`, `AE/plih_ae_summary.v`, `AE/plih_ae_instructor_guide.v` are still stub WIP (e.g. `Inductive AE := eq_refl.`, `:= sorry`/`eq_refl` proofs, unterminated comments). They do NOT compile and are intentionally excluded from the `make` target (`_CoqProject` only lists `AE/plih_rocq_ae_shared.v` + `AE/plih_ae_lecture.v`). Only the AE `/home/claude/...` import-path artifact was fixed.
- `TACTICS_CHEATSHEET.v` (repo root, AE-oriented) still teaches Lean tactics (`simp [eval]`, `rw [H]`, `cases`, `·`) despite being titled a Rocq cheat sheet — needs de-Leaning.

Reminder: the user instructed "DO NOT USE LEAN 4 TACTICS" — see [[plir-feedback-no-lean-tactics]].