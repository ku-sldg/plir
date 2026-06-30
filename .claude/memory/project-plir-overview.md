---
name: project-plir-overview
description: "What the plir project is, its source course, build command, and Rocq version"
metadata: 
  node_type: memory
  type: project
  originSessionId: d30c277d-435f-43de-8a3b-ef776a2ebbb5
---

`plir` is a port of the user's Haskell-based Programming Languages course (PLIH) to the Rocq Prover. The source-of-truth course is at https://ku-sldg.github.io/plih/ (chapters: AE "Arithmetic Expressions", ABE "Adding Booleans", then Identifiers, Functions, Typed Functions, State).

Layout: one folder per chapter (`AE/`, `ABE/`). Build with `make` at the repo root; it uses `_CoqProject` which maps both folders to the empty logical path (`-Q AE ""`, `-Q ABE ""`) so files cross-reference by short module name (e.g. `Require Import plih_rocq_ae_shared`). Tested on The Rocq Prover 9.1 (`rocq`/`coqc` at /Users/alex/.opam). `Makefile` is generated via `rocq makefile -f _CoqProject`.

See [[plir-abe-design-decisions]] and [[plir-pending-work]].