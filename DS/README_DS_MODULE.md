# Programming Languages in Rocq: DS Module (Data Structures)

A complete teaching scaffold for **Data Structures** — recursive types,
higher-order functions, and polymorphism — in the Rocq Prover.

## The idea

Every prior chapter in PLIH defines a small language, writes an interpreter,
and proves things about it.  This chapter steps back to examine how
*data structures* are built in Rocq itself, using lists as the running example.

The central lesson: **a function's recursive structure is determined by the
shape of the data, not the content of the elements.**  We prove this formally
by building an isomorphism between integer lists and polymorphic-nat lists and
showing that every higher-order function commutes with it.

## What is in the chapter

### Stage 1 — Integer lists (`IntList`)

```
Inductive IntList : Type :=
| Nil  : IntList
| Cons : nat -> IntList -> IntList.
```

The LISP observers `car`/`cdr`/`isEmpty` are defined as Rocq `Definition`s
returning `option nat`, `option IntList`, and `bool`.  Structural operations
(`length`, `append`, `reverse`) are `Fixpoint` definitions with proofs of the
key algebraic laws:

- `append_nil_r` — left identity requires induction; right identity does not
- `append_assoc` — proved by induction on the first argument
- `length_append` — `length (append xs ys) = length xs + length ys`
- `reverse_length` — `length (reverse xs) = length xs`

### Stage 2 — Higher-order functions

Four classical functions, each abstracting over the per-element operation:

| Function | Type | What it does |
|----------|------|-------------|
| `map` | `(nat -> nat) -> IntList -> IntList` | apply `f` to every element |
| `foldr` | `{B} (nat -> B -> B) -> B -> IntList -> B` | right fold |
| `foldl` | `{B} (B -> nat -> B) -> B -> IntList -> B` | left fold (tail-recursive) |
| `filter` | `(nat -> bool) -> IntList -> IntList` | keep elements satisfying `p` |

Key lemma: `map_length` — `length (map f xs) = length xs`.

### Stage 3 — Polymorphic lists (`PList A`)

```
Inductive PList (A : Type) : Type :=
| PNil  : PList A
| PCons : A -> PList A -> PList A.
```

Every observer and function re-appears with identical recursive structure,
replacing `nat` with the type parameter `A`.  `pmap {A B} (f : A -> B)` can
now change the element type, which `map (f : nat -> nat)` could not.

### Stage 4 — The isomorphism

```
intToP : IntList -> PList nat
pToInt : PList nat -> IntList
```

Both conversion functions are inverses (`intToP_pToInt`, `pToInt_intToP`).
Four commutation lemmas prove that the integer and polymorphic functions agree:

```
map_commutes    : intToP (map f xs)       = pmap f (intToP xs)
foldr_commutes  : foldr f acc xs          = pfoldr f acc (intToP xs)
foldl_commutes  : foldl f acc xs          = pfoldl f acc (intToP xs)
filter_commutes : intToP (filter p xs)    = pfilter p (intToP xs)
```

## What you get

| File | Purpose |
|------|---------|
| `plih_rocq_ds_shared.v` | Re-exports `Arith`, `Bool`, `Lia` |
| `plih_ds_lecture.v` | All definitions and proofs (Sections 1–5) |
| `plih_ds_exercises.v` | 16 exercises (`Admitted` stubs) |
| `plih_ds_solutions.v` | Complete, machine-checked solutions |
| `plih_ds_instructor_guide.v` | Lesson plan, pitfalls, exercise notes |
| `plih_ds_summary.v` | Module organisation and concept map |

## Exercise highlights

- **Part 1 (ex1–ex8)** — run every major function on a concrete list: `reflexivity` throughout
- **ex9** — `map_length`: standard structural induction, closes immediately
- **ex10** — `filter_le_length`: induction + `destruct (p n)` + `lia`
- **ex11–ex12** — `reverse_append` then `reverse_involutive`: the classic two-step; ex12 requires ex11
- **ex15** — `pmap_length`: identical proof structure to ex9, reinforcing the polymorphism point
- **ex16** — `foldl_commutes`: needs `revert acc` before induction to keep the hypothesis general

## Building

From the repository root:

```bash
make
```

`DS/` is mapped to the empty logical path in `_CoqProject` (`-Q DS ""`).  It
has no dependency on the interpreter chain: the shared file imports only
`Arith`, `Bool`, and `Lia`.

## Connections to other chapters

- `Env A = list (string * A)` used in every interpreter chapter from IDs onward
  is a `PList (string * A)`.  The `lookup`/`extend` proofs are the same
  structural induction pattern students practise here.
- The polymorphic `foldr` generalises directly to tree folds, which appear in
  typed language chapters when terms have a recursive inductive structure.
