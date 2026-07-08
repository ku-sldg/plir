(**
PLIH in Rocq: DS (Data Structures) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in DS/):
#<ol>#
#<li>#plih_rocq_ds_shared.v      -- shared infra (Arith, Bool, Lia)#</li>#
#<li>#plih_ds_lecture.v          -- lecture: IntList, HOFs, PList, isomorphism, A*B, A+B, records, sums-of-products#</li>#
#<li>#plih_ds_exercises.v        -- student problem set (Admitted stubs, 30 exercises)#</li>#
#<li>#plih_ds_solutions.v        -- complete solutions#</li>#
#<li>#plih_ds_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_ds_summary.v          -- this file#</li>#
#</ol>#
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Read plih_ds_lecture.v.#</li>#
#<li>#Work plih_ds_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_ds_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_ds_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEAS *)

(**
Recursive data and structural recursion are two sides of the same coin.
An [IntList] has exactly two cases ([Nil]/[Cons]) and every function on
[IntList] has exactly two cases matching those constructors.  The
_shape_ of the function is determined by the _shape_ of the type.
Higher-order functions expose that shape explicitly; generalizing the
element type from [nat] to any [A] then costs nothing.  The isomorphism
[IntList ≅ PList nat] formalizes this: integer lists and
polymorphic-nat lists are definitionally the same structure.

Two primitive operations build all inductive types:
  - [A * B] (product): "one of each" - pairs, tuples, records
  - [A + B] (sum): "one or the other" - tagged unions, variants

Every Rocq [Inductive] type is a sum of products: each constructor is
a product of its argument types, and the constructors are combined by
sum.  Records are products with named projections.  The [Shape] and
[Color] isomorphisms show this concretely.
 *)

(** * WHAT CARRIES OVER, WHAT IS NEW *)

(**
CARRIES OVER FROM EARLIER CHAPTERS:
  - [option] for partial observers ([car], [cdr]);
  - induction on inductive types (pattern: [Nil]/[Cons] split,
    use the IH in the [Cons] case, close with [reflexivity] or [lia]);
  - implicit type arguments ([{A : Type}]).

NEW HERE:
  - _Inductive types for data_: [IntList] and [PList A] - no
    interpreter, no environment, no fuel;
  - _Structural operations_: [length], [append], [reverse] and their
    key lemmas ([append_nil_r], [append_assoc], [length_append],
    [reverse_length]);
  - _Higher-order functions_: [map], [foldr], [foldl], [filter];
  - _Polymorphism_: [PList A] parameterised over the element type;
  - _Isomorphism_: [intToP]/[pToInt] and the four commutation lemmas;
  - _Product types_: [A * B], [pair]/[(a,b)], [fst]/[snd], [prod_eta];
  - _Sum types_: [A + B], [inl]/[inr], case analysis; [option A = unit + A];
  - _Records_: [Record] keyword, [{| field := v |}] construction, [p.(f)]
    projection; [point_eta]; [Point ≅ nat * nat];
  - _Sums of products_: [Shape = nat + (nat * nat)]; [Color = unit + (unit + unit)];
    the algebraic reading of every [Inductive].
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [IntList]             -- integer list type (Section 1)
  [car]/[cdr]/[isEmpty] -- LISP-style observers (Section 1)
  [length]/[append]/[reverse]      -- structural operations (Section 2)
  [append_nil_r], [append_assoc]   -- key lemmas (Section 2)
  [length_append], [reverse_length]-- key lemmas (Section 2)
  [map]/[foldr]/[foldl]/[filter]   -- higher-order functions (Section 3)
  [map_length], [filter_le_length] -- key lemmas (Section 3)
  [PList A]             -- polymorphic list type (Section 4)
  [pcar]/[pcdr]/[pisEmpty]         -- polymorphic observers (Section 4)
  [plength]/[pappend]/[preverse]   -- polymorphic structural ops (Section 4)
  [pmap]/[pfoldr]/[pfoldl]/[pfilter] -- polymorphic HOFs (Section 4)
  [intToP]/[pToInt]     -- the isomorphism (Section 5)
  [intToP_pToInt], [pToInt_intToP] -- inverse proofs (Section 5)
  [map_commutes], [foldr_commutes], [foldl_commutes], [filter_commutes]
                        -- HOFs respect the isomorphism (Section 5)
  [swap], [prod_eta]    -- products A*B (Section 6)
  [sumToNat], [optionToSum], [sumToOption] -- sums A+B (Section 7)
  [optionToSum_sumToOption], [sumToOption_optionToSum] -- option ≅ unit+A (Section 7)
  [Point]/[mkPoint]/[px]/[py]      -- record example (Section 8)
  [origin]/[point35], [translate]  -- record values and functions (Section 8)
  [point_eta], [pointToPair]/[pairToPoint] -- Point ≅ nat*nat (Section 8)
  [Shape]/[Circle]/[Rectangle]     -- sum-of-products example (Section 9)
  [shapeToAlg]/[algToShape]        -- Shape ≅ nat+(nat*nat) (Section 9)
  [shapeToAlg_algToShape], [algToShape_shapeToAlg] -- isomorphism proofs (Section 9)
 *)

(** * WHERE THIS GOES NEXT *)

(**
Lists are the foundation for more complex recursive structures: trees,
rose trees, association lists (already used in every interpreter chapter
as [Env]), queues, and graphs.  The same pattern - inductive type,
structural recursion, higher-order abstraction, polymorphism - scales
to all of them.  The algebraic reading extends too: a binary tree is
[unit + (A * Tree A * Tree A)] (leaf or node with two subtrees).

The deeper lesson connects back to the interpreter chapters.  [Env A =
list (string * A)] (introduced in the IDs chapter) IS a [PList (string
* A)] with identical structure.  The language types themselves - [FBAE],
[FBAEC], [FBAES] - are sums of products: each constructor is a product
of its subterm types, and the [Inductive] groups them all with [+].
Every proof by [induction e] in those chapters is exactly the sum-of-
products case analysis practiced here.
 *)
