(**
Programming Languages in Rocq - TADS Exercises
Typed Algebraic Data Structures - Student Problem Set

In these exercises you will:
#<ol>#
#<li>#Run the type checker on closed TADS terms.#</li>#
#<li>#Run the evaluator on closed TADS terms.#</li>#
#<li>#Prove typing judgements and identify ill-typed terms.#</li>#
#<li>#Work with product types ([Pair]/[Fst]/[Snd]).#</li>#
#<li>#Work with sum types ([InL]/[InR]/[SCase]).#</li>#
#<li>#Work with list types ([Nil]/[Cons]/[Car]/[Cdr]/[IsNil]).#</li>#
#<li>#Explore the algebraic representation of lists as sums of products.#</li>#
#<li>#Prove properties by induction ([Ty_eqb_refl], [evalM_mono] special case).#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: [Ty] ([TNum]/[TBool]/[TArr]/[TUnit]/[TProd]/[TSum]/[TList]),
[Ty_eqb], [Ty_eqb_refl], [Ty_eqb_eq], [Ty_eqb_true_iff]; [TADS] with all
constructors including [Unit]; [subst]; [typeof]/[typecheck]; [TVal] with
constructors [NumV]/[BoolV]/[ClosureV]/[UnitV]/[PairV]/[InLV]/[InRV]
(no [NilV] or [ConsV]); [evalM]/[eval]/[evalM_mono]; all definitions from
Sections 5-10.

Key fact: list values are sum/product values.
  [eval (Nil T)    = Some (InLV UnitV)]
  [eval (Cons h t) = Some (InRV (PairV vh vt))]

Difficulty: * trivial (reflexivity or one tactic), ** a few steps,
*** multi-step proof.
Solutions are in plih_ds_solutions.v.
 *)

From Stdlib Require Import String.
Require Import plih_rocq_ds_shared.
Require Import plih_ds_lecture.

Local Open Scope string_scope.

(** * PART 1: RUNNING THE TYPE CHECKER *)

(* * A number has type [TNum]. *)
Example ex1_ty_num : typecheck (Num 42) = Some TNum.
Proof. Admitted.

(* * A pair of a number and a Boolean. *)
Example ex2_ty_pair :
  typecheck (Pair (Num 5) (Boolean true)) = Some (TProd TNum TBool).
Proof. Admitted.

(* * [Fst] extracts the first component's type. *)
Example ex3_ty_fst :
  typecheck (Fst (Pair (Num 1) (Boolean false))) = Some TNum.
Proof. Admitted.

(* * [Nil TBool] has type [TList TBool]. *)
Example ex4_ty_nil_bool :
  typecheck (Nil TBool) = Some (TList TBool).
Proof. Admitted.

(* * A two-element list of numbers. *)
Example ex5_ty_cons :
  typecheck (Cons (Num 3) (Cons (Num 4) (Nil TNum))) = Some (TList TNum).
Proof. Admitted.

(* * [IsNil] on a list produces a Boolean. *)
Example ex6_ty_isnil :
  typecheck (IsNil (Nil TNum)) = Some TBool.
Proof. Admitted.

(* * [InL] with a [TSum TNum TBool] annotation and a number body. *)
Example ex7_ty_inl :
  typecheck (InL (TSum TNum TBool) (Num 7)) = Some (TSum TNum TBool).
Proof. Admitted.

(* * [Unit] has type [TUnit]. *)
Example ex7b_ty_unit :
  typecheck Unit = Some TUnit.
Proof. Admitted.

(** * PART 2: RUNNING THE EVALUATOR *)

(* * Evaluate a literal pair. *)
Example ex8_eval_pair :
  eval (Pair (Num 10) (Num 20)) = Some (PairV (NumV 10) (NumV 20)).
Proof. Admitted.

(* * Evaluate [Fst] of a pair. *)
Example ex9_eval_fst :
  eval (Fst (Pair (Num 3) (Boolean true))) = Some (NumV 3).
Proof. Admitted.

(* * Evaluate [Snd] of a pair. *)
Example ex10_eval_snd :
  eval (Snd (Pair (Boolean false) (Num 99))) = Some (NumV 99).
Proof. Admitted.

(* * [IsNil] on a non-empty list is [false].  The list value is [InRV _]. *)
Example ex11_eval_isnil_cons :
  eval (IsNil (Cons (Num 1) (Nil TNum))) = Some (BoolV false).
Proof. Admitted.

(* * [Car] of a two-element list. *)
Example ex12_eval_car :
  eval (Car (Cons (Num 5) (Cons (Num 6) (Nil TNum)))) = Some (NumV 5).
Proof. Admitted.

(* * [Cdr] returns the tail.  The tail is itself a list value [InRV (PairV _ _)]. *)
Example ex13_eval_cdr :
  eval (Cdr (Cons (Num 1) (Cons (Num 2) (Nil TNum)))) =
  Some (InRV (PairV (NumV 2) (InLV UnitV))).
Proof. Admitted.

(* * [InL] evaluates to [InLV]. *)
Example ex14_eval_inl :
  eval (InL (TSum TNum TBool) (Num 42)) = Some (InLV (NumV 42)).
Proof. Admitted.

(* * [InR] evaluates to [InRV]. *)
Example ex15_eval_inr :
  eval (InR (TSum TNum TBool) (Boolean true)) = Some (InRV (BoolV true)).
Proof. Admitted.

(** * PART 3: TYPING JUDGEMENTS *)

(* * [Snd] extracts the second component's type. *)
Example ex16_ty_snd :
  typecheck (Snd (Pair (Boolean true) (Num 8))) = Some TNum.
Proof. Admitted.

(* * [Car] on a list of Booleans gives [TBool]. *)
Example ex17_ty_car_bool :
  typecheck (Car (Cons (Boolean true) (Nil TBool))) = Some TBool.
Proof. Admitted.

(* * The type checker rejects [Car] on a non-list. *)
Example ex18_ill_car_num :
  typecheck (Car (Num 5)) = None.
Proof. Admitted.

(* * The type checker rejects [Cons] with mismatched element types. *)
Example ex19_ill_cons_mismatch :
  typecheck (Cons (Boolean true) (Nil TNum)) = None.
Proof. Admitted.

(* ** [SCase] with matching branch types. *)
Example ex20_ty_scase :
  typecheck
    (SCase (InL (TSum TNum TBool) (Num 5))
           "n" (Id "n")
           "b" (Num 0))
  = Some TNum.
Proof. Admitted.

(* ** The type checker rejects [SCase] with mismatched branch types. *)
Example ex21_ill_scase_mismatch :
  typecheck
    (SCase (InL (TSum TNum TBool) (Num 5))
           "n" (Id "n")
           "b" (Boolean false))
  = None.
Proof. Admitted.

(** * PART 4: PRODUCTS *)

(**
Define [tripleFirst] that takes a pair of pairs and returns the leftmost
number: [Fst (Fst p)] where [p : TProd (TProd TNum TNum) TNum].
 *)

(* ** Fill in the body. *)
Definition tripleFirst : TADS :=
  Lambda "p" (TProd (TProd TNum TNum) TNum)
    (Fst (Fst (Id "p"))).

(* * Type-check [tripleFirst]. *)
Example ex22_ty_tripleFirst :
  typecheck tripleFirst = Some (TArr (TProd (TProd TNum TNum) TNum) TNum).
Proof. Admitted.

(* * Evaluate [tripleFirst] applied to a nested pair. *)
Example ex23_run_tripleFirst :
  eval (App tripleFirst (Pair (Pair (Num 7) (Num 8)) (Num 9)))
  = Some (NumV 7).
Proof. Admitted.

(**
[swapTy] is the type of a swap function: [(A * B) -> (B * A)] for
[A = TNum], [B = TBool].
 *)

(* * Confirm the swap program type-checks with the right type. *)
Example ex24_ty_swap :
  typecheck
    (Lambda "p" (TProd TNum TBool)
       (Pair (Snd (Id "p")) (Fst (Id "p"))))
  = Some (TArr (TProd TNum TBool) (TProd TBool TNum)).
Proof. Admitted.

(** * PART 5: SUMS *)

(**
[safeHead] takes a list of numbers and returns [TSum TNum TBool]:
[InL] wrapping the head if the list is non-empty, or [InR (Boolean true)]
as an error flag if the list is empty.
 *)

Definition safeHead : TADS :=
  Lambda "xs" (TList TNum)
    (If (IsNil (Id "xs"))
        (InR (TSum TNum TBool) (Boolean true))
        (InL (TSum TNum TBool) (Car (Id "xs")))).

(* ** Type-check [safeHead]. *)
Example ex25_ty_safeHead :
  typecheck safeHead = Some (TArr (TList TNum) (TSum TNum TBool)).
Proof. Admitted.

(* ** Evaluate [safeHead] on a non-empty list. *)
Example ex26_run_safeHead_cons :
  eval (App safeHead (Cons (Num 42) (Nil TNum)))
  = Some (InLV (NumV 42)).
Proof. Admitted.

(* ** Evaluate [safeHead] on the empty list. *)
Example ex27_run_safeHead_nil :
  eval (App safeHead (Nil TNum))
  = Some (InRV (BoolV true)).
Proof. Admitted.

(** * PART 6: LISTS *)

(**
[doubleList] maps [n -> n * 2] over a list of numbers using [Fix].
Its generator takes [g] (the recursive call) and [xs] (the list).
 *)

Definition doubleGen : TADS :=
  Lambda "g" (TArr (TList TNum) (TList TNum))
    (Lambda "xs" (TList TNum)
      (If (IsNil (Id "xs"))
          (Nil TNum)
          (Cons (Mult (Car (Id "xs")) (Num 2))
                (App (Id "g") (Cdr (Id "xs")))))).

Definition doubleList : TADS := Fix doubleGen.

(* ** Type-check [doubleList]. *)
Example ex28_ty_doubleList :
  typecheck doubleList = Some (TArr (TList TNum) (TList TNum)).
Proof. Admitted.

(**
Apply [doubleList] to [1; 2; 3].  The result [2; 4; 6] is represented as
a sum/product tree since list values are [InRV (PairV _ _)] cells.
 *)

(* ** The result of doubling [1; 2; 3] is [2; 4; 6] as a sum/product tree. *)
Example ex29_run_doubleList :
  eval (App doubleList list123) =
  Some (InRV (PairV (NumV 2)
       (InRV (PairV (NumV 4)
       (InRV (PairV (NumV 6) (InLV UnitV))))))).
Proof. Admitted.

(* ** The [sumList] from the lecture sums [1 + 2 + 3 = 6]. *)
Example ex30_run_sumList :
  eval (App sumList list123) = Some (NumV 6).
Proof. Admitted.

(** * PART 7: LISTS AS SUMS OF PRODUCTS *)

(**
These exercises explore the algebraic representation of list values.
A list is either empty (left-injected unit) or a cons cell
(right-injected pair of head and tail).
 *)

(* * The empty list evaluates to left-injected unit. *)
Example ex31_nil_rep :
  eval (Nil TNum) = Some (InLV UnitV).
Proof. Admitted.

(* * A singleton list evaluates to a right-injected pair. *)
Example ex32_cons_rep :
  eval (Cons (Num 7) (Nil TNum)) =
  Some (InRV (PairV (NumV 7) (InLV UnitV))).
Proof. Admitted.

(**
Because [Nil TNum] evaluates to [InLV UnitV], and [SCase] matches on
[InLV _] / [InRV _], we can use [SCase] directly on a list.
 *)

(* ** [SCase] on a nil list takes the left branch (unit payload). *)
Example ex33_scase_on_nil :
  eval (SCase (Nil TNum) "u" (Num 0) "p" (Fst (Id "p"))) =
  Some (NumV 0).
Proof. Admitted.

(* ** [SCase] on a cons list takes the right branch (pair payload). *)
Example ex34_scase_on_cons :
  eval (SCase (Cons (Num 99) (Nil TNum))
              "u" (Num 0)
              "p" (Fst (Id "p"))) =
  Some (NumV 99).
Proof. Admitted.

(** * PART 8: INDUCTIONS *)

(**
The next two exercises ask you to prove properties of the TADS
infrastructure by induction.
 *)

(* ** [Ty_eqb] is reflexive for every [Ty].
   Induct on [t].  For [TArr], [TProd], [TSum]: [rewrite] both IHs then
   [reflexivity].  For [TList]: [rewrite] the single IH then [reflexivity].
   [TUnit] is nullary -- [reflexivity] closes it immediately. *)
Lemma ex35_Ty_eqb_refl : forall t, Ty_eqb t t = true.
Proof. Admitted.

(* *** A special case of [evalM_mono]: if the fuel is [S k] and the term
   is [Pair e1 e2], and [evalM (S k) env (Pair e1 e2) = Some v], then
   [evalM (S (S k)) env (Pair e1 e2) = Some v].

   Hint: use [evalM_mono] with [f1 := S k], [f2 := S (S k)], [Hle :=
   le_S _ _ (le_refl _)] (or [lia]) and the given hypothesis. *)
Lemma ex36_mono_pair : forall k env e1 e2 v,
  evalM (S k) env (Pair e1 e2) = Some v ->
  evalM (S (S k)) env (Pair e1 e2) = Some v.
Proof. Admitted.
