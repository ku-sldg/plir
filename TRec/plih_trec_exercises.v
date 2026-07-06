(**
Programming Languages in Rocq - Typed Recursion Exercises
A primitive typed [Fix] - Student Problem Set

In these exercises you will:
#<ol>#
#<li>#Type-check recursive programs, and see [Fix] rejected when its
argument is not a [T -> T] function (and self-application rejected)#</li>#
#<li>#RUN typed recursion (factorial, summation) and watch a well-typed
[Fix] DIVERGE#</li>#
#<li>#Use the metatheory: fuel monotonicity, canonical forms, determinism#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: the types [Ty] ([TNum]/[TBool]/[TArr]) with
[Ty_eqb] (+ [Ty_eqb_refl]/[Ty_eqb_eq]); the term language [TFBAEC] (now
with [Fix]) and [subst]; the checker [typeof]/[typecheck]; the values
[TVal] ([NumV]/[BoolV]/[ClosureV]); the strict interpreter
[evalM]/[eval]; [evalM_mono]; [isNumV]/[isBoolV] with
[iszero_yields_bool]/[mult_yields_num]; and the sample terms
[factGen]/[fact], [sumGen]/[sum], [selfApp], [loopT].

NOTE ON FUEL.  Keep fuel a VARIABLE whenever the term is abstract - a
literal fuel forces the kernel to unroll [evalM] and can blow up.  A
literal fuel is fine only on a CONCRETE closed term.

Difficulty: ★ trivial, ★★ a lemma citation, ★★★ short proof.
Solutions are in plih_trec_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_trec_shared.
Require Import plih_trec_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: TYPING RECURSION *)

(* ★ Applying factorial to a number has type [TNum]. *)
Example ex1_ty_fact_app : typecheck (App fact (Num 3)) = Some TNum.
Proof. Admitted.

(* ★ [Fix] needs a [T -> T] argument: a [Nat -> Bool] function is
   rejected (domain and range disagree). *)
Example ex2_reject_fix_mismatch :
  typecheck (Fix (Lambda "x" TNum (IsZero (Id "x")))) = None.
Proof. Admitted.

(* ★ Self-application is still untypable - [Fix] is the only loop. *)
Example ex3_reject_selfApp : typecheck (selfApp TNum) = None.
Proof. Admitted.

(* ★ Type checking under a nonempty context: with [g : Nat -> Nat]
   in scope, [g 1] has type [TNum]. *)
Example ex4_ty_ctx :
  typeof (extend "g" (TArr TNum TNum) nil) (App (Id "g") (Num 1)) = Some TNum.
Proof. Admitted.

(** * PART 2: RUNNING RECURSION *)

(* ★ Factorial actually computes: 3! = 6. *)
Example ex5_fact3 : eval (App fact (Num 3)) = Some (NumV 6).
Proof. Admitted.

(* ★ Summation: 0..4 = 10. *)
Example ex6_sum4 : eval (App sum (Num 4)) = Some (NumV 10).
Proof. Admitted.

(* ★ A well-typed term can DIVERGE now: [loopT] exhausts the fuel. *)
Example ex7_loop_diverges : evalM 200 nil loopT = None.
Proof. Admitted.

(** * PART 3: METATHEORY *)

(* ★★ Adding fuel cannot change an answer.  Cite [evalM_mono]; keep the
   fuel a VARIABLE. *)
Example ex8_more_fuel : forall f env e v,
  evalM f env e = Some v -> evalM (f + 7) env e = Some v.
Proof. Admitted.

(* ★★ Whenever [Mult _ _] produces a value, it is a number.  Cite
   [mult_yields_num]. *)
Example ex9_mult_num : forall f env a b v,
  evalM f env (Mult a b) = Some v -> isNumV v = true.
Proof. Admitted.

(* ★★★ The strict interpreter is deterministic for fixed fuel. *)
Example ex10_deterministic : forall f env e r1 r2,
  evalM f env e = r1 -> evalM f env e = r2 -> r1 = r2.
Proof. Admitted.

(** * PART 4: CONCRETE SYNTAX *)

(**
The lecture added two notations (Section 9): types between [<[ ... ]>]
([Nat], [Bool], the right-associative [->]), and terms between
[<{ ... }>] - the ascribed lambda [lambda ID : T in body] plus the new
prefix [fix f].  We open the scope to use them here.
 *)

Open Scope trec_scope.

(* ★ the function arrow is right-associative. *)
Example ex11_parse_ty :
  <[ (Nat -> Nat) -> Nat -> Nat ]> = TArr (TArr TNum TNum) (TArr TNum TNum).
Proof. Admitted.

(* ★ [fix (lambda ...)] parses to [Fix (Lambda ...)] - this is [loopT]. *)
Example ex12_parse_fix :
  <{ fix (lambda "x" : Nat in "x") }> = loopT.
Proof. Admitted.

(* ★★ the checker reads the concrete factorial and predicts [Nat -> Nat]. *)
Example ex13_typecheck_fact :
  typecheck <{ fix (lambda "g" : Nat -> Nat in
                      lambda "n" : Nat in
                        if iszero "n" then 1 else "n" * ("g" ("n" - 1))) }>
  = Some <[ Nat -> Nat ]>.
Proof. Admitted.

(* ★★ and the same concrete term runs: 4! = 24. *)
Example ex14_eval_fact :
  eval <{ (fix (lambda "g" : Nat -> Nat in
                  lambda "n" : Nat in
                    if iszero "n" then 1 else "n" * ("g" ("n" - 1)))) 4 }>
  = Some (NumV 24).
Proof. Admitted.
