(**
Programming Languages in Rocq - Untyped Recursion Exercises
Recursion via fixpoint combinators - Student Problem Set

In these exercises you will:
#<ol>#
#<li>#Run the strict [evalM] and lazy [evalL] interpreters for FBAEC#</li>#
#<li>#Drive PRODUCTIVE recursion with the Z (strict) and Y (lazy)
fixpoint combinators, and watch strict Y diverge#</li>#
#<li>#Use FUEL MONOTONICITY and simple value/branch laws#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: the language [FBAEC]; the value types [RVal]
([NumV]/[BoolV]/[ClosureV]) and [LVal] ([LNumV]/[LBoolV]/[LCloV]); the
interpreters [evalM] (strict) and [evalL] (lazy) with wrappers [eval]
and [evalLazy]; [evalM_mono]; the combinators [Yc]/[Zc]; and the
generators [sumGen]/[factGen].  [lookup]/[extend] come from the shared
library.

NOTE ON FUEL.  Keep fuel a VARIABLE whenever the term is abstract - a
literal fuel forces the kernel to unroll [evalM] and can blow up.  A
literal fuel is fine only on a CONCRETE closed term (it computes to a
value and stops).

Difficulty: ★ trivial, ★★ a lemma citation, ★★★ short proof.
Solutions are in plih_rec_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rec_shared.
Require Import plih_rec_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE INTERPRETERS *)

(* ★ Strict arithmetic. *)
Example ex1_arith : eval (Minus (Mult (Num 3) (Num 4)) (Num 2)) = Some (NumV 10).
Proof. Admitted.

(* ★ The conditional takes only the selected branch. *)
Example ex2_if : eval (If (IsZero (Num 3)) (Num 0) (Num 9)) = Some (NumV 9).
Proof. Admitted.

(* ★ Summation 0..3 = 6 via the Z combinator under strict evaluation. *)
Example ex3_sum3 : eval (App (App Zc sumGen) (Num 3)) = Some (NumV 6).
Proof. Admitted.

(* ★ Factorial 4 = 24 via the Z combinator under strict evaluation. *)
Example ex4_fact4 : eval (App (App Zc factGen) (Num 4)) = Some (NumV 24).
Proof. Admitted.

(* ★ Under LAZY evaluation the plain Y combinator computes factorial. *)
Example ex5_fact4_lazy : evalLazy (App (App Yc factGen) (Num 4)) = Some (LNumV 24).
Proof. Admitted.

(* ★ Under STRICT evaluation the plain Y combinator diverges. *)
Example ex6_Y_strict_diverges :
  evalM 100 nil (App (App Yc factGen) (Num 4)) = None.
Proof. Admitted.

(** * PART 2: VALUE AND BRANCH LAWS *)

(* ★ A Boolean literal evaluates to itself (given positive fuel). *)
Example ex7_boolean : forall k env b,
  evalM (S k) env (Boolean b) = Some (BoolV b).
Proof. Admitted.

(* ★ With a true condition, [If] reduces to its then-branch. *)
Example ex8_if_true : forall k env t f,
  evalM (S k) env (If (Boolean true) t f) = evalM k env t.
Proof. Admitted.

(** * PART 3: FUEL MONOTONICITY *)

(* ★★ Adding fuel cannot change an answer.  Cite [evalM_mono].  Keep
   the fuel a VARIABLE - do not instantiate it to a literal. *)
Example ex9_more_fuel : forall f env e v,
  evalM f env e = Some v -> evalM (f + 10) env e = Some v.
Proof. Admitted.

(* ★★★ The strict interpreter is deterministic for fixed fuel. *)
Example ex10_deterministic : forall f env e r1 r2,
  evalM f env e = r1 -> evalM f env e = r2 -> r1 = r2.
Proof. Admitted.

(** * PART 4: CONCRETE SYNTAX *)

(**
FBAEC has its own notation-based parser (Section 8): Func's grammar plus
[*], [true]/[false], [iszero e], and [if c then t else f].  We open its
scope to use it here.
 *)

Open Scope fbaec_scope.

(* ★ [iszero] and [if] parse to the expected tree. *)
Example ex11_parse_if :
  <{ if iszero 0 then 1 else 2 }> = If (IsZero (Num 0)) (Num 1) (Num 2).
Proof. Admitted.

(* ★ evaluation is oblivious to the notation. *)
Example ex12_eval_mult : eval <{ 6 * (3 + 4) }> = Some (NumV 42).
Proof. Admitted.

(* ★★ the productive recursion of Section 7, concretely: the Z
   combinator ties the knot and factorial runs under strict eval. *)
Example ex13_fact_Z : eval <{ Zc factGen 5 }> = Some (NumV 120).
Proof. Admitted.

(* ★★ the recursive generator reads as on paper.  Hint: [reflexivity]. *)
Example ex14_sumGen_concrete :
  <{ lambda "g" in lambda "z" in
       if iszero "z" then "z" else "z" + "g" ("z" - 1) }> = sumGen.
Proof. Admitted.
