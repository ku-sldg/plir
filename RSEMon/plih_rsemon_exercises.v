(**
Programming Languages in Rocq - Reader+State+Either Monad Exercises
Three-effect interpreter - Student Problem Set

In these exercises you will:
#<ol>#
#<li>#Run the three-effect interpreter [evalRSErr], observing successes
([inr]) and DESCRIPTIVE error messages ([inl])#</li>#
#<li>#Use the REFINEMENT theorem to relate it to the explicit [evalM]#</li>#
#<li>#Prove monad laws and effect-interaction facts#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: the language [FBAES]; values [RVal] and the
[Store]; the explicit interpreter [evalM]/[eval]; the combined monad
[RSE]/[retRSE]/[bindRSE]/[askRSE]/[localRSE]/[getRSE]/[putRSE]/[throwRSE]/
[runRSE] with [;;]; [forget]; the monadic interpreter
[evalRSE]/[evalRSErr]; and the theorems [evalRSE_refines] /
[evalRSErr_refines].

Difficulty: ★ trivial, ★★ a lemma citation, ★★★ short proof.
Solutions are in plih_rsemon_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rsemon_shared.
Require Import plih_rsemon_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE THREE-EFFECT INTERPRETER *)

(* ★ A success carries value and store on the [inr] side. *)
Example ex1_arith :
  evalRSErr (Minus (Mult (Num 3) (Num 4)) (Num 2)) = inr (NumV 10, nil).
Proof. Admitted.

(* ★ A cell round-trip succeeds with the updated store. *)
Example ex2_roundtrip :
  evalRSErr (Bind "r" (New (Num 0))
               (Seq (Assign (Id "r") (Num 42))
                    (Deref (Id "r"))))
  = inr (NumV 42, [NumV 42]).
Proof. Admitted.

(* ★ An unbound identifier raises a descriptive message. *)
Example ex3_unbound :
  evalRSErr (Id "nope") = inl "unbound identifier".
Proof. Admitted.

(* ★ A type error in [Plus] is reported, not silently dropped. *)
Example ex4_type_error :
  evalRSErr (Plus (Num 1) (Boolean true)) = inl "plus: operands must be numbers".
Proof. Admitted.

(* ★ Dereferencing a non-location is reported. *)
Example ex5_not_a_location :
  evalRSErr (Deref (Boolean true)) = inl "deref: not a location".
Proof. Admitted.

(** * PART 2: REFINEMENT IN ACTION *)

(* ★★ Forgetting the message recovers the explicit [eval] on this
   program.  Cite [evalRSErr_refines]. *)
Example ex6_forget_ok :
  forget (evalRSErr (Bind "r" (New (Num 5)) (Deref (Id "r"))))
  = eval (Bind "r" (New (Num 5)) (Deref (Id "r"))).
Proof. Admitted.

(* ★★ Refinement holds at ANY fuel, environment, and store.  Cite
   [evalRSE_refines]. *)
Example ex7_refines_general : forall env e s,
  forget (evalRSE 9 e env s) = evalM 9 env s e.
Proof. Admitted.

(* ★★★ A successful [inr] result transports to a [Some] of the explicit
   interpreter.  Hint: [rewrite <- evalRSErr_refines], then use the
   hypothesis; [forget (inr p) = Some p] by computation. *)
Example ex8_transport : forall e p,
  evalRSErr e = inr p -> eval e = Some p.
Proof. Admitted.

(** * PART 3: MONAD LAWS AND EFFECT INTERACTION *)

(* ★ LEFT IDENTITY. *)
Example ex9_left_id : forall (A B : Type) (a : A) (f : A -> RSE (Env RVal) Store B),
  bindRSE (retRSE a) f = f a.
Proof. Admitted.

(* ★★ THE EITHER CHANNEL SHORT-CIRCUITS: nothing runs after a [throwRSE]. *)
Example ex10_throw_short_circuit :
  forall (B : Type) (msg : string) (f : RVal -> RSE (Env RVal) Store B),
    bindRSE (throwRSE msg) f = throwRSE msg.
Proof. Admitted.

(* ★★ ALL THREE CHANNELS AT ONCE: read the environment, write the store,
   return the environment value - each effect leaves the others intact. *)
Example ex11_three_channels : forall (env : Env RVal) (s s' : Store),
  runRSE (x <- askRSE ;; _ <- putRSE s' ;; retRSE x) env s = inr (env, s').
Proof. Admitted.

(** * PART 4: CONCRETE SYNTAX *)

(**
[FBAES] gets the State chapter's notation parser (Rec's grammar plus
[new e], [! e], [l := e], [a ; b]).  Read the concrete programs through
[evalRSErr]: a success lands on [inr], a stuck program on [inl] with a
descriptive message.  Recall [!] binds tighter than [+], and [;] is
loosest and right-associative.
 *)

Open Scope rsemon_scope.

(* ★ dereference binds tighter than [+]. *)
Example ex12_deref_prec :
  <{ ! "r" + 1 }> = Plus (Deref (Id "r")) (Num 1).
Proof. Admitted.

(* ★★ a concrete cell round-trip succeeds on the [inr] side. *)
Example ex13_roundtrip :
  evalRSErr <{ bind "r" = new 5 in "r" := !"r" + 1 ; !"r" }>
  = inr (NumV 6, [NumV 6]).
Proof. Admitted.

(* ★★ a concrete stuck program lands on [inl] with a descriptive message. *)
Example ex14_descriptive_error :
  evalRSErr <{ !"x" }> = inl "unbound identifier".
Proof. Admitted.
