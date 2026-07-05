(**
Programming Languages in Rocq - Reader+State Monad Exercises
Combined Reader + State interpreter - Student Problem Set

In these exercises you will:
  1. Run the combined-monad interpreter [evalRS]/[evalReaderState],
     exercising both static scoping (Reader) and mutable cells (State)
  2. Use the AGREEMENT theorem to transport results to the explicit
     interpreter
  3. Prove monad laws and effect-independence facts

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: the language [FBAES]; values [RVal] and the
[Store]; the explicit interpreter [evalM]/[eval]; the combined monad
[RS]/[retRS]/[bindRS]/[askRS]/[localRS]/[getRS]/[putRS]/[failRS]/[runRS]
with [;;]; the monadic interpreter [evalRS]/[evalReaderState]; and the
theorems [evalRS_agrees] and [evalReaderState_agrees].

Difficulty: ★ trivial, ★★ a lemma citation, ★★★ short proof.
Solutions are in plih_rsmon_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rsmon_shared.
Require Import plih_rsmon_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE COMBINED INTERPRETER *)

(* ★ Pure arithmetic leaves the store empty. *)
Example ex1_arith :
  evalReaderState (Minus (Mult (Num 3) (Num 4)) (Num 2)) = Some (NumV 10, nil).
Proof. Admitted.

(* ★ STATIC SCOPING: the closure [f] captures [x = 5] at definition time,
   so rebinding [x] to 99 before the call does not change the result. *)
Example ex2_static_scope :
  evalReaderState (Bind "x" (Num 5)
                     (Bind "f" (Lambda "y" (Id "x"))
                        (Bind "x" (Num 99)
                           (App (Id "f") (Num 0)))))
  = Some (NumV 5, nil).
Proof. Admitted.

(* ★ A cell round-trip: allocate 0, write 42, read it back. *)
Example ex3_roundtrip :
  evalReaderState (Bind "r" (New (Num 0))
                     (Seq (Assign (Id "r") (Num 42))
                          (Deref (Id "r"))))
  = Some (NumV 42, [NumV 42]).
Proof. Admitted.

(* ★ SCOPING AND STATE together: a captured cell survives the call. *)
Example ex4_scope_and_state :
  evalReaderState (Bind "r" (New (Num 100))
                     (Bind "f" (Lambda "n" (Assign (Id "r") (Id "n")))
                        (Seq (App (Id "f") (Num 7))
                             (Deref (Id "r")))))
  = Some (NumV 7, [NumV 7]).
Proof. Admitted.

(** * PART 2: AGREEMENT IN ACTION *)

(* ★★ The combined-monad wrapper agrees with the explicit one on this
   program.  Cite [evalReaderState_agrees]. *)
Example ex5_wrapper_agrees :
  evalReaderState (App (Lambda "x" (Id "x")) (Num 5))
  = eval (App (Lambda "x" (Id "x")) (Num 5)).
Proof. Admitted.

(* ★★ Agreement holds at ANY fuel, environment, and store.  Cite
   [evalRS_agrees]. *)
Example ex6_agrees_general : forall env e s,
  evalRS 9 e env s = evalM 9 env s e.
Proof. Admitted.

(* ★★★ Agreement transports a result from the monadic interpreter to the
   explicit one.  Hint: [rewrite <- evalReaderState_agrees]. *)
Example ex7_transport : forall e v s',
  evalReaderState e = Some (v, s') -> eval e = Some (v, s').
Proof. Admitted.

(** * PART 3: MONAD LAWS AND EFFECT INTERACTION *)

(* ★ LEFT IDENTITY: binding a pure value just runs the continuation. *)
Example ex8_left_id : forall (A B : Type) (a : A) (f : A -> RS (Env RVal) Store B),
  bindRS (retRS a) f = f a.
Proof. Admitted.

(* ★★ Reading the environment leaves the store untouched. *)
Example ex9_ask_pure : forall (env : Env RVal) (s : Store),
  runRS askRS env s = Some (env, s).
Proof. Admitted.

(* ★★ PUT-THEN-GET (the State part, inside the combined monad): reading
   right after a write returns what was written, for any environment. *)
Example ex10_put_get : forall (env : Env RVal) (s0 s' : Store),
  runRS (bindRS (putRS s') (fun _ => getRS)) env s0 = Some (s', s').
Proof. Admitted.

(** * PART 4: CONCRETE SYNTAX *)

(**
[FBAES] gets the State chapter's notation parser (Rec's grammar plus
[new e], [! e], [l := e], [a ; b]).  Read the concrete programs through
the combined-monad interpreter [evalReaderState].  Recall [!] binds
tighter than [+], and [;] is loosest and right-associative.
 *)

Open Scope rsmon_scope.

(* ★ dereference binds tighter than [+]. *)
Example ex11_deref_prec :
  <{ ! "r" + 1 }> = Plus (Deref (Id "r")) (Num 1).
Proof. Admitted.

(* ★★ the concrete round-trip runs under the combined-monad interpreter. *)
Example ex12_roundtrip :
  evalReaderState <{ bind "r" = new 5 in "r" := !"r" + 1 ; !"r" }>
  = Some (NumV 6, [NumV 6]).
Proof. Admitted.

(* ★★ static scoping and state together, concretely: the closure captures
   cell [r], and its write is visible afterward. *)
Example ex13_scope_and_state :
  evalReaderState
    <{ bind "r" = new 1 in
         bind "f" = (lambda "n" in "r" := !"r" + "n") in
           "f" 10 ; !"r" }>
  = Some (NumV 11, [NumV 11]).
Proof. Admitted.
