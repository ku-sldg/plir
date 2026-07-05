(**
Programming Languages in Rocq - State Monad Exercises
Structuring the interpreter with a State monad - Student Problem Set

In these exercises you will:
  1. Run the monadic interpreter [evalS]/[evalStore] on cell programs
  2. Use the AGREEMENT theorem to transport results between the monadic
     and explicit interpreters
  3. Prove the State-monad laws that hold definitionally

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: the language [FBAES]; values [RVal]
([NumV]/[BoolV]/[ClosureV]/[LocV]) and the [Store]; the explicit
interpreter [evalM]/[eval]; the State monad [State]/[retS]/[bindS]/
[getS]/[putS]/[failS]/[runState] with [;;]; the monadic interpreter
[evalS]/[evalStore]; and the theorems [evalS_agrees] and
[evalStore_agrees].

Difficulty: ★ trivial, ★★ a lemma citation, ★★★ short proof.
Solutions are in plih_smon_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_smon_shared.
Require Import plih_smon_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE MONADIC INTERPRETER *)

(* ★ Pure arithmetic leaves the store empty. *)
Example ex1_arith :
  evalStore (Minus (Mult (Num 3) (Num 4)) (Num 2)) = Some (NumV 10, nil).
Proof. Admitted.

(* ★ A cell round-trip: allocate 0, write 42, read it back. *)
Example ex2_roundtrip :
  evalStore (Bind "r" (New (Num 0))
               (Seq (Assign (Id "r") (Num 42))
                    (Deref (Id "r"))))
  = Some (NumV 42, [NumV 42]).
Proof. Admitted.

(* ★ Distinct cells are independent: writing [p] does not disturb [q]. *)
Example ex3_two_cells :
  evalStore (Bind "p" (New (Num 1))
               (Bind "q" (New (Num 2))
                  (Seq (Assign (Id "p") (Num 9))
                       (Deref (Id "q")))))
  = Some (NumV 2, [NumV 9; NumV 2]).
Proof. Admitted.

(** * PART 2: AGREEMENT IN ACTION *)

(* ★★ The monadic wrapper agrees with the explicit one on this program.
   Cite [evalStore_agrees]. *)
Example ex4_wrapper_agrees :
  evalStore (New (Num 5)) = eval (New (Num 5)).
Proof. Admitted.

(* ★★ Agreement holds at ANY fuel, environment, and store.  Cite
   [evalS_agrees]. *)
Example ex5_agrees_general : forall env e s,
  evalS 7 env e s = evalM 7 env s e.
Proof. Admitted.

(* ★★★ Agreement transports a result from the monadic interpreter to the
   explicit one.  Hint: [rewrite <- evalStore_agrees]. *)
Example ex6_transport : forall e v s',
  evalStore e = Some (v, s') -> eval e = Some (v, s').
Proof. Admitted.

(** * PART 3: MONAD LAWS *)

(* ★ LEFT IDENTITY: binding a pure value just runs the continuation. *)
Example ex7_left_id : forall (A B : Type) (a : A) (f : A -> State Store B),
  bindS (retS a) f = f a.
Proof. Admitted.

(* ★★ FAILURE SHORT-CIRCUITS: binding after a failure fails. *)
Example ex8_fail_bind : forall (f : RVal -> State Store RVal),
  bindS failS f = failS.
Proof. Admitted.

(* ★ PUT-PUT: a second [putS] overwrites the first. *)
Example ex9_put_put : forall (s1 s2 : Store),
  bindS (putS s1) (fun _ => putS s2) = putS s2.
Proof. Admitted.

(* ★★ PUT-THEN-GET: reading right after a write returns what was written. *)
Example ex10_put_get : forall (s0 s' : Store),
  runState (bindS (putS s') (fun _ => getS)) s0 = Some (s', s').
Proof. Admitted.

(** * PART 4: CONCRETE SYNTAX *)

(**
[FBAES] gets the same notation parser as the State chapter: Rec's
grammar plus [new e], [! e], [l := e], [a ; b].  Read the concrete
programs through the MONADIC interpreter [evalStore].  Recall [!] binds
tighter than [+], and [;] is loosest and right-associative.
 *)

Open Scope smon_scope.

(* ★ dereference binds tighter than [+]. *)
Example ex11_deref_prec :
  <{ ! "r" + 1 }> = Plus (Deref (Id "r")) (Num 1).
Proof. Admitted.

(* ★★ the concrete cell round-trip runs under the monadic interpreter. *)
Example ex12_roundtrip :
  evalStore <{ bind "r" = new 5 in "r" := !"r" + 1 ; !"r" }>
  = Some (NumV 6, [NumV 6]).
Proof. Admitted.

(* ★★ a concrete counter under [evalStore]: bump the same cell twice. *)
Example ex13_counter :
  evalStore <{ bind "c" = new 0 in
                 "c" := !"c" + 1 ; "c" := !"c" + 1 ; !"c" }>
  = Some (NumV 2, [NumV 2]).
Proof. Admitted.
