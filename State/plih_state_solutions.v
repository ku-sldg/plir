(**
Programming Languages in Rocq - Mutable State Solutions
Complete solutions to plih_state_exercises.v

The language [FBAES], the store-threading interpreter [evalM] with
wrapper [eval], the metatheorem [evalM_mono], the derived forms
[MutBind]/[Get]/[SetVar], and the combinator [Zc] come from the Mutable
State lecture; [update_at]/[update_at_length]/[nth_error_snoc] come from
the shared library.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_state_shared.
Require Import plih_state_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE INTERPRETER *)

Example ex1_arith : eval (Plus (Num 2) (Num 3)) = Some (NumV 5, nil).
Proof. reflexivity. Qed.

Example ex2_new : eval (New (Num 9)) = Some (LocV 0, [NumV 9]).
Proof. reflexivity. Qed.

Example ex3_roundtrip :
  eval (Bind "r" (New (Num 0))
          (Seq (Assign (Id "r") (Num 42))
               (Deref (Id "r"))))
  = Some (NumV 42, [NumV 42]).
Proof. reflexivity. Qed.

Example ex4_aliasing :
  eval (MutBind "r" (Num 5)
          (Bind "a" (Id "r")
             (Seq (SetVar "a" (Num 8))
                  (Get "r"))))
  = Some (NumV 8, [NumV 8]).
Proof. reflexivity. Qed.

Example ex5_two_cells :
  eval (Bind "p" (New (Num 1))
          (Bind "q" (New (Num 2))
             (Seq (Assign (Id "p") (Num 9))
                  (Deref (Id "q")))))
  = Some (NumV 2, [NumV 9; NumV 2]).
Proof. reflexivity. Qed.

(** * PART 2: DERIVED FORMS AND VALUE LAWS *)

Example ex6_mutvar :
  eval (MutBind "n" (Num 10)
          (Seq (SetVar "n" (Minus (Get "n") (Num 3)))
               (Get "n")))
  = Some (NumV 7, [NumV 7]).
Proof. reflexivity. Qed.

Example ex7_num : forall k env st n,
  evalM (S k) env st (Num n) = Some (NumV n, st).
Proof. reflexivity. Qed.

(* [Id x] reads the environment and passes the store through unchanged:
   after [simpl] the goal is [match lookup x env with ... end]; rewrite
   the lookup hypothesis to select the [Some] branch. *)
Example ex8_id : forall k env st x v,
  lookup x env = Some v ->
  evalM (S k) env st (Id x) = Some (v, st).
Proof. intros k env st x v H. simpl. rewrite H. reflexivity. Qed.

(** * PART 3: METATHEORY AND THE STORE *)

Example ex9_more_fuel : forall f env st e p,
  evalM f env st e = Some p -> evalM (f + 10) env st e = Some p.
Proof.
  intros f env st e p H.
  apply (evalM_mono f (f + 10) env st e p); [lia | exact H].
Qed.

Example ex10_deterministic : forall f env st e r1 r2,
  evalM f env st e = r1 -> evalM f env st e = r2 -> r1 = r2.
Proof. intros f env st e r1 r2 H1 H2. rewrite <- H1, <- H2. reflexivity. Qed.

Example ex11_write_length : forall n v (xs ys : Store),
  update_at n v xs = Some ys -> length ys = length xs.
Proof. intros n v xs ys H. exact (update_at_length n v xs ys H). Qed.

Example ex12_fresh_read : forall (xs : Store) (v : RVal),
  nth_error (xs ++ [v])%list (length xs) = Some v.
Proof. intros xs v. apply nth_error_snoc. Qed.

(** * PART 4: CONCRETE SYNTAX *)

Open Scope state_scope.

(* ex13: [!] binds tighter than [+]. *)
Example ex13_deref_prec :
  <{ ! "r" + 1 }> = Plus (Deref (Id "r")) (Num 1).
Proof. reflexivity. Qed.

(* ex14: [;] is right-associative. *)
Example ex14_seq_assoc :
  <{ !"a" ; !"b" ; !"c" }>
  = Seq (Deref (Id "a")) (Seq (Deref (Id "b")) (Deref (Id "c"))).
Proof. reflexivity. Qed.

(* ex15: the concrete round-trip evaluates. *)
Example ex15_roundtrip :
  eval <{ bind "r" = new 5 in "r" := !"r" + 1 ; !"r" }>
  = Some (NumV 6, [NumV 6]).
Proof. reflexivity. Qed.

(* ex16: bump the same cell twice, read it. *)
Example ex16_counter :
  eval <{ bind "c" = new 0 in
            "c" := !"c" + 1 ; "c" := !"c" + 1 ; !"c" }>
  = Some (NumV 2, [NumV 2]).
Proof. reflexivity. Qed.
