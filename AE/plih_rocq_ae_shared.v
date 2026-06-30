(**
 * Programming Languages in Rocq
 * Shared Interpreter Infrastructure
 * 
 * This module defines reusable components for building and proving
 * properties about language interpreters.
 *)

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

(* ================================================================ *)
(* PART 1: Monadic Operations                                       *)
(* ================================================================ *)

(* The option monad for error handling *)
Definition M (A : Type) := option A.

Definition return_ {A : Type} (x : A) : M A := Some x.

Definition bind {A B : Type} (m : M A) (f : A -> M B) : M B :=
  match m with
  | None => None
  | Some x => f x
  end.

(* Syntactic sugar for monadic binding *)
Notation "m >>= f" := (bind m f) (at level 50, left associativity).

(* Lift a binary operation into the monad *)
Definition liftM2 {A B C : Type} (op : A -> B -> C) (m1 : M A) (m2 : M B) : M C :=
  match m1, m2 with
  | Some x, Some y => Some (op x y)
  | _,_ => None
  end.

(* ================================================================ *)
(* PART 2: Basic Monad Laws (Proven for Reference)                 *)
(* ================================================================ *)

Lemma monad_left_identity {A B : Type} (a : A) (f : A -> M B) :
  (return_ a >>= f) = f a.
Proof. reflexivity. Qed.

Lemma monad_right_identity {A : Type} (m : M A) :
  (m >>= return_) = m.
Proof. destruct m; reflexivity. Qed.

Lemma monad_assoc {A B C : Type} (m : M A) (f : A -> M B) (g : B -> M C) :
  ((m >>= f) >>= g) = (m >>= fun a => (f a >>= g)).
Proof. destruct m; reflexivity. Qed.

(* ================================================================ *)
(* PART 3: Decidable Equality for Basic Types                      *)
(* ================================================================ *)

Lemma nat_eq_dec : forall (n m : nat), {n = m} + {n <> m}.
Proof.
  apply eq_nat_dec.
Defined.
  
Lemma bool_eq_dec : forall (b1 b2 : bool), {b1 = b2} + {b1 <> b2}.
Proof.
  intros; destruct b1; destruct b2;
    try (left; reflexivity); right; discriminate.
Defined.

(* ================================================================ *)
(* PART 4: List Utilities                                           *)
(* ================================================================ *)

Definition Env A := list (string * A).

Definition extend {A : Type} (x : string) (v : A) (env : Env A) : Env A :=
  (x,v)::env.

Fixpoint lookup {A : Type} (x : string) (env : Env A) : option A :=
  match env with
  | nil => None
  | ((y,v)::e') => if (String.eqb x y) then Some v else lookup x e'
  end.
                            
(* Key lemmas for environments *)

Lemma lookup_extend_eq {A : Type} : forall x v (env : Env A),
  lookup x (extend x v env) = Some v.
Proof.
  intros x v env.
  induction env.
  -- simpl. rewrite eqb_refl. reflexivity.
  -- simpl. rewrite eqb_refl. reflexivity.
Qed.

Lemma lookup_extend_ne {A : Type} : forall x y v (env : Env A),
  (eqb x y)=false ->
  lookup x (extend y v env) = lookup x env.
Proof.
  intros x y v env Hne.
  induction env.
  -- simpl. rewrite Hne. reflexivity.
  -- simpl. rewrite Hne. reflexivity.
Qed.

Lemma lookup_none_extend {A : Type} : forall x y v (env : Env A),
  lookup x env = None ->
  (if String.eqb x y then Some v else None) = 
  (if String.eqb x y then Some v else lookup x env).
Proof.
  intros x y v env Hlookup.
  rewrite Hlookup.
  destruct (String.eqb x y); reflexivity.
Qed.

(* ================================================================ *)
(* PART 5: Exported Interface                                       *)
(* ================================================================ *)

(* Make these available to students *)
Export List.
Export Nat.
