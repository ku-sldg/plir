(**
Programming Languages in Rocq - State Shared Infrastructure
Mutable State (an explicit, threaded store)

This chapter mirrors the "Mutable State" unit of PLIH:
  https://ku-sldg.github.io/plih//state/

The Rec chapter gave us a Turing-powerful UNTYPED language (FBAEC) with
conditionals and recursion, but every binding was IMMUTABLE: [Bind] and
lambda application only ever EXTEND an environment, they never change a
value already stored.  Here we add genuine MUTATION with a STORE - a
heap of reference cells - and the interpreter must now THREAD that store
through evaluation, taking it in and handing a possibly-changed store
back out.  That read/write threading is the whole point of the chapter
(and, in the follow-on SMon chapter, the motivation for a State monad).

As with Rec, the language datatype is defined fresh in the lecture.
What this shared library adds - on top of everything re-exported from
the Rec chain (the option monad, [Env]/[lookup]/[extend] and their
lemmas) - is the STORE plumbing: an [update_at] for in-place writes and
a couple of small list lemmas about allocation and update.
 *)

Require Export plih_rocq_rec_shared.

From Stdlib Require Import List.
Import ListNotations.

(** * STORE PLUMBING *)

(**
A store is a list indexed by LOCATION (a [nat]).  We keep the store
polymorphic here so the plumbing does not depend on the value type,
which is defined later in the lecture.

  - READING a cell is just [nth_error];
  - ALLOCATING a cell appends at the end, so the fresh location is the
    old [length];
  - WRITING a cell replaces the element at a location, or fails
    ([None]) if the location is out of range.
 *)

Fixpoint update_at {A : Type} (n : nat) (v : A) (xs : list A) : option (list A) :=
  match xs, n with
  | nil, _ => None
  | _ :: tl, 0 => Some (v :: tl)
  | x :: tl, S k =>
      match update_at k v tl with
      | Some tl' => Some (x :: tl')
      | None => None
      end
  end.

(* An in-place write preserves the length of the store. *)
Lemma update_at_length {A : Type} : forall n (v : A) xs ys,
  update_at n v xs = Some ys -> length ys = length xs.
Proof.
  intros n v xs. revert n.
  induction xs as [| x tl IH]; intros n ys H.
  - destruct n; simpl in H; discriminate.
  - destruct n as [| k]; simpl in H.
    + injection H as H. subst ys. reflexivity.
    + destruct (update_at k v tl) as [tl' |] eqn:E; try discriminate.
      injection H as H. subst ys. simpl. f_equal. apply (IH k tl' E).
Qed.

(* Reading back the location just written returns the value written. *)
Lemma update_at_read {A : Type} : forall n (v : A) xs ys,
  update_at n v xs = Some ys -> nth_error ys n = Some v.
Proof.
  intros n v xs. revert n.
  induction xs as [| x tl IH]; intros n ys H.
  - destruct n; simpl in H; discriminate.
  - destruct n as [| k]; simpl in H.
    + injection H as H. subst ys. reflexivity.
    + destruct (update_at k v tl) as [tl' |] eqn:E; try discriminate.
      injection H as H. subst ys. simpl. apply (IH k tl' E).
Qed.

(* Allocation: the fresh location [length xs] reads back the new value. *)
Lemma nth_error_snoc {A : Type} : forall (xs : list A) (v : A),
  nth_error (xs ++ [v]) (length xs) = Some v.
Proof.
  induction xs as [| x tl IH]; intros v; simpl.
  - reflexivity.
  - apply IH.
Qed.
