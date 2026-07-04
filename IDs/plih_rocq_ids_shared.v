(**
Programming Languages in Rocq - IDs Shared Infrastructure
Adding Identifiers (the BAE language: Bind + Arithmetic Expressions)

This chapter mirrors "Adding Identifiers" from PLIH:
  https://ku-sldg.github.io/plih//ids/1-Adding-IDs.html

BAE extends AE with an identifier (Id) and a local binding
construct (Bind), the abstract-syntax version of a [let].  The
interpreter in this chapter gives meaning to identifiers by
SUBSTITUTION: [bind x = v in b] evaluates [v], then replaces every
free [x] in [b] with the resulting value.

All the general-purpose machinery we need - the option monad, the
[Env]/[lookup]/[extend] operations, and their lemmas - already lives
in the AE shared library, so we simply re-export it.  The identifier
operations here reuse [String.eqb] for name comparison.
 *)

From Stdlib Require Import String.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Export plih_rocq_ae_shared.

(** * PART 1: NAMES *)

(**
Identifiers are just strings.  We compare them with [String.eqb],
whose reflection lemmas ([String.eqb_eq], [String.eqb_neq],
[String.eqb_refl], [String.eqb_sym]) we will lean on throughout.

Two small convenience lemmas restated here so the later files can
cite them by a stable name.
 *)

Lemma string_eqb_refl : forall x : string, String.eqb x x = true.
Proof. intro x. apply String.eqb_refl. Qed.

Lemma string_eqb_sym : forall x y : string, String.eqb x y = String.eqb y x.
Proof.
  intros x y.
  destruct (String.eqb x y) eqn:Exy.
  - apply String.eqb_eq in Exy. subst. symmetry. apply String.eqb_refl.
  - destruct (String.eqb y x) eqn:Eyx; [| reflexivity].
    apply String.eqb_eq in Eyx. subst.
    rewrite String.eqb_refl in Exy. discriminate.
Qed.

(** * PART 2: EXPORTED INTERFACE *)

(* The [Env], [lookup] and [extend] operations, the option monad, and
   the arithmetic/list libraries all come through the AE re-export. *)
Export List.
Export Nat.
