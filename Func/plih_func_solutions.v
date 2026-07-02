(**
 * Programming Languages in Rocq - Func Solutions
 * Complete solutions to plih_func_exercises.v
 *
 * The FBAE syntax, [subst], the interpreters [evalS] (substitution),
 * [evalM] (closures) and [evalDyn] (dynamic scoping), the value types
 * [FBAEVal]/[DVal], [eval], [evalM_mono], [evalM_deterministic], and
 * the example terms [idFun], [incFun], [addFun], [scopeTest], [omega]
 * all come from the Func lecture.  The error-reporting interpreter
 * [evalErr] is defined here (and, identically, in the exercises file).
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_func_shared.
Require Import plih_func_lecture.

Local Open Scope string_scope.
Import ListNotations.

(* ================================================================ *)
(* WARM-UP: RUNNING THE INTERPRETER                                *)
(* ================================================================ *)

Example ex1_apply_id : eval (App idFun (Num 5)) = Some (NumV 5).
Proof. reflexivity. Qed.

Example ex2_apply_inc : eval (App incFun (Num 10)) = Some (NumV 11).
Proof. reflexivity. Qed.

Example ex3_curry : eval (App (App addFun (Num 2)) (Num 3)) = Some (NumV 5).
Proof. reflexivity. Qed.

Example ex4_free : eval (Id "q") = None.
Proof. reflexivity. Qed.

Example ex5_bind_fun :
  eval (Bind "f" incFun (App (Id "f") (Num 41))) = Some (NumV 42).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* PART 1: EQUATIONS AND VALUES                                     *)
(* ================================================================ *)

Lemma ex6_evalM_num : forall k env n, evalM (S k) env (Num n) = Some (NumV n).
Proof. reflexivity. Qed.

Lemma ex7_evalM_lambda : forall k env i b,
  evalM (S k) env (Lambda i b) = Some (ClosureV i b env).
Proof. reflexivity. Qed.

Lemma ex8_evalM_id : forall k env x,
  evalM (S k) env (Id x) = lookup x env.
Proof. reflexivity. Qed.

Lemma ex9_closure_captures :
  eval (Lambda "x" (Id "x")) = Some (ClosureV "x" (Id "x") nil).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* PART 2: FUEL MONOTONICITY AND DETERMINISM                       *)
(* ================================================================ *)

Lemma ex10_mono : forall f1 f2 env e v,
  f1 <= f2 -> evalM f1 env e = Some v -> evalM f2 env e = Some v.
Proof. exact evalM_mono. Qed.

(* The answer does not depend on the exact (sufficient) amount of fuel,
   shown here concretely - the general statement is [challenge1] below.
   (Stating this for an ABSTRACT term with a literal fuel like [200]
   would force the kernel to unroll [evalM] to depth 200 at [Qed]; on a
   concrete term [evalM] simply computes to a value and stops.) *)
Lemma ex11_fuel_irrelevant :
  evalM 10  nil (App (App addFun (Num 3)) (Num 4)) = Some (NumV 7) /\
  evalM 100 nil (App (App addFun (Num 3)) (Num 4)) = Some (NumV 7).
Proof. split; reflexivity. Qed.

Lemma ex12_deterministic : forall f env e r1 r2,
  evalM f env e = r1 -> evalM f env e = r2 -> r1 = r2.
Proof. exact evalM_deterministic. Qed.

(* Exercise 13: the dynamic interpreter is monotone in fuel too - the
   same proof, re-run for [evalDyn]/[DVal]. *)
Lemma ex13_evalDyn_mono : forall f1 f2 env e v,
  f1 <= f2 -> evalDyn f1 env e = Some v -> evalDyn f2 env e = Some v.
Proof.
  induction f1 as [| k IH]; intros f2 env e v Hle H.
  - simpl in H. discriminate.
  - destruct f2 as [| k2]; [lia |].
    destruct e; simpl in H |- *.
    + exact H.
    + destruct (evalDyn k env e1) as [[a | i b] |] eqn:El; try discriminate.
      destruct (evalDyn k env e2) as [[b0 | i b] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (DNumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (DNumV b0) ltac:(lia) Er). exact H.
    + destruct (evalDyn k env e1) as [[a | i b] |] eqn:El; try discriminate.
      destruct (evalDyn k env e2) as [[b0 | i b] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (DNumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (DNumV b0) ltac:(lia) Er). exact H.
    + destruct (evalDyn k env e1) as [v' |] eqn:Ev; try discriminate.
      rewrite (IH k2 env e1 v' ltac:(lia) Ev).
      apply (IH k2 (extend s v' env) e2 v). lia. exact H.
    + exact H.
    + destruct (evalDyn k env e1) as [[a | i b] |] eqn:Ef; try discriminate.
      destruct (evalDyn k env e2) as [a' |] eqn:Ea; try discriminate.
      rewrite (IH k2 env e1 (DLamV i b) ltac:(lia) Ef).
      rewrite (IH k2 env e2 a' ltac:(lia) Ea).
      apply (IH k2 (extend i a' env) b v). lia. exact H.
    + exact H.
Qed.

(* ================================================================ *)
(* PART 3: STATIC vs DYNAMIC SCOPING                               *)
(* ================================================================ *)

Lemma ex14_scope_static : eval scopeTest = Some (NumV 4).
Proof. reflexivity. Qed.

Lemma ex15_scope_dynamic : evalDyn 100 nil scopeTest = Some (DNumV 5).
Proof. reflexivity. Qed.

(* The two disciplines observably disagree on [scopeTest]. *)
Lemma ex16_scope_differs :
  eval scopeTest = Some (NumV 4) /\ evalDyn 100 nil scopeTest = Some (DNumV 5).
Proof. split; reflexivity. Qed.

(* ================================================================ *)
(* PART 4: CURRYING                                                *)
(* ================================================================ *)

(* Partial application of [addFun] returns a closure capturing [x]. *)
Lemma ex17_partial :
  eval (App addFun (Num 7))
  = Some (ClosureV "y" (Plus (Id "x") (Id "y")) (extend "x" (NumV 7) nil)).
Proof. reflexivity. Qed.

Definition constFun : FBAE := Lambda "x" (Lambda "y" (Id "x")).

Lemma ex18_const :
  eval (App (App constFun (Num 1)) (Num 2)) = Some (NumV 1).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* PART 5: DIVERGENCE, STRICT BINDING                              *)
(* ================================================================ *)

Lemma ex19_omega : eval omega = None.
Proof. reflexivity. Qed.

Lemma ex20_strict : eval (Bind "z" omega (Num 5)) = None.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* PART 6: AN ERROR-REPORTING INTERPRETER (PROVIDED)               *)
(* ================================================================ *)

(**
 * As in the Env chapter, [evalErr] returns a value OR a message, using
 * [Result = string + FBAEVal].  Now there are two ways to fail: running
 * out of gas, and getting STUCK (a type error or an unbound name).  The
 * [forget] map erases the message so we can relate [evalErr] to [evalM].
 *)

Definition Result : Type := sum string FBAEVal.

Definition forget (r : Result) : option FBAEVal :=
  match r with
  | inl _ => None
  | inr v => Some v
  end.

Fixpoint evalErr (fuel : nat) (env : Env FBAEVal) (e : FBAE) : Result :=
  match fuel with
  | 0 => inl "out of gas"
  | S k =>
      match e with
      | Num n => inr (NumV n)
      | Plus l r =>
          match evalErr k env l, evalErr k env r with
          | inr (NumV a), inr (NumV b) => inr (NumV (a + b))
          | inl s, _ => inl s
          | _, inl s => inl s
          | _, _ => inl "type error in +"
          end
      | Minus l r =>
          match evalErr k env l, evalErr k env r with
          | inr (NumV a), inr (NumV b) => inr (NumV (a - b))
          | inl s, _ => inl s
          | _, inl s => inl s
          | _, _ => inl "type error in -"
          end
      | Bind i v b =>
          match evalErr k env v with
          | inr v' => evalErr k (extend i v' env) b
          | inl s => inl s
          end
      | Lambda i b => inr (ClosureV i b env)
      | App f a =>
          match evalErr k env f with
          | inr (ClosureV i b ce) =>
              match evalErr k env a with
              | inr a' => evalErr k (extend i a' ce) b
              | inl s => inl s
              end
          | inr (NumV _) => inl "applying a non-function"
          | inl s => inl s
          end
      | Id x =>
          match lookup x env with
          | Some v => inr v
          | None => inl "unbound identifier"
          end
      end
  end.

Lemma ex21_evalErr_num : forall f env n,
  evalErr (S f) env (Num n) = inr (NumV n).
Proof. reflexivity. Qed.

(* Exercise 22: [evalErr] refines [evalM] - erasing the message
   recovers the option interpreter exactly.  Induction on fuel. *)
Lemma ex22_forget_evalErr : forall f env e,
  forget (evalErr f env e) = evalM f env e.
Proof.
  induction f as [| k IH]; intros env e.
  - reflexivity.
  - destruct e; simpl.
    + reflexivity.
    + (* Plus *)
      rewrite <- (IH env e1), <- (IH env e2).
      destruct (evalErr k env e1) as [s1 | [a | i b ce]];
        destruct (evalErr k env e2) as [s2 | [b0 | i2 b2 ce2]]; reflexivity.
    + (* Minus *)
      rewrite <- (IH env e1), <- (IH env e2).
      destruct (evalErr k env e1) as [s1 | [a | i b ce]];
        destruct (evalErr k env e2) as [s2 | [b0 | i2 b2 ce2]]; reflexivity.
    + (* Bind *)
      rewrite <- (IH env e1).
      destruct (evalErr k env e1) as [s1 | v']; simpl.
      * reflexivity.
      * apply IH.
    + (* Lambda *) reflexivity.
    + (* App *)
      rewrite <- (IH env e1), <- (IH env e2).
      destruct (evalErr k env e1) as [s1 | [a | i b ce]]; simpl.
      * reflexivity.
      * reflexivity.
      * destruct (evalErr k env e2) as [s2 | a']; simpl.
        -- reflexivity.
        -- apply IH.
    + (* Id *)
      destruct (lookup s env); reflexivity.
Qed.

(* ================================================================ *)
(* CHALLENGE PROBLEMS                                              *)
(* ================================================================ *)

(* Challenge 1: an answer found with some fuel survives any larger
   amount of fuel - so the limiting partial function is well defined.
   NOTE: we keep the fuel a VARIABLE.  Writing this for an ABSTRACT term
   with a LITERAL fuel (e.g. [evalM 200 nil e]) would make Rocq try to
   unroll [evalM] to that depth during unification - hopelessly slow. *)
Lemma challenge1_eval_stable : forall e v f1 f2,
  f1 <= f2 -> evalM f1 nil e = Some v -> evalM f2 nil e = Some v.
Proof.
  intros e v f1 f2 Hle H. exact (evalM_mono f1 f2 nil e v Hle H).
Qed.

(* Challenge 2: whenever the error interpreter yields a value, the pure
   interpreter agrees. *)
Lemma challenge2_evalErr_sound : forall f env e v,
  evalErr f env e = inr v -> evalM f env e = Some v.
Proof.
  intros f env e v H.
  pose proof (ex22_forget_evalErr f env e) as Hf.
  rewrite H in Hf. simpl in Hf. symmetry. exact Hf.
Qed.
