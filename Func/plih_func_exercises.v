(**
Programming Languages in Rocq - Func Exercises
Adding Functions - Student Problem Set

In these exercises you will:
  1. Run the closure interpreter [evalM] for FBAE
  2. State the value/equation laws and use FUEL MONOTONICITY
  3. Observe the difference between STATIC and DYNAMIC scoping
  4. Explore currying, divergence, and an error-reporting interpreter

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof
ending in [Qed].  The file compiles as given.

From the Func lecture you have: [FBAE], [subst], [evalS], [evalM],
[evalDyn], [eval], the value types [FBAEVal] ([NumV]/[ClosureV]) and
[DVal] ([DNumV]/[DLamV]), the metatheorems [evalM_mono] and
[evalM_deterministic], and the example terms [idFun], [incFun],
[addFun], [scopeTest], [omega].  The [lookup]/[extend] operations
come from the shared library.

The functions [constFun], [Result], [forget] and [evalErr] are
PROVIDED below; the exercises are to prove properties about them.

Difficulty: ★ trivial, ★★ a lemma citation, ★★★ short proof,
★★★★ induction.  Solutions are in plih_func_solutions.v.
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

(** * WARM-UP: RUNNING THE INTERPRETER *)

(* Exercise 1 ★ *)
Example ex1_apply_id : eval (App idFun (Num 5)) = Some (NumV 5).
Proof. Admitted.

(* Exercise 2 ★ *)
Example ex2_apply_inc : eval (App incFun (Num 10)) = Some (NumV 11).
Proof. Admitted.

(* Exercise 3 ★ *)
Example ex3_curry : eval (App (App addFun (Num 2)) (Num 3)) = Some (NumV 5).
Proof. Admitted.

(* Exercise 4 ★ *)
Example ex4_free : eval (Id "q") = None.
Proof. Admitted.

(* Exercise 5 ★ *)
Example ex5_bind_fun :
  eval (Bind "f" incFun (App (Id "f") (Num 41))) = Some (NumV 42).
Proof. Admitted.

(** * PART 1: EQUATIONS AND VALUES *)

(* Exercise 6 ★ *)
Lemma ex6_evalM_num : forall k env n, evalM (S k) env (Num n) = Some (NumV n).
Proof. Admitted.

(* Exercise 7 ★ *)
Lemma ex7_evalM_lambda : forall k env i b,
  evalM (S k) env (Lambda i b) = Some (ClosureV i b env).
Proof. Admitted.

(* Exercise 8 ★ *)
Lemma ex8_evalM_id : forall k env x,
  evalM (S k) env (Id x) = lookup x env.
Proof. Admitted.

(* Exercise 9 ★: a lambda evaluated in the empty environment captures
   [nil]. *)
Lemma ex9_closure_captures :
  eval (Lambda "x" (Id "x")) = Some (ClosureV "x" (Id "x") nil).
Proof. Admitted.

(** * PART 2: FUEL MONOTONICITY AND DETERMINISM *)

(* Exercise 10 ★: Hint: [evalM_mono]. *)
Lemma ex10_mono : forall f1 f2 env e v,
  f1 <= f2 -> evalM f1 env e = Some v -> evalM f2 env e = Some v.
Proof. Admitted.

(* Exercise 11 ★: the answer does not depend on the exact (sufficient)
   amount of fuel.  Hint: [split]; each is [reflexivity].  (The GENERAL
   statement, for an arbitrary term, is challenge 1 - it must keep the
   fuel a VARIABLE, since a literal fuel on an abstract term would make
   the kernel unroll [evalM] at [Qed].) *)
Lemma ex11_fuel_irrelevant :
  evalM 10  nil (App (App addFun (Num 3)) (Num 4)) = Some (NumV 7) /\
  evalM 100 nil (App (App addFun (Num 3)) (Num 4)) = Some (NumV 7).
Proof. Admitted.

(* Exercise 12 ★: Hint: [evalM_deterministic]. *)
Lemma ex12_deterministic : forall f env e r1 r2,
  evalM f env e = r1 -> evalM f env e = r2 -> r1 = r2.
Proof. Admitted.

(* Exercise 13 ★★★★: prove the dynamic interpreter is monotone in
   fuel, mirroring the proof of [evalM_mono] (induction on [f1], then
   [destruct f2] and case-split on [e]). *)
Lemma ex13_evalDyn_mono : forall f1 f2 env e v,
  f1 <= f2 -> evalDyn f1 env e = Some v -> evalDyn f2 env e = Some v.
Proof. Admitted.

(** * PART 3: STATIC vs DYNAMIC SCOPING *)

(* Exercise 14 ★: the closure interpreter is STATIC (answers 4). *)
Lemma ex14_scope_static : eval scopeTest = Some (NumV 4).
Proof. Admitted.

(* Exercise 15 ★: the environment-less interpreter is DYNAMIC
   (answers 5). *)
Lemma ex15_scope_dynamic : evalDyn 100 nil scopeTest = Some (DNumV 5).
Proof. Admitted.

(* Exercise 16 ★: the two disciplines observably disagree. *)
Lemma ex16_scope_differs :
  eval scopeTest = Some (NumV 4) /\ evalDyn 100 nil scopeTest = Some (DNumV 5).
Proof. Admitted.

(** * PART 4: CURRYING *)

(* Exercise 17 ★★: partial application returns a closure capturing [x]. *)
Lemma ex17_partial :
  eval (App addFun (Num 7))
  = Some (ClosureV "y" (Plus (Id "x") (Id "y")) (extend "x" (NumV 7) nil)).
Proof. Admitted.

Definition constFun : FBAE := Lambda "x" (Lambda "y" (Id "x")).

(* Exercise 18 ★ *)
Lemma ex18_const :
  eval (App (App constFun (Num 1)) (Num 2)) = Some (NumV 1).
Proof. Admitted.

(** * PART 5: DIVERGENCE, STRICT BINDING *)

(* Exercise 19 ★: [omega] exhausts the fuel. *)
Lemma ex19_omega : eval omega = None.
Proof. Admitted.

(* Exercise 20 ★: strict binding of a divergent expression diverges,
   even though the body never uses it. *)
Lemma ex20_strict : eval (Bind "z" omega (Num 5)) = None.
Proof. Admitted.

(** * PART 6: AN ERROR-REPORTING INTERPRETER (PROVIDED) *)

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

(* Exercise 21 ★ *)
Lemma ex21_evalErr_num : forall f env n,
  evalErr (S f) env (Num n) = inr (NumV n).
Proof. Admitted.

(* Exercise 22 ★★★★: [evalErr] refines [evalM].  Induction on fuel;
   the [Plus]/[Minus]/[App] cases rewrite with the IH then case-split on
   the recursive [Result]s. *)
Lemma ex22_forget_evalErr : forall f env e,
  forget (evalErr f env e) = evalM f env e.
Proof. Admitted.

(** * CHALLENGE PROBLEMS *)

(* Challenge 1 ★★: an answer found with some fuel survives any larger
   amount of fuel.  Keep the fuel a VARIABLE (a literal fuel on an
   abstract term would make Rocq unroll [evalM]).  Hint: [evalM_mono]. *)
Lemma challenge1_eval_stable : forall e v f1 f2,
  f1 <= f2 -> evalM f1 nil e = Some v -> evalM f2 nil e = Some v.
Proof. Admitted.

(* Challenge 2 ★★★: whenever the error interpreter yields a value, the
   pure interpreter agrees.  Hint: [ex22_forget_evalErr]. *)
Lemma challenge2_evalErr_sound : forall f env e v,
  evalErr f env e = inr v -> evalM f env e = Some v.
Proof. Admitted.

(** * PART 7: CONCRETE SYNTAX *)

(**
The lecture added a notation-based parser: [lambda ID in body] for
functions, JUXTAPOSITION [f a] for application (left-associative,
binding tightest), plus [bind]/[+]/[-] and the numeral/string
coercions.  We open its scope to use it here.
 *)

Open Scope fbae_scope.

(* Exercise 23 ★: a function value parses to [Lambda]. *)
Example ex23_parse_lambda : <{ lambda "x" in "x" }> = Lambda "x" (Id "x").
Proof. Admitted.

(* Exercise 24 ★: application is [App]. *)
Example ex24_parse_app : <{ "f" "x" }> = App (Id "f") (Id "x").
Proof. Admitted.

(* Exercise 25 ★★: apply a literal function and evaluate. *)
Example ex25_eval_app :
  eval <{ (lambda "x" in "x" + 1) 4 }> = Some (NumV 5).
Proof. Admitted.

(* Exercise 26 ★★: currying by juxtaposition - [f 3 4] is [(f 3) 4]. *)
Example ex26_eval_curry :
  eval <{ (lambda "x" in lambda "y" in "x" + "y") 3 4 }> = Some (NumV 7).
Proof. Admitted.

(** * SUBMISSION GUIDELINES *)

(**
Replace every [Admitted] with a complete proof ending in [Qed].
Compare your proofs against plih_func_solutions.v.
 *)
