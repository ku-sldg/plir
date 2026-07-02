(**
 * Programming Languages in Rocq - Func Lecture
 * Adding Functions (first-class functions, closures, scoping)
 *
 * This lecture covers:
 *   1. Extending BAE with [Lambda] and [App]: first-class functions.
 *   2. A SUBSTITUTION interpreter [evalS] - and why, now that we can
 *      substitute whole functions, [size] no longer bounds the fuel:
 *      the language can DIVERGE (the classic [omega] term).
 *   3. VALUES and CLOSURES: an environment interpreter [evalM] that
 *      captures the definition-time environment in a closure.
 *   4. FUEL MONOTONICITY - the well-definedness result that replaces
 *      the "size is enough fuel" theorem of the earlier chapters.
 *   5. STATIC vs DYNAMIC scoping, made precise with a third interpreter
 *      [evalDyn] and a term on which the two disagree.
 *   6. Currying, and strict-vs-lazy binding.
 *
 * This mirrors the "Functions" unit of PLIH:
 *   https://ku-sldg.github.io/plih//funs/1-Adding-Functions.html
 *   https://ku-sldg.github.io/plih//funs/2-Scoping.html
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_func_shared.

Local Open Scope string_scope.
Import ListNotations.

(* ================================================================ *)
(* SECTION 1: SYNTAX - The FBAE Language                            *)
(* ================================================================ *)

(**
 * FBAE ("Functions, Bind, and Arithmetic Expressions") is BAE plus two
 * new forms:
 *   - [Lambda x b] : an anonymous function of parameter [x], body [b]
 *   - [App f a]    : apply function [f] to argument [a]
 *
 * Concrete syntax:
 *   t ::= NUM | ID | t + t | t - t
 *       | bind ID = t in t
 *       | lambda ID in t          (* a function value *)
 *       | app t t                 (* application *)
 *
 * Compare to the Haskell course:
 *   data FBAE where
 *     Num    :: Int -> FBAE
 *     Plus   :: FBAE -> FBAE -> FBAE
 *     Minus  :: FBAE -> FBAE -> FBAE
 *     Bind   :: String -> FBAE -> FBAE -> FBAE
 *     Lambda :: String -> FBAE -> FBAE
 *     App    :: FBAE -> FBAE -> FBAE
 *     Id     :: String -> FBAE
 *)

Inductive FBAE : Type :=
| Num    : nat -> FBAE
| Plus   : FBAE -> FBAE -> FBAE
| Minus  : FBAE -> FBAE -> FBAE
| Bind   : string -> FBAE -> FBAE -> FBAE
| Lambda : string -> FBAE -> FBAE
| App    : FBAE -> FBAE -> FBAE
| Id     : string -> FBAE.

(* The identity function and a "successor" function. *)
Definition idFun : FBAE := Lambda "x" (Id "x").
Definition incFun : FBAE := Lambda "x" (Plus (Id "x") (Num 1)).

(* [(lambda x in x) 7]. *)
Definition apply_id : FBAE := App idFun (Num 7).

(* ================================================================ *)
(* SECTION 2: FREE IDENTIFIERS, SIZE, AND SUBSTITUTION              *)
(* ================================================================ *)

(**
 * As in BAE, [free_in] tracks free instances; now BOTH [Bind] and
 * [Lambda] are binders, so both shadow their bound name in their body.
 *)
Fixpoint free_in (x : string) (e : FBAE) : bool :=
  match e with
  | Num _      => false
  | Id y       => String.eqb x y
  | Plus  l r  => free_in x l || free_in x r
  | Minus l r  => free_in x l || free_in x r
  | Bind y v b => free_in x v || (if String.eqb x y then false else free_in x b)
  | Lambda y b => if String.eqb x y then false else free_in x b
  | App f a    => free_in x f || free_in x a
  end.

Definition closed (e : FBAE) : Prop := forall x, free_in x e = false.

Fixpoint size (e : FBAE) : nat :=
  match e with
  | Num _      => 1
  | Id _       => 1
  | Plus  l r  => 1 + size l + size r
  | Minus l r  => 1 + size l + size r
  | Bind _ v b => 1 + size v + size b
  | Lambda _ b => 1 + size b
  | App f a    => 1 + size f + size a
  end.

(**
 * Substitution [subst i v e] replaces every free [i] in [e] with the
 * term [v].  Both binders ([Bind] and [Lambda]) shadow [i] when their
 * bound name matches.
 *
 * Compare to Haskell:
 *   subst i v (Lambda i' b') = if i==i' then Lambda i' b'
 *                                        else Lambda i' (subst i v b')
 *   subst i v (App f a)      = App (subst i v f) (subst i v a)
 *)
Fixpoint subst (i : string) (v : FBAE) (e : FBAE) : FBAE :=
  match e with
  | Num x      => Num x
  | Plus  l r  => Plus  (subst i v l) (subst i v r)
  | Minus l r  => Minus (subst i v l) (subst i v r)
  | Bind i' v' b' =>
      if String.eqb i i'
      then Bind i' (subst i v v') b'
      else Bind i' (subst i v v') (subst i v b')
  | Lambda i' b' =>
      if String.eqb i i' then Lambda i' b' else Lambda i' (subst i v b')
  | App f a    => App (subst i v f) (subst i v a)
  | Id i'      => if String.eqb i i' then v else Id i'
  end.

(**
 * CRUCIAL DIFFERENCE FROM BAE.  In the IDs chapter we only ever
 * substituted a NUMBER, so [size (subst i (Num n) e) = size e] and
 * [size e] was always enough fuel.  Now we substitute whole VALUES -
 * including functions - so a substitution can make a term GROW.
 *)
Example subst_grows :
  size (subst "x" incFun (Plus (Id "x") (Id "x")))
  > size (Plus (Id "x") (Id "x")).
Proof. simpl. lia. Qed.

(* ================================================================ *)
(* SECTION 3: THE SUBSTITUTION INTERPRETER (WITH FUEL)             *)
(* ================================================================ *)

(**
 * The values of FBAE are numbers and functions.  Following the course,
 * the substitution interpreter returns an FBAE that is one of these:
 *
 *   evalS (Num x)      = Just (Num x)
 *   evalS (Lambda i b) = Just (Lambda i b)          -- functions are values
 *   evalS (App f a)    = do (Lambda i b) <- evalS f
 *                           a'            <- evalS a
 *                           evalS (subst i a' b)     -- beta reduction
 *   evalS (Id id)      = Nothing                      -- free identifier
 *
 * Because [App] and [Bind] recurse on freshly-built [subst ...] terms -
 * and because those terms can be LARGER than the original (Section 2) -
 * this is neither structurally recursive NOR bounded by [size].  In
 * fact the language can diverge, so no measure could work.  We drive
 * the interpreter with an explicit FUEL counter; running out of fuel
 * yields [None].
 *)
Fixpoint evalS (fuel : nat) (e : FBAE) : option FBAE :=
  match fuel with
  | 0 => None
  | S k =>
      match e with
      | Num n => Some (Num n)
      | Plus l r =>
          match evalS k l, evalS k r with
          | Some (Num a), Some (Num b) => Some (Num (a + b))
          | _, _ => None
          end
      | Minus l r =>
          match evalS k l, evalS k r with
          | Some (Num a), Some (Num b) => Some (Num (a - b))
          | _, _ => None
          end
      | Bind i v b =>
          match evalS k v with
          | Some v' => evalS k (subst i v' b)
          | None => None
          end
      | Lambda i b => Some (Lambda i b)
      | App f a =>
          match evalS k f with
          | Some (Lambda i b) =>
              match evalS k a with
              | Some a' => evalS k (subst i a' b)
              | None => None
              end
          | _ => None
          end
      | Id _ => None
      end
  end.

(* ================================================================ *)
(* SECTION 4: VALUES AND CLOSURES; THE ENVIRONMENT INTERPRETER     *)
(* ================================================================ *)

(**
 * The substitution interpreter re-walks the whole body on every
 * binding.  As before, we would rather DEFER substitution with an
 * environment.  But a function may be returned from the scope where its
 * free variables were bound, so an environment value cannot just be a
 * bare [Lambda] - it must also remember the environment in force WHERE
 * THE LAMBDA WAS DEFINED.  That bundle is a CLOSURE.
 *
 * Compare to Haskell:
 *   data FBAEVal where
 *     NumV     :: Int -> FBAEVal
 *     ClosureV :: String -> FBAE -> Env -> FBAEVal
 *   type Env = [(String, FBAEVal)]
 *
 * Note the mutual shape: a value may contain an environment, which is a
 * list of (name, value) pairs.  Rocq accepts this nested inductive.
 *)
Inductive FBAEVal : Type :=
| NumV     : nat -> FBAEVal
| ClosureV : string -> FBAE -> list (string * FBAEVal) -> FBAEVal.

(**
 * The environment interpreter.  Compare to Haskell:
 *   evalM env (Lambda i b) = return (ClosureV i b env)
 *   evalM env (App f a)    = do (ClosureV i b e) <- evalM env f
 *                               a'                <- evalM env a
 *                               evalM ((i,a'):e) b     -- e = STATIC env
 *   evalM env (Id id)      = lookup id env
 *
 * The [App] case evaluates the body in the closure's captured
 * environment [e], extended with the argument - NOT in the caller's
 * environment.  That single choice is what makes scoping STATIC.
 *
 * Like [evalS], this is not structurally recursive (the [App] case
 * recurses on the closure body [b], which is not a subterm of [App f
 * a]), and the language can diverge - so it, too, needs fuel.
 *)
Fixpoint evalM (fuel : nat) (env : Env FBAEVal) (e : FBAE) : option FBAEVal :=
  match fuel with
  | 0 => None
  | S k =>
      match e with
      | Num n => Some (NumV n)
      | Plus l r =>
          match evalM k env l, evalM k env r with
          | Some (NumV a), Some (NumV b) => Some (NumV (a + b))
          | _, _ => None
          end
      | Minus l r =>
          match evalM k env l, evalM k env r with
          | Some (NumV a), Some (NumV b) => Some (NumV (a - b))
          | _, _ => None
          end
      | Bind i v b =>
          match evalM k env v with
          | Some v' => evalM k (extend i v' env) b
          | None => None
          end
      | Lambda i b => Some (ClosureV i b env)
      | App f a =>
          match evalM k env f with
          | Some (ClosureV i b cenv) =>
              match evalM k env a with
              | Some a' => evalM k (extend i a' cenv) b
              | None => None
              end
          | _ => None
          end
      | Id x => lookup x env
      end
  end.

(* A convenience wrapper with fuel large enough for the small examples
   in this file.  There is no "right" default: a program may need more. *)
Definition eval (e : FBAE) : option FBAEVal := evalM 100 nil e.

(* ================================================================ *)
(* SECTION 5: RUNNING THE INTERPRETERS                             *)
(* ================================================================ *)

Example test_id : eval apply_id = Some (NumV 7).
Proof. reflexivity. Qed.

Example test_inc : eval (App incFun (Num 4)) = Some (NumV 5).
Proof. reflexivity. Qed.

Example test_bind_fun :
  eval (Bind "f" incFun (App (Id "f") (App (Id "f") (Num 0)))) = Some (NumV 2).
Proof. reflexivity. Qed.

(* The substitution interpreter agrees on these first-order examples. *)
Example test_evalS_inc : evalS 100 (App incFun (Num 4)) = Some (Num 5).
Proof. reflexivity. Qed.

(* A free identifier still has no value. *)
Example test_free : eval (Id "y") = None.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* SECTION 6: FUEL MONOTONICITY (THE HEADLINE METATHEOREM)         *)
(* ================================================================ *)

(**
 * In the IDs/Env chapters the well-definedness result was "[size e] is
 * enough fuel."  Here no measure works, so the result that takes its
 * place is MONOTONICITY: once the interpreter produces an answer, adding
 * more fuel never changes it.  Equivalently, [evalM] approximates a
 * partial function, and increasing fuel only ever turns [None] into
 * [Some] - never one [Some] into another.
 *)
Lemma evalM_mono : forall f1 f2 env e v,
  f1 <= f2 -> evalM f1 env e = Some v -> evalM f2 env e = Some v.
Proof.
  induction f1 as [| k IH]; intros f2 env e v Hle H.
  - simpl in H. discriminate.
  - destruct f2 as [| k2]; [lia |].
    destruct e; simpl in H |- *.
    + (* Num *) exact H.
    + (* Plus *)
      destruct (evalM k env e1) as [[a | i b ce] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | i b ce] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Minus *)
      destruct (evalM k env e1) as [[a | i b ce] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | i b ce] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Bind *)
      destruct (evalM k env e1) as [v' |] eqn:Ev; try discriminate.
      rewrite (IH k2 env e1 v' ltac:(lia) Ev).
      apply (IH k2 (extend s v' env) e2 v). lia. exact H.
    + (* Lambda *) exact H.
    + (* App *)
      destruct (evalM k env e1) as [[a | i b ce] |] eqn:Ef; try discriminate.
      destruct (evalM k env e2) as [a' |] eqn:Ea; try discriminate.
      rewrite (IH k2 env e1 (ClosureV i b ce) ltac:(lia) Ef).
      rewrite (IH k2 env e2 a' ltac:(lia) Ea).
      apply (IH k2 (extend i a' ce) b v). lia. exact H.
    + (* Id *) exact H.
Qed.

(**
 * Determinism is immediate ([evalM] is a function), but worth stating:
 * for a FIXED amount of fuel the answer is unique.  Together with
 * monotonicity this says the limiting partial function is well defined.
 *)
Lemma evalM_deterministic : forall f env e r1 r2,
  evalM f env e = r1 -> evalM f env e = r2 -> r1 = r2.
Proof. intros f env e r1 r2 H1 H2. rewrite <- H1, <- H2. reflexivity. Qed.

(* Values evaluate to themselves (given a positive amount of fuel). *)
Lemma evalM_num : forall k env n, evalM (S k) env (Num n) = Some (NumV n).
Proof. reflexivity. Qed.

Lemma evalM_lambda : forall k env i b,
  evalM (S k) env (Lambda i b) = Some (ClosureV i b env).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* SECTION 7: STATIC vs DYNAMIC SCOPING                            *)
(* ================================================================ *)

(**
 * Under STATIC scoping a function sees the bindings in force where it
 * was DEFINED; under DYNAMIC scoping it sees the bindings where it is
 * CALLED.  To make the difference precise we build a second value type
 * with function values that DO NOT capture an environment, and an
 * interpreter [evalDyn] that runs a called function's body in the
 * CALLER's environment.
 *)
Inductive DVal : Type :=
| DNumV : nat -> DVal
| DLamV : string -> FBAE -> DVal.       (* no captured environment! *)

Fixpoint evalDyn (fuel : nat) (env : Env DVal) (e : FBAE) : option DVal :=
  match fuel with
  | 0 => None
  | S k =>
      match e with
      | Num n => Some (DNumV n)
      | Plus l r =>
          match evalDyn k env l, evalDyn k env r with
          | Some (DNumV a), Some (DNumV b) => Some (DNumV (a + b))
          | _, _ => None
          end
      | Minus l r =>
          match evalDyn k env l, evalDyn k env r with
          | Some (DNumV a), Some (DNumV b) => Some (DNumV (a - b))
          | _, _ => None
          end
      | Bind i v b =>
          match evalDyn k env v with
          | Some v' => evalDyn k (extend i v' env) b
          | None => None
          end
      | Lambda i b => Some (DLamV i b)
      | App f a =>
          match evalDyn k env f with
          | Some (DLamV i b) =>
              match evalDyn k env a with
              (* body runs in the CALLER's [env], not a captured one *)
              | Some a' => evalDyn k (extend i a' env) b
              | None => None
              end
          | _ => None
          end
      | Id x => lookup x env
      end
  end.

(**
 * The classic witness:
 *
 *   bind n = 1 in
 *   bind f = (lambda x in x + n) in
 *   bind n = 2 in
 *     f 3
 *
 * Static scoping: [f] captured [n = 1], so [f 3 = 3 + 1 = 4].
 * Dynamic scoping: [f 3] uses the current [n = 2], so [f 3 = 3 + 2 = 5].
 *)
Definition scopeTest : FBAE :=
  Bind "n" (Num 1)
    (Bind "f" (Lambda "x" (Plus (Id "x") (Id "n")))
      (Bind "n" (Num 2)
        (App (Id "f") (Num 3)))).

(* The closure interpreter is STATIC: it answers 4. *)
Example scope_static : eval scopeTest = Some (NumV 4).
Proof. reflexivity. Qed.

(* The environment-less interpreter is DYNAMIC: it answers 5. *)
Example scope_dynamic : evalDyn 100 nil scopeTest = Some (DNumV 5).
Proof. reflexivity. Qed.

(* The substitution interpreter agrees with the closure interpreter:
   substitution is inherently STATIC.  It, too, answers 4. *)
Example scope_subst : evalS 100 scopeTest = Some (Num 4).
Proof. reflexivity. Qed.

(**
 * So [evalM] (closures) and [evalS] (substitution) implement the SAME,
 * static, discipline, while [evalDyn] genuinely differs.  Static
 * scoping is what we want: the meaning of a function is fixed at its
 * definition and does not depend on where it happens to be called.
 *)

(* ================================================================ *)
(* SECTION 8: CURRYING                                             *)
(* ================================================================ *)

(**
 * A function of one argument suffices for functions of many: a
 * two-argument function is a function returning a function (CURRYING).
 * Closures are what make this work - the inner lambda captures the
 * first argument.
 *)
Definition addFun : FBAE :=
  Lambda "x" (Lambda "y" (Plus (Id "x") (Id "y"))).

Example curry_partial :
  (* [add 3] is a closure capturing [x = 3] *)
  eval (App addFun (Num 3)) = Some (ClosureV "y" (Plus (Id "x") (Id "y"))
                                              (extend "x" (NumV 3) nil)).
Proof. reflexivity. Qed.

Example curry_full :
  eval (App (App addFun (Num 3)) (Num 4)) = Some (NumV 7).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* SECTION 9: DIVERGENCE, STRICT vs LAZY                           *)
(* ================================================================ *)

(**
 * With first-class functions the language is powerful enough to LOOP.
 * The canonical non-terminating term is [omega]: a self-application
 * that reduces to itself forever.
 *)
Definition selfApp : FBAE := Lambda "x" (App (Id "x") (Id "x")).
Definition omega : FBAE := App selfApp selfApp.

(* No matter how much fuel we supply, [omega] never returns - it just
   exhausts the fuel.  This is why no [size] measure can bound the
   interpreter: divergent programs exist. *)
Example omega_diverges_100 : eval omega = None.
Proof. reflexivity. Qed.

(**
 * Our [Bind] (and [App]) are STRICT (call-by-value): the bound
 * expression is evaluated BEFORE the body.  So binding a divergent
 * expression diverges, even when the body never uses it.
 *)
Example strict_bind : eval (Bind "z" omega (Num 5)) = None.
Proof. reflexivity. Qed.

(**
 * Under a LAZY (call-by-name / call-by-need) discipline the same term
 * would return [5], because [z] is never forced.  Choosing between
 * strict and lazy binding is exactly choosing whether to evaluate the
 * bound expression eagerly - a design decision explored further in the
 * exercises and the "Strict and Lazy" section of the course.
 *)

(* ================================================================ *)
(* SUMMARY                                                          *)
(* ================================================================ *)

(**
 * In this lecture we:
 *   1. Extended BAE to FBAE with first-class [Lambda]/[App].
 *   2. Wrote a SUBSTITUTION interpreter [evalS] and saw that
 *      substituting functions can GROW terms, so - unlike BAE - no
 *      [size] bound works and the language can DIVERGE.  Fuel is
 *      unavoidable.
 *   3. Introduced VALUES and CLOSURES and the environment interpreter
 *      [evalM]: a closure captures the definition-time environment.
 *   4. Proved FUEL MONOTONICITY, the well-definedness result that
 *      replaces "size is enough fuel," plus determinism.
 *   5. Distinguished STATIC from DYNAMIC scoping with [evalDyn] and a
 *      term on which they disagree (4 vs 5); [evalS] and [evalM] both
 *      give the static answer.
 *   6. Illustrated currying and the strict-vs-lazy choice ([omega]).
 *
 * Next: TYPED functions rule out the stuck/divergent programs that fuel
 * had to absorb here, restoring a total, structural story.
 *)
