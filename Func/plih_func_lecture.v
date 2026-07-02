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
 *   6. Currying, and strict-vs-lazy binding (a call-by-name [evalL]).
 *   7. ELABORATION: desugaring [Bind] into [App]/[Lambda], with a
 *      machine-checked proof that it preserves meaning.
 *   8. A teaser toward RECURSION: fixpoint combinators are definable from
 *      [Lambda]/[App], but productive recursion needs a conditional FBAE
 *      lacks - delivered in the Untyped Recursion chapter (Rec/).
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
(* SECTION 9: ELABORATION - DESUGARING [Bind] INTO [App]/[Lambda]   *)
(* ================================================================ *)

(**
 * [Bind] is not really primitive.  Once we have first-class functions,
 * a local binding is just the application of an anonymous function:
 *
 *   bind i = v in b     "is sugar for"     app (lambda i in b) v
 *
 * ELABORATION (a.k.a. DESUGARING) makes that precise as a
 * source-to-source translation into a [Bind]-free sublanguage, and -
 * unlike the informal "is sugar for" of a language manual - we can
 * PROVE the translation preserves meaning.  Everything other than
 * [Bind] is elaborated structurally.
 *)
Fixpoint elab (e : FBAE) : FBAE :=
  match e with
  | Num n      => Num n
  | Id x       => Id x
  | Plus  l r  => Plus  (elab l) (elab r)
  | Minus l r  => Minus (elab l) (elab r)
  | Lambda i b => Lambda i (elab b)
  | App f a    => App (elab f) (elab a)
  | Bind i v b => App (Lambda i (elab b)) (elab v)   (* the one real rule *)
  end.

(**
 * The target really is a [Bind]-free sublanguage: [bindFree] tests for
 * the absence of [Bind], and [elab] always lands in it.
 *)
Fixpoint bindFree (e : FBAE) : bool :=
  match e with
  | Num _      => true
  | Id _       => true
  | Plus  l r  => bindFree l && bindFree r
  | Minus l r  => bindFree l && bindFree r
  | Lambda _ b => bindFree b
  | App f a    => bindFree f && bindFree a
  | Bind _ _ _ => false
  end.

Theorem elab_bindFree : forall e, bindFree (elab e) = true.
Proof.
  induction e as
    [ n
    | l IHl r IHr
    | l IHl r IHr
    | i v IHv b IHb
    | i b IHb
    | f IHf a IHa
    | x ]; simpl.
  - reflexivity.                   (* Num    *)
  - rewrite IHl, IHr. reflexivity. (* Plus   *)
  - rewrite IHl, IHr. reflexivity. (* Minus  *)
  - rewrite IHv, IHb. reflexivity. (* Bind   *)
  - rewrite IHb. reflexivity.      (* Lambda *)
  - rewrite IHf, IHa. reflexivity. (* App    *)
  - reflexivity.                   (* Id     *)
Qed.

(* On the running example, elaboration eliminates [Bind] ... *)
Example elab_scopeTest_bindFree : bindFree (elab scopeTest) = true.
Proof. reflexivity. Qed.

(* ... and preserves the answer - keeping its STATIC reading (4, not 5),
   because [App]/[Lambda]/closures are themselves statically scoped. *)
Example elab_scopeTest_eval : eval (elab scopeTest) = eval scopeTest.
Proof. reflexivity. Qed.

Example elab_bind_fun :
  eval (elab (Bind "f" incFun (App (Id "f") (App (Id "f") (Num 0)))))
  = Some (NumV 2).
Proof. reflexivity. Qed.

(**
 * PRESERVATION OF MEANING.  We want elaboration to leave a program's
 * value unchanged.  There is one wrinkle: VALUES embed terms.  A
 * [ClosureV] carries its function body and captured environment, and
 * elaboration rewrites bodies - so the closure a program returns is the
 * ELABORATED closure.  We therefore lift [elab] to values and
 * environments (a mutual recursion, since a value contains an
 * environment) and state preservation UP TO that lifting.
 *)
Fixpoint elabV (v : FBAEVal) : FBAEVal :=
  match v with
  | NumV n         => NumV n
  | ClosureV i b e =>
      (* The captured environment is elaborated pointwise.  We need an
         inner [fix] here because [Env] is a list NESTED inside the value
         type, which the mutual-[Fixpoint] guard checker rejects. *)
      ClosureV i (elab b)
        ((fix eE (env : list (string * FBAEVal)) : list (string * FBAEVal) :=
            match env with
            | nil          => nil
            | (x, w) :: e' => (x, elabV w) :: eE e'
            end) e)
  end.

(* The same pointwise elaboration, as a standalone environment operation
   we can state lemmas about.  [elabV_clos] bridges the two. *)
Fixpoint elabEnv (env : Env FBAEVal) : Env FBAEVal :=
  match env with
  | nil          => nil
  | (x, w) :: e' => (x, elabV w) :: elabEnv e'
  end.

Lemma elabV_clos : forall i b e,
  elabV (ClosureV i b e) = ClosureV i (elab b) (elabEnv e).
Proof. intros; reflexivity. Qed.

Lemma elabEnv_extend : forall i v env,
  elabEnv (extend i v env) = extend i (elabV v) (elabEnv env).
Proof. reflexivity. Qed.

Lemma lookup_elabEnv : forall env x v,
  lookup x env = Some v -> lookup x (elabEnv env) = Some (elabV v).
Proof.
  induction env as [| [y w] e' IH]; intros x v H.
  - simpl in H. discriminate.
  - simpl in H. simpl. destruct (String.eqb x y) eqn:E.
    + injection H as H; subst. reflexivity.
    + apply IH. exact H.
Qed.

(* One-step unfolding of [evalM] on an [App], stated as a rewrite so we
   never have to [simpl] (which would over-eagerly unfold the argument
   and body evaluations along with it). *)
Lemma evalM_App : forall k env f a,
  evalM (S k) env (App f a) =
    match evalM k env f with
    | Some (ClosureV i b cenv) =>
        match evalM k env a with
        | Some a' => evalM k (extend i a' cenv) b
        | None => None
        end
    | _ => None
    end.
Proof. reflexivity. Qed.

(* Applying a value that is already known to be a closure. *)
Lemma evalM_app_closure : forall k env f a i body cenv av rv,
  evalM k env f = Some (ClosureV i body cenv) ->
  evalM k env a = Some av ->
  evalM k (extend i av cenv) body = Some rv ->
  evalM (S k) env (App f a) = Some rv.
Proof.
  intros k env f a i body cenv av rv Hf Ha Hb.
  rewrite evalM_App, Hf, Ha. cbv iota. exact Hb.
Qed.

(* Applying a literal [lambda] - the shape elaboration produces from a
   [Bind].  The [lambda] evaluates in one step, so [k] must be positive;
   [Ha] guarantees it (evaluation under zero fuel is [None]). *)
Lemma evalM_app_lambda : forall k env i body arg av rv,
  evalM k env arg = Some av ->
  evalM k (extend i av env) body = Some rv ->
  evalM (S k) env (App (Lambda i body) arg) = Some rv.
Proof.
  intros k env i body arg av rv Ha Hb.
  destruct k as [| k']; [simpl in Ha; discriminate |].
  eapply evalM_app_closure.
  - reflexivity.
  - exact Ha.
  - exact Hb.
Qed.

(**
 * The elaborated program takes MORE steps than the original (each
 * [Bind] becomes an extra [App]/[Lambda] layer), so we cannot promise
 * the SAME fuel works - only that SOME fuel does.  Fuel monotonicity
 * (Section 6) is exactly what lets us pick a large enough amount by
 * taking the max of the fuels supplied by the induction hypotheses.
 *)
Theorem elab_preserves : forall f env e v,
  evalM f env e = Some v ->
  exists f', evalM f' (elabEnv env) (elab e) = Some (elabV v).
Proof.
  induction f as [| k IH]; intros env e v H.
  - simpl in H. discriminate.
  - destruct e; simpl in H.
    + (* Num *)
      injection H as H; subst v. exists 1. reflexivity.
    + (* Plus *)
      destruct (evalM k env e1) as [[a | i b ce] |] eqn:E1; try discriminate.
      destruct (evalM k env e2) as [[b0 | i b ce] |] eqn:E2; try discriminate.
      injection H as H; subst v.
      destruct (IH env e1 (NumV a) E1) as [f1 H1]. simpl in H1.
      destruct (IH env e2 (NumV b0) E2) as [f2 H2]. simpl in H2.
      assert (L1 : f1 <= Nat.max f1 f2) by lia.
      assert (L2 : f2 <= Nat.max f1 f2) by lia.
      exists (S (Nat.max f1 f2)). simpl.
      rewrite (evalM_mono _ _ _ _ _ L1 H1).
      rewrite (evalM_mono _ _ _ _ _ L2 H2).
      reflexivity.
    + (* Minus *)
      destruct (evalM k env e1) as [[a | i b ce] |] eqn:E1; try discriminate.
      destruct (evalM k env e2) as [[b0 | i b ce] |] eqn:E2; try discriminate.
      injection H as H; subst v.
      destruct (IH env e1 (NumV a) E1) as [f1 H1]. simpl in H1.
      destruct (IH env e2 (NumV b0) E2) as [f2 H2]. simpl in H2.
      assert (L1 : f1 <= Nat.max f1 f2) by lia.
      assert (L2 : f2 <= Nat.max f1 f2) by lia.
      exists (S (Nat.max f1 f2)). simpl.
      rewrite (evalM_mono _ _ _ _ _ L1 H1).
      rewrite (evalM_mono _ _ _ _ _ L2 H2).
      reflexivity.
    + (* Bind -> App (Lambda s (elab e2)) (elab e1) *)
      destruct (evalM k env e1) as [v' |] eqn:E1; try discriminate.
      destruct (IH env e1 v' E1) as [f1 H1].
      destruct (IH (extend s v' env) e2 v H) as [f2 H2].
      rewrite elabEnv_extend in H2.
      exists (S (Nat.max f1 f2)).
      change (elab (Bind s e1 e2))
        with (App (Lambda s (elab e2)) (elab e1)).
      eapply evalM_app_lambda.
      * apply evalM_mono with (f1 := f1); [lia | exact H1].
      * apply evalM_mono with (f1 := f2); [lia | exact H2].
    + (* Lambda *)
      injection H as H; subst v. exists 1.
      rewrite elabV_clos. reflexivity.
    + (* App *)
      destruct (evalM k env e1) as [[a | i b ce] |] eqn:E1; try discriminate.
      destruct (evalM k env e2) as [a' |] eqn:E2; try discriminate.
      destruct (IH env e1 (ClosureV i b ce) E1) as [f1 H1].
      rewrite elabV_clos in H1.
      destruct (IH env e2 a' E2) as [f2 H2].
      destruct (IH (extend i a' ce) b v H) as [f3 H3].
      rewrite elabEnv_extend in H3.
      exists (S (Nat.max f1 (Nat.max f2 f3))).
      change (elab (App e1 e2)) with (App (elab e1) (elab e2)).
      eapply evalM_app_closure.
      * apply evalM_mono with (f1 := f1); [lia | exact H1].
      * apply evalM_mono with (f1 := f2); [lia | exact H2].
      * apply evalM_mono with (f1 := f3); [lia | exact H3].
    + (* Id *)
      exists 1. simpl. apply lookup_elabEnv. exact H.
Qed.

(**
 * So [Bind] earns no expressive power: it is definable sugar over
 * [App]/[Lambda], and [elab_preserves] certifies the desugaring.  A
 * real compiler front-end elaborates a large surface syntax down to a
 * small core exactly this way - here we have the whole story, proof
 * included, for one construct.
 *)

(* ================================================================ *)
(* SECTION 10: DIVERGENCE, STRICT vs LAZY                          *)
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
 * A LAZY (call-by-name) interpreter makes the alternative precise, and -
 * just like [evalDyn] for scoping - it DISAGREES with [evalM] on a
 * witness term.  The idea: a bound name (or a function argument) is not
 * evaluated eagerly; instead we store an unevaluated THUNK - the
 * expression paired with the environment it should run in - and force it
 * only when the name is actually looked up.
 *
 * An environment now maps names to thunks, and a thunk carries an
 * environment of thunks, so [LThunk] is a nested inductive (through
 * [list]/[prod]), exactly as [ClosureV] was.
 *)
Inductive LThunk : Type :=
| Thk : FBAE -> list (string * LThunk) -> LThunk.

(* Lazy values: numbers and closures, closures capturing a thunk-env. *)
Inductive LVal : Type :=
| LNumV : nat -> LVal
| LCloV : string -> FBAE -> list (string * LThunk) -> LVal.

(**
 * Compare to [evalM].  The only cases that differ are the ones that
 * INTRODUCE a binding ([Bind], [App]) - which now thunk instead of
 * evaluate - and [Id], which now FORCES the thunk it finds.  Arithmetic
 * is still strict in its operands (you cannot add a thunk), so [Plus]
 * and [Minus] force by evaluating their subexpressions.  Like every
 * interpreter in this chapter it is fuel-driven.
 *)
Fixpoint evalL (fuel : nat) (env : Env LThunk) (e : FBAE) : option LVal :=
  match fuel with
  | 0 => None
  | S k =>
      match e with
      | Num n => Some (LNumV n)
      | Plus l r =>
          match evalL k env l, evalL k env r with
          | Some (LNumV a), Some (LNumV b) => Some (LNumV (a + b))
          | _, _ => None
          end
      | Minus l r =>
          match evalL k env l, evalL k env r with
          | Some (LNumV a), Some (LNumV b) => Some (LNumV (a - b))
          | _, _ => None
          end
      | Bind i v b =>
          (* the bound expression is NOT evaluated - just thunked *)
          evalL k (extend i (Thk v env) env) b
      | Lambda i b => Some (LCloV i b env)
      | App f a =>
          match evalL k env f with
          | Some (LCloV i b cenv) =>
              (* the ARGUMENT is thunked in the CALLER's env, unevaluated *)
              evalL k (extend i (Thk a env) cenv) b
          | _ => None
          end
      | Id x =>
          match lookup x env with
          | Some (Thk e' env') => evalL k env' e'   (* force on demand *)
          | None => None
          end
      end
  end.

(**
 * THE DISAGREEMENT.  On [unusedDiverge], the strict [eval] forces the
 * divergent [omega] before ever reaching the body and loops; the lazy
 * [evalL] binds [z] to a thunk it never forces, so it returns [5].  This
 * is the strict/lazy analogue of the 4-vs-5 [scopeTest].
 *)
Definition unusedDiverge : FBAE := Bind "z" omega (Num 5).

Example strict_unusedDiverge : eval unusedDiverge = None.
Proof. reflexivity. Qed.

Example lazy_unusedDiverge : evalL 100 nil unusedDiverge = Some (LNumV 5).
Proof. reflexivity. Qed.

(* Laziness only DEFERS - it does not discard.  If the body actually
   USES the bound name, forcing its thunk still diverges. *)
Example lazy_usedDiverge : evalL 100 nil (Bind "z" omega (Id "z")) = None.
Proof. reflexivity. Qed.

(* And on terminating programs the lazy interpreter agrees with the
   strict one: forcing an argument that is genuinely needed. *)
Example lazy_inc : evalL 100 nil (App incFun (Num 4)) = Some (LNumV 5).
Proof. reflexivity. Qed.

(**
 * So strict and lazy are not cosmetic: they disagree on TERMINATION.
 * Choosing between them is choosing whether [Bind]/[App] evaluate the
 * bound/argument expression eagerly or defer it in a thunk - the topic
 * of the course's "Strict and Lazy" section.
 *)

(* ================================================================ *)
(* SECTION 11: TOWARD RECURSION (TEASER)                            *)
(* ================================================================ *)

(**
 * [omega] was self-application that loops.  RECURSION is the same trick
 * made useful: self-application PARAMETERISED by the function to iterate.
 * A FIXPOINT COMBINATOR [fix] is a closed term with [fix F ~> F (fix F)],
 * so a function receives its own recursive call as an argument - and it
 * is DEFINABLE from [Lambda]/[App] alone, with NO new language construct.
 * The Y combinator does this; the Z combinator eta-guards the
 * self-application so it also survives call-by-value.
 *
 * But we cannot make recursion PRODUCTIVE here: FBAE has no CONDITIONAL
 * (no [if]/[isZero], and [Minus] is truncated but nothing BRANCHES on
 * it), so a recursion can never test its argument and stop - it can only
 * diverge.  That missing ingredient, and the Y/Z combinators running real
 * summation and factorial (Z under strict [evalM], Y under lazy [evalL]),
 * are the subject of the next chapter:
 *
 *   Untyped Recursion  --  Rec/plih_rec_lecture.v
 *   https://ku-sldg.github.io/plih//funs/7-Untyped-Recursion.html
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
 *   6. Illustrated currying, and made the strict-vs-lazy choice precise
 *      with a call-by-name interpreter [evalL] (thunks forced on demand)
 *      that DISAGREES with strict [evalM] on termination ([omega] bound
 *      but unused: [None] vs [Some 5]).
 *   7. Defined ELABORATION [elab] desugaring [Bind] into [App]/[Lambda],
 *      showed it eliminates every [Bind] ([elab_bindFree]), and proved it
 *      preserves evaluation ([elab_preserves]).
 *   8. Previewed RECURSION: fixpoint combinators ([Y]/[Z]) are definable
 *      from [Lambda]/[App], but productive recursion needs a CONDITIONAL
 *      FBAE lacks - delivered in the Untyped Recursion chapter (Rec/).
 *
 * Next: UNTYPED RECURSION adds a conditional and runs the Y/Z combinators
 * for real (Rec/).  Then TYPED functions rule out the stuck/divergent
 * programs that fuel had to absorb here, restoring a total story.
 *)
