(**
 * Programming Languages in Rocq - Typed Recursion Lecture
 * Putting recursion back with a primitive typed [Fix]
 *
 * Typing in TFun became so strict that RECURSION disappeared: the Y and Z
 * combinators relied on self-application ([x x]), which cannot be typed.
 * In fact the simply-typed language TFun left is STRONGLY NORMALIZING -
 * every well-typed term terminates.  That is a lovely guarantee, but a
 * language with no recursion cannot compute much.
 *
 * This chapter adds recursion back the honest way: a PRIMITIVE typed
 * [Fix] with its own typing rule.  The bargain is explicit:
 *   - we KEEP type safety - well-typed programs never get stuck;
 *   - we GIVE UP normalization - [Fix] can loop, so a well-typed term may
 *     once again diverge, and the interpreter stays fuel-driven/partial.
 *
 * The plan:
 *   1. TFun's type language [Ty] and typed terms [TFBAEC], plus ONE new
 *      form [Fix f] and a term-level [subst] to unfold it.
 *   2. The type checker [typeof] with the [Fix] rule: if [f : T -> T] then
 *      [Fix f : T].
 *   3. The STRICT interpreter [evalM]: [Fix f] unfolds by substituting the
 *      whole recursion back in for the recursive-call parameter - "fix
 *      sets up what replaces the recursive call", it does not step once.
 *   4. Real recursion: FACTORIAL and SUMMATION, well-typed and computed.
 *   5. The trade-off, machine-checked: self-application is STILL rejected,
 *      yet [Fix] lets a well-typed term DIVERGE ([loopT]).  Type soundness
 *      survives; normalization does not.
 *
 * This mirrors the "Typed Recursion" unit of PLIH:
 *   https://ku-sldg.github.io/plih//types/3-Typed-Recursion.html
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_trec_shared.

Local Open Scope string_scope.
Import ListNotations.

(* ================================================================ *)
(* SECTION 1: THE TYPE LANGUAGE (unchanged from TFun)              *)
(* ================================================================ *)

(**
 * Types are exactly as in Typed Functions: numbers, Booleans, and
 * function types [TArr d r].  [Fix] adds no new TYPE - it recurses at an
 * existing type - so [Ty] and its decidable equality carry over verbatim.
 *)
Inductive Ty : Type :=
| TNum  : Ty
| TBool : Ty
| TArr  : Ty -> Ty -> Ty.

Fixpoint Ty_eqb (a b : Ty) : bool :=
  match a, b with
  | TNum, TNum   => true
  | TBool, TBool => true
  | TArr d1 r1, TArr d2 r2 => andb (Ty_eqb d1 d2) (Ty_eqb r1 r2)
  | _, _ => false
  end.

Lemma Ty_eqb_refl : forall t, Ty_eqb t t = true.
Proof.
  intros t. induction t as [| | d IHd r IHr]; simpl; try reflexivity.
  rewrite IHd, IHr. reflexivity.
Qed.

Lemma Ty_eqb_eq : forall a b, Ty_eqb a b = true -> a = b.
Proof.
  induction a as [| | d1 IHd r1 IHr]; intros b H; destruct b as [| | d2 r2];
    simpl in H; try discriminate; try reflexivity.
  apply andb_true_iff in H. destruct H as [Hd Hr].
  rewrite (IHd d2 Hd), (IHr r2 Hr). reflexivity.
Qed.

Lemma Ty_eqb_true_iff : forall a b, Ty_eqb a b = true <-> a = b.
Proof.
  intros a b. split; [apply Ty_eqb_eq | intros H; subst; apply Ty_eqb_refl].
Qed.

(* ================================================================ *)
(* SECTION 2: THE TERM LANGUAGE + SUBSTITUTION                     *)
(* ================================================================ *)

(**
 * [TFBAEC] is TFun's typed language with ONE new constructor, [Fix].
 * [Fix f] denotes the fixed point of [f]: if [f] is a function that takes
 * "the recursive call" as its argument and returns the recursive
 * function, [Fix f] ties the knot.
 *)
Inductive TFBAEC : Type :=
| Num     : nat -> TFBAEC
| Plus    : TFBAEC -> TFBAEC -> TFBAEC
| Minus   : TFBAEC -> TFBAEC -> TFBAEC
| Mult    : TFBAEC -> TFBAEC -> TFBAEC
| Boolean : bool -> TFBAEC
| IsZero  : TFBAEC -> TFBAEC
| If      : TFBAEC -> TFBAEC -> TFBAEC -> TFBAEC
| Bind    : string -> TFBAEC -> TFBAEC -> TFBAEC
| Lambda  : string -> Ty -> TFBAEC -> TFBAEC
| App     : TFBAEC -> TFBAEC -> TFBAEC
| Fix     : TFBAEC -> TFBAEC                       (* the new form *)
| Id      : string -> TFBAEC.

(**
 * To UNFOLD a [Fix] we substitute a term for an identifier - the same
 * capture-naive [subst] as the Func chapter's substitution interpreter,
 * now over the typed syntax.  Both binders ([Bind] and [Lambda]) shadow
 * the substituted name in their body; [Fix] is not a binder.
 *)
Fixpoint subst (i : string) (v : TFBAEC) (e : TFBAEC) : TFBAEC :=
  match e with
  | Num n      => Num n
  | Plus  l r  => Plus  (subst i v l) (subst i v r)
  | Minus l r  => Minus (subst i v l) (subst i v r)
  | Mult  l r  => Mult  (subst i v l) (subst i v r)
  | Boolean b  => Boolean b
  | IsZero e0  => IsZero (subst i v e0)
  | If c t f   => If (subst i v c) (subst i v t) (subst i v f)
  | Bind i' val b =>
      if String.eqb i i'
      then Bind i' (subst i v val) b
      else Bind i' (subst i v val) (subst i v b)
  | Lambda i' t b =>
      if String.eqb i i' then Lambda i' t b else Lambda i' t (subst i v b)
  | App f a    => App (subst i v f) (subst i v a)
  | Fix f      => Fix (subst i v f)
  | Id i'      => if String.eqb i i' then v else Id i'
  end.

(* ================================================================ *)
(* SECTION 3: THE TYPE CHECKER                                     *)
(* ================================================================ *)

Definition Ctx := Env Ty.

Definition tnumBinop (a b : option Ty) : option Ty :=
  match a, b with
  | Some TNum, Some TNum => Some TNum
  | _, _ => None
  end.

(**
 * [typeof] is TFun's checker with the [Fix] rule added.  THE RULE:
 *
 *     ctx |- f : T -> T
 *   ----------------------
 *     ctx |- Fix f : T
 *
 * [f] must be a function whose domain and range are the SAME type [T]
 * (it maps "a recursive function of type [T]" to "a recursive function of
 * type [T]"), and then [Fix f] has that type [T].  Requiring domain =
 * range is what keeps typing SOUND; PLIH states the rule as "take the
 * range", which coincides here because the two are equal.
 *)
Fixpoint typeof (ctx : Ctx) (e : TFBAEC) : option Ty :=
  match e with
  | Num _ => Some TNum
  | Plus  l r => tnumBinop (typeof ctx l) (typeof ctx r)
  | Minus l r => tnumBinop (typeof ctx l) (typeof ctx r)
  | Mult  l r => tnumBinop (typeof ctx l) (typeof ctx r)
  | Boolean _ => Some TBool
  | IsZero e0 =>
      match typeof ctx e0 with
      | Some TNum => Some TBool
      | _ => None
      end
  | If c t f =>
      match typeof ctx c with
      | Some TBool =>
          match typeof ctx t, typeof ctx f with
          | Some tThen, Some tElse =>
              if Ty_eqb tThen tElse then Some tThen else None
          | _, _ => None
          end
      | _ => None
      end
  | Bind i v b =>
      match typeof ctx v with
      | Some tv => typeof (extend i tv ctx) b
      | None => None
      end
  | Lambda i t b =>
      match typeof (extend i t ctx) b with
      | Some tb => Some (TArr t tb)
      | None => None
      end
  | App f a =>
      match typeof ctx f, typeof ctx a with
      | Some (TArr d r), Some ta => if Ty_eqb d ta then Some r else None
      | _, _ => None
      end
  | Fix f =>
      match typeof ctx f with
      | Some (TArr d r) => if Ty_eqb d r then Some r else None
      | _ => None
      end
  | Id x => lookup x ctx
  end.

Definition typecheck (e : TFBAEC) : option Ty := typeof nil e.

(* ================================================================ *)
(* SECTION 4: THE STRICT INTERPRETER                              *)
(* ================================================================ *)

(**
 * Values are TFun's [NumV]/[BoolV]/[ClosureV].  Unlike TFun, the closure
 * now also stores the parameter's TYPE: [Fix] needs to reconstruct the
 * lambda [Lambda i t b] from the closure in order to substitute the whole
 * recursion back in, and that term requires the ascription [t].
 *)
Inductive TVal : Type :=
| NumV     : nat -> TVal
| BoolV    : bool -> TVal
| ClosureV : string -> Ty -> TFBAEC -> list (string * TVal) -> TVal.

(**
 * The strict (call-by-value) interpreter, TFun's [evalM] plus [Fix].
 *
 * THE [Fix] RULE.  Evaluate [f] to a closure [ClosureV i t b e] (its
 * parameter [i] is the recursive-call name, [b] the body).  Then unfold:
 * substitute the WHOLE recursion [Fix (Lambda i t b)] for [i] in [b], and
 * evaluate that in the closure's environment.  [Fix] does not take one
 * recursion step; it installs "what the recursive call means" and lets
 * ordinary evaluation proceed - looping only as far as the program forces
 * it.  Fuel remains because [Fix] can diverge.
 *)
Fixpoint evalM (fuel : nat) (env : Env TVal) (e : TFBAEC) : option TVal :=
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
      | Mult l r =>
          match evalM k env l, evalM k env r with
          | Some (NumV a), Some (NumV b) => Some (NumV (a * b))
          | _, _ => None
          end
      | Boolean b => Some (BoolV b)
      | IsZero e0 =>
          match evalM k env e0 with
          | Some (NumV n) => Some (BoolV (Nat.eqb n 0))
          | _ => None
          end
      | If c t f =>
          match evalM k env c with
          | Some (BoolV true)  => evalM k env t
          | Some (BoolV false) => evalM k env f
          | _ => None
          end
      | Bind i v b =>
          match evalM k env v with
          | Some v' => evalM k (extend i v' env) b
          | None => None
          end
      | Lambda i t b => Some (ClosureV i t b env)
      | App f a =>
          match evalM k env f with
          | Some (ClosureV i _ b cenv) =>
              match evalM k env a with
              | Some a' => evalM k (extend i a' cenv) b
              | None => None
              end
          | _ => None
          end
      | Fix f =>
          match evalM k env f with
          | Some (ClosureV i t b cenv) =>
              evalM k cenv (subst i (Fix (Lambda i t b)) b)
          | _ => None
          end
      | Id x => lookup x env
      end
  end.

Definition eval (e : TFBAEC) : option TVal := evalM 1000 nil e.

(* ================================================================ *)
(* SECTION 5: FUEL MONOTONICITY (well-definedness of [evalM])      *)
(* ================================================================ *)

(**
 * [Fix] can diverge, so - as in Func and Rec - the well-definedness
 * result is MONOTONICITY: more fuel never changes an answer.  The proof is
 * TFun's, with the closure's new type field and a new [Fix] case (whose
 * unfolded body is handled by the IH exactly like [Bind]'s body).
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
      destruct (evalM k env e1) as [[a | b | s t bd ce] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | b | s t bd ce] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Minus *)
      destruct (evalM k env e1) as [[a | b | s t bd ce] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | b | s t bd ce] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Mult *)
      destruct (evalM k env e1) as [[a | b | s t bd ce] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | b | s t bd ce] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Boolean *) exact H.
    + (* IsZero *)
      destruct (evalM k env e) as [[n | b | s t bd ce] |] eqn:E0; try discriminate.
      rewrite (IH k2 env e (NumV n) ltac:(lia) E0). exact H.
    + (* If *)
      destruct (evalM k env e1) as [[a | bb | s t bd ce] |] eqn:Ec; try discriminate.
      destruct bb.
      * rewrite (IH k2 env e1 (BoolV true) ltac:(lia) Ec).
        apply (IH k2 env e2 v). lia. exact H.
      * rewrite (IH k2 env e1 (BoolV false) ltac:(lia) Ec).
        apply (IH k2 env e3 v). lia. exact H.
    + (* Bind *)
      destruct (evalM k env e1) as [v' |] eqn:Ev; try discriminate.
      rewrite (IH k2 env e1 v' ltac:(lia) Ev).
      apply (IH k2 (extend s v' env) e2 v). lia. exact H.
    + (* Lambda *) exact H.
    + (* App *)
      destruct (evalM k env e1) as [[a | b | s t bd ce] |] eqn:Ef; try discriminate.
      destruct (evalM k env e2) as [a' |] eqn:Ea; try discriminate.
      rewrite (IH k2 env e1 (ClosureV s t bd ce) ltac:(lia) Ef).
      rewrite (IH k2 env e2 a' ltac:(lia) Ea).
      apply (IH k2 (extend s a' ce) bd v). lia. exact H.
    + (* Fix *)
      destruct (evalM k env e) as [[a | b | s t bd ce] |] eqn:Ef; try discriminate.
      rewrite (IH k2 env e (ClosureV s t bd ce) ltac:(lia) Ef).
      apply (IH k2 ce (subst s (Fix (Lambda s t bd)) bd) v). lia. exact H.
    + (* Id *) exact H.
Qed.

(* ================================================================ *)
(* SECTION 6: TYPED RECURSION IN ACTION                           *)
(* ================================================================ *)

(**
 * A recursive GENERATOR takes the recursive call [g] as a parameter and
 * returns the recursive function.  For it to be a legal argument to [Fix]
 * its type must be [T -> T]; here [T = TNum -> TNum].
 *
 *   factGen = \g:(Nat->Nat). \n:Nat. if n=0 then 1 else n * (g (n-1))
 *)
Definition factGen : TFBAEC :=
  Lambda "g" (TArr TNum TNum)
    (Lambda "n" TNum
      (If (IsZero (Id "n"))
          (Num 1)
          (Mult (Id "n") (App (Id "g") (Minus (Id "n") (Num 1)))))).

Definition fact : TFBAEC := Fix factGen.

(* The generator is [(Nat->Nat) -> (Nat->Nat)], so [Fix] gives [Nat->Nat]. *)
Example ty_factGen :
  typecheck factGen = Some (TArr (TArr TNum TNum) (TArr TNum TNum)).
Proof. reflexivity. Qed.

Example ty_fact : typecheck fact = Some (TArr TNum TNum).
Proof. reflexivity. Qed.

Example ty_fact_app : typecheck (App fact (Num 5)) = Some TNum.
Proof. reflexivity. Qed.

(* And it RUNS: 5! = 120, real recursion under a strict interpreter. *)
Example run_fact5 : eval (App fact (Num 5)) = Some (NumV 120).
Proof. reflexivity. Qed.

Example run_fact0 : eval (App fact (Num 0)) = Some (NumV 1).
Proof. reflexivity. Qed.

(* Summation, sum n = n + (n-1) + ... + 0, the PLIH example. *)
Definition sumGen : TFBAEC :=
  Lambda "g" (TArr TNum TNum)
    (Lambda "n" TNum
      (If (IsZero (Id "n"))
          (Num 0)
          (Plus (Id "n") (App (Id "g") (Minus (Id "n") (Num 1)))))).

Definition sum : TFBAEC := Fix sumGen.

Example ty_sum_app : typecheck (App sum (Num 5)) = Some TNum.
Proof. reflexivity. Qed.

Example run_sum5 : eval (App sum (Num 5)) = Some (NumV 15).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* SECTION 7: THE TRADE-OFF (safety kept, normalization lost)      *)
(* ================================================================ *)

(**
 * TYPE SAFETY SURVIVES.  Self-application still cannot be typed - the term
 * that made the untyped language loop is rejected before evaluation, so
 * [Fix] is the ONLY way to write a loop, and it is a deliberate,
 * well-typed one.
 *)
Definition selfApp (t : Ty) : TFBAEC :=
  Lambda "x" t (App (Id "x") (Id "x")).

Example ill_selfApp : typecheck (selfApp (TArr TNum TNum)) = None.
Proof. reflexivity. Qed.

(* [Fix] is still guarded by types: its argument must be a function whose
   domain and range agree.  A non-function, or a mismatched one, is out. *)
Example ill_fix_nonfun : typecheck (Fix (Num 1)) = None.
Proof. reflexivity. Qed.

Example ill_fix_mismatch :
  typecheck (Fix (Lambda "x" TNum (Boolean true))) = None.  (* Nat -> Bool *)
Proof. reflexivity. Qed.

(**
 * NORMALIZATION IS GONE.  This is the price of [Fix].  In pure TFun every
 * well-typed term terminates; here [loopT] is WELL-TYPED (it has type
 * [TNum]) yet DIVERGES - [Fix] of the identity endlessly reinstalls
 * itself with nothing to force a base case.  So [evalM] is genuinely
 * partial again, and the fuel is not a convenience but a necessity.
 *)
Definition loopT : TFBAEC := Fix (Lambda "x" TNum (Id "x")).

Example loopT_well_typed : typecheck loopT = Some TNum.
Proof. reflexivity. Qed.

Example loopT_diverges : evalM 500 nil loopT = None.
Proof. reflexivity. Qed.

(**
 * So the arc completes.  Untyped (Func/Rec): can get STUCK and can
 * DIVERGE.  Simply typed (TFun): neither - total and safe, but no
 * recursion.  Typed recursion (here): SAFE again (no stuck terms) but
 * intentionally NON-total - [Fix] buys back Turing power at the cost of
 * the normalization guarantee.
 *)

(* ================================================================ *)
(* SECTION 8: TYPE SOUNDNESS, WITNESSED                           *)
(* ================================================================ *)

(**
 * Type soundness - well-typed programs do not get stuck - still holds
 * (the [Fix]-induced divergence returns [None] by fuel exhaustion, which
 * is "not yet done", not "stuck on a type error").  As in TFun we witness
 * it: a well-typed program and its value side by side, the value's kind
 * matching the predicted type; a full logical-relations proof is left as
 * advanced material.
 *)
Example sound_fact_ty : typecheck (App fact (Num 4)) = Some TNum.
Proof. reflexivity. Qed.
Example sound_fact_val : eval (App fact (Num 4)) = Some (NumV 24).
Proof. reflexivity. Qed.

(* The base-type canonical-forms slices carry over unchanged from TFun. *)
Definition isNumV (v : TVal) : bool :=
  match v with NumV _ => true | _ => false end.
Definition isBoolV (v : TVal) : bool :=
  match v with BoolV _ => true | _ => false end.

Lemma iszero_yields_bool : forall f env e v,
  evalM f env (IsZero e) = Some v -> isBoolV v = true.
Proof.
  intros [| k] env e v H; simpl in H; [discriminate |].
  destruct (evalM k env e) as [[n | b | s t bd ce] |]; try discriminate.
  injection H as H; subst v. reflexivity.
Qed.

Lemma mult_yields_num : forall f env a b v,
  evalM f env (Mult a b) = Some v -> isNumV v = true.
Proof.
  intros [| k] env a b v H; simpl in H; [discriminate |].
  destruct (evalM k env a) as [[n | bb | s t bd ce] |]; try discriminate;
  destruct (evalM k env b) as [[m | bb | s t bd ce] |]; try discriminate.
  injection H as H; subst v. reflexivity.
Qed.

(* ================================================================ *)
(* SUMMARY                                                          *)
(* ================================================================ *)

(**
 * In this lecture we:
 *   1. Added a primitive [Fix] to TFun's typed language, with a term-level
 *      [subst] to unfold it.
 *   2. Gave [Fix] a typing rule - [f : T -> T] yields [Fix f : T] - and an
 *      evaluation rule that substitutes the whole recursion back in for
 *      the recursive-call parameter.
 *   3. Wrote real, well-typed RECURSION: factorial (5! = 120) and
 *      summation (0..5 = 15), running under the strict interpreter.
 *   4. Re-proved FUEL MONOTONICITY (now with a [Fix] case).
 *   5. Made the bargain explicit and machine-checked: self-application is
 *      still rejected (safety kept), but [Fix] lets a well-typed term
 *      DIVERGE ([loopT]) - normalization is deliberately traded away.
 *
 * Next: the course turns to modeling evaluation itself as a MONAD (the
 * Reader/Either interpreters), and then to STATE.
 *)
