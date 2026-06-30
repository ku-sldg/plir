(**
 * ROCQ TACTICS CHEAT SHEET for AE Module
 * ================================================================
 *
 * Quick reference for the tactics used in Arithmetic Expressions.
 *
 * Recall the AE type and interpreter from the lecture:
 *
 *   Inductive AE : Type :=
 *   | Num   : nat -> AE
 *   | Plus  : AE -> AE -> AE
 *   | Minus : AE -> AE -> AE.
 *
 *   Fixpoint eval (e : AE) : nat :=
 *     match e with
 *     | Num x    => x
 *     | Plus x y  => eval x + eval y
 *     | Minus x y => eval x - eval y
 *     end.
 *
 *   Definition ae_equiv (e1 e2 : AE) : Prop := eval e1 = eval e2.
 *
 * Print this out and keep it on your desk while working on exercises!
 *)

(* ================================================================ *)
(* BASIC TACTICS                                                    *)
(* ================================================================ *)

(**
 * intro x
 * ---------
 * Introduce a variable from a [forall] into the context.
 *
 * Goal: forall x, P x
 * After 'intro x.':
 *   Context: x : ...
 *   Goal:    P x
 *
 * Use: Always use this to get variables into scope.
 *)

(**
 * intros x y z
 * ---------
 * Introduce several variables (or hypotheses) at once.
 *
 * Goal: forall x y z, P x y z
 * After 'intros x y z.':
 *   Context: x y z : ...
 *   Goal:    P x y z
 *
 * Use: Faster than multiple 'intro' calls.  With no names,
 *      'intros' introduces everything it can with chosen names.
 *)

(**
 * reflexivity
 * ---------
 * Close a goal whose two sides are equal by computation.
 *
 * Goal: eval (Num 5) = 5
 * After 'reflexivity.':
 *   Proof complete! (Both sides compute to 5.)
 *
 * Use: When both sides reduce to the same term.  In Rocq,
 *      'reflexivity' performs the needed computation itself,
 *      so 'eval (Plus (Num 3) (Num 4)) = 7' closes directly.
 *)

(**
 * simpl
 * ---------
 * Simplify the goal by computing/unfolding recursive definitions.
 *
 * Goal: eval (Plus (Num 3) (Num 4)) = 7
 * After 'simpl.':
 *   Goal: 3 + 4 = 7   (and often Rocq finishes the arithmetic too)
 *
 * Use: To expand [eval] (and other Fixpoints) so you can see the
 *      arithmetic underneath.  Follow with 'lia' or 'reflexivity'.
 *
 * Related: 'cbn' is a more controllable cousin; 'cbn [eval]'
 *          unfolds only the named definitions.  'unfold eval'
 *          unfolds without doing any further reduction.
 *)

(**
 * lia
 * ---------
 * Solve linear integer/natural arithmetic automatically.
 *
 * Goal: n + 5 >= n + 1
 * After 'lia.':
 *   Proof complete!
 *
 * Use: For any goal built from +, -, *, <, >, =, >=, <=, and the
 *      logical connectives over them.  'lia' knows commutativity,
 *      associativity, etc.  Import it with 'From Stdlib Require
 *      Import Lia.'
 *)

(* ================================================================ *)
(* CONTROL FLOW TACTICS                                             *)
(* ================================================================ *)

(**
 * assert (H : P)
 * ---------
 * Introduce an intermediate fact you then have to prove.
 *
 * After 'assert (H : P).':
 *   Subgoal 1: P                 (prove the fact)
 *   Subgoal 2: original goal     (now with H : P in context)
 *
 * Use: To break a hard proof into a lemma you establish on the way.
 *      'assert (H : P) by tac.' proves the fact inline with 'tac'.
 *)

(**
 * exact H
 * ---------
 * Finish a goal using an existing hypothesis (or term).
 *
 * Context: H : P x
 * Goal:    P x
 * After 'exact H.':
 *   Proof complete!
 *
 * Use: When you already have the exact proof in context.
 *)

(**
 * apply L
 * ---------
 * Use a lemma/hypothesis to transform the goal.
 *
 * Lemma: L : P x -> Q x
 * Goal:  Q x
 * After 'apply L.':
 *   Goal: P x
 *
 * Use: When the conclusion of L matches the goal; you are left to
 *      prove L's premises.  'apply L in H.' instead transforms a
 *      hypothesis H forward.
 *)

(**
 * revert x
 * ---------
 * Move a variable from the context back into the goal (the
 * opposite of 'intro').
 *
 * Context: x : nat
 * Goal:    P x
 * After 'revert x.':
 *   Goal: forall x, P x
 *
 * Use: To generalize/strengthen the goal before 'induction'.
 *)

(* ================================================================ *)
(* INDUCTION & CASE ANALYSIS                                        *)
(* ================================================================ *)

(**
 * induction e as [ n | a IHa b IHb | a IHa b IHb ]
 * ---------
 * Structural induction on e : AE.  The bracketed pattern names the
 * arguments and inductive hypotheses, one '|'-separated group per
 * constructor, in declaration order:
 *
 *   [ n                  ]   -- Num n
 *   [ a IHa b IHb        ]   -- Plus a b,  with IHa : ... a, IHb : ... b
 *   [ a IHa b IHb        ]   -- Minus a b, with IHa, IHb likewise
 *
 * Use: For properties that must hold for every e : AE.
 *
 * Example:
 *   Lemma eval_nonneg : forall e, 0 <= eval e.
 *   Proof. intro e. induction e; simpl; lia. Qed.
 *
 * (Here the plain 'induction e' with no 'as' lets Rocq pick names;
 *  '; simpl; lia' then discharges all three cases uniformly.)
 *)

(**
 * destruct e as [ n | a b | a b ]
 * ---------
 * Case analysis: split into one subgoal per constructor of e,
 * WITHOUT inductive hypotheses.
 *
 * Use: When a function behaves differently per constructor but you
 *      do not need a hypothesis about the subterms.
 *
 * Example (split on whether the goal's boolean test holds):
 *   destruct (eval e1 <? eval e2) eqn:E.
 *   - (* E : (eval e1 <? eval e2) = true  *) ...
 *   - (* E : (eval e1 <? eval e2) = false *) ...
 *
 * The 'eqn:E' clause records the result of the test as a hypothesis
 * H named E, which you usually feed to 'lia' via 'Nat.ltb_lt' /
 * 'Nat.ltb_ge'.
 *)

(**
 * destruct H   (on an equality or disjunction)
 * ---------
 * Context: H : A \/ B
 * After 'destruct H as [HA | HB].':
 *   Subgoal 1: HA : A
 *   Subgoal 2: HB : B
 *
 * For an equality H : x = e, 'destruct H' (or 'subst') substitutes
 * e for x everywhere.
 *
 * Use: To take apart disjunctions, conjunctions, existentials, and
 *      equalities found in the context.
 *)

(* ================================================================ *)
(* EQUALITY & REWRITING TACTICS                                     *)
(* ================================================================ *)

(**
 * congruence
 * ---------
 * Close goals that follow from the given equalities by purely
 * structural reasoning.
 *
 * Goal: Plus (Num 3) e = Plus (Num 3) e
 * After 'congruence.':
 *   Proof complete!
 *
 * Use: When the structure on both sides is obviously the same, or
 *      contradictory equalities are in context.
 *)

(**
 * symmetry
 * ---------
 * Flip an equality goal.
 *
 * Context: H : X = Y
 * Goal:    Y = X
 * After 'symmetry. exact H.':
 *   Proof complete!
 *
 * Use: When you have an equality in the "wrong" direction.
 *)

(**
 * transitivity X
 * ---------
 * Prove Y = Z by going through an intermediate X.
 *
 * Goal: Y = Z
 * After 'transitivity X.':
 *   Subgoal 1: Y = X
 *   Subgoal 2: X = Z
 *
 * Use: When an intermediate value makes each half easy.
 *)

(**
 * rewrite H   (and rewrite <- H)
 * ---------
 * Replace terms in the goal using an equality.
 *
 * Context: H : f x = g x
 * Goal:    P (f x)
 * After 'rewrite H.':
 *   Goal: P (g x)
 *
 * 'rewrite <- H.' rewrites right-to-left (g x back to f x).
 * 'rewrite H in H2.' rewrites inside another hypothesis instead.
 *
 * Use: To substitute equals for equals, including library lemmas
 *      like 'rewrite Nat.add_comm.'
 *)

(* ================================================================ *)
(* TACTICS FOR LOGICAL CONNECTIVES                                  *)
(* ================================================================ *)

(**
 * left / right
 * ---------
 * Choose which side of a disjunction to prove.
 *
 * Goal: P \/ Q
 * After 'left.':
 *   Goal: P
 * After 'right.':
 *   Goal: Q
 *
 * Use: When you know which disjunct holds.
 *)

(**
 * split
 * ---------
 * Break a conjunction into its two halves.
 *
 * Goal: P /\ Q
 * After 'split.':
 *   Subgoal 1: P
 *   Subgoal 2: Q
 *
 * Use: For conjunction goals (and "if and only if").
 *)

(**
 * exists w   /   constructor
 * ---------
 * Provide a witness for an existential.
 *
 * Goal: exists x, P x
 * After 'exists w.':
 *   Goal: P w
 *
 * Use: 'exists (eval e).' is the typical move when the witness is a
 *      concrete value.  'constructor' applies the goal type's
 *      constructor automatically when there is an obvious choice.
 *)

(**
 * intro H   (on an implication)
 * ---------
 * Move the premise of an implication into the context.
 *
 * Goal: P -> Q
 * After 'intro H.':
 *   Context: H : P
 *   Goal:    Q
 *
 * Use: The same 'intro'/'intros' as for forall, applied to '->'.
 *)

(* ================================================================ *)
(* ARITHMETIC: lia                                                  *)
(* ================================================================ *)

(**
 * lia is the workhorse for arithmetic.
 *
 * Handles: +, -, *, <, >, =, >=, <=, and the connectives /\, \/, ->
 * over linear (in)equalities.
 *
 * Examples lia solves automatically:
 *   n + 5 >= n
 *   (n - 3) + 3 = n        (for n >= 3)
 *   Nat.max n m >= n
 *   Nat.min n m <= n
 *   n > 0 -> n >= 1
 *
 * Use: Whenever the remaining goal is arithmetic.  If 'lia' fails,
 *      the goal is probably not (yet) linear arithmetic -- 'simpl'
 *      first, or supply a missing hypothesis.
 *
 * Related: 'nia' handles some nonlinear goals; 'lia' is enough for
 *          everything in the AE module.
 *)

(* ================================================================ *)
(* COMMON PROOF PATTERNS                                            *)
(* ================================================================ *)

(**
 * PATTERN 1: Prove a computation
 * ================================================================
 *
 * Goal: eval (Num 5) = 5
 *
 *   Proof. reflexivity. Qed.        (* both sides compute to 5 *)
 *
 * Goal: eval (Plus (Num 3) (Num 4)) = 7
 *
 *   Proof. simpl. reflexivity. Qed. (* or just 'reflexivity.' *)
 *)

(**
 * PATTERN 2: Prove a property by induction
 * ================================================================
 *
 * Goal: forall e, 0 <= eval e
 *
 *   Proof.
 *     intro e.
 *     induction e; simpl; lia.
 *   Qed.
 *
 * Key: the ';' combinator runs 'simpl; lia' on EVERY case, including
 *      the Plus/Minus cases where the inductive hypotheses are in
 *      scope and 'lia' can use them.
 *)

(**
 * PATTERN 3: Prove an equivalence
 * ================================================================
 *
 * Goal: ae_equiv (Plus e1 e2) (Plus e2 e1)
 * Definition: ae_equiv e1 e2 := eval e1 = eval e2.
 *
 *   Proof.
 *     intros e1 e2.
 *     unfold ae_equiv.
 *     simpl.
 *     lia.                          (* eval e1 + eval e2 = eval e2 + eval e1 *)
 *   Qed.
 *)

(**
 * PATTERN 4: Case split with special handling
 * ================================================================
 *
 * Goal: forall e, eval (optimize_zero e) = eval e
 * where optimize_zero treats (Plus e1 (Num 0)) specially.
 *
 *   Proof.
 *     intro e.
 *     induction e as [ n | a IHa b IHb | a IHa b IHb ].
 *     - (* Num *)   reflexivity.
 *     - (* Plus *)  destruct b as [ m | | ];      (* is the rhs a literal? *)
 *                   simpl; ... (* use IHa, IHb *)
 *     - (* Minus *) simpl; rewrite IHa, IHb; reflexivity.
 *   Abort.  (* sketch only -- the real proof is in the solutions *)
 *)

(**
 * PATTERN 5: Introduce intermediate facts
 * ================================================================
 *
 * Goal: P x where the proof needs a lemma along the way.
 *
 *   Proof.
 *     intro x.
 *     assert (H1 : fact1 x).
 *     { (* prove fact1 x *) ... }
 *     (* now H1 : fact1 x is available *)
 *     ...
 *   Qed.
 *)

(* ================================================================ *)
(* COMMON MISTAKES & FIXES                                          *)
(* ================================================================ *)

(**
 * MISTAKE 1: Forgetting to simplify the definition
 * ================================================================
 *
 * If the goal still mentions 'eval (Plus ...)' and 'reflexivity'
 * fails, run 'simpl.' (or 'unfold eval.') first so the recursive
 * definition is computed away.
 *)

(**
 * MISTAKE 2: Not using the inductive hypotheses
 * ================================================================
 *
 * A property like 'forall e, 0 <= eval e' needs 'induction e', not
 * 'destruct e' -- only induction gives you IHa/IHb for the subterms.
 *)

(**
 * MISTAKE 3: Using induction where case analysis suffices
 * ================================================================
 *
 * If you never use an inductive hypothesis, 'destruct e' is clearer
 * (and avoids dangling IHs) than 'induction e'.
 *)

(**
 * MISTAKE 4: Expecting 'simpl' to finish the goal
 * ================================================================
 *
 * 'simpl' only reduces; it does not prove arithmetic.  The usual
 * idiom is 'simpl; lia.' (reduce, then let lia close it).  If 'simpl'
 * over-reduces and obscures the goal, use 'cbn [eval]' or 'unfold
 * eval' to control exactly what unfolds.
 *)

(* ================================================================ *)
(* WORKFLOW: Proving a Lemma                                        *)
(* ================================================================ *)

(**
 * STEP-BY-STEP WORKFLOW:
 *
 * 1. READ the goal carefully.
 *    e.g. Goal: eval (Plus e1 e2) = eval e1 + eval e2
 *    "What does this mean?  Which part is hard?"
 *
 * 2. INTRODUCE variables and hypotheses.
 *    intros e1 e2.
 *
 * 3. SIMPLIFY the goal.
 *    simpl.       (* unfold eval to expose the arithmetic *)
 *
 * 4. CHECK if reflexivity closes it.
 *    reflexivity. (* if both sides are equal by computation *)
 *
 * 5. IF NOT, reach for lia or induction.
 *    lia.                 (* arithmetic goal *)
 *    induction e as [...]. (* structural property over all e *)
 *
 * 6. IN INDUCTION, discharge each case.
 *    Often 'induction e; simpl; lia.' handles all of them at once.
 *
 * 7. WHEN STUCK, introduce an intermediate fact.
 *    assert (H : useful_fact). { ... }
 *)

(* ================================================================ *)
(* DECISION TREE: WHICH TACTIC TO USE?                              *)
(* ================================================================ *)

(**
 * Is the goal an equality?
 * |- Yes, both sides compute to the same thing
 * |   -> reflexivity
 * |- Yes, need to compute eval first
 * |   -> simpl. reflexivity   (or just reflexivity)
 * |- Yes, reduces to an arithmetic identity
 * |   -> simpl. lia
 * |- No -> next question
 *
 * Is it "forall x, ..."  or  "P -> Q"?
 * |- Yes -> intro x  /  intros   (then handle the body)
 * |- No  -> next question
 *
 * Is it a linear arithmetic fact (+, -, <, >, =, >=, <=)?
 * |- Yes -> lia
 * |- No  -> next question
 *
 * Does it depend on the structure of e : AE?
 * |- Yes, must hold for all e and needs facts about subterms
 * |   -> intro e. induction e as [...]
 * |- Yes, just a per-constructor case split
 * |   -> destruct e as [...]
 * |- No -> next question
 *
 * Is it an equivalence (ae_equiv) goal?
 * |- Yes -> unfold ae_equiv. simpl. (then reflexivity / lia)
 * |- No  -> look for a relevant lemma
 *
 * Is there a relevant lemma L?
 * |- It matches the goal exactly        -> exact L   (or apply L)
 * |- It is one step of the proof         -> apply L
 * |- You must combine it with other facts -> assert (...) by apply L; ...
 *)

(* ================================================================ *)
(* QUICK REFERENCE TABLE                                            *)
(* ================================================================ *)

(**
 * TACTIC               | USE WHEN                  | EXAMPLE
 * =====================|===========================|=========================
 * reflexivity          | both sides equal by comp. | eval (Num 5) = 5
 * simpl                | need to unfold eval       | eval (Plus ...) = ...
 * lia                  | linear arithmetic goal    | n + 5 >= n
 * intro x / intros     | goal is forall / ->       | forall x, P x
 * induction e as [...] | property for all e : AE   | forall e, 0 <= eval e
 * destruct e as [...]  | per-constructor split     | handle Num/Plus/Minus
 * destruct t eqn:E     | record result of a test   | destruct (a <? b) eqn:E
 * unfold d             | expose a Definition        | unfold ae_equiv
 * rewrite H            | substitute via equality    | rewrite Nat.add_comm
 * assert (H : P)       | need an intermediate fact  | assert (H : 0 <= eval e)
 *)

(* ================================================================ *)
(* FINAL TIPS                                                       *)
(* ================================================================ *)

(**
 * TIP 1: If stuck, 'simpl' first to see the real arithmetic.
 * TIP 2: Then try 'lia' -- it is excellent at arithmetic reasoning.
 * TIP 3: If 'lia' cannot help, the goal is structural: use induction.
 * TIP 4: Name your inductive hypotheses clearly: IHa, IHb beat H1, H2.
 * TIP 5: The ';' combinator (e.g. 'induction e; simpl; lia') applies a
 *        tactic to every generated subgoal -- great for uniform cases.
 * TIP 6: Check the goal after each tactic to confirm you are making
 *        progress (the IDE shows it live).
 * TIP 7: Use plih_ae_solutions.v as a reference if a proof balloons --
 *        there is usually a shorter way.
 *)
