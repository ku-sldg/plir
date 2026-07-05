(**
 * ROCQ TACTICS CHEAT SHEET
 * ================================================================
 *
 * Quick reference for the tactics used across all PLIH chapters.
 * Covers AE through RSEMon; earlier chapters are simpler subsets.
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
(* OPTION & CONSTRUCTOR TACTICS                                     *)
(* ================================================================ *)

(**
 * discriminate
 * ---------
 * Refute a hypothesis that equates two distinct constructors.
 *
 * Context: H : Some x = None   (or  H : NumV n = BoolV b, etc.)
 * After 'discriminate.':
 *   Proof complete! (the hypothesis is absurd)
 *
 * Use: After 'destruct (f x) as [v |] eqn:E' when one branch of
 *      'f x = None' contradicts a hypothesis saying it succeeded.
 *      Also: 'simpl in H. discriminate.' when the hypothesis only
 *      becomes contradictory after one reduction step.
 *
 * Common idiom: 'try discriminate.' dispatches all the impossible
 *      branches at once after a uniform destruct over constructors.
 *)

(**
 * injection H as H
 * ---------
 * Extract the argument of a constructor equality.
 *
 * Context: H : Some v = Some w   (or  H : NumV n = NumV m)
 * After 'injection H as H.':
 *   Context: H : v = w
 *
 * Use: When you know two wrapped values are equal and need the
 *      inner equality.  Almost always followed by 'subst.':
 *
 *   injection H as H; subst v.
 *
 *      After which v is replaced by w everywhere in the context.
 *)

(**
 * subst x   /   subst
 * ---------
 * Replace a variable by its definition using an equality hypothesis.
 *
 * Context: H : x = expr
 * After 'subst x.' (or plain 'subst'):
 *   Every occurrence of x in the goal and context becomes expr,
 *   and H is consumed.
 *
 * Use: After 'injection H as H.' when the inner equality identifies
 *      a variable.  'subst' with no argument substitutes every
 *      variable that has a unique equality hypothesis.
 *)

(**
 * destruct (f x) as [v |] eqn:E   (option case split)
 * ---------
 * Case-split on whether an option-returning function succeeded.
 *
 * After 'destruct (f x) as [v |] eqn:E.':
 *   Subgoal 1:  E : f x = Some v   (success branch)
 *   Subgoal 2:  E : f x = None     (failure branch)
 *
 * Use: The single most common pattern once eval returns
 *      'option Value'.  Name the equation E so you can rewrite
 *      with it or feed it to 'discriminate'.
 *
 * Variant for match on a nested result:
 *   destruct (evalM k env e) as [[n | b | i bd ce] |] eqn:E; try discriminate.
 *   -- one branch per constructor of Value, plus the None branch;
 *      'try discriminate' kills the off-type constructors at once.
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
(* WORKING WITH HYPOTHESES                                          *)
(* ================================================================ *)

(**
 * simpl in H   /   simpl in *
 * ---------
 * Simplify a hypothesis (or all hypotheses and the goal).
 *
 * Context: H : eval (Num 5) = v
 * After 'simpl in H.':
 *   Context: H : Some (NumV 5) = v
 *
 * Use: When 'discriminate' or 'injection' needs the hypothesis to be
 *      reduced first.  'simpl in *' normalises everywhere at once.
 *
 * Common idiom: 'simpl in H; discriminate.' refutes a hypothesis
 *      that only becomes contradictory after one reduction step.
 *)

(**
 * apply L in H
 * ---------
 * Use a lemma L to transform hypothesis H forward.
 *
 * Context: H : P /\ Q
 *          (and library lemma andb_true_iff : A && B = true <-> A = true /\ B = true)
 * After 'apply andb_true_iff in H. destruct H as [Ha Hb].':
 *   Context: Ha : A = true   Hb : B = true
 *
 * Use: Forward reasoning.  Common with 'andb_true_iff', 'orb_false_iff',
 *      'String.eqb_eq', 'String.eqb_neq', 'Nat.ltb_lt', 'Nat.eqb_eq'.
 *)

(**
 * rewrite H in H2   /   rewrite H in *
 * ---------
 * Substitute equals-for-equals inside a hypothesis (or everywhere).
 *
 * Context: H : eval e = Some v    H2 : P (eval e)
 * After 'rewrite H in H2.':
 *   Context: H2 : P (Some v)
 *
 * Use: When the evidence you need is in a hypothesis, not the goal.
 *      'rewrite H in *' updates both the goal and every hypothesis
 *      simultaneously (useful but can be noisy).
 *)

(**
 * pose proof (L args) as H
 * ---------
 * Add a fact to the context without changing the goal.
 *
 * After 'pose proof (size_pos e) as Hpos.':
 *   Context: Hpos : 0 < size e
 *   Goal:    unchanged
 *
 * Use: To introduce a library result or IH application into context
 *      before you can use it.  Often paired with 'lia'.
 *)

(**
 * unfold f in *   /   unfold f in H
 * ---------
 * Expand a Definition in hypotheses (or a specific hypothesis).
 *
 * Use: Same as 'unfold f' for the goal, but targets hypotheses.
 *      'unfold ae_equiv in *.' is the canonical first step when
 *      an equivalence relation defined by 'Definition' appears in
 *      both a hypothesis and the goal.
 *)

(* ================================================================ *)
(* CONTROLLED REDUCTION                                             *)
(* ================================================================ *)

(**
 * cbn [f]   /   cbn -[f]
 * ---------
 * Perform beta/iota reduction, unfolding only (or everything except)
 * the named definitions.
 *
 * cbn [evalM]:
 *   Unfolds one top-level call to evalM and reduces, while leaving
 *   recursive calls to evalM as-is.  Use this to expose the match
 *   on a single constructor without unwinding the whole interpreter.
 *
 * cbn -[evalM]:
 *   Reduce all beta/iota redexes EXCEPT inside evalM.  This is the
 *   workhorse after rewriting the IH in a monotonicity proof: it
 *   peels one layer of the outer wrapper (a pair, a monad action)
 *   so the next 'destruct' or 'exact H' can fire.
 *
 * Use: Wherever 'simpl' is too aggressive (it unrolls everything) or
 *      too weak (it stops at a match it cannot reduce).
 *)

(**
 * cbv beta iota delta [ops]
 * ---------
 * Unfold exactly the listed definitions and perform all beta/iota
 * steps, leaving everything else alone.
 *
 * Example:
 *   cbv beta iota delta [bindS retS getS putS failS].
 *
 * Use: For monad-law proofs where you need the monad operations to
 *      compute down to their underlying pair/option/function
 *      manipulations, but you do not want to unfold the semantic
 *      function 'evalM' itself.  This is more surgical than 'simpl'
 *      and avoids the performance trap of unrolling large fixpoints.
 *)

(**
 * cbn [forget]
 * ---------
 * Project the success branch of a Reader+State+Either computation,
 * discarding the error channel.  Appears in the RSEMon refinement
 * proof after each 'destruct (evalRSE ...)' to expose what the
 * forget-map produces on the Success/Error cases.
 *
 * Idiom:
 *   destruct (evalRSE k e env s) as [msg | [v s']];
 *   cbn [forget]; try reflexivity.
 *
 * Use: Refinement theorems (evalRSE_refines) only.
 *)

(**
 * eapply L
 * ---------
 * Like 'apply', but leaves unresolved arguments as metavariables to
 * be filled in later (often by the next tactic or by unification).
 *
 * Example:
 *   eapply evalM_app_closure.
 *   -- Rocq figures out the closure components from the goal.
 *
 * Use: When 'apply L' fails because one or more of L's arguments
 *      cannot be inferred from the goal alone.  The unknowns appear
 *      as '?x' and must be resolved before 'Qed'.
 *)

(**
 * ltac:(tac)
 * ---------
 * Run a tactic inline, as a term, inside a larger expression.
 *
 * Example:
 *   rewrite (IH k2 env e (NumV a) ltac:(lia) El).
 *   -- 'ltac:(lia)' produces the proof of the arithmetic side-
 *      condition (k2 < k1, or 0 < k2, etc.) on the spot.
 *
 * Use: When a lemma requires a proof as one of its arguments and that
 *      proof is trivial arithmetic.  Avoids a separate 'assert'.
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

(**
 * PATTERN 6: Prove a property about an option-returning evaluator
 * ================================================================
 *
 * Goal: eval e = Some v -> isNumV v = true
 * (where eval returns 'option Value')
 *
 *   Proof.
 *     intros [| k] env e v H; simpl in H; [discriminate |].
 *     destruct (evalM k env e1) as [[n | b | i bd ce] |] eqn:E1;
 *       try discriminate.
 *     injection H as H; subst v.
 *     reflexivity.
 *   Qed.
 *
 * Key steps:
 *   1. 'simpl in H' exposes the constructor match inside eval.
 *   2. 'destruct ... eqn:E; try discriminate' kills impossible branches.
 *   3. 'injection H as H; subst v' extracts the exact value.
 *)

(**
 * PATTERN 7: Prove an inductive predicate with 'simpl. rewrite H1, H2.'
 * ================================================================
 *
 * Goal: exists n, eval (Plus a b) = Some (NumV n)
 * Given: IH1 : exists n1, eval a = Some (NumV n1)
 *        IH2 : exists n2, eval b = Some (NumV n2)
 *
 *   Proof.
 *     destruct IH1 as [n1 H1]. destruct IH2 as [n2 H2].
 *     exists (n1 + n2).
 *     simpl. rewrite H1, H2. reflexivity.
 *   Qed.
 *
 * Key: 'simpl' opens the match; 'rewrite H1, H2' fills in the
 *      known option results so the remaining goal is 'reflexivity'.
 *)

(**
 * PATTERN 8: Fuel monotonicity proof
 * ================================================================
 *
 * Goal: forall f1 f2 env e v, f1 <= f2 -> evalM f1 env e = Some v
 *                                       -> evalM f2 env e = Some v
 *
 *   Proof.
 *     induction f1 as [| k IH]; intros f2 env e v Hle H.
 *     - simpl in H. discriminate.       (* 0 fuel never succeeds *)
 *     - destruct f2 as [| k2]; [lia |].
 *       destruct e; simpl in H |- *.
 *       + (* leaf constructor *) exact H.
 *       + (* binary constructor *)
 *         destruct (evalM k env e1) as [...] eqn:El; try discriminate.
 *         rewrite (IH k2 env e1 _ ltac:(lia) El).
 *         cbn -[evalM].
 *         rewrite (IH k2 env e2 _ ltac:(lia) Er).
 *         cbn -[evalM]. exact H.
 *   Qed.
 *
 * Key recipe:
 *   1. Induction on the SMALLER fuel f1.
 *   2. Base (f1=0): 'simpl in H; discriminate' since 0 fuel yields None.
 *   3. Step: peel f2 with 'destruct f2 as [| k2]'; kill f2=0 with 'lia'.
 *   4. For each sub-computation: 'destruct ... eqn:E; try discriminate'
 *      to get the intermediate result; apply IH with 'ltac:(lia)'; then
 *      'cbn -[evalM]' to expose the next step without expanding evalM.
 *)

(**
 * PATTERN 9: Monadic law proof
 * ================================================================
 *
 * Goal: bindM (retM a) f = f a
 * (where retM and bindM are defined as functions over option/state/reader/either)
 *
 *   Proof.
 *     intros ctx.
 *     cbv beta iota delta [bindM retM askM localM failM].
 *     reflexivity.
 *   Qed.
 *
 * Key: 'cbv beta iota delta [ops]' unfolds ONLY the listed monad
 *      combinators, reducing the goal to an equality that
 *      'reflexivity' can close.  Avoid 'simpl' here — it tends to
 *      over-unfold and produce unreadable goals.
 *)

(**
 * PATTERN 10: Agreement theorem
 * ================================================================
 *
 * Goal: forall e env, evalMonad e env = evalDirect e env
 * (prove that a monadic refactor computes the same answer)
 *
 *   Proof.
 *     induction e; intros env.
 *     - (* leaf *) reflexivity.
 *     - (* unary *)
 *       simpl. rewrite <- IHe. reflexivity.
 *     - (* binary *)
 *       simpl. rewrite <- IHe1, <- IHe2. reflexivity.
 *   Qed.
 *
 * Key: 'simpl' unfolds both evaluators to the same shape; the IHs
 *      close each sub-expression.  When the goal does not line up
 *      automatically, 'unfold bindM, retM.' before 'simpl' often
 *      helps.  See RMon/EMon/SMon/RSMon/RSEMon for real instances.
 *)

(**
 * PATTERN 11: Refinement theorem (forget map)
 * ================================================================
 *
 * Goal: forall e env s,
 *         forget (evalRSE e env s) = evalRS e env s
 * (prove that dropping the error channel recovers the simpler semantics)
 *
 *   Proof.
 *     induction e; intros env s; simpl.
 *     - reflexivity.
 *     - rewrite <- IHe1.
 *       destruct (evalRSE _ e1 env s) as [msg | [v s1]];
 *         cbn [forget]; try reflexivity.
 *       rewrite <- IHe2.
 *       destruct (evalRSE _ e2 env s1) as [m2 | [v2 s2]];
 *         cbn [forget]; reflexivity.
 *   Qed.
 *
 * Key recipe:
 *   1. 'rewrite <- IH' aligns the sub-expression before destructing.
 *   2. 'destruct (evalRSE ...) as [msg | [v s']]' splits on error/success.
 *   3. 'cbn [forget]' reduces the projection on each branch.
 *   4. 'try reflexivity' closes trivial branches; non-trivial ones
 *      recurse into the next 'destruct'.
 *)

(**
 * PATTERN 12: String identifier case split
 * ================================================================
 *
 * Goal: subst i v (Id j) = if i == j then v else Id j
 * or any property involving identifier equality (String.eqb).
 *
 *   Proof.
 *     intros i j v.
 *     destruct (String.eqb i j) eqn:E.
 *     - apply String.eqb_eq in E. subst. simpl. rewrite String.eqb_refl. reflexivity.
 *     - apply String.eqb_neq in E. simpl. rewrite E. reflexivity.
 *   Qed.
 *
 * Key library lemmas:
 *   String.eqb_eq  : String.eqb x y = true  -> x = y
 *   String.eqb_neq : String.eqb x y = false -> x <> y
 *   String.eqb_refl : String.eqb x x = true
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
 * Does it depend on the structure of e?
 * |- Yes, must hold for all e and needs facts about subterms
 * |   -> intro e. induction e as [...]
 * |- Yes, just a per-constructor case split
 * |   -> destruct e as [...]
 * |- No -> next question
 *
 * Is there an option-valued sub-computation to case-split?
 * |- Yes -> destruct (evalM k env e) as [[n | b | ...] |] eqn:E;
 * |         try discriminate.
 * |         (then injection / subst / rewrite for the success branch)
 * |- No  -> next question
 *
 * Does a hypothesis contain a contradictory equality?
 * |- Yes, directly (Some x = None, NumV n = BoolV b)
 * |   -> discriminate.
 * |- Yes, but only after reduction
 * |   -> simpl in H. discriminate.
 * |- No -> next question
 *
 * Is it an equivalence (ae_equiv / abe_equiv / ...) goal?
 * |- Yes -> unfold ae_equiv in *. simpl. (then reflexivity / lia)
 * |- No  -> next question
 *
 * Is it a monadic agreement or law goal?
 * |- Law (bind (ret a) f = f a, etc.)
 * |   -> intros. cbv beta iota delta [bind ret ...]. reflexivity.
 * |- Agreement (evalMonadic = evalDirect)
 * |   -> induction e; simpl; rewrite <- IHe (or IHe1, IHe2); reflexivity.
 * |- Refinement (forget (evalRSE ...) = evalRS ...)
 * |   -> induction e; rewrite <- IH; destruct evalRSE; cbn [forget]; ...
 * |- No -> next question
 *
 * Is there a relevant lemma L?
 * |- It matches the goal exactly         -> exact L   (or apply L)
 * |- It is one step of the proof          -> apply L
 * |- It applies to a hypothesis H         -> apply L in H
 * |- You must combine it with other facts -> assert (...) by apply L; ...
 * |- It needs an arithmetic side-condition inline
 * |   -> rewrite (L args ltac:(lia) ...).
 *)

(* ================================================================ *)
(* QUICK REFERENCE TABLE                                            *)
(* ================================================================ *)

(**
 * TACTIC                        | USE WHEN                       | EXAMPLE
 * ==============================|================================|============================
 * reflexivity                   | both sides equal by comp.      | eval (Num 5) = 5
 * simpl                         | need to unfold eval            | eval (Plus ...) = ...
 * simpl in H                    | simplify a hypothesis          | simpl in H; discriminate
 * lia                           | linear arithmetic goal         | n + 5 >= n
 * intro x / intros              | goal is forall / ->            | forall x, P x
 * induction e as [...]          | property for all e             | forall e, 0 <= eval e
 * destruct e as [...]           | per-constructor split          | handle Num/Plus/Minus
 * destruct (f x) as [v|] eqn:E  | option case split              | destruct (eval e) as [v|]
 * discriminate                  | hypothesis equates two ctors   | Some x = None -> ...
 * injection H as H; subst       | extract inner equality         | Some v = Some w -> v=w
 * unfold d                      | expose a Definition            | unfold ae_equiv
 * unfold d in *                 | expose Definition in hyps too  | unfold ae_equiv in *
 * rewrite H                     | substitute via equality        | rewrite Nat.add_comm
 * rewrite H in H2               | rewrite inside a hypothesis    | rewrite Ev in H
 * apply L in H                  | forward reasoning from hyp     | apply andb_true_iff in H
 * pose proof (L args) as H      | add fact to context            | pose proof (size_pos e)
 * assert (H : P)                | need an intermediate fact      | assert (H : 0 <= eval e)
 * cbn [f]                       | unfold only f, reduce rest     | cbn [evalM]
 * cbn -[f]                      | reduce all except f            | cbn -[evalM]
 * cbv beta iota delta [ops]     | unfold exact monad ops         | cbv beta iota delta [bindS]
 * eapply L                      | apply with unresolved args     | eapply evalM_app_closure
 * ltac:(tac)                    | tactic as inline term          | rewrite (IH _ ltac:(lia) H)
 * try tac                       | attempt, continue on failure   | try discriminate
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
 * TIP 7: Use plih_ae_solutions.v (and other _solutions.v files) as a
 *        reference if a proof balloons -- there is usually a shorter way.
 * TIP 8: When eval returns 'option Value', your first move is nearly
 *        always 'destruct (eval ...) as [v |] eqn:E; try discriminate.'
 *        It kills the impossible branches immediately.
 * TIP 9: 'injection H as H; subst v.' is the idiom to extract a value
 *        from 'Some v = Some w'; do them together, not separately.
 * TIP 10: Prefer 'cbn [f]' over 'simpl' when you only want one
 *         definition to unfold -- 'simpl' can cascade unpredictably.
 * TIP 11: 'cbn -[evalM]' after rewriting an IH in a monotonicity proof
 *         peels one wrapper layer without unrolling the interpreter.
 *         It is the bridge between each 'destruct ... eqn:E' step.
 * TIP 12: For monad law proofs use 'cbv beta iota delta [ops].' with
 *         ONLY the monad combinators listed -- never 'simpl' or plain
 *         'unfold', which can pull in evalM and blow up the goal.
 * TIP 13: 'ltac:(lia)' lets you discharge arithmetic side-conditions
 *         inline inside a 'rewrite (IH k2 ... ltac:(lia) ...).'
 *         without a separate 'assert'.
 * TIP 14: 'try tac.' after a uniform 'destruct' eliminates impossible
 *         branches silently.  'try discriminate.' and 'try reflexivity.'
 *         together close most of the off-type sub-goals in one shot.
 * TIP 15: 'apply L in H.' (forward) vs 'apply L.' (backward) -- use
 *         forward when you have the evidence and need the conclusion;
 *         backward when you have the conclusion and need to produce
 *         evidence.  'andb_true_iff', 'orb_false_iff', 'String.eqb_eq'
 *         are almost always used forward.
 *)
