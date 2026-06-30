(**
 * ROCQ TACTICS CHEAT SHEET for AE Module
 * ================================================================
 * 
 * Quick reference for tactics used in Arithmetic Expressions
 * 
 * Print this out and keep it your desk while working on exercises!
 *)

(* ================================================================ *)
(* BASIC TACTICS                                                    *)
(* ================================================================ *)

(**
 * intro x
 * ---------
 * Introduce a variable from a forall into the context
 * 
 * Goal: forall x, P x
 * After 'intro x':
 * Goal: P x
 * Context: x : ...
 * 
 * Use: Always use this to get variables into scope
 *)

(**
 * intros x y z
 * ---------
 * Introduce multiple variables at once
 * 
 * Goal: forall x y z, P x y z
 * After 'intros x y z':
 * Goal: P x y z
 * Context: x y z : ...
 * 
 * Use: Faster than multiple 'intro' calls
 *)

(**
 * reflexivity (or eq_refl)
 * ---------
 * Prove a goal computation
 * 
 * Goal: eval (Num 5) = 5
 * After 'reflexivity':
 * Proof is complete! (Both sides compute to 5)
 * 
 * Use: When both sides simplify to the same term
 *)

(**
 * simp [def1, def2, ...]
 * ---------
 * Simplify the goal unfolding definitions
 * 
 * Goal: eval (Plus (Num 3) (Num 4)) = 7
 * After 'simp [eval]':
 * Goal: 3 + 4 = 7
 * 
 * Use: To expand recursive definitions
 *)

(**
 * lia
 * ---------
 * Solve linear arithmetic automatically
 * 
 * Goal: n + 5 >= n + 1
 * After 'lia':
 * Proof is complete!
 * 
 * Use: For any goal involving +, -, *, <, >, =, >=, <=
 * lia knows: commutativity, associativity, etc.
 *)

(* ================================================================ *)
(* CONTROL FLOW TACTICS                                             *)
(* ================================================================ *)

(**
 * have : P := proof_of_P

(**
 * exact H
 * ---------
 * Finish a goal using an existing hypothesis
 * 
 * Goal: P x
 * Context: H : P x
 * After 'exact H':
 * Proof is complete!
 * 
 * Use: When you already have the exact proof in context
 *)

(**
 * apply L
 * ---------
 * Use a lemma to transform the goal
 * 
 * Goal: P x -> Q x
 * Lemma: L : P x -> Q x
 * After 'apply L':
 * Goal: P x
 * 
 * Use: When you have a lemma that covers part of the goal
 *)

(**
 * revert x
 * ---------
 * Move a variable from context back to goal (opposite of intro)
 * 
 * Goal: P x
 * Context: x : nat
 * After 'revert x':
 * Goal: forall x, P x
 * 
 * Use: When you need to strengthen the goal for induction
 *)

(* ================================================================ *)
(* INDUCTION & CASE ANALYSIS                                        *)
(* ================================================================ *)

(**
 * induction e with
 * | Num n => ...
 * | Plus e1 IHe1 e2 IHe2 => ...
 * | Minus e1 IHe1 e2 IHe2 => ...
 * 
 * Prove structural induction on e : AE
 * 
 * Each case gets:
 * - The pattern (Num n, Plus e1 e2, etc.)
 * - Inductive hypotheses (IHe1, IHe2) for subterms
 * 
 * Use: For properties of recursively-defined types like AE
 * 
 * Example:
 *   Lemma eval_nonneg : forall e, 0 <= eval e := *     intro e

(**
 * cases e with
 * | Num n => ...
 * | Plus e1 e2 => ...
 * | Minus e1 e2 => ...
 * 
 * Case analysis: split a goal into sub-goals constructor
 * 
 * Unlike induction, you don't get inductive hypotheses.
 * Used when you want to analyze what structure e has.
 * 
 * Use: When a function has special behavior for each constructor
 * 
 * Example:
 *   Lemma optimize_correct : forall e,
 *     eval (optimize e) = eval e := *     intro e

(**
 * split_ifs with H
 * ---------
 * Split on all if-then-else in the goal
 * 
 * Goal: if n = 0 then X else Y
 * After 'split_ifs with H':
 * Subgoal 1: n = 0 | X
 * Subgoal 2: ¬(n = 0) | Y
 * 
 * Use: When goal contains if-then-else
 *)

(**
 * destruct H
 * ---------
 * Destructure an equality or disjunction
 * 
 * Context: H : e = Num 5
 * After 'destruct H':
 * e is replaced Num 5 everywhere
 * 
 * Use: When you have an equality and want to substitute
 *)

(* ================================================================ *)
(* EQUALITY & CONVERSION TACTICS                                    *)
(* ================================================================ *)

(**
 * congruence
 * ---------
 * Solve goals structural equality
 * 
 * Goal: Plus (Num 3) e = Plus (Num 3) e
 * After 'congruence':
 * Proof is complete!
 * 
 * Use: When structure is obviously the same
 *)

(**
 * symmetry
 * ---------
 * Flip an equality
 * 
 * Goal: Y = X
 * Context: H : X = Y
 * After 'symmetry; exact H':
 * Proof is complete!
 * 
 * Use: When you have equality in the "wrong" direction
 *)

(**
 * transitivity X
 * ---------
 * Prove Y = Z first proving Y = X and X = Z
 * 
 * Goal: Y = Z
 * After 'transitivity X':
 * Subgoal 1: Y = X
 * Subgoal 2: X = Z
 * 
 * Use: When intermediate value helps
 *)

(**
 * rw [H]
 * ---------
 * Rewrite using an equality
 * 
 * Goal: P (f x)
 * Context: H : f x = g x
 * After 'rw [H]':
 * Goal: P (g x)
 * 
 * Use: To replace terms using equalities
 *)

(* ================================================================ *)
(* TACTICS FOR LOGICAL CONNECTIVES                                  *)
(* ================================================================ *)

(**
 * left / right
 * ---------
 * Prove a disjunction choosing left or right branch
 * 
 * Goal: P ∨ Q
 * After 'left':
 * Goal: P
 * 
 * Use: When you know which side of the disjunction to prove
 *)

(**
 * constructor
 * ---------
 * Apply a constructor automatically
 * 
 * Goal: exists x, P x
 * After 'constructor':
 * Goal: P ?x   (with fresh variable ?x)
 * 
 * Use: For existential quantification
 *)

(**
 * intro H
 * ---------
 * Introduce a hypothesis from implication
 * 
 * Goal: P -> Q
 * After 'intro H':
 * Goal: Q
 * Context: H : P
 * 
 * Use: For implications
 *)

(* ================================================================ *)
(* ARITHMETIC TACTICS                                               *)
(* ================================================================ *)

(**
 * lia
 * ---------
 * The workhorse for arithmetic!
 * 
 * Handles: +, -, <, >, =, >=, <=, and, or
 * 
 * Examples that lia solves automatically:
 *   n + 5 >= n
 *   (n - 3) + 3 = n  (for n >= 3)
 *   max n m >= n
 *   min n m <= n
 * 
 * Use: Whenever you have an arithmetic goal
 *)

(**
 * lia. (with period)
 * ---------
 * Finish goal with lia, proving it's solvable
 * 
 * Goal: n > 0 -> n >= 1
 * After 'lia':
 * Proof is complete!
 * 
 * Use: When lia definitely solves the goal
 *)

(**
 * lia?
 * ---------
 * Try lia, but don't fail if it doesn't work
 * 
 * Use: When you're not sure if lia can solve it
 *)

(* ================================================================ *)
(* COMMON PROOF PATTERNS                                            *)
(* ================================================================ *)

(**
 * PATTERN 1: Prove computation
 * ================================================================
 * 
 * Goal: eval (Num 5) = 5
 * 
 * Solution:
 *   reflexivity.  -- Both sides compute to 5
 * 
 * Or:
 *   simp [eval].  -- Unfold eval, then reflexivity
 *)

(**
 * PATTERN 2: Prove induction
 * ================================================================
 * 
 * Goal: forall e, 0 <= eval e
 * 
 * Solution:
 *   intro e
 *   induction e with
 *   | Num n => simp [eval]; lia
 *   | Plus e1 IH1 e2 IH2 => simp [eval]; lia
 *   | Minus e1 IH1 e2 IH2 => simp [eval]; lia
 * 
 * Key: Use lia to see all hypotheses including IH
 *)

(**
 * PATTERN 3: Prove equivalence
 * ================================================================
 * 
 * Goal: ae_equiv (Plus e1 e2) (Plus e2 e1)
 * Definition: ae_equiv e1 e2 := eval e1 = eval e2

(**
 * PATTERN 4: Case split with special handling
 * ================================================================
 * 
 * Goal: eval (optimize e) = eval e
 * optimize treats (Plus e1 (Num 0)) specially
 * 
 * Solution:
 *   intro e
 *   induction e with
 *   | Plus e1 IH1 e2 IH2 =>
 *     cases e2 with      -- Split on whether e2 is special
 *     | Num n =>
 *       cases n with     -- Is it 0?
 *       | zero => simp [optimize, eval, IH1]
 *       | succ m => simp [optimize, eval]; lia
 *     | _ => simp [optimize, eval]; lia
 *)

(**
 * PATTERN 5: Introduce intermediate lemmas
 * ================================================================
 * 
 * Goal: P x where proof is complex
 * 
 * Solution:
 *   intro x
 *   have h1 : fact1 x := (proof of fact1)

(* ================================================================ *)
(* COMMON MISTAKES & FIXES                                          *)
(* ================================================================ *)

(**
 * MISTAKE 1: Forgetting to unfold the definition
 * ================================================================
 * 
 * ✗ WRONG:
 *   Lemma ex : forall e1 e2, eval (Plus e1 e2) = ... := *     intro e1 e2

(**
 * MISTAKE 2: Not using inductive hypotheses
 * ================================================================
 * 
 * ✗ WRONG:
 *   Lemma eval_nonneg : forall e, 0 <= eval e := *     intro e

(**
 * MISTAKE 3: Mixing cases unnecessarily
 * ================================================================
 * 
 * ✗ WRONG:
 *   Lemma ex : forall e, ... := *     intro e

(**
 * MISTAKE 4: Confusing simp with simplification
 * ================================================================
 * 
 * simp [eval] does THREE things:
 * 1. Unfold the definition 'eval'
 * 2. Apply all known simplification rules
 * 3. Try reflexivity
 * 
 * Sometimes simp is TOO aggressive and simplifies too much!
 * 
 * Solution:
 *   Use 'unfold eval' to just unfold, then separate tactics
 *)

(* ================================================================ *)
(* WORKFLOW: Proving a Lemma                                        *)
(* ================================================================ *)

(**
 * STEP-BY-STEP WORKFLOW:
 * 
 * 1. READ the goal carefully
 *    Goal: eval (Plus e1 e2) = eval e1 + eval e2
 *    "What does this mean? Which part is hard?"
 * 
 * 2. INTRODUCE variables and hypotheses
 *    intro e1 e2
 *    "Now work with concrete e1, e2"
 * 
 * 3. SIMPLIFY the goal
 *    simp [eval]
 *    "Unfold definitions to see what we're really proving"
 * 
 * 4. CHECK if reflexivity works
 *    reflexivity.
 *    "If both sides are equal computation, we're done"
 * 
 * 5. IF NOT, use lia or induction
 *    lia.  -- If it's arithmetic
 *    induction e with ... -- If it's structural
 * 
 * 6. IN INDUCTION, handle each case
 *    | Num n => simp [eval]; lia
 *    "Solve each case as before"
 * 
 * 7. WHEN STUCK, introduce intermediate facts
 *    have h : useful_fact := (proof)

(* ================================================================ *)
(* DECISION TREE: WHICH TACTIC TO USE?                              *)
(* ================================================================ *)

(**
 * Is the goal an equality?
 * ├─ Yes, both sides compute to the same thing
 * │  └─ Use: reflexivity (or eq_refl)
 * ├─ Yes, need to simplify first
 * │  └─ Use: simp [defs]; reflexivity
 * ├─ Yes, need to show computation equals arithmetic
 * │  └─ Use: simp [defs]; lia
 * └─ No, go to next question
 * 
 * Is it a "forall x, ..."?
 * ├─ Yes
 * │  └─ Use: intro x (or intros)
 * │     Then handle the body
 * └─ No, go to next question
 * 
 * Is it an arithmetic fact (involving +, -, <, >, etc.)?
 * ├─ Yes
 * │  └─ Use: lia
 * └─ No, go to next question
 * 
 * Does it depend on structure of e : AE?
 * ├─ Yes, prove for all e
 * │  └─ Use: intro e; induction e with ...
 * ├─ Yes, need to case-split
 * │  └─ Use: cases e with ...
 * └─ No, go to next question
 * 
 * Is it a relation (equality, equivalence)?
 * ├─ Yes, show it's reflexive/symmetric/transitive
 * │  └─ Use: unfold def; reflexivity (or symmetry, transitivity)
 * └─ No, check if there's a lemma that helps
 * 
 * Is there a relevant lemma L?
 * ├─ Yes, and it matches exactly
 * │  └─ Use: exact L
 * ├─ Yes, and it's part of the proof
 * │  └─ Use: apply L
 * ├─ Yes, and I need to combine it with other facts
 * │  └─ Use: have : ... := L; ...

(* ================================================================ *)
(* QUICK REFERENCE TABLE                                            *)
(* ================================================================ *)

(**
 * TACTIC          | USE WHEN                | EXAMPLE
 * ================|========================|=================================
 * reflexivity     | both sides are equal    | goal: 3 + 4 = 7
 * simp [eval]     | need to unfold def      | goal: eval (Num 5) = 5
 * lia           | arithmetic goal         | goal: n + 5 >= n
 * intro x         | goal is forall x, ...   | goal: forall x, P x
 * induction e     | e is an AE              | prove for all e : AE
 * cases e         | need to split cases     | handle each constructor
 * have : P := H   | need intermediate fact  | lemmas to build on

(* ================================================================ *)
(* FINAL TIPS                                                       *)
(* ================================================================ *)

(**
 * TIP 1: If stuck, try simp [eval] first
 *        Unfold definitions to see what you're really proving
 * 
 * TIP 2: If still stuck, try lia
 *        It's amazing at arithmetic reasoning
 * 
 * TIP 3: If lia doesn't work, use induction
 *        Structure your proof to handle each case
 * 
 * TIP 4: Name your inductive hypotheses clearly
 *        IHe1, IHe2 are better than H1, H2
 * 
 * TIP 5: When in doubt, write it out
 *        Paper + pencil to sketch the proof first
 * 
 * TIP 6: Check the goal after each tactic
 *        Make sure you're making progress
 * 
 * TIP 7: Use the solution file as a reference
 *        If your proof gets too complicated, check if there's a simpler way
 *)
