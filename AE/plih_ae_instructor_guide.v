(**
 * INSTRUCTOR GUIDE: Teaching the AE Section
 * 
 * This guide explains:
 * 1. How to structure the course
 * 2. What to emphasize at each stage
 * 3. Common student mistakes and how to help
 * 4. Time estimates
 * 5. Extensions and variants
 *)

(* ================================================================ *)
(* PART 1: COURSE STRUCTURE                                         *)
(* ================================================================ *)

(**
 * WEEK 1: Introduction to Rocq Syntax (2-3 hours)
 * 
 * Before diving into AE, students must understand:
 * 
 * 1. Inductive Types
 *    - Explain how AE is like a Haskell data type
 *    - Show: Num n, Plus e1 e2 are CONSTRUCTORS
 *    - Emphasize: These are VALUES, not programs
 * 
 * 2. Pattern Matching (Fixpoint)
 *    - Show how Fixpoint mirrors Haskell pattern matching
 *    - Rocq requires structural recursion proof
 *    - This is the KEY difference: eval MUST terminate
 * 
 * 3. Basic Tactics
 *    - intro (introduce variables)
 *    - reflexivity (prove computation)
 *    - simp [eval] (unfold definitions)
 *    - lia (linear arithmetic)
 * 
 * Recommendation: Have students play with simple examples:
 *   eval (Num 5) = 5  -- prove eq_refl
 *   eval (Plus (Num 2) (Num 3)) = 5  -- prove eq_refl
 *   eval (Plus e1 e2) = eval e1 + eval e2  -- prove simp
 *)

(* ================================================================ *)
(* PART 2: LESSON PLAN (One Week)                                   *)
(* ================================================================ *)

(**
 * HOUR 1: DEFINING THE LANGUAGE
 * 
 * Learning Objectives:
 * - Understand abstract syntax
 * - Write inductive type definitions
 * - Distinguish between syntax and semantics
 * 
 * Activities:
 * - Draw the AST for: 3 + 4, (1 + 2) + 3, 10 - 2
 * - Write out the Coq terms: Plus (Num 3) (Num 4)
 * - Show invalid terms: Plus (Num 3)  -- ERROR: missing argument
 * - Comparison to Haskell:
 *     Haskell: data AE = Num Int | Plus AE AE | Minus AE AE
 *     Rocq: Inductive AE : Type := Num : nat -> AE | ...

(**
 * HOUR 2: EVALUATION (SEMANTICS)
 * 
 * Learning Objectives:
 * - Write an interpreter
 * - Understand Fixpoint and termination
 * - Test the evaluator
 * 
 * Activities:
 * - Trace eval through an example hand
 * - Show evaluation as a mathematical function
 * - Explain why Rocq requires termination proofs
 * - Run the examples (let Rocq compute)
 * 
 * Comparison to Haskell:
 *   Haskell eval is untyped, can diverge
 *   Rocq eval is proved terminating structural recursion
 * 
 * Deliverable: Students test eval on 5 terms and verify results
 * 
 * Time: 30 minutes
 *)

(**
 * HOUR 3: SIMPLE PROOFS
 * 
 * Learning Objectives:
 * - Prove properties reflexivity
 * - Use simp and lia tactics
 * - Understand Rocq's computational power
 * 
 * Activities:
 * 1. Direct proofs (Exercises 1-7):
 *    - These are: just unfold, then reflexivity
 *    - Students should see: Rocq CAN compute
 * 
 * 2. Commutativity of Plus (Exercise 8):
 *    - First time using lia
 *    - Show: eval (Plus e1 e2) = eval e1 + eval e2
 *    - Goal reduces to: eval e1 + eval e2 = eval e2 + eval e1
 *    - lia knows: Nat.add_comm
 * 
 * Tactical tip: Use simp [eval] to unfold, then lia
 * 
 * Deliverable: Students complete Exercises 6-8
 * 
 * Time: 40 minutes
 *)

(**
 * HOUR 4: INDUCTION
 * 
 * Learning Objectives:
 * - Understand structural induction on AE
 * - Write proofs induction
 * - Connect to mathematical induction
 * 
 * Activities:
 * 1. Prove hand first (non-Rocq):
 *    - "eval e >= 0 for all AE e"
 *    - Base case: Num n => n >= 0
 *    - Inductive cases: Plus/Minus => use IH
 * 
 * 2. Translate to Rocq:
 *    - Use: induction e as [n | e1 IH1 e2 IH2 | ...]
 *    - Each case gets the inductive hypothesis
 *    - Name your IH clearly!
 * 
 * 3. Common mistake: Forgetting to use IH
 *    - lia won't see it unless you have it as a hypothesis
 *    - Always: have: IH := (inductive hypothesis)

(**
 * HOUR 5: OPTIMIZATION & OPEN PROBLEMS
 * 
 * Learning Objectives:
 * - Prove optimization correctness
 * - Work with helper functions
 * - Tackle larger proofs
 * 
 * Activities:
 * 1. Study optimize_zero from lecture
 *    - Explain: why remove (Plus e (Num 0))?
 *    - Show: case split on e2 in the Plus case
 *    - Discuss: when is optimization valid?
 * 
 * 2. Have students prove:
 *    - optimize_zero changes nothing semantically
 *    - This requires careful case analysis
 * 
 * 3. Challenge: Define simplify (Exercise 30)
 *    - Fold constants: (3 + 4) becomes 7
 *    - Students must define it themselves
 *    - Then prove correctness
 * 
 * Deliverable: Students complete Exercise 24, attempt 30
 * 
 * Time: 50 minutes
 * 
 * TOTAL: ~3 hours of instruction + 2 hours of problem-solving
 *)

(* ================================================================ *)
(* PART 3: COMMON STUDENT MISTAKES                                  *)
(* ================================================================ *)

(**
 * MISTAKE 1: Confusing syntax and semantics
 * 
 * Student writes:
 *   Lemma weird : forall e, Plus e (Num 0) = e := sorry.

(**
 * MISTAKE 2: Forgetting to use inductive hypotheses
 * 
 * Student writes:
 *   Lemma eval_nonneg : forall e, 0 <= eval e := *     intro e

(**
 * MISTAKE 3: Destructing the wrong thing
 * 
 * Student writes:
 *   Lemma optimize_correct : forall e,
 *     eval (optimize e) = eval e := *     intro e

(**
 * MISTAKE 4: Not simplifying enough
 * 
 * Student writes:
 *   Lemma ex : forall e1 e2,
 *     eval (Plus e1 e2) = eval (Plus e2 e1) := *     intro e1 e2

(**
 * MISTAKE 5: Confusing = (equality) and iff (if and only if)
 * 
 * Student writes:
 *   Lemma bad : forall e1 e2,
 *     (eval e1 = eval e2) <-> (e1 = e2) := sorry.

(* ================================================================ *)
(* PART 4: PEDAGOGICAL TIPS                                         *)
(* ================================================================ *)

(**
 * TIP 1: Use Lean 4 Mode
 * 
 * The tactics shown here use Lean 4 syntax (by ... tactic):
 * 
 *   Lemma ex : forall e, eval e = eval e := *     reflexivity.

(**
 * TIP 2: Use Examples Before Lemmas
 * 
 * Students understand better if you show:
 * 
 *   Example test_1 : eval (Num 5) = 5 := eq_refl.
 *   Example test_2 : eval (Plus (Num 3) (Num 4)) = 7 := eq_refl.
 * 
 * Before asking them to prove:
 * 
 *   Lemma general_plus : forall e1 e2, eval (Plus e1 e2) = ... := ...

(**
 * TIP 3: Have Students Trace Hand
 * 
 * Before proving evaluate hand on paper:
 * 
 *   eval (Plus (Plus (Num 1) (Num 2)) (Num 3))
 *   = eval (Plus (Num 1) (Num 2)) + eval (Num 3)
 *   = (eval (Num 1) + eval (Num 2)) + eval (Num 3)
 *   = (1 + 2) + 3
 *   = 3 + 3
 *   = 6
 * 
 * Then show: simp [eval] does EXACTLY this
 *)

(**
 * TIP 4: Emphasize Modular Proofs
 * 
 * Show students that proofs build on each other:
 * 
 *   Lemma A : forall e, ... := ...

(**
 * TIP 5: Create a "Tactics Cheat Sheet"
 * 
 * Print this for students:
 * 
 *   intro x         -- Introduce a variable
 *   intros x y z    -- Introduce multiple variables
 *   simp [def]      -- Simplify using definition
 *   lia           -- Solve linear arithmetic
 *   reflexivity     -- Prove computation
 *   induction e     -- Proof induction
 *   cases e         -- Case analysis
 *   have : P := H   -- Introduce intermediate result

(* ================================================================ *)
(* PART 5: ASSESSMENT RUBRIC                                        *)
(* ================================================================ *)

(**
 * Grading Rubric for Exercise Set:
 * 
 * Exercises 1-10 (Basic): 10 points each
 * - Requires simple tactics only
 * - Student should understand reflexivity and lia
 * 
 * Exercises 11-20 (Standard): 15 points each
 * - Requires induction
 * - Expect some mistakes with inductive hypothesis
 * 
 * Exercises 21-29 (Intermediate): 20 points each
 * - Requires careful proof planning
 * - Multiple tactics in sequence
 * 
 * Exercises 30-31 (Advanced): 25 points each
 * - Requires independent problem-solving
 * - May need to define new functions
 * 
 * Challenge Problems: +50 points each (optional)
 * 
 * Total: 500 points core + 100 bonus
 * 
 * Letter Grade Conversion:
 *   450-500: A
 *   400-449: B
 *   350-399: C
 *   300-349: D
 *   < 300:   F
 *)

(* ================================================================ *)
(* PART 6: EXTENSIONS & VARIANTS                                    *)
(* ================================================================ *)

(**
 * VARIANT 1: Introduce Error Handling
 * 
 * Add division:
 * 
 *   Inductive AE : Type := eq_refl.

(**
 * VARIANT 2: Add Booleans Early
 * 
 * Create ABE (Arithmetic + Boolean Expressions):
 * 
 *   Inductive ABE : Type := eq_refl.

(**
 * VARIANT 3: Static Analysis
 * 
 * Prove: "No division zero in expression e"
 * 
 *   Definition safe (e : AE) : Prop := eq_refl.

(**
 * VARIANT 4: Optimization Proofs
 * 
 * Define multiple optimizations:
 * 
 *   opt_zero : (e + 0) ~> e
 *   opt_identity : (e * 1) ~> e
 *   opt_associative : ((e1 + e2) + e3) ~> (e1 + (e2 + e3))
 * 
 * Prove: Composing optimizations preserves semantics
 * 
 *   Lemma opt_compose : forall e,
 *     eval (opt1 (opt2 (opt3 e))) = eval e.
 *)

(**
 * VARIANT 5: Equivalence Classes
 * 
 * Prove that ae_equiv partitions AE into equivalence classes:
 * 
 *   Definition equiv_class (e : AE) := eq_refl.

(* ================================================================ *)
(* PART 7: TRANSITION TO ABE                                        *)
(* ================================================================ *)

(**
 * After students master AE, introduce ABE (Arithmetic + Booleans)
 * 
 * KEY CHANGES:
 * 
 * 1. Multiple result types:
 *    - AE evaluates to nat
 *    - ABE needs to evaluate to (nat | bool)
 *    - Introduce sum types or separate Value type
 * 
 * 2. Type mismatch errors:
 *    - (3 + True) is syntactically valid but semantically nonsense
 *    - Introduce error handling
 *    - Discuss: should this be rejected at parse time or eval time?
 * 
 * 3. New properties to prove:
 *    - Type safety (well-formed evaluation)
 *    - Error analysis (when does eval return None?)
 * 
 * 4. Optimization becomes harder:
 *    - (3 + 4) reduces to 7: still an AE
 *    - (3 < 4) reduces to True: now a bool
 *    - Need to be careful about types
 *)

(* ================================================================ *)
(* PART 8: RESOURCES                                                *)
(* ================================================================ *)

(**
 * Rocq/Coq Resources:
 * - Rocq Reference Manual: https://rocq-prover.org/doc/
 * - Coq Proof General IDE
 * - VS Code with Rocq extension
 * 
 * Related Textbooks:
 * - "Software Foundations" series (great PL pedagogy + proofs)
 * - "Practical Foundations for Programming Languages" Harper
 * - "TAPL" (Types and Programming Languages) Pierce
 * 
 * Comparison to PLIH (Haskell version):
 * - Same progression (AE → ABE → identifiers → functions → types)
 * - Rocq adds proofs at each step
 * - Haskell emphasizes implementation; Rocq emphasizes correctness
 *)

(* ================================================================ *)
(* SUMMARY                                                          *)
(* ================================================================ *)

(**
 * The AE section teaches:
 * 
 * 1. SYNTAX: How to formally define a language (Inductive types)
 * 2. SEMANTICS: How to formally specify meaning (Fixpoint eval)
 * 3. PROOF: How to verify properties formally (Rocq tactics)
 * 4. PRACTICE: How to apply these ideas (Exercises 1-31)
 * 
 * By the end of this section, students should:
 * ✓ Understand inductive types and pattern matching
 * ✓ Write recursive functions with termination proofs
 * ✓ Prove properties reflexivity, lia, and induction
 * ✓ Distinguish syntax from semantics
 * ✓ Identify and correct common proof mistakes
 * 
 * This foundation prepares them for:
 * - Adding booleans (ABE)
 * - Adding identifiers and environments
 * - Adding functions and closures
 * - Adding types and type checking
 * - Adding state and mutable references
 *)
