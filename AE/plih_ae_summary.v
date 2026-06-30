(*
 * PLIH in Rocq: AE (Arithmetic Expressions) Module
 * ================================================================
 * 
 * This document summarizes the complete AE module and explains
 * how to integrate it into your course.
 * 
 * FILES PROVIDED:
 * 1. plih_rocq_ae_shared.v      -- Shared infrastructure
 * 2. plih_ae_lecture.v           -- Lecture with worked examples
 * 3. plih_ae_exercises.v         -- Student problem set
 * 4. plih_ae_solutions.v         -- Complete solutions
 * 5. plih_ae_instructor_guide.v  -- Teaching guide
 * 6. plih_ae_summary.v           -- This file
 * 
 * ================================================================ *)

(* ================================================================ *)
(* QUICK START                                                      *)
(* ================================================================ *)

(**
 * FOR STUDENTS:
 * 
 * 1. Read plih_ae_lecture.v for concepts and worked examples
 * 2. Work through plih_ae_exercises.v and fill in "sorry"
 * 3. Check your work against plih_ae_solutions.v
 * 4. Run: coq_makefile plih_rocq_ae_shared.v plih_ae_lecture.v ... > Makefile
 * 5. Run: make to check everything compiles
 * 
 * FOR INSTRUCTORS:
 * 
 * 1. Read plih_ae_instructor_guide.v for teaching strategies
 * 2. Assign plih_ae_exercises.v in weekly increments
 * 3. Use plih_ae_solutions.v to grade
 * 4. Adapt lecture examples to your class style
 *)

(* ================================================================ *)
(* MODULE STRUCTURE                                                 *)
(* ================================================================ *)

(**
 * LAYER 1: Foundations (plih_rocq_ae_shared.v)
 * ================================================================
 * 
 * Defines reusable infrastructure:
 * - Option monad (bind, return_, liftM2)
 * - Monad laws (left_identity, right_identity, assoc)
 * - Numeric operations (safe_minus)
 * - Environment operations (lookup, extend)
 * - Basic lemmas about all of the above
 * 
 * USE: Import this in all other files
 * TIME TO UNDERSTAND: 1 hour
 * 
 * Key Takeaway: Rocq has powerful libraries; reuse them!
 *)

(**
 * LAYER 2: Lecture (plih_ae_lecture.v)
 * ================================================================
 * 
 * Teaches the AE language in 9 sections:
 * 
 * SECTION 1: Syntax
 *   - Inductive definition of AE
 *   - Constructors: Num, Plus, Minus
 *   - Example terms
 * 
 * SECTION 2: Semantics
 *   - Fixpoint eval function
 *   - Test cases
 *   - Explanation of termination
 * 
 * SECTION 3: Simple Properties
 *   - Evaluation is deterministic
 *   - Plus distributes into eval
 *   - Commutativity of Plus
 *   - Associativity of Plus
 *   - Minus is not commutative
 * 
 * SECTION 4: Induction
 *   - Prove properties structural induction
 *   - Distribution of multiplication
 *   - Zero identity
 *   - Non-negativity (key proof!)
 * 
 * SECTION 5: Auxiliary Functions
 *   - Helper functions (size, count_ops)
 *   - Properties about helpers
 *   - When helpers are useful
 * 
 * SECTION 6: Equivalence
 *   - Define semantic equivalence (ae_equiv)
 *   - Prove it's an equivalence relation (refl, sym, trans)
 * 
 * SECTION 7: Inequalities
 *   - Plus increases values
 *   - Working with < and >
 * 
 * SECTION 8: Optimizations
 *   - Define optimize_zero
 *   - Prove correctness
 *   - Discuss optimization safety
 * 
 * SECTION 9: Reflection/Decidability
 *   - Decision procedure: ae_eq_dec
 *   - Prove correctness of decision procedure
 * 
 * USE: Read in order, study proofs, try to reproduce them
 * TIME TO UNDERSTAND: 3-4 hours of reading + 2-3 hours practicing
 * 
 * Key Takeaway: Rocq combines computation and proof elegantly
 *)

(**
 * LAYER 3: Exercises (plih_ae_exercises.v)
 * ================================================================
 * 
 * 31 exercises organized difficulty:
 * 
 * WARM-UP (5 exercises): [*]
 *   - Basic evaluation examples
 *   - Prove reflexivity
 *   - Tests understanding of what eval does
 * 
 * PART 1: Simple Lemmas (3 exercises): [*] to [**]
 *   - Distributivity of Plus/Minus
 *   - Commutativity (new proof from exercise)
 * 
 * PART 2: Induction Proofs (4 exercises): [**] to [***]
 *   - Zero identity
 *   - Non-negativity
 *   - Positivity (equivalent formulation)
 *   - Associativity
 * 
 * PART 3: Operation Properties (4 exercises): [**] to [***]
 *   - Plus zero right
 *   - Minus self
 *   - Minus twice
 * 
 * PART 4: Inequalities (3 exercises): [**] to [***]
 *   - Plus increases values
 *   - Minus decreases values
 *   - Both positive => sum > 1
 * 
 * PART 5: Auxiliary Functions (4 exercises): [**] to [***]
 *   - Size is positive
 *   - Size of Plus
 *   - Depth of Num
 *   - Size-depth relation (classic result!)
 * 
 * PART 6: Optimization (2 exercises): [**] to [***]
 *   - Optimization preserves semantics
 *   - Optimization reduces size
 * 
 * PART 7: Equivalence (4 exercises): [*] to [**]
 *   - Reflexivity, symmetry, transitivity
 *   - Example of different syntaxes being equivalent
 * 
 * PART 8: Creative Problems (2 exercises): [***] to [****]
 *   - Define constant folding
 *   - Prove double property
 * 
 * CHALLENGES (2 bonus problems): [****] to [*****]
 *   - Count operations predicate
 *   - Simplification with multiple optimizations
 * 
 * USE: Assign incrementally (5 per week recommended)
 * TIME TO COMPLETE: 6-8 hours of focused work
 * 
 * Key Takeaway: Proof is a skill; practice makes perfect
 *)

(**
 * LAYER 4: Solutions (plih_ae_solutions.v)
 * ================================================================
 * 
 * Complete proofs for all 31 exercises + 2 challenges
 * 
 * USE: Grade against this, or check your work
 * TIME: Compare your proof to the solution
 * 
 * Note: Solutions are not unique. Many proofs can be written
 * multiple ways. Your proof is correct if it:
 * - Has no "sorry"
 * - Compiles without error
 * - Uses only basic tactics (intro, simp, lia, induction, etc.)
 * 
 * Key Takeaway: Learn to recognize correct proofs
 *)

(**
 * LAYER 5: Instructor Guide (plih_ae_instructor_guide.v)
 * ================================================================
 * 
 * Comprehensive teaching guide with:
 * 
 * - Course structure and timing
 * - Lesson plan (5 hours) with learning objectives
 * - Common student mistakes and fixes
 * - Pedagogical tips and tricks
 * - Assessment rubric (500 points total)
 * - Extensions and variants
 * - Transition to next section (ABE)
 * - Additional resources
 * 
 * USE: Before class, review the relevant hour
 * TIME: 30 minutes to 1 hour to prepare for each 1-hour lesson
 * 
 * Key Takeaway: Good teaching requires planning
 *)

(* ================================================================ *)
(* SUGGESTED WEEKLY SCHEDULE                                        *)
(* ================================================================ *)

(**
 * WEEK 1: Introduction to Rocq Syntax (Prerequisite)
 * =====================================================
 * 
 * Before starting AE, students must understand:
 * - Inductive type definitions
 * - Pattern matching
 * - Basic tactics (intro, reflexivity, simp, lia)
 * 
 * Recommendation: Provide a separate "Rocq Bootcamp" module
 * or assign Pierce's "Programming Language Foundations"
 * chapters 1-2 before this course begins.
 * 
 * Time: 3-4 hours self-study + 1 hour Q&A session
 * 
 * ================================================================
 * 
 * WEEK 2: AE (Arithmetic Expressions)
 * ====================================
 * 
 * MONDAY (Hour 1-2):
 *   - Lecture: Syntax and Semantics (1 hour)
 *   - Activity: Write 5 AE terms, test eval on them
 *   - Assign: Exercises 1-5 (warm-up)
 * 
 * WEDNESDAY (Hour 3-4):
 *   - Lecture: Simple Proofs (1 hour)
 *   - Worked examples on board
 *   - Assign: Exercises 6-12
 * 
 * FRIDAY (Hour 5):
 *   - Lecture: Induction and Properties (1 hour)
 *   - Live proof of eval_nonneg on whiteboard
 *   - Assign: Exercises 13-21
 * 
 * Homework:
 *   - Complete Exercises 1-21
 *   - Due: Next Monday
 *   - Expected time: 6-8 hours
 * 
 * ================================================================
 * 
 * WEEK 3: AE Continued + Transitions
 * ===================================
 * 
 * MONDAY:
 *   - Review homework, discuss hard exercises
 *   - Q&A on proofs and tactics
 * 
 * WEDNESDAY:
 *   - Lecture: Optimization and Correctness (30 min)
 *   - Lecture: Beyond AE (30 min)
 *   - Assign: Exercises 22-31, Challenge problems
 * 
 * FRIDAY:
 *   - Student presentations (optional)
 *   - Discussion: What makes a proof beautiful?
 * 
 * Homework:
 *   - Complete Exercises 22-31
 *   - (Challenges optional but highly recommended)
 *   - Due: Following Monday
 * 
 * ================================================================
 * 
 * Then proceed to: ABE (Arithmetic + Boolean Expressions)
 *)

(* ================================================================ *)
(* KEY CONCEPTS TESTED BY EXERCISES                                 *)
(* ================================================================ *)

(**
 * Exercises 1-5 (Warm-up):
 *   ✓ Understanding what eval does
 *   ✓ Computation reflexivity
 * 
 * Exercises 6-8 (Simple Lemmas):
 *   ✓ Using simp to unfold definitions
 *   ✓ Using lia for arithmetic
 *   ✓ Introducing variables with intro
 * 
 * Exercises 9-15 (Induction):
 *   ✓ Structural induction on AE
 *   ✓ Using inductive hypotheses
 *   ✓ Case analysis (Plus vs Minus)
 * 
 * Exercises 16-20 (Inequalities):
 *   ✓ Working with >, <, >= operators
 *   ✓ lia's knowledge of inequality reasoning
 *   ✓ Combining multiple hypotheses
 * 
 * Exercises 21-25 (Auxiliary Functions):
 *   ✓ Defining and reasoning about helper functions
 *   ✓ Connecting different properties
 *   ✓ Case splitting on pattern matches
 * 
 * Exercises 26-29 (Equivalence):
 *   ✓ Understanding relations and properties
 *   ✓ Proving refl/sym/trans
 *   ✓ Unfold and congruence reasoning
 * 
 * Exercises 30-31 (Creative):
 *   ✓ Independent problem-solving
 *   ✓ Combining multiple tactics
 *   ✓ Verifying optimizations
 * 
 * Challenges:
 *   ✓ Sophisticated induction and case analysis
 *   ✓ Working with recursive predicates
 *   ✓ Proving non-trivial properties
 *)

(* ================================================================ *)
(* COMMON PROOF PATTERNS IN AE                                      *)
(* ================================================================ *)

(**
 * PATTERN 1: Computation + Arithmetic
 * 
 *   Lemma foo : forall e1 e2,
 *     eval (Plus e1 e2) = eval e1 + eval e2 := *     intro e1 e2

(* ================================================================ *)
(* ASSESSMENT STRATEGIES                                            *)
(* ================================================================ *)

(**
 * STRATEGY 1: Weekly Homework (Recommended)
 * 
 * Week 1: Exercises 1-10 (50 points)
 * Week 2: Exercises 11-21 (100 points)
 * Week 3: Exercises 22-31 (100 points)
 * Challenges: +50 points each (100 points available)
 * 
 * Total: 250-350 points depending on challenges
 * Grading: 90%+ = A, 80%+ = B, 70%+ = C, 60%+ = D
 * 
 * ================================================================
 * 
 * STRATEGY 2: Tiered Assignments
 * 
 * All students must complete: Exercises 1-15 (Core)
 * Most students complete: Exercises 16-25 (Standard)
 * Advanced students complete: Exercises 26-31 + Challenges
 * 
 * This allows differentiation while ensuring basics are solid
 * 
 * ================================================================
 * 
 * STRATEGY 3: Peer Review
 * 
 * Students exchange solutions with a partner
 * Each reviews the other's proofs:
 *   - Is it correct? (Does it type-check?)
 *   - Is it clear? (Can you understand it?)
 *   - Is it elegant? (Could it be simpler?)
 * 
 * This builds communication skills and deepens understanding
 * 
 * ================================================================
 * 
 * STRATEGY 4: Live Coding
 * 
 * In office hours or review session:
 * - Student presents their solution
 * - Live-code the proof on screen
 * - Discuss alternative approaches
 * - Debug errors together
 * 
 * This is the best way to learn!
 *)

(* ================================================================ *)
(* ADAPTING TO YOUR CONTEXT                                         *)
(* ================================================================ *)

(**
 * FOR A 1-SEMESTER COURSE:
 * 
 * - Spend 2 weeks on AE (Weeks 2-3)
 * - Assign Exercises 1-21 (core)
 * - Make Exercises 22-31 optional
 * - Then proceed: ABE (Week 4-5), IDs (Week 6-7), etc.
 * 
 * ================================================================
 * 
 * FOR A 2-SEMESTER COURSE:
 * 
 * Semester 1 (Foundations):
 * - Spend 3 weeks on AE (all exercises)
 * - Spend 3 weeks on ABE (all exercises)
 * - Spend 3 weeks on IDs (all exercises)
 * - Spend 3 weeks on Functions (untyped)
 * - Review and wrap-up
 * 
 * Semester 2 (Advanced Topics):
 * - Typed Functions + Type Checking
 * - State and Mutable References
 * - Advanced topics (modules, exceptions, etc.)
 * - Student research projects
 * 
 * ================================================================
 * 
 * FOR A SUMMER BOOTCAMP (2 weeks):
 * 
 * - Compress AE + ABE into one intensive week
 * - Assign only Exercises 1-10 per section
 * - Focus on understanding concepts, not solving all problems
 * - Second week: Functions + Types
 * 
 * ================================================================
 * 
 * FOR SELF-STUDY:
 * 
 * - Read lecture carefully (3-4 hours)
 * - Work through Exercises 1-5 (30 minutes)
 * - Work through Exercises 6-15 (2-3 hours)
 * - Compare against solutions (1 hour)
 * - Challenge yourself with Exercises 16-31 (2-3 hours)
 * 
 * Total time investment: 9-12 hours for mastery
 *)

(* ================================================================ *)
(* TRANSITION TO NEXT SECTION                                       *)
(* ================================================================ *)

(**
 * After completing AE, students are ready for:
 * 
 * ABE (Arithmetic + Boolean Expressions):
 * - Add boolean literals (True, False)
 * - Add boolean operations (And, Or)
 * - Add comparison operations (LessThan, Equal)
 * - Add conditionals (IfThenElse)
 * - Introduce sum type for values: Value := NumV nat | BoolV bool

(* ================================================================ *)
(* FINAL NOTES                                                      *)
(* ================================================================ *)

(**
 * This AE module demonstrates the power of formal verification:
 * 
 * 1. EXECUTABLE SPECIFICATIONS:
 *    The eval function is not just a specification;
 *    it's a working interpreter that Rocq can execute.
 * 
 * 2. MECHANIZED PROOFS:
 *    Every lemma is machine-checked.
 *    There's no hand-waving; every step is justified.
 * 
 * 3. CONFIDENCE IN CORRECTNESS:
 *    Unlike informal proofs, Rocq proofs can't be wrong.
 *    If it compiles, it's correct.
 * 
 * 4. COMPOSITION:
 *    Proofs build on each other.
 *    A bug in one lemma propagates up; this catches errors early.
 * 
 * By completing this module, students have:
 * ✓ Written a language implementation
 * ✓ Proven it correct
 * ✓ Built confidence in formal verification
 * ✓ Prepared for more advanced topics
 * 
 * This is real computer science, not just exercises!
 *)
