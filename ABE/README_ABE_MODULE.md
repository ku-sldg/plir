# Programming Languages in Rocq: ABE Module

**ABE = Arithmetic + Boolean Expressions**

This is a complete scaffold for teaching the second major section of your PLIH course in Rocq. It builds on the AE module by adding multiple value types, error handling, and type consistency concepts.

## Files Included

| File | Purpose | Size |
|------|---------|------|
| `plih_rocq_abe_shared.v` | Infrastructure: Value type, boolean ops, comparisons | 300 LOC |
| `plih_abe_lecture.v` | Complete lecture with 10 sections + 40+ proofs | 500 LOC |
| `plih_abe_exercises.v` | 40 exercises + 4 challenges, graduated difficulty | 450 LOC |
| `plih_abe_solutions.v` | Complete solutions to all exercises | 700 LOC |
| `plih_abe_instructor_guide.v` | Teaching strategies, lesson plans, assessment | 400 LOC |
| `plih_abe_summary.v` | Module overview, progression, tips | 350 LOC |
| `README_ABE_MODULE.md` | This file | - |

**Total: ~2,700 lines of code + documentation**

## Quick Start

### For Students
1. **Prerequisite**: Complete the AE module first
2. **Read**: `plih_abe_lecture.v` sections 1-3 (2 hours)
3. **Practice**: Solve `plih_abe_exercises.v` exercises 1-20 (4 hours)
4. **Check**: Compare against `plih_abe_solutions.v` (1 hour)
5. **Extend**: Work on exercises 21-40 + challenges (5-6 hours)
6. **Total time**: 10-12 hours for mastery

### For Instructors
1. **Review**: Read `plih_abe_instructor_guide.v` (30 minutes)
2. **Prepare**: Create lecture slides based on sections 1-3 (1 hour)
3. **Teach**: 3 one-hour lectures across 1-2 weeks
4. **Assign**: Distribute exercises incrementally (5-10 per week)
5. **Grade**: Use `plih_abe_solutions.v` as reference (~15 min per student)
6. **Transition**: Prepare next section (Identifiers)

## What's Different from AE?

| Aspect | AE | ABE |
|--------|----|----|
| **Values** | Only nat | NumV nat \| BoolV bool |
| **Semantics** | eval returns nat | eval returns option Value |
| **Errors** | None—all succeed | TypeErrors: (True + 3) = None |
| **Operations** | Arithmetic only | Arithmetic + Boolean + Conditionals |
| **Key Lemma** | Determinism | Type Consistency: well-typed never fails |
| **Proof Patterns** | Induction, lia | + Case analysis on option, + Disjunctions |

## Lecture Structure

### Lecture 1: Values & Error Handling (1 hour)
- **Concepts**: Sum types, multiple value types, error handling
- **Syntax**: Value := NumV nat | BoolV bool
- **Semantics**: eval e : option Value
- **Key Idea**: Some expressions can fail with type errors
- **Examples**: eval BTrue = Some (BoolV true), eval (Plus BTrue (Num 3)) = None

### Lecture 2: Boolean Ops & Conditionals (1 hour)
- **Concepts**: Boolean operations, comparisons, conditionals
- **Operations**: And, Or, Not (require booleans); LessThan, Equal (produce booleans)
- **IfThenElse**: Condition must be boolean; branches can be anything
- **Lazy Evaluation**: We don't evaluate branches we don't take
- **Key Idea**: Mixing types requires careful handling

### Lecture 3: Type Consistency (1 hour)
- **Concepts**: Type classifiers, type safety, preventing errors
- **Predicates**: is_numeric e, is_boolean e
- **Key Lemmas**: 
  - numeric_never_fails: is_numeric e → ∃n, eval e = Some (NumV n)
  - boolean_never_fails: is_boolean e → ∃b, eval e = Some (BoolV b)
- **Bridge to Type Checking**: These lemmas show why type checking prevents errors
- **Key Idea**: "Well-typed expressions never fail"

## Exercise Breakdown

**Difficulty Levels:**
- `[*]` = Trivial (reflexivity)
- `[**]` = Easy (straightforward proof)
- `[***]` = Medium (requires case analysis)
- `[****]` = Hard (sophisticated reasoning)

**Sections:**
- **Exercises 1-5** [*]: Basic boolean evaluation (50 points)
- **Exercises 6-8** [*-**]: Type mismatches (36 points)
- **Exercises 9-13** [**]: Conditionals (60 points)
- **Exercises 14-17** [*]: Comparisons (48 points)
- **Exercises 18-22** [**]: Boolean algebra (90 points)
- **Exercises 23-25** [**]: Conditional properties (45 points)
- **Exercises 26-27** [**]: Complex combinations (36 points)
- **Exercises 28-30** [***]: Type consistency (45 points) ⭐ Most Important
- **Exercises 31-35** [**-***]: Equivalence (90 points)
- **Exercises 36-40** [***]: Optimization (90 points)
- **Challenges** [****+]: Advanced (100 bonus points)

**Total: 569 core points + 100 bonus**

## Key Proof Patterns

### Pattern 1: Option Handling
```coq
Lemma ex9_type_mismatch_both_operands : forall e1 e2,
  eval (Plus e1 e2) = None \/
  exists n1 n2, eval (Plus e1 e2) = Some (NumV (n1 + n2)).
Proof.
  intros e1 e2. simpl.
  destruct (eval e1) as [ [n1|b1] | ];
  destruct (eval e2) as [ [n2|b2] | ];
    try (left; reflexivity).
  right. exists n1, n2. reflexivity.
Qed.
```

### Pattern 2: Boolean Case Analysis
```coq
Lemma ex20_double_negation : forall (b : bool),
  eval (Not (Not (if b then BTrue else BFalse))) = Some (BoolV b).
Proof.
  intro b. destruct b; reflexivity.   (* one branch per boolean value *)
Qed.
```

### Pattern 3: Type Consistency Induction
```coq
Lemma numeric_never_fails : forall e,
  is_numeric e -> exists n, eval e = Some (NumV n).
Proof.
  intros e Hnum. induction Hnum.
  - exists n. reflexivity.
  - destruct IHHnum1 as [n1 H1]. destruct IHHnum2 as [n2 H2].
    exists (n1 + n2). simpl. rewrite H1, H2. reflexivity.
  - destruct IHHnum1 as [n1 H1]. destruct IHHnum2 as [n2 H2].
    exists (n1 - n2). simpl. rewrite H1, H2. reflexivity.
Qed.
```

## Assessment Rubric

**Grading (per exercise):**
- **Compilation** (50%): Does it compile? No remaining `Admitted`?
- **Correctness** (30%): Does the proof prove the claim?
- **Clarity** (20%): Well-structured? Good naming?

**Efficient Grading:**
Since Rocq type-checks proofs:
1. Run `coqc plih_abe_exercises.v` on student submission
2. If it compiles → 80% grade (compilation + correctness guaranteed)
3. Spot-check 5-10 proofs for clarity
4. Time per student: 15-30 minutes

## Suggested Weekly Schedule

### Week 2: Start ABE

**Monday (1 hour lecture)**
- Teach: Syntax & Semantics (sections 1-2)
- Activity: Write ABE terms by hand, trace eval
- Assign: Exercises 1-8 (warm-up)

**Wednesday (1 hour lecture)**
- Teach: Boolean ops & Conditionals (sections 3-4)
- Worked example: Complex conditional proof
- Assign: Exercises 9-20

**Friday (1 hour lecture)**
- Teach: Type Consistency (sections 5-6)
- Live proof: numeric_never_fails with induction
- Assign: Exercises 21-35

### Week 3: Complete ABE

**Monday**
- Office hours: Debug exercises 1-20
- Clarify error handling patterns

**Wednesday**
- Teach: Advanced topics (sections 7-10)
- Worked example: De Morgan's Laws proof
- Assign: Exercises 36-40 + Challenges

**Friday**
- Student presentations (optional)
- Questions on remaining exercises
- Preview: Identifiers section

## Integration with PLIH

**Progression:**
1. **AE** (Arithmetic Expressions) - Week 1
   - Simple syntax, simple semantics, simple proofs
   
2. **ABE** (+ Booleans) - Weeks 2-3 ← YOU ARE HERE
   - Multiple types, error handling, type consistency
   
3. **AABE** (+ Identifiers) - Weeks 4-5
   - Variable binding, environments, lookup
   
4. **Functions** (Lambda calculus) - Weeks 6-8
   - Higher-order functions, closures, scoping
   
5. **Typed Functions** - Weeks 9-11
   - Type checking, type safety proofs
   
6. **State** (Mutable references) - Weeks 12-13
   - Imperative features, store typing
   
7. **Advanced Topics** - Weeks 14-15
   - Modules, exceptions, tail recursion, optimizations

Each section follows the same structure: lecture + exercises + solutions + guide.

## Common Student Mistakes

### Mistake 1: Confusing Value Type
**Wrong**: `eval (Num 5) = 5`
**Right**: `eval (Num 5) = Some (NumV 5)`

### Mistake 2: Forgetting Option Cases
**Wrong**: `simpl; lia.` (does not handle the `None` / non-numeric cases)
**Right**:
```coq
destruct (eval e1) as [ [n|b] | ].
(* three cases: NumV n, BoolV b, and None *)
```

### Mistake 3: Type Mismatch in Proofs
**Wrong**: `eval (And e BTrue) = Some true` (type error: should be BoolV)
**Right**: `eval (And e BTrue) = Some (BoolV b)` for some boolean b

### Mistake 4: Ignoring De Morgan's Laws
**Hard**: Proving De Morgan's Laws requires sophisticated case analysis
**Solution**: Study the lecture proof carefully; use it as a reference

### Mistake 5: Not Using Inductive Hypotheses
**Wrong**: Proving `is_numeric e → ∃n, eval e = Some (NumV n)` without using IH
**Right**: Each inductive case applies the IH to subexpressions

## Extensions & Variants

### Easy Extensions
- **Add more comparisons**: GreaterThan, LessEqual, etc.
- **Add more boolean operations**: Xor, Implication
- **Prove all boolean algebra**: Associativity, idempotence, absorption

### Medium Extensions
- **Add strings**: Value := NumV nat | BoolV bool | StringV string
- **Add string operations**: Concatenation, StringEqual, StringLength
- **Prove more complex optimizations**

### Hard Extensions
- **Add formal type annotations**: Type expressions with type checking
- **Prove type safety**: Well-typed expressions have matching runtime values
- **Add evaluation strategies**: Compare eager vs. lazy evaluation

## Glossary

- **ABE**: Arithmetic + Boolean Expressions
- **Value**: The result of evaluation (either a number or boolean)
- **Option**: Type representing success (Some) or failure (None)
- **is_numeric**: Predicate classifying numeric expressions
- **is_boolean**: Predicate classifying boolean expressions
- **Type consistency**: Well-formed expressions have consistent types
- **Lazy evaluation**: We only evaluate expressions we need
- **De Morgan's Laws**: Logical equivalences about negation

## Next Steps

1. **After This Module**: Move to Identifiers section
2. **For Students**: Work through all 40 exercises systematically
3. **For Instructors**: Prepare lecture slides for week 4 (Identifiers)

## Resources

- **Rocq Documentation**: https://rocq-prover.org/doc/
- **PLIH Original (Haskell)**: https://ku-sldg.github.io/plih/
- **Pierce's PLF (Coq)**: https://softwarefoundations.cis.upenn.edu/
- **TAPL**: "Types and Programming Languages" by Benjamin C. Pierce

## Questions?

**For Students:**
- Review the lecture carefully before tackling exercises
- Use the solutions as a guide for proof structure
- Ask for help on proofs stuck > 30 minutes

**For Instructors:**
- The instructor guide has common mistakes and fixes
- Assessment rubric provides grading guidelines
- All solutions are provided for reference

---

**Status**: Complete and tested ✓ (builds cleanly with `make`)  
**Rocq Version**: tested on The Rocq Prover 9.1  
**Effort**: ~10-12 hours for students, ~8-10 hours preparation for instructors

Good luck! This module is crucial for understanding type systems and formal verification.
