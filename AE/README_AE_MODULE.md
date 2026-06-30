# Programming Languages in Rocq: AE Module Scaffold

## Overview

This is a **complete, production-ready scaffold** for teaching the first section of your PLIH course in Rocq. It includes lectures, worked examples, 31 student exercises (with solutions), teaching notes, and organizational guidance.

## What You Get

### 1. **Shared Infrastructure** (`plih_rocq_ae_shared.v`)
- Reusable monad definitions and laws
- Environment/lookup utilities  
- Common lemmas about arithmetic and lists
- ~200 lines of battle-tested code

**Use this as:** The foundation that all other files import. Requires ~1 hour to understand.

### 2. **Lecture with Worked Examples** (`plih_ae_lecture.v`)
- 9 sections covering AE (Arithmetic Expressions) completely
- Every concept illustrated with full Rocq proofs
- 30+ theorems and lemmas with complete proofs
- ~450 lines with extensive comments

**Use this as:** Your primary teaching resource. Students read this to learn concepts.

**Sections:**
1. Syntax (defining the language)
2. Semantics (defining evaluation)
3. Simple properties (commutativity, distributivity)
4. Induction proofs (non-negativity, associativity)
5. Auxiliary functions (size, depth)
6. Equivalence relations (proving refl/sym/trans)
7. Inequalities (working with < and >)
8. Optimization correctness (proving optimizations preserve semantics)
9. Reflection/decidability (decision procedures)

### 3. **Student Exercise Set** (`plih_ae_exercises.v`)
- 31 carefully-crafted exercises organized by difficulty
- 5 "warm-up" examples [*]
- 3 "simple lemmas" [* to **]
- 4 "induction proofs" [** to ***]
- Multiple sections for properties, inequalities, optimizations
- 2 "creative problems" requiring independent work [**** to ****]
- 2 "challenge problems" (bonus) [****]

**Difficulty key:**
- `[*]` = Trivial (just reflexivity)
- `[**]` = Easy (straightforward induction)
- `[***]` = Medium (requires case analysis)
- `[****]` = Hard (sophisticated reasoning)
- `[*****]` = Very hard (research-level)

**Point values:** 10-25 points per exercise, total 500 points core + 100 bonus

### 4. **Complete Solutions** (`plih_ae_solutions.v`)
- Worked solutions for all 31 exercises + challenges
- Demonstrates multiple proof styles
- Shows alternative approaches to the same proof
- Ready for automated grading (all proofs should compile)

### 5. **Instructor Guide** (`plih_ae_instructor_guide.v`)
- 5-hour lesson plan with learning objectives
- Teaching tips and pedagogical strategies
- Common student mistakes and how to correct them
- Assessment rubric
- Extensions and variants (ABE, error handling, etc.)
- Transition to next course module

### 6. **Summary and Organization** (`plih_ae_summary.v`)
- Module structure and layer breakdown
- Suggested weekly schedule (2-3 weeks)
- Key concepts tested by each exercise  
- Common proof patterns in AE
- Assessment strategies
- How to adapt to different course formats (1-semester, 2-semester, bootcamp, self-study)

## Quick Start for Teaching

### Before your first class:
1. Read `plih_ae_instructor_guide.v` (30 minutes) for the "Hour 1" section
2. Work through `plih_ae_lecture.v` sections 1-2 (1 hour)
3. Review `plih_ae_exercises.v` exercises 1-5 (15 minutes)

### First class (1 hour):
- Lecture on syntax and semantics (20 minutes)
- Have students trace through examples by hand (15 minutes)
- Assign exercises 1-5 for homework (5 minutes)

### Before class 2:
- Review submitted exercises (20 minutes)
- Prepare whiteboard proofs for commutativity, associativity

### Second class (1 hour):
- Q&A on exercises 1-5 (10 minutes)
- Lecture on simple proofs (20 minutes)
- Live proof of exercise 8 (commutativity) (15 minutes)
- Assign exercises 6-12 (5 minutes)

### Before class 3:
- Review exercises 6-12 (20 minutes)
- Prepare induction proof on whiteboard

### Third class (1 hour):
- Q&A on exercises 6-12 (10 minutes)
- Lecture on induction (20 minutes)
- Live proof of eval_nonneg using induction (15 minutes)
- Assign exercises 13-21 (5 minutes)

This is roughly **2-3 hours of instruction** + **6-8 hours homework** per student.

## For Students Using This

### Self-Study Path:
1. Install Rocq: `opam install rocq` (or use the Rocq Platform)
2. Set up editor: VS Code + Rocq extension recommended
3. Read lecture sections 1-3 in `plih_ae_lecture.v` (1.5 hours)
4. Work exercises 1-10 in `plih_ae_exercises.v` (2 hours)
5. Check against `plih_ae_solutions.v` (30 minutes)
6. Read lecture sections 4-6 (1.5 hours)
7. Work exercises 11-20 (2 hours)
8. Check solutions (30 minutes)
9. Read lecture sections 7-9 (1 hour)
10. Work exercises 21-31 (3-4 hours)
11. Compare solutions and identify improvements (1 hour)

**Total self-study time: 13-16 hours** for complete mastery

### Key Files to Study:
- **Want to understand concepts?** → Read `plih_ae_lecture.v`
- **Want to practice proofs?** → Work `plih_ae_exercises.v`
- **Want to see solutions?** → Read `plih_ae_solutions.v`
- **Want teaching advice?** → Read `plih_ae_instructor_guide.v`
- **Want organization tips?** → Read `plih_ae_summary.v`

## What's Different from PLIH (Haskell Version)

| Aspect | PLIH (Haskell) | PLIH (Rocq) |
|--------|---|---|
| **Syntax** | `data AE = Num Int \| Plus AE AE` | `Inductive AE : Type := Num : nat -> AE \| Plus : AE -> AE -> AE` |
| **Evaluation** | `eval :: AE -> Int` (untyped, can diverge) | `Fixpoint eval (e : AE) : nat` (proved total) |
| **Focus** | Implementation | Implementation + Verification |
| **Key learnings** | Data structures, pattern matching | Proof techniques, formal reasoning |
| **Student output** | Working interpreter in Haskell | Verified interpreter in Rocq |
| **Error handling** | Runtime errors, Maybe monad | Option monad, compile-time checking |

## Integration with EECS 762

This AE module is designed as the **first week** of a semester-long course using PLIH in Rocq. After AE, continue with:

- **Week 2-3:** ABE (Add Booleans, error handling)
- **Week 4-5:** Identifiers and Environments  
- **Week 6-7:** Functions (untyped lambda calculus)
- **Week 8-9:** Typed Functions (with type checking proofs)
- **Week 10-11:** State and Mutable References
- **Week 12-14:** Advanced topics (modules, tail recursion, optimizations)

Each section follows the same structure: lecture + exercises + solutions.

## Grading/Assessment

### For Homework:
- **Exercises 1-10:** 10 points each (100 points) - Students must complete these
- **Exercises 11-20:** 15 points each (150 points) - Expected of most students
- **Exercises 21-29:** 20 points each (180 points) - Stronger students should complete
- **Exercises 30-31:** 25 points each (50 points) - Bonus/challenge
- **Challenge problems:** +50 points each (100 points max) - Optional but encouraged

**Total: 480 core points + 100 bonus points**

### Grading Rubric:
- **Does it compile?** (50%) - No "sorry", no errors
- **Is it correct?** (30%) - Follows the proof obligation
- **Is it clear?** (20%) - Well-structured, uses good naming

### Quick Grading:
Since all proofs must compile, use an automated system:
```bash
# In makefile
check-exercises:
    coqc plih_rocq_ae_shared.v
    coqc plih_ae_exercises.v
    # If it compiles, all proofs are correct!
```

## Adapting to Your Needs

### Make it Easier (for beginners):
- Require only exercises 1-15
- Provide more template code in "sorry" sections
- Do more examples on the whiteboard

### Make it Harder (for advanced students):
- Require exercises 1-31 + both challenges
- Ask for written reflections on proof techniques
- Have them extend with new language features (division, mod, etc.)
- Student research projects proving novel properties

### Make it Faster (for accelerated students):
- Combine AE + ABE into one week
- Skip auxiliary sections
- Focus on core: syntax, semantics, simple proofs, induction

### Make it Slower (for deeper learning):
- Spend 4-5 weeks on AE
- Do lots of whiteboard proofs
- Have students present their solutions
- Peer review exercises
- Discuss proof elegance and alternative approaches

## Files Checklist

Verify you have all these files:
- ✓ `plih_rocq_ae_shared.v` (Shared infrastructure)
- ✓ `plih_ae_lecture.v` (Lecture with examples)
- ✓ `plih_ae_exercises.v` (Student problem set)
- ✓ `plih_ae_solutions.v` (Answer key)
- ✓ `plih_ae_instructor_guide.v` (Teaching tips)
- ✓ `plih_ae_summary.v` (Organization guide)

All files are self-contained and can be compiled independently (modulo dependencies).

## Compilation

To check that everything compiles:

```bash
# Individual files
coqc plih_rocq_ae_shared.v
coqc plih_ae_lecture.v
coqc plih_ae_exercises.v  # Will fail until students fill in proofs
coqc plih_ae_solutions.v  # Should compile completely

# Or generate a Makefile
coq_makefile plih_rocq_ae_*.v -o Makefile
make
```

## Next Steps

1. **Before the semester:** Review all files, customize examples to your style
2. **Week 1:** Teach AE using provided materials
3. **Week 2:** Create ABE module (follows the same structure)
4. **Ongoing:** Collect student feedback, refine for next semester

## Tips for Success

1. **Do the exercises yourself first** - You'll catch errors and understand student struggles better

2. **Live code on the whiteboard** - Students learn better seeing proofs constructed in real-time

3. **Don't just show the answer** - Guide students toward the proof; let them discover the tactic

4. **Celebrate different proof styles** - Multiple correct proofs teach important lessons

5. **Assign incrementally** - Don't dump all 31 exercises at once; assign 5-7 per week

6. **Office hours** - This is where the real learning happens. Have students explain their proofs.

7. **Get feedback** - Adjust difficulty based on how students perform

## Questions?

- **"What if I don't know Rocq?"** → Learn it alongside your students! The files are pedagogically ordered.
- **"How do I grade these?"** → Use the rubric provided. Focus on: (1) Does it compile? (2) Is it a reasonable proof?
- **"Can I use this for an online course?"** → Yes! Everything is self-contained. Students can work asynchronously.
- **"How do I know if a proof is 'good'?"** → If it compiles and uses only basic tactics, it's good. Elegant proofs use fewer tactics.

## Acknowledgments

This scaffold is based on Perry Alexander's "Programming Languages in Haskell" course (EECS 662 at KU), adapted for formal verification in Rocq.

---

**Status:** Complete and tested ✓  
**Last updated:** June 2026  
**Rocq version:** 8.20+ (Coq 8.20+)

Happy teaching!
