(**
INSTRUCTOR GUIDE: Teaching the TRec (Typed Recursion) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have completed TFun: the type language [Ty], the
checker [typeof]/[typecheck], the single strict [evalM], and - crucially
- the observation that self-application no longer type-checks, so the
Rec chapter's Y/Z combinators are gone.  Motivate this chapter as
answering "then how do we ever recur again?"
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
1. THE PROBLEM.  Types outlawed self-application, and with it all
   recursion.  Worse (better?), pure TFun is strongly normalizing:
   there is provably no way to loop.  A total language cannot be
   Turing complete, so we must ADD something.

2. THE NEW FORM.  Add ONE constructor, [Fix], and its typing rule
   [f : T -> T  =>  Fix f : T].  Emphasize the shape: the argument is a
   generator that takes "the recursive call" (type [T]) and returns the
   recursive object (also type [T]).  Contrast [App]'s rule.

3. THE EVALUATION RULE.  This is the subtle part.  [Fix f] does NOT take
   one step of the recursion.  It evaluates [f] to a closure
   [ClosureV i t b e], then evaluates [b] with [i] replaced by the WHOLE
   recursion [Fix (Lambda i t b)] (via term-level [subst]).  So [i] -
   the recursive-call parameter - now means "do the fix again".  Because
   [b] is itself a lambda, evaluating it yields a closure immediately;
   the looping happens only when that closure is later applied and
   reaches the substituted [Fix].  Trace [fact 2] by hand once.
   (This is why the closure must store the parameter TYPE [t] - it is
   needed to rebuild [Lambda i t b].)

4. THE PAYOFF.  Factorial and summation are well-typed and RUN.  Show
   [ty_fact] then [run_fact5].

5. THE HONEST BARGAIN.  This is the conceptual heart of the chapter:
   - SAFETY KEPT: [ill_selfApp], [ill_fix_mismatch] - the type checker
     still rejects the untyped divergence source, and guards [Fix].
   - NORMALIZATION LOST: [loopT] is WELL-TYPED yet DIVERGES
     ([loopT_diverges]).  Draw the table:
         untyped  : stuck? yes   diverge? yes
         TFun     : stuck? no    diverge? no    (total)
         TRec     : stuck? no    diverge? yes   (safe, not total)
     [Fix] buys back Turing power at the price of totality.
 *)

(** * PART 3: A NOTE ON THE METATHEORY *)

(**
We deliberately do NOT claim (or prove) normalization - it is FALSE here
([loopT] is the counterexample).  What survives from TFun is TYPE
SOUNDNESS: well-typed programs do not get STUCK.  A [None] from [evalM]
on a well-typed term now means "fuel exhausted / still running", never
"stuck on a type error".  As in TFun, full soundness needs a
logical-relations argument over closures and is left as advanced
material; we witness it with example batteries and prove the base-type
canonical-forms slices ([iszero_yields_bool], [mult_yields_num]).  Fuel
MONOTONICITY [evalM_mono] carries over (with a new [Fix] case).
 *)

(** * PART 4: COMMON PITFALLS *)

(**
- "Isn't a typed language supposed to always terminate?"  Only WITHOUT
  a general [Fix].  Make students state which property [loopT] refutes
  (normalization) and which it does NOT (safety).

- The [Fix] evaluation rule reconstructs [Lambda i t b] from the
  closure.  Students may ask why the closure stores [t] when [evalM]
  ignores lambda annotations elsewhere - it is exactly this
  reconstruction that needs it.

- LITERAL FUEL ON AN ABSTRACT TERM still bites (see TFun/Rec notes):
  keep fuel a VARIABLE in lemmas over abstract terms ([ex8_more_fuel]);
  literal fuel is fine only on concrete closed terms.

- Divergent examples ([loopT]) return [None] at ANY fuel - use a modest
  amount so the [reflexivity] stays fast.  Productive recursion needs
  ENOUGH fuel ([eval] uses 1000); a [None] there means out of gas.
 *)

(** * PART 5: THE EXERCISES *)

(**
Part 1 (ex1-ex4): typing recursion - accept [fact], reject a mismatched
  [Fix] and self-application, check under a context.
Part 2 (ex5-ex7): run factorial/summation; observe a well-typed loop
  diverge.
Part 3 (ex8-ex10): fuel monotonicity (variable fuel), a canonical-forms
  citation, determinism.

Grade by building plih_trec_exercises.v with the [Admitted]s replaced.
 *)
