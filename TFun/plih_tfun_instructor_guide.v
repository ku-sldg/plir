(**
INSTRUCTOR GUIDE: Teaching the TFun (Typed Functions) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have completed Func and Rec: closures ([ClosureV]), the
fuel-driven strict interpreter [evalM], fuel monotonicity, and the
Booleans/[IsZero]/[If] added in Rec.  The lazy interpreter is NOT needed
(we drop it here).  This chapter answers the question Rec left open:
"recursion works, but the language is Turing powerful and can get stuck
- can we rule the bad programs out?"  Teach it right after Rec.
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
1. WHY TYPES.  Open with a STUCK term: [Plus (Boolean true) (Num 1)]
   evaluates to [None] - but only after evaluation starts.  The goal is
   to reject it WITHOUT running it.  Motivates a static analysis.

2. THE TYPE LANGUAGE.  Introduce [Ty] = [TNum] | [TBool] | [TArr d r].
   Function types are the interesting part: they record what a lambda
   expects and what an application yields.  Type checking must COMPARE
   types, hence [Ty_eqb] and its correctness ([Ty_eqb_refl]/[Ty_eqb_eq]).

3. TYPEOF IS AN INTERPRETER.  The key framing: [typeof ctx e] has the
   SAME shape as [evalM] but returns TYPES and needs no fuel (type
   checking always terminates).  Walk the [App] rule (function must be
   [D -> R], argument must be [D], result is [R]) and the [If] rule
   (Boolean condition, BOTH branches the same type - a static term does
   not know which branch runs).  Note [Lambda]'s ascribed parameter type
   and WHY it is required (you cannot infer a domain before application).

4. ACCEPT AND REJECT.  Run the accept examples ([ty_inc], [ty_app],
   [ty_higher_order]) and, more importantly, the REJECTIONS: bad
   arithmetic, mismatched [If] branches, non-Boolean conditions,
   applying a number, argument-type mismatch, unbound ids.  Land the big
   one: [selfApp] does not type-check at ANY parameter type - the term
   behind [omega] and Y/Z is gone.

5. ONE INTERPRETER, THEN SOUNDNESS.  Keep only the strict [evalM] and
   re-prove fuel monotonicity (the [Lambda] case's new type argument is
   the only change).  State TYPE SOUNDNESS - well-typed programs run to a
   value of the predicted type - and witness it: good programs' type and
   value side by side, plus the canonical-forms slices
   ([iszero_yields_bool], [plus_yields_num]).
 *)

(** * PART 3: COMMON PITFALLS *)

(**
- TYPE CONTEXT vs ENVIRONMENT.  [typeof] carries [Ctx = Env Ty] (names
  to TYPES); [evalM] carries [Env TVal] (names to VALUES).  Same
  association-list machinery, different payload.  Students conflate them.

- WHY ASCRIBE THE PARAMETER TYPE.  Without applying the function there
  is no value for [x], hence no way to infer its type.  This is the one
  syntactic change from the untyped language and it is easy to overlook.

- BOTH [If] BRANCHES MUST AGREE.  The checker requires [tThen = tElse]
  because a static term cannot know which branch executes.  Contrast with
  [evalM], which runs only one branch - typing is necessarily more
  conservative than evaluation.

- SOUNDNESS IS NOT FULLY MACHINE-PROVED HERE.  The general theorem needs
  a logical-relations development (a type-indexed "value has type"
  predicate constraining closures' captured environments).  We match
  PLIH: state it, witness it on examples, prove the base-type canonical
  forms, and leave the full proof as advanced material.  Be explicit
  with students about what is proved vs illustrated.

- LITERAL FUEL ON AN ABSTRACT TERM.  Same trap as Func/Rec: keep fuel a
  VARIABLE in lemmas over abstract terms ([ex10_more_fuel]); literal fuel
  is fine only on concrete closed terms.
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex5) - the type checker: accept arithmetic and a lambda,
  reject a bad condition, an argument-type mismatch, and self-application.
  All [reflexivity].
Part 2 (ex6-ex8) - the strict interpreter: evaluate an application and a
  conditional; [ex8] gives a lambda's closure under positive fuel.
Part 3 (ex9-ex12) - metatheory: [Ty_eqb] soundness (cite [Ty_eqb_eq]),
  fuel monotonicity (cite [evalM_mono], keep fuel a variable), a
  canonical-forms proof for [Mult] (model on [plus_yields_num]), and
  determinism.
Challenges - [twice]: its function type, and soundness in miniature
  ([twice inc 5] type-checks at [TNum] and evaluates to [NumV 7]).
Part 4 (ex13-ex16) - concrete syntax (Section 8).  TWO notations: types
  between [<[ ... ]>] (base [Nat]/[Bool] and the RIGHT-associative arrow
  [->]) and terms between [<{ ... }>] with the ascribed lambda
  [lambda ID : T in body].  Emphasize that [v : T] is the ONLY type
  ascription in the term language, because [Lambda] is the only
  constructor carrying a [Ty].  All [reflexivity].
  Common mistakes: writing the type outside its brackets (types live in
  [<[ ]>], not [<{ }>]); and reading [Nat -> Nat -> Nat] left-associated
  (the arrow is RIGHT-associative: [Nat -> (Nat -> Nat)]).

Grade by building plih_tfun_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: LOOKING AHEAD *)

(**
Types rejected self-application, so the Y/Z combinators no longer work -
recursion is gone.  The Typed Recursion chapter reintroduces it as a
primitive typed [fix], with the striking payoff that every well-typed
term NORMALIZES (terminates).  Foreshadow this so students see the
trade: types buy safety and totality but cost the combinator trick.
 *)
