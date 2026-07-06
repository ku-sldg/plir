(**
INSTRUCTOR GUIDE: Teaching the TFun (Typed Functions) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have completed Func and Rec: closures ([ClosureV]), the
fuel-driven strict interpreter [evalM], fuel monotonicity, and the
Booleans/[IsZero]/[If] added in Rec.  The lazy interpreter is _not_ needed
(we drop it here).  This chapter answers the question Rec left open:
"recursion works, but the language is Turing powerful and can get stuck
- can we rule the bad programs out?"  Teach it right after Rec.
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
#<ol>#
#<li>#_Why types._ Open with a _stuck_ term: [Plus (Boolean true) (Num 1)] evaluates to [None] - but only after evaluation starts.  The goal is to reject it _without_ running it.  Motivates a static analysis.#</li>#
#<li>#_The type language._ Introduce [Ty] = [TNum] | [TBool] | [TArr d r].  Function types are the interesting part: they record what a lambda expects and what an application yields.  Type checking must _compare_ types, hence [Ty_eqb] and its correctness ([Ty_eqb_refl]/[Ty_eqb_eq]).#</li>#
#<li>#_typeof is an interpreter._ The key framing: [typeof ctx e] has the _same_ shape as [evalM] but returns _types_ and needs no fuel (type checking always terminates).  Walk the [App] rule (function must be [D -> R], argument must be [D], result is [R]) and the [If] rule (Boolean condition, _both_ branches the same type - a static term does not know which branch runs).  Note [Lambda]'s ascribed parameter type and _why_ it is required (you cannot infer a domain before application).#</li>#
#<li>#_Accept and reject._ Run the accept examples ([ty_inc], [ty_app], [ty_higher_order]) and, more importantly, the rejections: bad arithmetic, mismatched [If] branches, non-Boolean conditions, applying a number, argument-type mismatch, unbound ids.  Land the big one: [selfApp] does not type-check at _any_ parameter type - the term behind [omega] and Y/Z is gone.#</li>#
#<li>#_One interpreter, then soundness._ Keep only the strict [evalM] and re-prove fuel monotonicity (the [Lambda] case's new type argument is the only change).  State _type soundness_ - well-typed programs run to a value of the predicted type - and witness it: good programs' type and value side by side, plus the canonical-forms slices ([iszero_yields_bool], [plus_yields_num]).#</li>#
#</ol>#
 *)

(** * PART 3: COMMON PITFALLS *)

(**
  - _Type context vs environment._ [typeof] carries [Ctx = Env Ty] (names
    to _types_); [evalM] carries [Env TVal] (names to _values_).  Same
    association-list machinery, different payload.  Students conflate them.

  - _Why ascribe the parameter type._ Without applying the function there
    is no value for [x], hence no way to infer its type.  This is the one
    syntactic change from the untyped language and it is easy to overlook.

  - _Both [If] branches must agree._ The checker requires [tThen = tElse]
    because a static term cannot know which branch executes.  Contrast with
    [evalM], which runs only one branch - typing is necessarily more
    conservative than evaluation.

  - _Soundness is not fully machine-proved here._ The general theorem needs
    a logical-relations development (a type-indexed "value has type"
    predicate constraining closures' captured environments).  We match
    PLIH: state it, witness it on examples, prove the base-type canonical
    forms, and leave the full proof as advanced material.  Be explicit
    with students about what is proved vs illustrated.

  - _Literal fuel on an abstract term._ Same trap as Func/Rec: keep fuel a
    _variable_ in lemmas over abstract terms ([ex10_more_fuel]); literal fuel
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
Part 4 (ex13-ex16) - concrete syntax (Section 8).  Two notations: types
  between [<[ ... ]>] (base [Nat]/[Bool] and the _right_-associative arrow
  [->]) and terms between [<{ ... }>] with the ascribed lambda
  [lambda ID : T in body].  Emphasize that [v : T] is the _only_ type
  ascription in the term language, because [Lambda] is the only
  constructor carrying a [Ty].  All [reflexivity].
  Common mistakes: writing the type outside its brackets (types live in
  [<[ ]>], not [<{ }>]); and reading [Nat -> Nat -> Nat] left-associated
  (the arrow is _right_-associative: [Nat -> (Nat -> Nat)]).

Grade by building plih_tfun_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: LOOKING AHEAD *)

(**
Types rejected self-application, so the Y/Z combinators no longer work -
recursion is gone.  The Typed Recursion chapter reintroduces it as a
primitive typed [fix], with the striking payoff that every well-typed
term _normalizes_ (terminates).  Foreshadow this so students see the
trade: types buy safety and totality but cost the combinator trick.
 *)
