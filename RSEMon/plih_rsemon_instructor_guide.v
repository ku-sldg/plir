(**
INSTRUCTOR GUIDE: Teaching the RSEMon (Reader+State+Either) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
This is the capstone of the monad arc, so students should have done all
four earlier monad chapters: RMon (Reader), EMon (Either + [forget] +
refinement), SMon (State), and RSMon (Reader+State combined).  This
chapter contributes _no_ new individual effect - the whole lesson is that
three known effects _compose_ into one monad.  A quick "which effect does
which operation, and how does each thread" recap is the ideal warm-up.
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
#<ol>#
#<li>#_The missing channel._ RSMon hid the environment and store but still failed _silently_.  Recall EMon: an Either layer turns [None] into a descriptive message, and forgetting the message recovers the plain answer.  Goal: add that third channel to RSMon.#</li>#
#<li>#_The three-effect monad._ Define [RSE E S A := E -> S -> sum string (A * S)].  Read the shape aloud: given an environment and a store, _either_ a message ([inl]) _or_ a value with the updated store ([inr]).  Give the three op groups - Reader ([askRSE]/[localRSE]), State ([getRSE]/[putRSE]), Either ([throwRSE]) - and the one [bindRSE] that threads env and store through [inr] and short-circuits on [inl].  Define [forget] exactly as in EMon.#</li>#
#<li>#_The monadic interpreter._ Rewrite the interpreter as [evalRSE].  It is RSMon's [evalRS] with every silent failure replaced by a descriptive [throwRSE] - unbound identifier, non-number operand, non-Boolean condition, non-function application, non-location deref/assign, and "out of fuel" at the base case.  Nothing else changes.#</li>#
#<li>#_Refinement._ Prove [forget (evalRSE fuel e env s) = evalM fuel env s e] by induction on fuel.  Emphasise the shape of the statement: the extra messages are provably _invisible_ once forgotten.  This is the same refinement idea as EMon, now for the (fuel-driven, stateful) evaluator.#</li>#
#<li>#_Laws._ Close with left identity, Either short-circuit ([throw_short_circuits]), and the three-channel independence lemma ([channels_independent]).  The takeaway: each effect keeps its own behavior while sharing one [bind] - the essence of monad transformers.#</li>#
#</ol>#
 *)

(** * PART 3: COMMON PITFALLS *)

(**
  - _Why [sum string (A * S)] and not [(sum string A) * S]?_  On failure the
    store is _discarded_ (the whole computation is [inl msg]); there is no
    "value and store" to keep.  This matches [evalM]'s [None], which also
    keeps no store.  Putting the store outside the [sum] would force you to
    invent a store to return on error.

  - _"Out of fuel" is an error too._  At fuel 0 the interpreter [throwRSE]s
    "out of fuel".  Under [forget] this is [None] - exactly [evalM 0].  So
    the Either channel carries _both_ genuine type errors and resource
    exhaustion; [forget] erases the distinction, which is why refinement
    holds.

  - _The refinement proof._  Same recipe as EMon, threaded through fuel and
    store: [cbn [evalRSE evalM]] then
    [cbv beta iota delta [retRSE bindRSE askRSE localRSE getRSE putRSE throwRSE]];
    then per subexpression [rewrite <- (IH ...)] to turn the [evalM] side
    into [forget (evalRSE ...)], [destruct] the [sum] result (splitting
    message vs value/store, and the value into its four shapes), and - the
    key step - [cbn [forget]] _after_ the destruct so the [forget (inr ...)]
    wrapper reduces and the next [evalM]/[evalRSE] under it is exposed for
    the following [rewrite].  Without that [cbn [forget]], the intermediate
    store stays a bound match variable and the rewrite finds no subterm.

  - _Laws by [reflexivity]._  Left identity, short-circuit, and the
    three-channel lemma all hold definitionally (Rocq conversion includes
    eta).
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex5) - running [evalRSErr]: two successes and three distinct
  error messages; all [reflexivity].
Part 2 (ex6-ex8) - refinement in action: cite [evalRSErr_refines] /
  [evalRSE_refines], and transport an [inr] result to a [Some]
  ([rewrite <- ...], then the hypothesis).
Part 3 (ex9-ex11) - left identity, Either short-circuit, and the
  three-channel independence fact; all [reflexivity].
Part 4 (ex12-ex14) - concrete syntax (Section 7): the State chapter's
  FBAES parser, read through [evalRSErr].  All [reflexivity].  ex13 is a
  success on [inr]; ex14 shows a concrete stuck program landing on [inl]
  with a descriptive message - the chapter's payoff in the surface
  syntax.  Same precedence reminders: [!] tighter than [+], [;] loosest
  and right-associative.

Grade by building plih_rsemon_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: LOOKING AHEAD *)

(**
The moral, complete: effects _compose_.  Reader, State, and Either each
contribute their operations to a single [bind]; the interpreter reads
like a plain recursive definition while three resources are threaded
underneath, and the whole thing provably refines the explicit reference.
This is what monad transformers deliver.  Additional layers - a Writer
for an execution trace, a list monad for nondeterminism - slot in by the
same recipe, each adding its operations and its own thread to [bind].
 *)
