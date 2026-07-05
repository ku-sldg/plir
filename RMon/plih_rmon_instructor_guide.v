(**
INSTRUCTOR GUIDE: Teaching the RMon (Reader Monad) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have TFun/TRec: the type language [Ty], the checker
[typeof] with its explicit context parameter, and comfort reading a
recursive [Fixpoint] over the term language.  No new language is
introduced here - the point is a REFACTORING technique.
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
1. NAME THE PLUMBING.  Re-read [typeof] and count how often [ctx]
   appears: passed in, extended for [Bind]/[Lambda], read for [Id].  The
   context is threaded through EVERY call, mechanically.  That is the
   boilerplate we want to factor out.

2. THE READER MONAD.  Introduce [Reader E A = E -> option A]: "a
   computation that may read a fixed environment [E] and may fail."
   Present the operations one at a time and tie each to a checker case:
     [askR]  <-> reading [ctx] in the [Id] case;
     [localR (extend i t)] <-> extending [ctx] in [Bind]/[Lambda];
     [bindR]/[;;] <-> sequencing that used to pass [ctx] along;
     [retR]/[failR] <-> returning a type / signalling ill-typed.

3. THE MONADIC CHECKER.  Put [typeof] and [typeofR] SIDE BY SIDE.  The
   per-node logic is identical; the difference is that [typeofR] never
   mentions [ctx].  Stress [Bind]: [localR (extend i tv) (typeofR b)]
   replaces "recurse with an EXTENDED context".

4. AGREEMENT.  The payoff theorem [typeofR_agrees : typeofR e ctx =
   typeof ctx e].  The proof is one induction; each case unfolds the
   monad operations (they are plain definitions) and finishes by the
   IHs.  Emphasize what it MEANS: refactoring to the monad provably did
   not change behavior.  A refactor you can prove correct is the whole
   selling point.
 *)

(** * PART 3: COMMON PITFALLS *)

(**
- "Where did [ctx] go?"  It is the hidden argument of every [Reader].
  [runR m ctx] is where it re-appears.  [typeofR e] is a FUNCTION
  awaiting a context; [typeofR e ctx] supplies it.

- The [;;] notation is just [bindR]: [x <- m ;; k] means "run [m], call
  its result [x], then run [k]".  Both steps see the same context.

- MONAD LAWS.  Left identity [bindR (retR a) f = f a] holds by
  reduction (eta).  Right identity [bindR m retR = m] needs functional
  extensionality (equality of functions), so we do NOT ask for it -
  flag this as the reason it is absent from the exercises.

- The proof of agreement leans on the monad operators being TRANSPARENT
  definitions so [simpl]/reduction can unfold them; if you make them
  opaque the case analysis stops going through.
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex3): run [typecheckR] - accept/reject, and a [Bind] whose
  body reads an extended context.
Part 2 (ex4-ex5): use [typeofR_agrees]/[typecheckR_agrees] to relate the
  monadic and direct checkers.
Part 3 (ex6-ex8): small Reader laws - left identity (reduction), and the
  defining behaviors of [askR] and [localR].
Part 4 (ex9-ex11): concrete syntax (Section 6).  TRec's two notations -
  types [<[ ... ]>] (right-associative [->]) and terms [<{ ... }>] with
  the ascribed lambda [lambda ID : T in body] and prefix [fix] - read
  through the MONADIC checker [typecheckR].  All [reflexivity].  Common
  mistakes: reading [->] as left-associative, and forgetting [fix] wants
  its whole generator in parens.

Grade by building plih_rmon_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: LOOKING AHEAD *)

(**
Failure here is a bare [None].  The next chapter keeps the Reader
threading but swaps [option] for [Either]/sum, so a rejection carries a
MESSAGE - the beginning of real error reporting.  The agreement theorem
becomes a REFINEMENT: forgetting the message recovers this chapter's
[option] answer.
 *)
