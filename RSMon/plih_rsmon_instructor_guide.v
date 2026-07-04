(**
INSTRUCTOR GUIDE: Teaching the RSMon (Reader+State Monad) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have completed RMon (a Reader monad hiding the type
context) and SMon (a State monad hiding the store, with the environment
still explicit).  This chapter is the synthesis: it COMBINES those two
effects, so it lands best right after SMon while both are fresh.  A quick
recap of "what did each monad hide, and how" is a good warm-up.
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
1. THE LEFTOVER.  SMon hid the store but STILL passed [env] by hand.
   Ask: can we hide the environment too?  It is a DIFFERENT kind of
   effect - read-only, never returned - so it wants Reader operations,
   not State ones.  The goal: one monad with both.

2. THE COMBINED MONAD.  Define [RS E S A := E -> S -> option (A * S)].
   Stress the asymmetry: the environment [E] is an INPUT only (a Reader),
   the store [S] is threaded in AND out (a State).  Give the Reader ops
   [askRS]/[localRS], the State ops [getRS]/[putRS], and one [bindRS]
   that carries both.  Point out [bindRS] passes the SAME [e] to the
   continuation (Reader: environment is constant) but the UPDATED [s']
   (State: store flows).

3. THE MONADIC INTERPRETER.  Rewrite the interpreter as [evalRS] with no
   [env] and no [s].  Walk the four env cases: [Id] uses [askRS];
   [Lambda] captures with [askRS]; [Bind] extends with
   [localRS (extend i a)]; [App] SWITCHES to the closure's environment
   with [localRS (fun _ => extend i w cenv)] - a great place to re-explain
   STATIC SCOPING.  The store cases are exactly SMon's.

4. AGREEMENT.  Prove [evalRS fuel e env s = evalM fuel env s e].  The
   striking point: ONE induction handles both resources at once -
   [localRS]/[askRS] line up with [evalM]'s [env] argument while
   [getRS]/[putRS] line up with its returned store.

5. LAWS AND INDEPENDENCE.  Close with left identity and the
   effect-INDEPENDENCE lemmas ([ask_get_comm], [local_scoped]): reading
   the environment ignores the store and vice versa - the two effects do
   not interfere.  This is the conceptual core of stacking monads.
 *)

(** * PART 3: COMMON PITFALLS *)

(**
- WHY IS THE ENVIRONMENT NOT RETURNED?  Students may expect [RS] to
  return [(A * E * S)].  It does not: the environment is read-only, so a
  computation can only OBSERVE it (via [askRS]) or run a sub-computation
  under a changed one (via [localRS]); changes never propagate outward.
  Contrast with the store, which is returned because it genuinely
  mutates.

- [localRS] vs [putRS].  [localRS g m] changes the environment ONLY for
  [m] (scoped, Reader-style); [putRS s'] changes the store for the REST
  of the computation (persistent, State-style).  Using one where you mean
  the other is the classic combined-monad bug.  [App]'s
  [localRS (fun _ => ...)] is scoped to the closure body precisely
  because the caller's environment must be restored afterward.

- THE AGREEMENT PROOF.  Same recipe as SMon: [cbn [evalRS evalM]] then
  [cbv beta iota delta [retRS bindRS askRS localRS getRS putRS failRS]]
  to expose [match evalRS k .. env s with ...]; [rewrite] the IH at each
  subexpression and [destruct] the [evalM] result (splitting value shape
  and store).  The env cases just feed [extend i _ env] as the IH's
  environment argument; [If] needs [cbn -[evalRS evalM]] after the
  Boolean split; [Deref]/[Assign] add a [destruct] on
  [nth_error]/[update_at].

- [reflexivity] FOR LAWS.  Left identity and the independence lemmas hold
  definitionally (Rocq conversion includes eta); no law-by-law algebra
  needed.
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex4) - running [evalReaderState]: arithmetic, static
  scoping, a cell round-trip, and scoping+state combined; all
  [reflexivity].
Part 2 (ex5-ex7) - agreement in action: cite [evalReaderState_agrees] /
  [evalRS_agrees], and transport a result with [rewrite <- ...].
Part 3 (ex8-ex10) - left identity, [askRS] purity, and put-then-get in
  the combined monad; all [reflexivity].

Grade by building plih_rsmon_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: LOOKING AHEAD *)

(**
The moral: effects COMPOSE.  Each monad (Reader, State, Either)
contributes its own operations to a shared [bind], and stacking them is
the essence of MONAD TRANSFORMERS.  A natural capstone adds Either on top
for descriptive error messages - an interpreter that reads its
environment, mutates its store, and reports typed failures, all through
one monad - echoing how EMon added Either to the checker.
 *)
