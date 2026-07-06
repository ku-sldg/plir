(**
INSTRUCTOR GUIDE: Teaching the SMon (State Monad) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have completed the State chapter: the reference-cell
language [FBAES], the explicit store-threading interpreter [evalM]
returning a (value, store) pair, and the feel of naming intermediate
stores [s1], [s2], ... by hand.  Seeing RMon first (the Reader monad for
the type checker) helps a lot - SMon is the same move for the store, and
the agreement-theorem proof has the same shape.
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
#<ol>#
#<li>#_The pain, restated._ Put [evalM]'s [Plus] or [Assign] case on the board and count the store variables.  The store is threaded correctly _only_ because every case passes the right [s1]/[s2]; there is no help from the types if you pass the wrong one.  Motivate: can we make the threading automatic and mechanical?#</li>#
#<li>#_The state monad._ Introduce [State S A := S -> option (A * S)] as "the type of exactly what [evalM] returns, as a function of the incoming store."  Define [retS] (store untouched), [bindS] (the _one_ place threading happens: run [m], feed its store to the continuation), [getS], [putS], [failS].  Stress that [bindS] is the whole trick - it captures the [match ... with Some (a, s') => ...] idiom once.#</li>#
#<li>#_The monadic interpreter._ Rewrite the interpreter as [evalS].  Put [evalM] and [evalS] side by side: the pure cases ([Plus], [If], [App], ...) lose all store variables, and the store shows up _only_ at [New]/[Deref]/[Assign] via [getS]/[putS].  The environment stays an explicit argument because it is read-only (a Reader monad could hide it too - a good "where next" remark).#</li>#
#<li>#_Agreement._ State and prove [evalS fuel env e s = evalM fuel env s e] by induction on fuel.  This is the payoff: the refactor is provably behavior-preserving.  Then the corollary [evalStore_agrees] for the top-level wrappers.#</li>#
#<li>#_Monad laws._ Close with the laws that hold by computation ([left_id_S], [get_put_S], and the exercise laws).  Note that right identity needs functional extensionality, so it is left out - same caveat as the Reader/Either chapters.#</li>#
#</ol>#
 *)

(** * PART 3: COMMON PITFALLS *)

(**
  - _Where did the store go?_  Students expect to see a store argument in
    [evalS].  Point at the type [State Store RVal] = [Store -> ...]: the
    store is the argument the _whole_ computation is waiting for, supplied
    once by [runState].

  - _Short-circuiting._  [evalS]'s arithmetic checks the operand shape
    ([match a with NumV x => ... | _ => failS]) _inside_ the bind, exactly
    mirroring [evalM], so a non-numeric left operand fails without running
    the right one.  Writing it as [a <- ..;; b <- ..;; match a,b] instead
    would still _agree_ (both give [None]) but would evaluate the second
    operand first - a good discussion of effect order.

  - _The agreement proof._  Each case: [cbn [evalS evalM]] to unfold both one
    step, then [cbv beta iota delta [bindS retS getS putS failS]] to
    expose the underlying [match evalS k .. s with ...]; then [rewrite]
    the IH at each subexpression and [destruct] the resulting [evalM]
    result (as [ [[[a|b|i bd ce|loc] s1]|] ] to split value shape and
    store).  [getS]/[putS] cases additionally [destruct] on [nth_error] /
    [update_at].  The [If] case needs [cbn -[evalS evalM]] after
    [destruct]-ing the Boolean so the [if] reduces before the next
    [rewrite].

  - _Monad laws by [reflexivity]._  Left identity and get-after-put hold
    definitionally _because_ Rocq's conversion includes eta for functions;
    students coming from Haskell may expect to need a law-by-law proof.
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex3) - running [evalStore] on cell programs; all
  [reflexivity].
Part 2 (ex4-ex6) - agreement in action: cite [evalStore_agrees] /
  [evalS_agrees], and transport a result with [rewrite <- ...].
Part 3 (ex7-ex10) - the monad laws (left identity, fail short-circuit,
  put-put, put-then-get), all [reflexivity].
Part 4 (ex11-ex13) - concrete syntax (Section 7): the State chapter's
  FBAES parser reused here, read through the _monadic_ [evalStore].  All
  [reflexivity].  Same two precedence reminders as State: [!] binds
  tighter than [+], and [;] is loosest and right-associative.  (The
  term-level [;] is unrelated to the monadic [;;] on [State] values.)

Grade by building plih_smon_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: LOOKING AHEAD *)

(**
The moral: a monad turns a threaded resource into implicit plumbing,
provably without changing behavior.  Students have now seen it twice -
Reader for the type context (RMon) and State for the store (SMon).  The
natural next step is _combining_ them: one interpreter that reads its
environment through a Reader and mutates its store through a State,
echoing how EMon stacked Reader with Either for the checker.
 *)
