(**
INSTRUCTOR GUIDE: Teaching the EMon (Reader+Either Monad) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have RMon: the Reader monad, the monadic checker
[typeofR], and the agreement theorem.  This chapter changes only the
FAILURE half of the monad, so frame it as "same threading, richer
errors".
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
1. THE COMPLAINT.  RMon rejects [Plus (Boolean true) (Num 1)] with
   [None].  A real compiler says WHERE and WHY.  We want messages.

2. STACK EITHER ON READER.  [RE E A = E -> string + A].  Walk the
   operations, contrasting with RMon: [retE]/[askE]/[localE] mirror the
   Reader ones; the difference is [bindE] threads [inl msg] through
   (short-circuit) and [throwE msg] replaces [failR].  Success is [inr],
   failure is [inl] with a message.

3. THE CHECKER.  [typeofE] is [typeofR] with each [failR] turned into a
   descriptive [throwE].  Show a couple of error strings; note the logic
   is byte-for-byte the same otherwise.

4. REFINEMENT.  Introduce [forget : string + A -> option A].  The
   theorem [typeofE_refines : forget (typeofE e ctx) = typeof ctx e]
   says the messages are pure ADDED VALUE - erase them and you are back
   to the exact [option] checker.  So no program's accept/reject status
   changed; only the diagnostics improved.

5. THE PROOF SHAPE.  Same induction as RMon's agreement, but because
   [forget] sits on the OUTSIDE we rewrite the direct side BACKWARDS
   ([rewrite <- IH]) to expose [forget (typeofE ...)] and then case on
   the [sum] ([inl]/[inr]).  Worth showing once; the rest is mechanical.
 *)

(** * PART 3: COMMON PITFALLS *)

(**
- [inl]/[inr] direction.  Convention here: [inl] = error (a [string]),
  [inr] = success (a value).  "Right is right."  Mixing these up flips
  every case.

- Messages are DATA, not control.  The refinement theorem is exactly the
  statement that the particular strings do not affect what is decided -
  [forget] throws them away and nothing changes.

- As in RMon, the proof needs the monad operators to be transparent so
  reduction can unfold them; [throwE]'s message is irrelevant to
  [forget], which is why the string literals never appear in the proof.

- Left identity [bindE (retE a) f = f a] and error short-circuit
  [bindE (throwE msg) f = throwE msg] both hold by reduction; right
  identity would need functional extensionality (hence omitted).
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex3): run [typecheckE] - a success and two explanatory
  error messages.
Part 2 (ex4-ex5): use [typeofE_refines]/[typecheckE_refines].
Part 3 (ex6-ex8): monad laws - left identity, error short-circuit, and
  [askE]'s defining behavior.

Grade by building plih_emon_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: LOOKING AHEAD *)

(**
This closes the monadic-interpreter thread: Reader for context, Either
for errors, each a proven behavior-preserving restructuring.  The same
toolkit (a monad that threads something through an interpreter) reappears
when the course adds mutable STATE - there the threaded thing is a store.
 *)
