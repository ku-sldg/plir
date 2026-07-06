(**
Programming Languages in Rocq - Mutable State Lecture
An explicit, threaded store

Every language so far has had IMMUTABLE bindings: environments only grow
(via [Bind] and application), a value once stored is never changed.
This chapter adds real MUTATION:
#<ol>#
#<li>#FBAES = FBAEC + reference cells: [New] (allocate), [Deref] (read),
[Assign] (write), and [Seq] (evaluate for effect, keep the store).#</li>#
#<li>#A STORE-THREADING interpreter [evalM]: the environment stays
read-only, but the store is BOTH read and written, so it can no
longer be threaded like the environment - the interpreter must
RETURN a (value, store) pair and pass the new store to the next
subexpression.  This plumbing is deliberately verbose.#</li>#
#<li>#FUEL MONOTONICITY for the store-threading interpreter (the
well-definedness metatheorem, carried over with the store).#</li>#
#<li>#MUTABLE VARIABLES as a DERIVED FORM: a mutable variable is just
sugar for a cell.  This gives ALIASING - two names for one cell -
which immutable [Bind] can never express.#</li>#
#<li>#STATE + RECURSION together: a Z-combinator loop that accumulates
its result in a mutable cell.#</li>#
#</ol>#

This mirrors the "Mutable State" unit of PLIH:
  https://ku-sldg.github.io/plih//state/

The verbose store-threading here is exactly what the follow-on SMon
chapter cleans up with a State monad.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_state_shared.

Local Open Scope string_scope.
Import ListNotations.

(** * SECTION 1: SYNTAX - The FBAES Language *)

(**
FBAES ("FBAE + State") is the Rec language extended with REFERENCE
CELLS - the primitive form of mutable state:
  - [New e]      : evaluate [e], allocate a fresh cell holding its
                   value, and return the cell's LOCATION;
  - [Deref e]    : evaluate [e] to a location and read that cell;
  - [Assign l e] : evaluate [l] to a location and [e] to a value,
                   overwrite the cell, and return the value;
  - [Seq a b]    : evaluate [a] for its EFFECT (the store it leaves),
                   discard its value, then evaluate [b].
Everything else is inherited from FBAEC.
 *)
Inductive FBAES : Type :=
| Num     : nat -> FBAES
| Plus    : FBAES -> FBAES -> FBAES
| Minus   : FBAES -> FBAES -> FBAES
| Mult    : FBAES -> FBAES -> FBAES
| Boolean : bool -> FBAES
| IsZero  : FBAES -> FBAES
| If      : FBAES -> FBAES -> FBAES -> FBAES
| Bind    : string -> FBAES -> FBAES -> FBAES
| Lambda  : string -> FBAES -> FBAES
| App     : FBAES -> FBAES -> FBAES
| Id      : string -> FBAES
| Seq     : FBAES -> FBAES -> FBAES
| New     : FBAES -> FBAES
| Deref   : FBAES -> FBAES
| Assign  : FBAES -> FBAES -> FBAES.

(** * SECTION 2: VALUES AND THE STORE *)

(**
Values are Rec's numbers, Booleans, and closures, plus one new kind:
a LOCATION [LocV n], the runtime result of [New].  A location is an
index into the store; it is a first-class value, so it can be bound,
passed to functions, and stored in other cells (that last is what makes
aliasing possible).
 *)
Inductive RVal : Type :=
| NumV     : nat -> RVal
| BoolV    : bool -> RVal
| ClosureV : string -> FBAES -> list (string * RVal) -> RVal
| LocV     : nat -> RVal.

(**
The STORE maps locations to values.  Location [n] is the [n]th element;
allocation appends at the end (so the fresh location is [length]), and
assignment overwrites in place via [update_at] (from the shared library).
 *)
Definition Store := list RVal.

(** * SECTION 3: THE STORE-THREADING INTERPRETER *)

(**
The interpreter now takes a store IN and returns a (value, store) pair.
The ENVIRONMENT is read-only and threaded implicitly (as before); the
STORE is threaded EXPLICITLY, left to right: each subexpression is
evaluated in the store its predecessor left behind.  Even [Id], which
changes nothing, must pass the store along unchanged.

  - [New e]      : evaluate [e] in store [s] to [(v, s1)], then return
                   location [length s1] in the extended store [s1 ++ [v]];
  - [Deref e]    : evaluate to [(LocV n, s1)] and read [nth_error s1 n];
  - [Assign l e] : evaluate [l] then [e], then [update_at] the cell;
  - [Seq a b]    : run [a] for its store, throw its value away, run [b].

Fuel-driven, since FBAES still contains all of Rec's diverging terms.
 *)
Fixpoint evalM (fuel : nat) (env : Env RVal) (s : Store) (e : FBAES)
  : option (RVal * Store) :=
  match fuel with
  | 0 => None
  | S k =>
      match e with
      | Num n => Some (NumV n, s)
      | Plus l r =>
          match evalM k env s l with
          | Some (NumV a, s1) =>
              match evalM k env s1 r with
              | Some (NumV b, s2) => Some (NumV (a + b), s2)
              | _ => None
              end
          | _ => None
          end
      | Minus l r =>
          match evalM k env s l with
          | Some (NumV a, s1) =>
              match evalM k env s1 r with
              | Some (NumV b, s2) => Some (NumV (a - b), s2)
              | _ => None
              end
          | _ => None
          end
      | Mult l r =>
          match evalM k env s l with
          | Some (NumV a, s1) =>
              match evalM k env s1 r with
              | Some (NumV b, s2) => Some (NumV (a * b), s2)
              | _ => None
              end
          | _ => None
          end
      | Boolean b => Some (BoolV b, s)
      | IsZero e0 =>
          match evalM k env s e0 with
          | Some (NumV n, s1) => Some (BoolV (Nat.eqb n 0), s1)
          | _ => None
          end
      | If c t f =>
          match evalM k env s c with
          | Some (BoolV b, s1) =>
              if b then evalM k env s1 t else evalM k env s1 f
          | _ => None
          end
      | Bind i v b =>
          match evalM k env s v with
          | Some (v', s1) => evalM k (extend i v' env) s1 b
          | None => None
          end
      | Lambda i b => Some (ClosureV i b env, s)
      | App f a =>
          match evalM k env s f with
          | Some (ClosureV i b cenv, s1) =>
              match evalM k env s1 a with
              | Some (a', s2) => evalM k (extend i a' cenv) s2 b
              | None => None
              end
          | _ => None
          end
      | Id x =>
          match lookup x env with
          | Some v => Some (v, s)
          | None => None
          end
      | Seq a b =>
          match evalM k env s a with
          | Some (_, s1) => evalM k env s1 b
          | None => None
          end
      | New e0 =>
          match evalM k env s e0 with
          | Some (v, s1) => Some (LocV (length s1), (s1 ++ [v])%list)
          | None => None
          end
      | Deref e0 =>
          match evalM k env s e0 with
          | Some (LocV n, s1) =>
              match nth_error s1 n with
              | Some v => Some (v, s1)
              | None => None
              end
          | _ => None
          end
      | Assign l r =>
          match evalM k env s l with
          | Some (LocV n, s1) =>
              match evalM k env s1 r with
              | Some (v, s2) =>
                  match update_at n v s2 with
                  | Some s3 => Some (v, s3)
                  | None => None
                  end
              | None => None
              end
          | _ => None
          end
      end
  end.

(* A convenience wrapper: empty environment, empty store, generous fuel.
   The result is a (value, final store) pair - the store is now part of
   the observable answer. *)
Definition eval (e : FBAES) : option (RVal * Store) := evalM 1000 nil nil e.

(** * SECTION 4: RUNNING THE BASICS *)

(* Pure arithmetic leaves the store untouched (here, empty). *)
Example ev_arith :
  eval (Mult (Num 6) (Plus (Num 3) (Num 4))) = Some (NumV 42, nil).
Proof. reflexivity. Qed.

(* Allocation returns a LOCATION and grows the store. *)
Example ev_new :
  eval (New (Num 7)) = Some (LocV 0, [NumV 7]).
Proof. reflexivity. Qed.

(* A full cell round-trip: allocate, write, then read the new value.
   [Bind "r" (New (Num 0)) ...] binds [r] to the fresh location. *)
Example ev_cell_roundtrip :
  eval (Bind "r" (New (Num 0))
          (Seq (Assign (Id "r") (Num 7))
               (Deref (Id "r"))))
  = Some (NumV 7, [NumV 7]).
Proof. reflexivity. Qed.

(* Effects PERSIST across a sequence: the write in the first [Seq] arm is
   visible to the [Deref] in the second, because the store is threaded. *)
Example ev_seq_effect :
  eval (Bind "r" (New (Num 1))
          (Seq (Assign (Id "r") (Plus (Deref (Id "r")) (Num 10)))
               (Deref (Id "r"))))
  = Some (NumV 11, [NumV 11]).
Proof. reflexivity. Qed.

(** * SECTION 5: FUEL MONOTONICITY *)

(**
As in Rec, no measure bounds the fuel, so well-definedness is again
MONOTONICITY: more fuel never changes an answer already produced - and
"an answer" is now a (value, store) PAIR, so the store is preserved too.
The proof is Rec's, threaded through the store: each recursive subcall
is bumped from [k] to [k2] by the induction hypothesis, and the store
carried out of one subcall feeds the next.
 *)
Lemma evalM_mono : forall f1 f2 env st e p,
  f1 <= f2 -> evalM f1 env st e = Some p -> evalM f2 env st e = Some p.
Proof.
  induction f1 as [| k IH]; intros f2 env st e p Hle H.
  - simpl in H. discriminate.
  - destruct f2 as [| k2]; [lia |].
    destruct e; simpl in H |- *.
    + (* Num *) exact H.
    + (* Plus *)
      destruct (evalM k env st e1) as [[[a|b|i bd ce|loc] s1]|] eqn:El; try discriminate.
      destruct (evalM k env s1 e2) as [[[a2|b2|i2 bd2 ce2|loc2] s2]|] eqn:Er; try discriminate.
      rewrite (IH k2 env st e1 (NumV a, s1) ltac:(lia) El).
      cbn -[evalM].
      rewrite (IH k2 env s1 e2 (NumV a2, s2) ltac:(lia) Er).
      cbn -[evalM]. exact H.
    + (* Minus *)
      destruct (evalM k env st e1) as [[[a|b|i bd ce|loc] s1]|] eqn:El; try discriminate.
      destruct (evalM k env s1 e2) as [[[a2|b2|i2 bd2 ce2|loc2] s2]|] eqn:Er; try discriminate.
      rewrite (IH k2 env st e1 (NumV a, s1) ltac:(lia) El).
      cbn -[evalM].
      rewrite (IH k2 env s1 e2 (NumV a2, s2) ltac:(lia) Er).
      cbn -[evalM]. exact H.
    + (* Mult *)
      destruct (evalM k env st e1) as [[[a|b|i bd ce|loc] s1]|] eqn:El; try discriminate.
      destruct (evalM k env s1 e2) as [[[a2|b2|i2 bd2 ce2|loc2] s2]|] eqn:Er; try discriminate.
      rewrite (IH k2 env st e1 (NumV a, s1) ltac:(lia) El).
      cbn -[evalM].
      rewrite (IH k2 env s1 e2 (NumV a2, s2) ltac:(lia) Er).
      cbn -[evalM]. exact H.
    + (* Boolean *) exact H.
    + (* IsZero *)
      destruct (evalM k env st e) as [[[n|b|i bd ce|loc] s1]|] eqn:E0; try discriminate.
      rewrite (IH k2 env st e (NumV n, s1) ltac:(lia) E0).
      cbn -[evalM]. exact H.
    + (* If *)
      destruct (evalM k env st e1) as [[[a|bb|i bd ce|loc] s1]|] eqn:Ec; try discriminate.
      destruct bb.
      * rewrite (IH k2 env st e1 (BoolV true, s1) ltac:(lia) Ec).
        cbn -[evalM]. apply (IH k2); [lia | exact H].
      * rewrite (IH k2 env st e1 (BoolV false, s1) ltac:(lia) Ec).
        cbn -[evalM]. apply (IH k2); [lia | exact H].
    + (* Bind *)
      destruct (evalM k env st e1) as [[v1 s1]|] eqn:Ev; try discriminate.
      rewrite (IH k2 env st e1 (v1, s1) ltac:(lia) Ev).
      cbn -[evalM]. apply (IH k2); [lia | exact H].
    + (* Lambda *) exact H.
    + (* App *)
      destruct (evalM k env st e1) as [[[a|b|i bd ce|loc] s1]|] eqn:Ef; try discriminate.
      destruct (evalM k env s1 e2) as [[v2 s2]|] eqn:Ea; try discriminate.
      rewrite (IH k2 env st e1 (ClosureV i bd ce, s1) ltac:(lia) Ef).
      cbn -[evalM].
      rewrite (IH k2 env s1 e2 (v2, s2) ltac:(lia) Ea).
      cbn -[evalM]. apply (IH k2); [lia | exact H].
    + (* Id *) exact H.
    + (* Seq *)
      destruct (evalM k env st e1) as [[v1 s1]|] eqn:E1; try discriminate.
      rewrite (IH k2 env st e1 (v1, s1) ltac:(lia) E1).
      cbn -[evalM]. apply (IH k2); [lia | exact H].
    + (* New *)
      destruct (evalM k env st e) as [[v1 s1]|] eqn:E0; try discriminate.
      rewrite (IH k2 env st e (v1, s1) ltac:(lia) E0).
      cbn -[evalM]. exact H.
    + (* Deref *)
      destruct (evalM k env st e) as [[[a|b|i bd ce|loc] s1]|] eqn:E0; try discriminate.
      rewrite (IH k2 env st e (LocV loc, s1) ltac:(lia) E0).
      cbn -[evalM]. exact H.
    + (* Assign *)
      destruct (evalM k env st e1) as [[[a|b|i bd ce|loc] s1]|] eqn:El; try discriminate.
      destruct (evalM k env s1 e2) as [[v2 s2]|] eqn:Er; try discriminate.
      rewrite (IH k2 env st e1 (LocV loc, s1) ltac:(lia) El).
      cbn -[evalM].
      rewrite (IH k2 env s1 e2 (v2, s2) ltac:(lia) Er).
      cbn -[evalM]. exact H.
Qed.

(** * SECTION 6: MUTABLE VARIABLES AS A DERIVED FORM *)

(**
We never added a "mutable variable" construct - we do not need one.  A
mutable variable is just a NAME bound to a reference cell.  The three
surface operations ELABORATE into the ref-cell core:

  MutBind x e b  ==  Bind x (New e) b       (* x names a fresh cell *)
 *   Get x          ==  Deref (Id x)           (* read through the name *)
 *   SetVar x e     ==  Assign (Id x) e        (* write through the name *)
 *
 * These are ordinary Rocq definitions building FBAES terms - the
 * "elaboration" is definitional unfolding, exactly the derived-form idea
 * from the Func chapter.
 *)
Definition MutBind (x : string) (e b : FBAES) : FBAES := Bind x (New e) b.
Definition Get (x : string) : FBAES := Deref (Id x).
Definition SetVar (x : string) (e : FBAES) : FBAES := Assign (Id x) e.

(* A mutable counter reads and writes the same variable. *)
Example ev_mutvar :
  eval (MutBind "c" (Num 0)
          (Seq (SetVar "c" (Plus (Get "c") (Num 1)))
               (Seq (SetVar "c" (Plus (Get "c") (Num 1)))
                    (Get "c"))))
  = Some (NumV 2, [NumV 2]).
Proof. reflexivity. Qed.

(**
ALIASING - the thing immutable [Bind] can NEVER do.  Binding [a] to the
value of [Id "r"] copies the LOCATION, not the cell, so [a] and [r] name
the SAME cell.  A write through [r] is therefore visible through [a].
 *)
Example ev_aliasing :
  eval (MutBind "r" (Num 0)
          (Bind "a" (Id "r")                 (* a and r share one cell *)
             (Seq (SetVar "r" (Num 99))       (* write through r ... *)
                  (Get "a"))))                (* ... read through a *)
  = Some (NumV 99, [NumV 99]).
Proof. reflexivity. Qed.

(**
Contrast: a PLAIN (immutable) [Bind] copies the VALUE, so the two names
are independent - rebinding one leaves the other alone.  Aliasing is a
property of shared MUTABLE state, not of naming.
 *)
Example ev_no_aliasing_immutable :
  eval (Bind "x" (Num 0)
          (Bind "y" (Id "x")
             (Bind "x" (Num 99)              (* shadows x; y is unaffected *)
                (Id "y"))))
  = Some (NumV 0, nil).
Proof. reflexivity. Qed.

(** * SECTION 7: STATE MEETS RECURSION *)

(**
The Z (call-by-value) fixpoint combinator from the Rec chapter is an
ordinary term here too - FBAES contains all of FBAEC.  We restate it
over FBAES so we can tie state and recursion together.
 *)
Definition Zc : FBAES :=
  Lambda "f"
    (App (Lambda "x" (App (Id "f")
            (Lambda "v" (App (App (Id "x") (Id "x")) (Id "v")))))
         (Lambda "x" (App (Id "f")
            (Lambda "v" (App (App (Id "x") (Id "x")) (Id "v")))))).

(**
A recursive loop that COUNTS DOWN from [c], bumping a shared mutable
cell [acc] by one on every step.  [acc] is captured from the enclosing
environment, so all recursive calls hit the SAME cell.

  incTo = \rec. \c. if c = 0 then 0
                    else (acc := acc + 1 ; rec (c - 1))
 *)
Definition incTo : FBAES :=
  Lambda "rec"
    (Lambda "c"
      (If (IsZero (Id "c"))
          (Num 0)
          (Seq (SetVar "acc" (Plus (Get "acc") (Num 1)))
               (App (Id "rec") (Minus (Id "c") (Num 1)))))).

(**
Allocate [acc := 0], run the loop 5 times via [Z], then read [acc].
The recursion (Z, from Rec) and the mutation (the cell) cooperate: the
store threads through every recursive call, so the five increments
accumulate to 5.
 *)
Definition counterProg : FBAES :=
  MutBind "acc" (Num 0)
    (Seq (App (App Zc incTo) (Num 5))
         (Get "acc")).

Example ev_counter :
  eval counterProg = Some (NumV 5, [NumV 5]).
Proof. reflexivity. Qed.

(** * SECTION 8: CONCRETE SYNTAX - A NOTATION PARSER *)

(**
FBAES is a new type, so - as in Rec - it gets its OWN notation parser:
Rec's FBAEC grammar (numerals/identifiers via coercion, arithmetic,
Booleans, [if], [lambda], [bind], juxtaposition application) plus FOUR
state forms.  The state notations are chosen to read like ML/imperative
code:

  - [new e]   : allocate a cell ([New]);
  - [! e]     : dereference/read ([Deref]) - binds TIGHTER than [+], so
                [! "acc" + 1] is [(! "acc") + 1], not [! ("acc" + 1)];
  - [l := e]  : assign ([Assign]); with an identifier on the left,
                [x := e] is exactly the mutable-variable write [SetVar];
  - [a ; b]   : sequence ([Seq]), the LOOSEST operator and
                right-associative, so [a ; b ; c] is [a ; (b ; c)].
 *)

Coercion Num : nat >-> FBAES.
Coercion Id  : string >-> FBAES.

Declare Custom Entry fbaes.
Declare Scope state_scope.
Delimit Scope state_scope with state.

Notation "<{ e }>" := e (e custom fbaes at level 99) : state_scope.
Notation "( x )" := x (in custom fbaes, x at level 99) : state_scope.
Notation "x" := x (in custom fbaes at level 0, x constr at level 0) : state_scope.

Notation "f x" := (App f x) (in custom fbaes at level 1, left associativity) : state_scope.
Notation "'!' e" := (Deref e) (in custom fbaes at level 1, e custom fbaes at level 0) : state_scope.
Notation "'new' e" := (New e) (in custom fbaes at level 75, right associativity) : state_scope.
Notation "'iszero' x" := (IsZero x) (in custom fbaes at level 75, right associativity) : state_scope.
Notation "x * y" := (Mult x y)  (in custom fbaes at level 40, left associativity) : state_scope.
Notation "x + y" := (Plus x y)  (in custom fbaes at level 50, left associativity) : state_scope.
Notation "x - y" := (Minus x y) (in custom fbaes at level 50, left associativity) : state_scope.
Notation "'true'"  := (Boolean true)  (in custom fbaes at level 0) : state_scope.
Notation "'false'" := (Boolean false) (in custom fbaes at level 0) : state_scope.
Notation "'if' c 'then' t 'else' f" := (If c t f)
  (in custom fbaes at level 89, c custom fbaes at level 99,
   t custom fbaes at level 99, f custom fbaes at level 99) : state_scope.
Notation "'lambda' v 'in' e" := (Lambda v e)
  (in custom fbaes at level 90, v constr at level 0, e custom fbaes at level 99) : state_scope.
Notation "'bind' v '=' e1 'in' e2" := (Bind v e1 e2)
  (in custom fbaes at level 89, v constr at level 0,
   e1 custom fbaes at level 99, e2 custom fbaes at level 99) : state_scope.
Notation "l ':=' e" := (Assign l e)
  (in custom fbaes at level 85, e custom fbaes at level 84, no associativity) : state_scope.
Notation "a ';' b" := (Seq a b)
  (in custom fbaes at level 90, right associativity) : state_scope.

Open Scope state_scope.

(**
Dereference binds tighter than arithmetic, and sequence is the loosest,
right-associative operator.
 *)
Example parse_deref_prec :
  <{ "acc" := ! "acc" + 1 }>
  = Assign (Id "acc") (Plus (Deref (Id "acc")) (Num 1)).
Proof. reflexivity. Qed.

Example parse_seq_assoc :
  <{ "a" := 1 ; "b" := 2 ; !"a" }>
  = Seq (Assign (Id "a") (Num 1))
        (Seq (Assign (Id "b") (Num 2)) (Deref (Id "a"))).
Proof. reflexivity. Qed.

(**
The Section 4 cell round-trip, written concretely.  A [bind] body (level
99) absorbs a whole sequence with no extra parentheses.
 *)
Example roundtrip_concrete :
  <{ bind "r" = new 0 in "r" := 7 ; !"r" }>
  = Bind "r" (New (Num 0))
      (Seq (Assign (Id "r") (Num 7)) (Deref (Id "r"))).
Proof. reflexivity. Qed.

Example roundtrip_runs :
  eval <{ bind "r" = new 0 in "r" := 7 ; !"r" }> = Some (NumV 7, [NumV 7]).
Proof. reflexivity. Qed.

(**
Because [x := e] is [Assign (Id x) e] and [!x] is [Deref (Id x)], the
mutable-variable operations of Section 6 need no special sugar - they
ARE the concrete syntax.  The [incTo] loop body reads directly.
 *)
Example incTo_concrete :
  <{ lambda "rec" in lambda "c" in
       if iszero "c" then 0
       else ("acc" := !"acc" + 1 ; "rec" ("c" - 1)) }>
  = incTo.
Proof. reflexivity. Qed.

(** * SUMMARY *)

(**
In this lecture we:
#<ol>#
#<li>#Extended FBAEC to FBAES with reference cells - [New], [Deref],
[Assign], [Seq] - the PRIMITIVE form of mutable state, and added
locations [LocV] to the value domain.#</li>#
#<li>#Gave a STORE-THREADING interpreter [evalM] that returns a
(value, store) pair: the environment stays read-only, but the
store is read AND written, so it is threaded explicitly, left to
right, through every subexpression.#</li>#
#<li>#Proved FUEL MONOTONICITY for [evalM] - now preserving the store as
part of the answer.#</li>#
#<li>#Recovered MUTABLE VARIABLES as a DERIVED FORM ([MutBind]/[Get]/
[SetVar] = sugar over cells) and saw ALIASING fall out - two names
for one cell, which immutable [Bind] cannot express.#</li>#
#<li>#Combined STATE and RECURSION: a Z-combinator loop accumulating into
a shared cell.#</li>#
#<li>#Added CONCRETE SYNTAX (Section 8): Rec's FBAEC parser plus the four
state forms [new e], [! e], [l := e], [a ; b] - reading like ML,
with [!] binding tighter than arithmetic and [;] the loosest,
right-associative operator.#</li>#
#</ol>#

The catch: this explicit store-threading is PAINFUL - every case has to
name intermediate stores [s1], [s2], ... and thread them by hand, and
one wrong store variable is a silent bug.  The follow-on SMon chapter
hides all of it behind a STATE MONAD, so the interpreter reads like the
pure ones again while still threading the store underneath.
 *)
