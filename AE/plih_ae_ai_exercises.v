(**
Programming Languages in Rocq - AE AI-Assisted Exercises
Arithmetic Expressions - AI Collaboration Problem Set

In these exercises you will:
#<ol>#
#<li>#Ask an AI assistant to write or extend Rocq code#</li>#
#<li>#_Read and verify_ every line the AI produces before accepting it#</li>#
#<li>#Prove lemmas that the AI suggests, understanding each step#</li>#
#<li>#Reflect on what properties hold — and which surprisingly do not#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Each exercise has an "Ask Claude:" prompt telling you what to request
from an AI assistant, and a "Reflect:" section asking you to think
critically about the result.  Scaffold definitions are PROVIDED so
the file compiles as given.  Student proof obligations end in
[Admitted].  Replace each [Admitted] with a real proof.

Difficulty: ★ trivial, ★★ easy, ★★★ requires case analysis or nia.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import plih_rocq_ae_shared.
Require Import plih_ae_lecture.

(** * Exercise 1 (★★★): Extending AE with Multiplication

_Ask Claude:_
"I have an arithmetic expression language [AE] with [Num], [Plus], and
[Minus].  Please add a [TTimes] constructor to produce a new type [AET]
and write an [evalT] interpreter for it.  Then prove the three lemmas
below."

Once Claude responds, read every line of [evalT] and each proof
carefully.  Make sure the interpreter recurses on _both_ subterms for
[TTimes] and that each lemma follows from simple arithmetic.

_Reflect:_
#<ol>#
#<li>#Does [evalT] always succeed?  Why?  (Hint: what is the return type?)#</li>#
#<li>#Would totality still hold if you added a [TDiv] (division) constructor?
   What would you have to change, and why?#</li>#
#<li>#The hints suggest [simpl; nia] and [simpl; lia].  What do [nia] and
   [lia] do differently?  When does [nia] beat [lia]?#</li>#
#</ol>#
 *)

(** The extended expression type.  [TTimes] is the new constructor. *)
Inductive AET : Type :=
| TNum   : nat -> AET
| TPlus  : AET -> AET -> AET
| TMinus : AET -> AET -> AET
| TTimes : AET -> AET -> AET.

(** Interpreter for [AET].  Multiplication is handled by [Nat.mul]. *)
Fixpoint evalT (e : AET) : nat :=
  match e with
  | TNum n     => n
  | TPlus  l r => evalT l + evalT r
  | TMinus l r => evalT l - evalT r
  | TTimes l r => evalT l * evalT r
  end.

(** Multiplication is commutative at the expression level.
    Hint: [simpl; nia]. *)
Lemma ai1a_times_comm : forall e1 e2,
  evalT (TTimes e1 e2) = evalT (TTimes e2 e1).
Proof. Admitted.

(** Multiplying by zero on the left gives zero.
    Hint: [simpl; lia]. *)
Lemma ai1b_times_zero : forall e,
  evalT (TTimes (TNum 0) e) = 0.
Proof. Admitted.

(** Multiplication distributes over addition on the left.
    Hint: [simpl; nia]. *)
Lemma ai1c_times_distributes : forall l r e3,
  evalT (TTimes (TPlus l r) e3) =
  evalT (TPlus (TTimes l e3) (TTimes r e3)).
Proof. Admitted.

(** * Exercise 2 (★★★): Constant Folding

_Ask Claude:_
"Please write a [fold_constants] function for [AE] that evaluates any
subexpression whose two operands are both numeric literals, and recurses
on all other subterms."

Inspect the definition below — it is the answer Claude should produce.
Then ask Claude to prove [ai2_fold_constants_correct].

_Reflect:_
#<ol>#
#<li>#Ask Claude whether [fold_constants] and [optimize_zero] from the
   lecture are the same function.  How do they differ in what they
   simplify?#</li>#
#<li>#The proof hint says to use [destruct (fold_constants l)] and
   [destruct (fold_constants r)] inside the [Plus] and [Minus] cases.
   Why are those [destruct]s needed?#</li>#
#</ol>#
 *)

(** Scaffold provided — this is the definition you should verify
    Claude produces when asked.  It recurses on children first and
    then checks whether both results are literals. *)
Fixpoint fold_constants (e : AE) : AE :=
  match e with
  | Num n     => Num n
  | Plus  l r =>
      match fold_constants l, fold_constants r with
      | Num a, Num b => Num (a + b)
      | l',    r'    => Plus l' r'
      end
  | Minus l r =>
      match fold_constants l, fold_constants r with
      | Num a, Num b => Num (a - b)
      | l',    r'    => Minus l' r'
      end
  end.

(** Constant folding preserves the value of every expression.
    Hint: induction on [e]; in the [Plus] and [Minus] cases, use
    [destruct (fold_constants l)] then [destruct (fold_constants r)],
    and rewrite using the induction hypotheses. *)
Lemma ai2_fold_constants_correct : forall e,
  eval (fold_constants e) = eval e.
Proof. Admitted.

(** * Exercise 3 (★★): Natural-Number Subtraction Surprises

_Ask Claude:_
"In Rocq, subtraction on [nat] is _truncated_ at zero.  Which of the
following three equivalences holds for [AE]?  Prove the true ones and
give a counterexample for the false one."

#<ol>#
#<li>#[ae_equiv (Minus e (Num 0)) e] — subtracting zero does nothing#</li>#
#<li>#[ae_equiv (Minus (Num 0) e) (Num 0)] — zero minus anything is zero#</li>#
#<li>#[ae_equiv (Plus (Minus e (Num 1)) (Num 1)) e] — subtracting then
   adding one is the identity#</li>#
#</ol>#

Verify that Claude identifies (1) and (2) as true and (3) as false.
Then complete the proofs and counterexample below.

_Reflect:_
In ordinary integers, [(e - 1) + 1 = e] always.  Why does it fail for
[nat] in Rocq?  What value of [e] is the witness?
 *)

(** Subtracting zero is the identity. *)
Lemma ai3a : forall e,
  ae_equiv (Minus e (Num 0)) e.
Proof. Admitted.

(** Zero minus anything truncates to zero (a [nat]-specific fact). *)
Lemma ai3b : forall e,
  ae_equiv (Minus (Num 0) e) (Num 0).
Proof. Admitted.

(** The general claim [(e - 1) + 1 ≡ e] is FALSE in [nat].
    The expression below evaluates to [1] (because [0 - 1 = 0] in [nat],
    so [(0 - 1) + 1 = 0 + 1 = 1]), but [Num 0] evaluates to [0].
    Hence [~ ae_equiv (Plus (Minus (Num 0) (Num 1)) (Num 1)) (Num 0)]
    disproves the general claim. *)
Example ai3c_counterexample :
  ~ ae_equiv (Plus (Minus (Num 0) (Num 1)) (Num 1)) (Num 0).
Proof. Admitted.

(** * Exercise 4 (Written): Why is [eval] Total?

_Ask Claude_ each of the following questions and write a prose
explanation (here, in a comment) covering all three.

#<ol>#
#<li>#"Why does [eval : AE -> nat] always succeed — why is its return
   type [nat] rather than [option nat]?"#</li>#
#<li>#"What change to the [AE] language would force [eval] to become
   partial, returning [option nat] instead?"#</li>#
#<li>#"AE uses Rocq's [nat] subtraction, which truncates at zero.  Is
   that a feature or a limitation?  When does the difference from
   integer subtraction matter?"#</li>#
#</ol>#

After reading Claude's answers, write your own explanation below.
There is no Rocq proof obligation for this exercise.
 *)

(**
STUDENT ANSWER (replace this text with your prose explanation):

(1) [eval] is total because ...

(2) A change that would make [eval] partial is ...

(3) Truncating subtraction is ...
 *)
