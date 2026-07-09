(**
Programming Languages in Rocq - TADS Solutions
Complete solutions to plih_ds_exercises.v

Do not read this file until you have made a genuine attempt at each
exercise.
 *)

From Stdlib Require Import String.
From Stdlib Require Import Lia.
Require Import plih_rocq_ds_shared.
Require Import plih_ds_lecture.

Local Open Scope string_scope.

(** * PART 1: RUNNING THE TYPE CHECKER *)

Example ex1_ty_num : typecheck (Num 42) = Some TNum.
Proof. reflexivity. Qed.

Example ex2_ty_pair :
  typecheck (Pair (Num 5) (Boolean true)) = Some (TProd TNum TBool).
Proof. reflexivity. Qed.

Example ex3_ty_fst :
  typecheck (Fst (Pair (Num 1) (Boolean false))) = Some TNum.
Proof. reflexivity. Qed.

Example ex4_ty_nil_bool :
  typecheck (Nil TBool) = Some (TList TBool).
Proof. reflexivity. Qed.

Example ex5_ty_cons :
  typecheck (Cons (Num 3) (Cons (Num 4) (Nil TNum))) = Some (TList TNum).
Proof. reflexivity. Qed.

Example ex6_ty_isnil :
  typecheck (IsNil (Nil TNum)) = Some TBool.
Proof. reflexivity. Qed.

Example ex7_ty_inl :
  typecheck (InL (TSum TNum TBool) (Num 7)) = Some (TSum TNum TBool).
Proof. reflexivity. Qed.

Example ex7b_ty_unit :
  typecheck Unit = Some TUnit.
Proof. reflexivity. Qed.

(** * PART 2: RUNNING THE EVALUATOR *)

Example ex8_eval_pair :
  eval (Pair (Num 10) (Num 20)) = Some (PairV (NumV 10) (NumV 20)).
Proof. reflexivity. Qed.

Example ex9_eval_fst :
  eval (Fst (Pair (Num 3) (Boolean true))) = Some (NumV 3).
Proof. reflexivity. Qed.

Example ex10_eval_snd :
  eval (Snd (Pair (Boolean false) (Num 99))) = Some (NumV 99).
Proof. reflexivity. Qed.

Example ex11_eval_isnil_cons :
  eval (IsNil (Cons (Num 1) (Nil TNum))) = Some (BoolV false).
Proof. reflexivity. Qed.

Example ex12_eval_car :
  eval (Car (Cons (Num 5) (Cons (Num 6) (Nil TNum)))) = Some (NumV 5).
Proof. reflexivity. Qed.

Example ex13_eval_cdr :
  eval (Cdr (Cons (Num 1) (Cons (Num 2) (Nil TNum)))) =
  Some (InRV (PairV (NumV 2) (InLV UnitV))).
Proof. reflexivity. Qed.

Example ex14_eval_inl :
  eval (InL (TSum TNum TBool) (Num 42)) = Some (InLV (NumV 42)).
Proof. reflexivity. Qed.

Example ex15_eval_inr :
  eval (InR (TSum TNum TBool) (Boolean true)) = Some (InRV (BoolV true)).
Proof. reflexivity. Qed.

(** * PART 3: TYPING JUDGEMENTS *)

Example ex16_ty_snd :
  typecheck (Snd (Pair (Boolean true) (Num 8))) = Some TNum.
Proof. reflexivity. Qed.

Example ex17_ty_car_bool :
  typecheck (Car (Cons (Boolean true) (Nil TBool))) = Some TBool.
Proof. reflexivity. Qed.

Example ex18_ill_car_num :
  typecheck (Car (Num 5)) = None.
Proof. reflexivity. Qed.

Example ex19_ill_cons_mismatch :
  typecheck (Cons (Boolean true) (Nil TNum)) = None.
Proof. reflexivity. Qed.

Example ex20_ty_scase :
  typecheck
    (SCase (InL (TSum TNum TBool) (Num 5))
           "n" (Id "n")
           "b" (Num 0))
  = Some TNum.
Proof. reflexivity. Qed.

Example ex21_ill_scase_mismatch :
  typecheck
    (SCase (InL (TSum TNum TBool) (Num 5))
           "n" (Id "n")
           "b" (Boolean false))
  = None.
Proof. reflexivity. Qed.

(** * PART 4: PRODUCTS *)

Definition tripleFirst : TADS :=
  Lambda "p" (TProd (TProd TNum TNum) TNum)
    (Fst (Fst (Id "p"))).

Example ex22_ty_tripleFirst :
  typecheck tripleFirst = Some (TArr (TProd (TProd TNum TNum) TNum) TNum).
Proof. reflexivity. Qed.

Example ex23_run_tripleFirst :
  eval (App tripleFirst (Pair (Pair (Num 7) (Num 8)) (Num 9)))
  = Some (NumV 7).
Proof. reflexivity. Qed.

Example ex24_ty_swap :
  typecheck
    (Lambda "p" (TProd TNum TBool)
       (Pair (Snd (Id "p")) (Fst (Id "p"))))
  = Some (TArr (TProd TNum TBool) (TProd TBool TNum)).
Proof. reflexivity. Qed.

(** * PART 5: SUMS *)

Definition safeHead : TADS :=
  Lambda "xs" (TList TNum)
    (If (IsNil (Id "xs"))
        (InR (TSum TNum TBool) (Boolean true))
        (InL (TSum TNum TBool) (Car (Id "xs")))).

Example ex25_ty_safeHead :
  typecheck safeHead = Some (TArr (TList TNum) (TSum TNum TBool)).
Proof. reflexivity. Qed.

Example ex26_run_safeHead_cons :
  eval (App safeHead (Cons (Num 42) (Nil TNum)))
  = Some (InLV (NumV 42)).
Proof. reflexivity. Qed.

Example ex27_run_safeHead_nil :
  eval (App safeHead (Nil TNum))
  = Some (InRV (BoolV true)).
Proof. reflexivity. Qed.

(** * PART 6: LISTS *)

Definition doubleGen : TADS :=
  Lambda "g" (TArr (TList TNum) (TList TNum))
    (Lambda "xs" (TList TNum)
      (If (IsNil (Id "xs"))
          (Nil TNum)
          (Cons (Mult (Car (Id "xs")) (Num 2))
                (App (Id "g") (Cdr (Id "xs")))))).

Definition doubleList : TADS := Fix doubleGen.

Example ex28_ty_doubleList :
  typecheck doubleList = Some (TArr (TList TNum) (TList TNum)).
Proof. reflexivity. Qed.

Example ex29_run_doubleList :
  eval (App doubleList list123) =
  Some (InRV (PairV (NumV 2)
       (InRV (PairV (NumV 4)
       (InRV (PairV (NumV 6) (InLV UnitV))))))).
Proof. reflexivity. Qed.

Example ex30_run_sumList :
  eval (App sumList list123) = Some (NumV 6).
Proof. reflexivity. Qed.

(** * PART 7: LISTS AS SUMS OF PRODUCTS *)

Example ex31_nil_rep :
  eval (Nil TNum) = Some (InLV UnitV).
Proof. reflexivity. Qed.

Example ex32_cons_rep :
  eval (Cons (Num 7) (Nil TNum)) =
  Some (InRV (PairV (NumV 7) (InLV UnitV))).
Proof. reflexivity. Qed.

Example ex33_scase_on_nil :
  eval (SCase (Nil TNum) "u" (Num 0) "p" (Fst (Id "p"))) =
  Some (NumV 0).
Proof. reflexivity. Qed.

Example ex34_scase_on_cons :
  eval (SCase (Cons (Num 99) (Nil TNum))
              "u" (Num 0)
              "p" (Fst (Id "p"))) =
  Some (NumV 99).
Proof. reflexivity. Qed.

(** * PART 8: INDUCTIONS *)

Lemma ex35_Ty_eqb_refl : forall t, Ty_eqb t t = true.
Proof.
  intros t.
  induction t as [| | d IHd r IHr | | a1 IH1 b1 IH2 | a1 IH1 b1 IH2 | t IH];
    simpl; try reflexivity.
  - rewrite IHd, IHr. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma ex36_mono_pair : forall k env e1 e2 v,
  evalM (S k) env (Pair e1 e2) = Some v ->
  evalM (S (S k)) env (Pair e1 e2) = Some v.
Proof.
  intros k env e1 e2 v H.
  apply (evalM_mono (S k) (S (S k)) env (Pair e1 e2) v).
  - lia.
  - exact H.
Qed.
