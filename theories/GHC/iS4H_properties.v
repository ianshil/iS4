Require Import List.
Require Import ListDec.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import general_export.

Require Import iS4_Syntax.
Require Import iS4H.
Require Import iS4H_logic.

Lemma Thm_irrel : forall A B Γ , iS4H_rules (Γ , A -->  (B -->  A)).
Proof.
intros A B Γ. apply Ax. apply AxRule_I. left ; apply IA1_I. exists A ; exists B ; auto.
Qed.

Lemma imp_Id_gen : forall A Γ , iS4H_rules (Γ , A -->  A).
Proof.
intros.
eapply MP with ([(_,(A --> (Top --> (Bot --> Top))) --> (A --> A));(_,(A --> (Top --> (Bot --> Top))))]).
2: apply MPRule_I. intros ; inversion H ; subst.
eapply MP with ([(_,(A --> ((Top --> (Bot --> Top)) --> A)) --> ((A --> (Top --> (Bot --> Top))) --> (A --> A)));(_,A --> ((Top --> (Bot --> Top)) --> A))]).
2: apply MPRule_I. intros ; inversion H0 ; subst.
apply Ax. apply AxRule_I. left. apply IA2_I. exists A. exists (Top --> ⊥ --> Top). exists A ; auto.
inversion H1 ; subst. 2: inversion H2.
apply Ax. apply AxRule_I. left. apply IA1_I. exists A. exists (Top --> ⊥ --> Top). auto.
inversion H0 ; subst. 2: inversion H1.
eapply MP with ([(_,(Top --> ⊥ --> Top) --> (A --> Top --> ⊥ --> Top));(_,Top --> ⊥ --> Top)]).
2: apply MPRule_I. intros ; inversion H1 ; subst.
apply Ax. apply AxRule_I. left. apply IA1_I. exists (Top --> ⊥ --> Top). exists A. auto.
inversion H2 ; subst. 2: inversion H3.
apply Ax. apply AxRule_I. left. apply IA1_I. exists Top. exists Bot. auto.
Qed.

Lemma comm_And_obj : forall A B Γ ,
    (iS4H_rules (Γ , And A B -->  And B A)).
Proof.
intros A B Γ .
apply MP with (ps:=[(Γ , (And A B -->  A) -->  (And A B -->  And B A));(Γ , (And A B -->  A))]).
2: apply MPRule_I. intros. inversion H. subst. 
apply MP with (ps:=[(Γ , (And A B -->  B) -->  (And A B -->  A) -->  (And A B -->  And B A));(Γ , (And A B -->  B))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. left. apply IA8_I. exists (And A B). exists B. exists A.
auto. inversion H1. subst.
apply Ax. apply AxRule_I. left. apply IA7_I. exists A. exists B. auto. inversion H2.
inversion H0. subst. apply Ax. apply AxRule_I. left. apply IA6_I. exists A. exists B. auto.
inversion H1.
Qed.

Lemma comm_Or_obj : forall A B Γ , (iS4H_rules (Γ , Or A B -->  Or B A)).
Proof.
intros A B Γ .
apply MP with (ps:=[(Γ , (B -->  Or B A) -->  (Or A B -->  Or B A));(Γ , (B -->  Or B A))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ , (A -->  Or B A) -->  (B -->  Or B A) -->  (Or A B -->  Or B A));(Γ , (A -->  Or B A))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. left. apply IA5_I. exists A. exists B. exists (Or B A).
auto. inversion H1. subst.
apply Ax. apply AxRule_I. left. apply IA4_I. exists B. exists A. auto.
inversion H2. inversion H0. subst.
apply Ax. apply AxRule_I. left. apply IA3_I. exists B. exists A. auto.
inversion H1.
Qed.

Lemma comm_Or : forall A B Γ , (iS4H_rules (Γ , Or A B)) -> (iS4H_rules (Γ , Or B A)).
Proof.
intros A B Γ  D.
apply MP with (ps:=[(Γ , Or A B -->  Or B A);(Γ , Or A B)]).
2: apply MPRule_I. intros. inversion H. subst. apply comm_Or_obj.
inversion H0. subst. assumption. inversion H1.
Qed.

Lemma EFQ : forall A Γ , iS4H_rules (Γ , (Bot) -->  A).
Proof.
intros A Γ. apply Ax. apply AxRule_I. left. apply IA9_I ; eexists ; auto.
Qed.

Lemma Imp_trans_help7 : forall x y z Γ, iS4H_rules (Γ , (x --> (y --> (z --> y)))).
Proof.
intros.
eapply  MP with (ps:=[(_, ((y --> (z --> y))) --> (x --> (y --> (z --> y))));(_, (y --> (z --> y)))]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
all: apply Ax ; apply AxRule_I ; left ; apply IA1_I ; eexists ; eexists ; unfold IA1 ; auto.
Qed.

Lemma Imp_trans_help8 : forall x y z Γ,
  iS4H_rules (Γ , (((x --> (y --> z)) --> (x --> y)) --> ((x --> (y --> z)) --> (x --> z)))).
Proof.
intros.
eapply  MP with (ps:=[(_, ((x --> (y --> z)) --> ((x --> y) --> (x --> z))) --> (((x --> (y --> z)) --> (x --> y)) --> ((x --> (y --> z)) --> (x --> z))));
(_, ((x --> (y --> z)) --> ((x --> y) --> (x --> z))))]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
all: apply Ax ; apply AxRule_I ; left ; apply IA2_I ; eexists ; eexists ; eexists ; unfold IA2 ; auto.
Qed.

Lemma Imp_trans_help9 : forall x y z u Γ,
  iS4H_rules (Γ , (x --> ((y --> (z --> u)) --> ((y --> z) --> (y --> u))))).
Proof.
intros.
eapply  MP with (ps:=[(_, ((y --> (z --> u)) --> ((y --> z) --> (y --> u))) --> (x --> ((y --> (z --> u)) --> ((y --> z) --> (y --> u)))));
(_, ((y --> (z --> u)) --> ((y --> z) --> (y --> u))))]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
all: apply Ax ; apply AxRule_I ; left.
apply IA1_I. eexists ; eexists ; unfold IA1 ; auto.
apply IA2_I. eexists ; eexists ; eexists ; unfold IA2 ; auto.
Qed.

Lemma Imp_trans_help14 : forall x y z u Γ,
  iS4H_rules (Γ , (x --> (y --> (z --> (u --> z))))).
Proof.
intros.
eapply  MP with (ps:=[(_, (y --> (z --> (u --> z))) --> (x --> (y --> (z --> (u --> z)))));
(_, (y --> (z --> (u --> z))))]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
apply Ax ; apply AxRule_I ; left. apply IA1_I. eexists ; eexists ; unfold IA1 ; auto.
apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help35 : forall x y z Γ, iS4H_rules (Γ , (x --> ((y --> x) --> z)) --> (x --> z)).
Proof.
intros.
eapply  MP with (ps:=[(_, _ --> (x --> ((y --> x) --> z)) --> (x --> z));
(_, _)]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
apply Imp_trans_help8.
apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help37 : forall x y z u Γ, iS4H_rules (Γ , ((x --> ((y --> (z --> y)) --> u)) --> (x --> u))).
Proof.
intros.
eapply  MP with (ps:=[(_, _ --> ((x --> ((y --> (z --> y)) --> u)) --> (x --> u)));
(_, _)]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
apply Imp_trans_help8.
apply Imp_trans_help14.
Qed.

Lemma Imp_trans_help54 : forall x y z u Γ,
  iS4H_rules (Γ , (((x --> (y --> z)) --> (((x --> y) --> (x --> z)) --> u)) --> ((x --> (y --> z)) --> u))).
Proof.
intros.
eapply  MP with (ps:=[(_, _ --> _);(_, _)]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
apply Imp_trans_help8.
apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help170 : forall x y z Γ, iS4H_rules (Γ , (x --> y) --> ((z --> x) --> (z --> y))).
Proof.
intros.
eapply  MP with (ps:=[(_, ((x --> y) --> ((z --> (x --> y)) --> ((z --> x) --> (z --> y)))) --> ((x --> y) --> ((z --> x) --> (z --> y))));
(_, ((x --> y) --> ((z --> (x --> y)) --> ((z --> x) --> (z --> y)))))]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
apply Imp_trans_help35.
apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help410 : forall x y z Γ,
  iS4H_rules (Γ , (((x --> y) --> z) --> (y --> z))).
Proof.
intros.
eapply  MP with (ps:=[(_, _ --> _);(_, _)]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
apply Imp_trans_help37.
apply Imp_trans_help170.
Qed.

Lemma Imp_trans_help427 : forall x y z u Γ,
  iS4H_rules (Γ , (x --> (((y --> z) --> u) --> (z --> u)))).
Proof.
intros.
eapply  MP with (ps:=[(_, _ --> _);(_, _)]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1.
2: apply Imp_trans_help410.
apply Ax ; apply AxRule_I ; left. apply IA1_I. eexists ; eexists ; unfold IA1 ; auto.
Qed.

Lemma Imp_trans : forall A B C Γ, iS4H_rules (Γ , (A --> B) -->  (B --> C) --> (A --> C)).
Proof.
intros.
eapply  MP with (ps:=[(_, _ --> _);(_, _)]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1. all: clear H.
eapply  MP with (ps:=[(_, _ --> _);(_, _)]).
2: apply MPRule_I. intros. inversion H ; subst. 2: inversion H0 ; subst. 3: inversion H1. 1,2: clear H.
apply Imp_trans_help54.
apply Imp_trans_help427.
apply Imp_trans_help170.
Qed.

Lemma monotR_Or : forall A B Γ ,
    (iS4H_rules (Γ , A -->  B)) ->
    (forall C, iS4H_rules (Γ , (Or A C) -->  (Or B C))).
Proof.
intros A B Γ  D C.
apply MP with (ps:=[(Γ , (C -->  Or B C) -->  (Or A C -->  Or B C));(Γ ,(C -->  Or B C))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ , (A -->  Or B C) -->  (C -->  Or B C) -->  (Or A C -->  Or B C));(Γ ,(A -->  Or B C))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. left. apply IA5_I. exists A. exists C.
exists (Or B C). auto. inversion H1. subst.
apply MP with (ps:=[(Γ , (B -->  Or B C) -->  (A -->  Or B C));(Γ ,((B -->  Or B C)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ , (A -->  B) -->  (B -->  Or B C) -->  (A -->  Or B C));(Γ ,(A -->  B))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Imp_trans.
inversion H4. subst. assumption. inversion H5. inversion H3. subst. apply Ax.
apply AxRule_I. left. apply IA3_I. exists B. exists C.
auto. inversion H4. inversion H2. inversion H0. subst. apply Ax. apply AxRule_I. left. apply IA4_I.
exists B. exists C. auto. inversion H1.
Qed.

Lemma monotL_Or : forall A B Γ,
    (iS4H_rules (Γ, A -->  B)) ->
    (forall C, iS4H_rules (Γ, (Or C A) -->  (Or C B))).
Proof.
intros A B Γ  D C.
apply MP with (ps:=[(Γ , (A -->  Or C B) -->  ((Or C A) -->  (Or C B)));(Γ ,(A -->  Or C B))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ , (C -->  Or C B) -->  (A -->  Or C B) -->  ((Or C A) -->  (Or C B)));(Γ ,(C -->  Or C B))]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. left. apply IA5_I. exists C. exists A.
exists (Or C B). auto. inversion H1. subst. apply Ax.
apply AxRule_I. left. apply IA3_I. exists C. exists B.
auto. inversion H2. inversion H0. subst.
apply MP with (ps:=[(Γ , (B -->  Or C B) -->  (A -->  Or C B));(Γ ,((B -->  Or C B)))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply MP with (ps:=[(Γ , (A -->  B) -->  (B -->  Or C B) -->  (A -->  Or C B));(Γ ,(A -->  B))]).
2: apply MPRule_I. intros. inversion H2. subst. apply Imp_trans.
inversion H3. subst.
assumption. inversion H4. inversion H2. subst. apply Ax.
apply AxRule_I. left. apply IA4_I. exists C. exists B.
auto. inversion H3. inversion H1.
Qed.

Lemma monot_Or2 : forall A B Γ , (iS4H_rules (Γ , A -->  B)) ->
    (forall C, iS4H_rules (Γ , (Or A C) -->  (Or C B))).
Proof.
intros A B Γ  D C.
apply MP with (ps:=[(Γ , (C -->  Or C B) -->  (Or A C -->  Or C B));(Γ , C -->  Or C B)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ , (A -->  Or C B) -->  (C -->  Or C B) -->  (Or A C -->  Or C B));(Γ , A -->  Or C B)]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax.
apply AxRule_I. left. apply IA5_I. exists A. exists C. exists (Or C B). auto.
inversion H1. subst.
apply MP with (ps:=[(Γ , (B -->  Or C B) -->  (A -->  Or C B));(Γ , B -->  Or C B)]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ , (A -->  B) -->  (B -->  Or C B) -->  (A -->  Or C B));(Γ , A -->  B)]).
2: apply MPRule_I. intros. inversion H3. subst. apply Imp_trans.
inversion H4. subst. assumption. inversion H5. inversion H3. subst.
apply Ax. apply AxRule_I. left. apply IA4_I. exists C. exists B. auto. inversion H4.
inversion H2. inversion H0. subst. apply Ax. apply AxRule_I. left.
apply IA3_I. exists C. exists B. auto. inversion H1.
Qed.

Lemma prv_Top : forall Γ , iS4H_rules (Γ , Top).
Proof.
intros. apply imp_Id_gen.
Qed.

Lemma absorp_Or1 : forall A Γ ,
    (iS4H_rules (Γ , Or A (Bot))) ->
    (iS4H_rules (Γ , A)).
Proof.
intros A Γ  D.
apply MP with (ps:=[(Γ , Imp (Or A (Bot)) A);(Γ , Or A (Bot))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ , (Bot -->  A) -->  (Or A (Bot) -->  A));(Γ , (Bot -->  A))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ , (A -->  A) -->  (Bot -->  A) -->  (Or A (Bot) -->  A));(Γ , A -->  A)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. left. apply IA5_I. exists A. exists (Bot).
exists A. auto. inversion H2. subst. apply imp_Id_gen. inversion H3.
inversion H1. subst. apply EFQ. inversion H2. inversion H0. subst.
assumption. inversion H1.
Qed.

Lemma Imp_And : forall A B C Γ, iS4H_rules (Γ , (A -->  (B -->  C)) --> ((And A B) -->  C)).
Proof.
intros A B C Γ.
eapply MP with ([(_, (((And A B) --> (B --> C)) --> ((And A B) -->  C)) --> (A -->  (B -->  C)) --> ((And A B) -->  C));(_,(((And A B) --> (B --> C)) --> ((And A B) -->  C)))]).
2: apply MPRule_I. intros. inversion H. subst.
eapply MP with ([(_, ((A --> (B --> C)) --> ((And A B) --> (B --> C))) --> (((A ∧ B) --> B --> C) --> (A ∧ B) --> C) --> (A --> B --> C) --> (A ∧ B) --> C);
(_,(A --> (B --> C)) --> ((And A B) --> (B --> C)))]).
2: apply MPRule_I. intros. inversion H0 ; subst.
apply Imp_trans. inversion H1 ; subst. 2: inversion H2.
eapply MP with ([(_, ((A ∧ B) --> A) --> (A --> B --> C) --> (A ∧ B) --> B --> C); (_,(A ∧ B) --> A)]).
2: apply MPRule_I. intros. inversion H2 ; subst.
apply Imp_trans. inversion H3 ; subst. 2: inversion H4.
apply Ax. apply AxRule_I. left. apply IA6_I. exists A. exists B. auto.
inversion H0 ; subst. 2: inversion H1 ; subst.
eapply MP with ([(_, (((A ∧ B) --> (B --> C)) --> ((A ∧ B) --> B)) --> ((A ∧ B) --> B --> C) --> (A ∧ B) --> C); (_,((A ∧ B) --> (B --> C)) --> ((A ∧ B) --> B))]).
2: apply MPRule_I. intros. inversion H1 ; subst.
eapply MP with ([(_, (((A ∧ B) --> (B --> C)) --> (((A ∧ B) --> B) --> ((A ∧ B) --> C))) --> ((((A ∧ B) --> (B --> C)) --> ((A ∧ B) --> B)) --> ((A ∧ B) --> B --> C) --> (A ∧ B) --> C));
(_,((A ∧ B) --> (B --> C)) --> (((A ∧ B) --> B) --> ((A ∧ B) --> C)))]).
2: apply MPRule_I. intros. inversion H2 ; subst.
apply Ax. apply AxRule_I. left. apply IA2_I. exists ((A ∧ B) --> B --> C). exists ((A ∧ B) --> B). exists ((A ∧ B) --> C). auto.
inversion H3 ; subst. 2: inversion H4.
apply Ax. apply AxRule_I. left. apply IA2_I. exists (A ∧ B). exists B. exists C. auto.
inversion H2 ; subst. 2: inversion H3.
eapply MP with ([(_, ((A ∧ B) --> B) --> (((A ∧ B) --> B --> C) --> (A ∧ B) --> B));(_,(A ∧ B) --> B)]).
2: apply MPRule_I. intros. inversion H3 ; subst.
apply Ax. apply AxRule_I. left. apply IA1_I. exists ((A ∧ B) --> B). exists ((A ∧ B) --> B --> C). auto.
inversion H4 ; subst. 2: inversion H5. apply Ax. apply AxRule_I. left. apply IA7_I. exists A ; exists B ; auto.
Qed.

Lemma Contr_Bot : forall A Γ , iS4H_rules (Γ , And A (Neg A) -->  (Bot)).
Proof.
intros A Γ .
apply MP with (ps:=[(Γ , (And (Neg A) A -->  Bot) -->  (And A (Neg A) -->  Bot));(Γ , And (Neg A) A -->  Bot)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ , (And A (Neg A) -->  And (Neg A) A) -->  (And (Neg A) A -->  Bot) -->  (And A (Neg A) -->  Bot));(Γ , And A (Neg A) -->  And (Neg A) A)]).
2: apply MPRule_I. intros. inversion H0. subst. apply Imp_trans.
inversion H1. subst. apply comm_And_obj. inversion H2. inversion H0. subst.
apply MP with (ps:=[(Γ , ((Neg A) -->  A -->  Bot) -->  (And (Neg A) A  -->  Bot));(Γ , ((Neg A) -->  A -->  Bot))]).
2: apply MPRule_I. intros. inversion H1. subst.
2: inversion H2 ; subst. 3: inversion H3. 3: inversion H1.
2: apply imp_Id_gen. apply Imp_And.
Qed.

Theorem iS4H_Detachment_Theorem : forall A B Γ,
           (iS4H_rules (Γ, A --> B)) ->
                          iS4H_rules  (Union _ Γ  (Singleton _ (A)), B).
Proof.
intros A B Γ D.
apply MP with (ps:=[(Union _ Γ (Singleton _ A), Imp A B);(Union _ Γ (Singleton _ A), A)]).
2: apply MPRule_I.
intros. inversion H ; subst.
pose (iS4H_monot (Γ, A --> B)). simpl in i. apply i ; auto.
intros C HC. apply Union_introl; auto. inversion H0 ; subst.
apply Id. apply IdRule_I. apply Union_intror. apply In_singleton.
inversion H1.
Qed.

Theorem iS4H_Deduction_Theorem : forall s,
           (iS4H_rules s) ->
           (forall A B Γ , (fst s = Union _ Γ  (Singleton _ (A))) ->
                          (snd s = B) ->
                          iS4H_rules (Γ , A -->  B)).
Proof.
intros s D. induction D.
(* Id *)
- intros A B Γ  id1 id2. inversion H. subst. simpl in id1. subst. simpl. inversion H0.
  + subst. apply MP with (ps:=[(Γ , A0 -->  A -->  A0);(Γ , A0)]). 2: apply MPRule_I. intros. inversion H2. subst.
    apply Thm_irrel. inversion H3. subst. apply Id. apply IdRule_I. assumption.
    inversion H4.
  + subst. inversion H1. subst. apply imp_Id_gen.
(* Ax *)
- intros A B Γ  id1 id2. inversion H. subst. simpl in id1. subst. simpl.
  apply MP with (ps:=[(Γ , A0 -->  A -->  A0);(Γ , A0)]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply Thm_irrel. inversion H2. subst.
  apply Ax. apply AxRule_I. assumption. inversion H3.
(* MP *)
- intros A B Γ  id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: Union _ Γ  (Singleton _ A) = Union _ Γ  (Singleton _ A)). reflexivity.
  assert (J2: A0 -->  B0 = A0 -->  B0). reflexivity.
  assert (J20: List.In (Union (form) Γ  (Singleton (form) A), A0 -->  B0) [(Union (form) Γ  (Singleton (form) A), A0 -->  B0); (Union (form) Γ  (Singleton (form) A), A0)]).
  apply in_eq.
  pose (H0 (Union (form) Γ  (Singleton (form) A),  A0 -->  B0) J20
  A (Imp A0 B0) Γ  J1 J2).
  assert (J3: A0 = A0). reflexivity.
  apply MP with (ps:=[(Γ , (And A A0 -->  B0) -->  (A -->  B0));(Γ , And A A0 -->  B0)]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ , (A -->  And A A0) -->  (And A A0 -->  B0) -->  (A -->  B0));(Γ , A -->  And A A0)]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Imp_trans.
  inversion H4. subst. 2: inversion H5.
  apply MP with (ps:=[(Γ , (A -->  A0) -->  (A -->  And A A0));(Γ , A -->  A0)]).
  2: apply MPRule_I. intros. inversion H5. subst.
  apply MP with (ps:=[(Γ , (A -->  A) -->  (A -->  A0) -->  (A -->  And A A0));(Γ , A -->  A)]).
  2: apply MPRule_I. intros. inversion H6. subst. apply Ax.
  apply AxRule_I. left. apply IA8_I. exists A. exists A. exists A0. auto. inversion H7.
  subst. apply imp_Id_gen. inversion H8. inversion H6. subst. 2: inversion H7.
  assert (J30: List.In (Union (form) Γ  (Singleton (form) A), A0) [(Union (form) Γ  (Singleton (form) A), A0 -->  B0); (Union (form) Γ  (Singleton (form) A), A0)]).
  apply in_cons. apply in_eq. assert (J40: A0 = A0). reflexivity.
  pose (H0 (Union (form) Γ  (Singleton (form) A), A0) J30
  A A0 Γ  J1 J40). auto. inversion H3. subst.
  apply MP with (ps:=[(Γ , (A -->  A0 -->  B0) -->  (And A A0 -->  B0));(Γ , (A -->  A0 -->  B0))]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Imp_And.
  inversion H5. subst. assumption. inversion H6. inversion H4.
(* DNw *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: iS4H_prv (Empty_set _, Box A0)).
  apply Nec with (ps:=[(Empty_set _, A0)]). 2: apply NecRule_I. assumption.
  assert (J2: Included _ (fst (Empty_set _, Box A0)) Γ). intro. intro. inversion H2.
  pose (iS4H_monot (Empty_set _, Box A0) J1 Γ J2). simpl in i.
  apply MP with (ps:=[(Γ, (Box A0) --> A --> (Box A0)); (Γ, Box A0)]).
  2: apply MPRule_I. intros. inversion H2. subst. apply Thm_irrel.
  inversion H3. subst. 2: inversion H4. assumption.
Qed.

Lemma And_Imp : forall A B C Γ, iS4H_rules (Γ , ((And A B) -->  C) --> (A --> (B -->  C))).
Proof.
intros.
apply iS4H_Deduction_Theorem with (Union _ Γ (Singleton _ ((A ∧ B) --> C)), A --> B --> C) ; auto.
apply iS4H_Deduction_Theorem with (Union _ (Union _ Γ (Singleton _ ((A ∧ B) --> C))) (Singleton _ A), B --> C) ; auto.
apply iS4H_Deduction_Theorem with (Union _ (Union _ (Union _ Γ (Singleton _ ((A ∧ B) --> C))) (Singleton _ A)) (Singleton _ B), C) ; auto.
eapply MP with ([(_,(A ∧ B) --> C);(_,(A ∧ B))]).
2: apply MPRule_I. intros. inversion H ; subst.
apply Id. apply IdRule_I. apply Union_introl. apply Union_introl.
apply Union_intror. apply In_singleton.
inversion H0 ; subst. 2: inversion H1.
eapply MP with ([(_,Top --> (A ∧ B));(_, Top)]).
2: apply MPRule_I.
intros. inversion H1 ; subst.
eapply MP with ([(_,(Top --> B) --> (Top --> (A ∧ B)));(_, Top --> B)]).
2: apply MPRule_I. intros. inversion H2 ; subst.
eapply MP with ([(_,(Top --> A) --> (Top --> B) --> (Top --> (A ∧ B)));(_, Top --> A)]).
2: apply MPRule_I. intros. inversion H3 ; subst.
apply Ax. apply AxRule_I. left. apply IA8_I. exists Top. exists A. exists B. auto.
inversion H4 ; subst. 2: inversion H5.
apply iS4H_Deduction_Theorem with (Union _ (Union form (Union form
(Union form Γ (Singleton form ((A ∧ B) --> C))) (Singleton form A)) (Singleton form B)) (Singleton _ Top), A) ; auto.
apply Id. apply IdRule_I. apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
inversion H3 ; subst. 2: inversion H4.
apply iS4H_Deduction_Theorem with (Union _ (Union form (Union form
(Union form Γ (Singleton form ((A ∧ B) --> C))) (Singleton form A)) (Singleton form B)) (Singleton _ Top), B) ; auto.
apply Id. apply IdRule_I. apply Union_introl. apply Union_intror. apply In_singleton.
inversion H2 ; subst. 2: inversion H3.
apply prv_Top.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)

(* Some results about remove. *)

Lemma In_remove : forall (A : form) B (l : list (form)), List.In A (remove eq_dec_form B l) -> List.In A l.
Proof.
intros A B. induction l.
- simpl. auto.
- intro. simpl in H. destruct (eq_dec_form B a).
  * subst. apply in_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply in_eq.
    + subst. apply in_cons. apply IHl. auto.
Qed.

Lemma InT_remove : forall (A : form) B (l : list (form)), InT A (remove eq_dec_form B l) -> InT A l.
Proof.
intros A B. induction l.
- simpl. auto.
- intro. simpl in H. destruct (eq_dec_form B a).
  * subst. apply InT_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply InT_eq.
    + subst. apply InT_cons. apply IHl. auto.
Qed.

Lemma NoDup_remove : forall A (l : list (form)), NoDup l -> NoDup (remove eq_dec_form A l).
Proof.
intro A. induction l.
- intro. simpl. apply NoDup_nil.
- intro H. simpl. destruct (eq_dec_form A a).
  * subst. apply IHl. inversion H. assumption.
  * inversion H. subst. apply NoDup_cons. intro. apply H2. apply In_remove with (B:= A).
    assumption. apply IHl. assumption.
Qed.

(* To help for the Lindenbaum lemma. *)

Lemma Explosion : forall Γ A B,
  iS4H_prv (Γ, (B --> Bot) --> (B --> A)).
Proof.
intros.
apply iS4H_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ (B --> Bot)),  B --> A)) ; auto.
apply iS4H_Deduction_Theorem with (s:=(Union _ (Union _ Γ (Singleton _ (B --> Bot))) (Singleton _ B), A)) ; auto.
remember (Union form (Union form Γ (Singleton form (B --> Bot))) (Singleton form B)) as X.
apply MP with (ps:=[(X, Bot --> A);(X, Bot)]). 2: apply MPRule_I.
intros. inversion H. subst. apply Ax. apply AxRule_I. left. apply IA9_I. exists A ; auto.
inversion H0. 2: inversion H1. rewrite <- H1.
apply MP with (ps:=[(X, B --> Bot);(X, B)]). 2: apply MPRule_I.
intros. inversion H2. subst. apply Id. apply IdRule_I. apply Union_introl.
apply Union_intror. apply In_singleton. inversion H3. subst.
apply Id. apply IdRule_I. apply Union_intror. apply In_singleton. inversion H4.
Qed.

Lemma Imp_list_Imp : forall l Γ A B,
    iS4H_prv (Γ, list_Imp (A --> B) l) <->
    iS4H_prv (Γ, A --> list_Imp B l).
Proof.
induction l ; simpl ; intros.
- split ; intro ; auto.
- split ; intro.
  * apply iS4H_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ A), a --> list_Imp B l)) ; auto.
    apply iS4H_Deduction_Theorem with (s:=(Union _ (Union _ Γ (Singleton _ A)) (Singleton _ a), list_Imp B l)) ; auto.
    assert (Union form (Union form Γ (Singleton form A)) (Singleton form a) =
    Union form (Union form Γ (Singleton form a)) (Singleton form A)).
    apply Extensionality_Ensembles. split ; intro ; intros. inversion H0. subst.
    inversion H1. subst. apply Union_introl. apply Union_introl  ; auto. subst.
    inversion H2. subst. apply Union_intror. apply In_singleton. subst. apply Union_introl.
    apply Union_intror. auto. inversion H0. subst. inversion H1. subst. apply Union_introl.
    apply Union_introl. auto. subst. apply Union_intror. auto. subst.
    apply Union_introl. apply Union_intror. auto. rewrite H0.
    apply iS4H_Detachment_Theorem. apply IHl.
    apply iS4H_Detachment_Theorem. auto.
  * apply iS4H_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ a), list_Imp (A --> B) l)) ; auto.
    apply IHl.
    apply iS4H_Deduction_Theorem with (s:=(Union _ (Union _ Γ (Singleton _ a)) (Singleton _ A), list_Imp B l)) ; auto.
    assert (Union form (Union form Γ (Singleton form A)) (Singleton form a) =
    Union form (Union form Γ (Singleton form a)) (Singleton form A)).
    apply Extensionality_Ensembles. split ; intro ; intros. inversion H0. subst.
    inversion H1. subst. apply Union_introl. apply Union_introl  ; auto. subst.
    inversion H2. subst. apply Union_intror. apply In_singleton. subst. apply Union_introl.
    apply Union_intror. auto. inversion H0. subst. inversion H1. subst. apply Union_introl.
    apply Union_introl. auto. subst. apply Union_intror. auto. subst.
    apply Union_introl. apply Union_intror. auto. rewrite <- H0. clear H0.
    apply iS4H_Detachment_Theorem.
    apply iS4H_Detachment_Theorem. auto.
Qed.

Lemma iS4H_Imp_list_Detachment_Deduction_Theorem : forall l (Γ: Ensemble form) A,
    (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
    ((iS4H_prv (Γ, A)) <-> (iS4H_prv (Empty_set _, list_Imp A l))).
Proof.
induction l ; simpl ; intros.
- split ; intro.
  * assert (Γ = Empty_set form). apply Extensionality_Ensembles.
    split ; intro ; intros. apply H in H1. exfalso ; auto. inversion H1.
    rewrite H1 in H0 ; auto.
  * assert (Γ = Empty_set form). apply Extensionality_Ensembles.
    split ; intro ; intros. apply H in H1. exfalso ; auto. inversion H1.
    rewrite H1 ; auto.
- split ; intro.
  * assert (decidable_eq form). unfold decidable_eq. intros.
    destruct (eq_dec_form x y). subst. unfold Decidable.decidable. auto.
    unfold Decidable.decidable. auto.
    pose (In_decidable H1 a l). destruct d.
    + assert (J0: forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)).
       intros. split ; intro. pose (H B). destruct p. apply o in H3. destruct H3.
       subst. auto. auto. apply H. auto.
       pose (IHl Γ A J0). apply i in H0.
       apply MP with (ps:=[(Empty_set form, (list_Imp A l) --> (a --> list_Imp A l));
       (Empty_set form, list_Imp A l)]).
       2: apply MPRule_I. intros. inversion H3. subst.
       apply Thm_irrel. inversion H4. subst. 2: inversion H5. auto.
    + assert (J0: forall B : form,
       ((fun y : form => In form Γ y /\ y <> a) B -> List.In B l) *
       (List.In B l -> (fun y : form => In form Γ y /\ y <> a) B)).
       intros. split ; intro. destruct H3. pose (H B). destruct p.
       apply o in H3. destruct H3 ; subst. exfalso. apply H4 ; auto.
       auto. split ; auto. apply H ; auto. intro. subst. auto.
       pose (IHl (fun y => (In _ Γ y) /\ (y <> a)) (a --> A) J0).
       destruct i. apply Imp_list_Imp. apply H3.
       apply iS4H_Deduction_Theorem with (s:=(Γ, A)) ; simpl ; auto.
       apply Extensionality_Ensembles. split ; intro ; intros. unfold In.
       destruct (eq_dec_form a x). subst. apply Union_intror. apply In_singleton.
       apply Union_introl. unfold In. split ; auto. inversion H5. subst.
       inversion H6. auto. subst. inversion H6. subst. apply H. auto.
  * assert (decidable_eq form). unfold decidable_eq. intros.
    destruct (eq_dec_form x y). subst. unfold Decidable.decidable. auto.
    unfold Decidable.decidable. auto.
    pose (In_decidable H1 a l). destruct d.
    + assert (J0: forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)).
       intros. split ; intro. pose (H B). destruct p. apply o in H3. destruct H3.
       subst. auto. auto. apply H. auto.
       apply Imp_list_Imp in H0.
       pose (IHl Γ (a --> A)).
       apply MP with (ps:=[(Γ, a --> A);(Γ, a)]).
       2: apply MPRule_I. intros. inversion H3. subst. apply i. intros.
       split ; intros. pose (H B). destruct p. apply o in H4. destruct H4 ; subst.
       auto. auto. apply H. auto. auto. inversion H4 ; subst.
       apply Id. apply IdRule_I. apply H. auto. inversion H5.
    + assert (J0: forall B : form,
       ((fun y : form => In form Γ y /\ y <> a) B -> List.In B l) *
       (List.In B l -> (fun y : form => In form Γ y /\ y <> a) B)).
       intros. split ; intro. destruct H3. pose (H B). destruct p.
       apply o in H3. destruct H3 ; subst. exfalso. apply H4 ; auto.
       auto. split ; auto. apply H ; auto. intro. subst. auto.
       pose (IHl (fun y => (In _ Γ y) /\ (y <> a)) (a --> A) J0).
       destruct i. apply Imp_list_Imp in H0. apply H4 in H0.
       apply iS4H_Detachment_Theorem in H0.
       assert (Γ = Union form (fun y : form => In form Γ y /\ y <> a)
       (Singleton form a)).
       apply Extensionality_Ensembles. split ; intro ; intros. unfold In.
       destruct (eq_dec_form a x). subst. apply Union_intror. apply In_singleton.
       apply Union_introl. unfold In. split ; auto. inversion H5. subst.
       inversion H6. auto. subst. inversion H6. subst. apply H. auto.
       rewrite H5. auto.
Qed.

Lemma K_list_Imp : forall l Γ A,
iS4H_rules (Γ, Box (list_Imp A l) --> list_Imp (Box A) (Box_list l)).
Proof.
induction l ; simpl ; intros.
- apply imp_Id_gen.
- apply iS4H_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ (Box (a --> list_Imp A l))),  Box a --> list_Imp (Box A) (Box_list l))) ; auto.
  apply iS4H_Deduction_Theorem with (s:=(Union _ (Union _ Γ (Singleton _ (Box (a --> list_Imp A l)))) (Singleton _ (Box a)),  list_Imp (Box A) (Box_list l))) ; auto.
  remember (Union form (Union form Γ (Singleton form (Box (a --> list_Imp A l)))) (Singleton form (Box a))) as X.
  apply MP with (ps:=[(X, Box (list_Imp A l) --> list_Imp (Box A) (Box_list l));(X,Box (list_Imp A l))]).
  2: apply MPRule_I. intros. inversion H. rewrite <- H0. auto.
  inversion H0. 2: inversion H1. rewrite <- H1.
  apply MP with (ps:=[(X, Box a --> Box (list_Imp A l));(X, Box a)]).
  2: apply MPRule_I. intros. inversion H2. rewrite <- H3.
  apply MP with (ps:=[(X, Box (a --> list_Imp A l) --> (Box a --> Box (list_Imp A l)));(X, Box (a --> list_Imp A l))]).
  2: apply MPRule_I. intros. inversion H4. rewrite <- H5. apply Ax.
  apply AxRule_I. right. apply MAK_I. exists a. exists (list_Imp A l). auto.
  inversion H5. subst. apply Id. apply IdRule_I. apply Union_introl.
  apply Union_intror. apply In_singleton. inversion H6.
  inversion H3. subst. apply Id. apply IdRule_I. apply Union_intror.
  apply In_singleton. inversion H4.
Qed.

Lemma Box_distrib_list_Imp : forall l A,
    iS4H_prv (Empty_set form, list_Imp A l) ->
    iS4H_prv (Empty_set form, list_Imp (Box A) (Box_list l)).
Proof.
induction l ; simpl ; intros.
- apply Nec with (ps:=[(Empty_set form, A)]).
  2: apply NecRule_I. intros. inversion H0 ; subst ; auto.
  inversion H1.
- apply MP with (ps:=[(Empty_set form, (Box (list_Imp A l) --> list_Imp (Box A) (Box_list l)) --> (Box a --> list_Imp (Box A) (Box_list l)));
  (Empty_set form, Box (list_Imp A l) --> list_Imp (Box A) (Box_list l))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Empty_set form, (Box a --> Box (list_Imp A l)) --> ((Box (list_Imp A l) --> list_Imp (Box A) (Box_list l)) --> (Box a --> list_Imp (Box A) (Box_list l))));
  (Empty_set form, Box a --> Box (list_Imp A l))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Imp_trans.
  inversion H2 ; subst. 2: inversion H3.
  apply MP with (ps:=[(Empty_set form, Box (a --> (list_Imp A l)) --> (Box a --> Box (list_Imp A l)));
  (Empty_set form, Box (a --> (list_Imp A l)))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply Ax. apply AxRule_I. right. apply MAK_I. exists a. exists (list_Imp A l).
  auto. inversion H4. subst. 2: inversion H5.
  apply Nec with (ps:=[(Empty_set form, a --> list_Imp A l)]).
  2: apply NecRule_I. intros. inversion H5 ; subst. 2: inversion H6.
  auto. inversion H1 ; subst. 2: inversion H2. apply K_list_Imp.
Qed.

Lemma In_list_In_Box_list : forall l A,
    List.In A l -> List.In (Box A) (Box_list l).
Proof.
induction l ; intros ; simpl.
- inversion H.
- inversion H ;  subst ; auto.
Qed.

Lemma In_Box_list_In_list : forall l A,
     List.In A (Box_list l) -> (exists B, List.In B l /\ A = Box B).
Proof.
induction l ; simpl ; intros.
- inversion H.
- destruct H ; subst. exists a. split ; auto. apply IHl in H.
  destruct H. destruct H. subst. exists x ; auto.
Qed.

Lemma K_rule : forall Γ A, iS4H_prv (Γ, A) ->
    iS4H_prv ((fun x => (exists B, In _ Γ B /\ x = Box B)), Box A).
Proof.
intros. apply iS4H_finite in H. simpl in H. destruct H. destruct H. destruct p.
destruct e.
pose (iS4H_monot (fun x1 : form => exists B : form, List.In B x0 /\ x1 = Box B, Box A)).
apply i1 ; simpl ; auto. clear i1.
pose (iS4H_Imp_list_Detachment_Deduction_Theorem x0 x A H).
apply i1 in i0. clear i1.
apply Box_distrib_list_Imp in i0.
remember (fun y => exists B : form, List.In B x0 /\ y = Box B) as Boxed_x.
pose (iS4H_Imp_list_Detachment_Deduction_Theorem (Box_list x0) Boxed_x  (Box A)).
apply i1 in i0 ; auto. intros. split ; intro. subst. destruct H1. destruct H1. subst.
simpl. apply In_list_In_Box_list ; auto. subst. apply In_Box_list_In_list in H1.
auto. intro. intros. inversion H0. destruct H1. subst. unfold In.
exists x2 ; split ; auto. apply i. apply H ; auto.
Qed.

Lemma Box_BoxTwo_prv : forall Γ A, iS4H_prv (Γ, Box A) ->
    iS4H_prv (Γ, BoxTwo A).
Proof.
intros. destruct A ; simpl in *.
1-5: eapply MP with (ps:=[(Γ, (Box _) --> Box (Box _));(Γ, Box _)]) ; 
       [ intros prem H0 ; inversion H0 ; [ subst ; apply Ax ; apply AxRule_I ; 
        right ; apply MA4_I ; eexists _ ; unfold MA4 ; auto |
        inversion H1 ; [ subst ; apply H | inversion H2] ] | apply MPRule_I].
destruct A ; simpl in * ; auto.
apply MP with (ps:=[(Γ, Box (Box (Box A)) --> Box (Box A));(Γ, Box (Box (Box A)))]).
2: apply MPRule_I. intros. inversion H0 ; subst. 2: inversion H1 ; [subst ; auto |  inversion H2].
apply Ax. apply AxRule_I. right. apply MAT_I. exists (Box (Box A)) ; auto.
Qed.

Lemma BoxTwo_Box_prv : forall Γ A, iS4H_prv (Γ, BoxTwo A) ->
    iS4H_prv (Γ, Box A).
Proof.
intros. destruct A ; simpl in *.
1-5: eapply MP with (ps:=[(Γ, Box (Box _) --> (Box _));(Γ, Box (Box _))]) ; 
       [ intros prem H0 ; inversion H0 ; [ subst ; apply Ax ; apply AxRule_I ; 
        right ; apply MAT_I ; eexists _ ; unfold MAT ; auto |
        inversion H1 ; [ subst ; apply H | inversion H2] ] | apply MPRule_I].
destruct A ; simpl in * ; auto.
apply MP with (ps:=[(Γ, Box (Box A) --> Box (Box (Box A)));(Γ, Box (Box A))]).
2: apply MPRule_I. intros. inversion H0 ; subst. 2: inversion H1 ; [subst ; auto |  inversion H2].
apply Ax. apply AxRule_I. right. apply MA4_I. exists (Box A) ; auto.
Qed.

Lemma UnBox_BoxTwo_Box_prv : forall Γ A, iS4H_prv (Γ, UnBox (BoxTwo A)) ->
    iS4H_prv (Γ, Box A).
Proof.
intros. destruct A ; simpl in * ; auto.
destruct A ; simpl in * ; auto.
1-5: eapply MP with (ps:=[(Γ, (Box _) --> Box (Box _));(Γ, Box _)]) ; 
       [ intros prem H0 ; inversion H0 ; [ subst ; apply Ax ; apply AxRule_I ; 
        right ; apply MA4_I ; eexists _ ; unfold MA4 ; auto |
        inversion H1 ; [ subst ; apply H | inversion H2] ] | apply MPRule_I].
apply MP with (ps:=[(Γ, Box (Box A) --> Box (Box (Box A)));(Γ, Box (Box A))]).
2: apply MPRule_I. intros. inversion H0 ; subst. 2: inversion H1 ; [subst ; auto |  inversion H2].
apply Ax. apply AxRule_I. right. apply MA4_I. exists (Box A) ; auto.
apply MP with (ps:=[(Γ, Box A --> Box (Box A));(Γ, Box A)]).
2: apply MPRule_I. intros. inversion H2 ; subst. 2: inversion H3 ; [subst ; auto |  inversion H4].
apply Ax. apply AxRule_I. right. apply MA4_I. exists A ; auto.
Qed.

