Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import iS4_Syntax.
Require Import iS4H.
Require Import iS4_topol_sem.


Lemma Ax_valid : forall A, Axioms A ->
  (forall M w, forces M w A).
Proof.
intros A Ax. destruct Ax as [Ax | Ax].
(* Intuitionistic axioms *)
+ inversion Ax ; simpl ; intros ; auto.
  - destruct H ; destruct H ; subst ; simpl ; intros. apply Persistence with (w:=v) ; auto.
  - destruct H; destruct H ; destruct H ; subst ; simpl ; intros ; auto. apply H0 with v1 ; auto.
    apply (@reach_tran (@pos M)) with (v:=v0) ; auto. apply (@reach_refl (@pos M)).
  - destruct H ; destruct H ; subst ; simpl ; intros ; auto ;  destruct H0 ; auto.
  - destruct H ; destruct H ; subst ; simpl ; intros ; auto.
  - destruct H ; destruct H ; destruct H ; subst ; simpl ; intros ; auto. destruct H4 ; auto. apply H0 ; auto.
    apply (@reach_tran (@pos M)) with (v:=v0) ; auto.
  - destruct H ; destruct H ; subst ; simpl ; intros ; auto. destruct H0. auto.
  - destruct H ; destruct H ; subst ; simpl ; intros ; auto. destruct H0. auto.
  - destruct H ; destruct H ; destruct H ; subst ; simpl ; intros ; auto. split.
    apply H0 ; auto. apply (@reach_tran (@pos M)) with (v:=v0) ; auto. apply H2 ; auto.
  - destruct H ; subst. simpl. intros. inversion H0.
(* Modal axioms *)
+ inversion Ax ; simpl ; intros ; auto.
  (* K *)
  - destruct H ; destruct H ; subst. intros v0 R0 F0 v1 R1 F1.
    pose (force_Box_interior_truthset (x --> x0) M v0). destruct i.
    pose (H F0). clear H0.
    pose (force_Box_interior_truthset x M v1). destruct i.
    pose (H0 F1). clear H1.
    apply force_Box_interior_truthset. unfold uset in *.
    pose (@is_upset _ (i (truthset_upset M (x --> x0))) v0 u _ R1).
    assert (@uset _ (inter_upset _ ( i (truthset_upset M (x --> x0))) (i (truthset_upset M x))) v1).
    unfold uset. unfold inter_upset ; auto.
    assert (@uset _ (i (inter_upset _ (truthset_upset M (x --> x0)) (truthset_upset M x))) v1).
    rewrite i_inter ; auto.
    apply i_subset_uset_mon with (u0:=inter_upset pos (truthset_upset M (x --> x0)) (truthset_upset M x)) ; auto.
    intros. destruct H3. pose (force_truthset x0 M w0). destruct i. apply H5.
    pose (force_truthset x M w0). destruct i. apply H8 in H4.
    pose (force_truthset (x --> x0) M w0). destruct i. apply H10 in H3.
    simpl in H3. apply H3 ; auto. apply reach_refl.
  (* T *)
  - destruct H ; subst ; simpl ; intros. apply force_truthset. apply i_T. unfold In. apply H0.
    split ; auto.
  (* 4 *)
  - destruct H ; subst. unfold MA4 in *. intros v R F. apply force_Box_interior_truthset in F.
    apply i_4 in F. unfold In in F. simpl. intros.
    pose (i_id_uset_preserv M (i (truthset_upset M x)) u). apply i ; auto.
    intros. split ; auto ; intros ; auto.
    * apply H ; auto. intros ; auto. unfold uset. unfold uset in H0.
      pose (i_id_uset_preserv M (truthset_upset M x) u0). apply i0 ; auto.
    * apply H ; auto. intros ; split ; auto.
Qed.

Theorem Soundness : forall s, (iS4H_rules s) ->  (loc_conseq (fst s) (snd s)).
Proof.
intros s D. induction D.
(* Id *)
- inversion H. subst. simpl. intro. intros. auto.
(* Ax *)
- inversion H. subst. simpl. intro. intros. apply Ax_valid. auto.
(* MP *)
- inversion H1. subst. simpl. assert (J1: loc_conseq Γ (A --> B)).
  apply H0 with (prem:=(Γ, A --> B)). apply in_eq. assert (J2: loc_conseq Γ (A)).
  apply H0 with (prem:=(Γ, A)). apply in_cons. apply in_eq.
  intro. intros. unfold loc_conseq in J1.
  pose (J1 M w H2). pose (J2 M w H2). apply f ; auto. apply (@reach_refl (@pos M)).
(* Nec *)
- inversion H1. subst. simpl. assert (J1: loc_conseq (Empty_set form) A).
  apply H0 with (prem:=(Empty_set form, A)) ; apply in_eq.
  intro. intros. apply force_Box_interior_truthset. unfold uset.
  rewrite upset_prf_irrel with (u1:=unit_upset _) (u0:=(truthset_upset M A)). rewrite i_unit.
  unfold unit_upset ; auto.
  apply Extensionality_Ensembles. split ; intros x Hx ; unfold In in * ; auto.
  unfold uset. unfold unit_upset ; auto.
  pose (force_truthset A M x). destruct i. apply H3.
  apply J1 ; auto. intros. inversion H5.
Qed.

