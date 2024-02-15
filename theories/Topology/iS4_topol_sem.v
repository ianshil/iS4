Require Import Arith.
Require Import Lia.
Require Import Ensembles.
Require Import Init.Wf.

Require Import iS4_Syntax.

Section TopologicalSemantics.

    Class preorder :=
      {
        (* Carrier *)
        nodes : Type ;

        (* Intuitionistic Relation *)
        reachable : nodes -> nodes -> Prop ;
        reach_refl u : reachable u u ;
        reach_tran u v w : reachable u v -> reachable v w -> reachable u w
      }.

  Class upset (pre : preorder) :=
    {
      uset : Ensemble (@nodes pre);
      is_upset : forall w, (uset w) -> forall x, @reachable pre w x -> (uset x)
    }.

  (* We use the next axiom to make sure that upsets are identified by their underlying
      set, and not their proof of being an upset. *)

  Axiom upset_prf_irrel : forall pre (u0 u1 : upset pre), (@uset _ u0 = @uset _ u1) -> u0 = u1.

  Lemma unit_is_upset : forall (pre : preorder), forall w, ((fun (x : @nodes pre) => x = x) w) ->
            forall y, @reachable pre w y -> ((fun (x : @nodes pre) => x = x) y).
  Proof.
  intros. simpl in H. simpl ; auto.
  Qed.

  Instance unit_upset (pre : preorder) : upset pre :=
      {|
        uset := (fun (x : @nodes pre) => x = x);
        is_upset := unit_is_upset pre
      |}.

  Lemma inter_is_upset : forall (pre : preorder) (u0 u1 : upset pre), forall w, ((fun (x : @nodes pre) => (@uset pre u0) x /\ (@uset pre u1) x) w) ->
            forall y, @reachable pre w y -> ((fun (x : @nodes pre) => (@uset pre u0) x /\ (@uset pre u1) x) y).
  Proof.
  intros. simpl in H. simpl. destruct H ; split.
  - apply (@is_upset pre u0 w) ; auto.
  - apply (@is_upset pre u1 w) ; auto.
  Qed.

  Instance inter_upset (pre : preorder) (u0 u1 : upset pre) : upset pre :=
      {|
        uset := (fun (x : @nodes pre) => (@uset pre u0) x /\ (@uset pre u1) x);
        is_upset := inter_is_upset pre u0 u1
      |}.

    Class model :=
      {
        (* Base preorder *)
        pre : preorder ;

        (* Interior operator *)
        i : (upset pre) -> (upset pre) ;
        i_unit : i (unit_upset pre) = (unit_upset pre) ;
        i_inter : forall u0 u1, @uset _ (i (inter_upset pre u0 u1)) = @uset _ (inter_upset pre (i u0) (i u1)) ;
        i_T : forall u, Included _ (@uset pre (i u)) (@uset pre u) ;
        i_4 : forall u, Included _ (@uset pre (i u)) (@uset pre (i (i u))) ;

        (* Valuation on upsets *)
        val : nat -> (upset pre)
      }.

  Fixpoint forces (M: model) (w : nodes) (φ : form) : Prop :=
  match φ with
    | Var p => (@uset (@pre M) (val p)) w
    | Bot => False
    | ψ ∧ χ => (forces M w ψ) /\ (forces M w χ)
    | ψ ∨ χ => (forces M w ψ) \/ (forces M w χ)
    | ψ --> χ => forall v, reachable w v -> forces M v ψ -> forces M v χ
    | Box ψ => forall u, (forall v, forces M v ψ <-> (@uset (@pre M) u) v) -> (@uset (@pre M) (i u)) w
  end.

  Definition mforces M (φ : form) : Prop := forall w , forces M w φ.

  Definition valid_form φ := forall M, mforces M φ.

  Definition loc_conseq (Γ : Ensemble form) (φ : form) :=
   forall M w, (forall ψ, (In _ Γ ψ) -> forces M w ψ) -> (forces M w φ).

  Lemma Persistence : forall A M w, forces M w A ->
              (forall v, reachable w v -> forces M v A).
  Proof.
  induction A ; intros ; try auto.
  - simpl. simpl in H. apply (@is_upset pre _ w) ; auto.
  - simpl. split. inversion H. apply IHA1 with (w:=w) ; auto.
    inversion H. apply IHA2 with (w:=w) ; auto.
  - simpl. inversion H. left. apply IHA1 with (w:=w) ; auto.
    right. apply IHA2 with (w:=w) ; auto.
  - simpl. intros. simpl in H. apply H with (v:=v0) ; auto.
    pose ((@reach_tran) _ _ _ _ H0 H1). auto.
  - simpl. simpl in H. intros. pose (H u H1).
    apply (@is_upset pre _ w) ; auto.
  Qed.

  Lemma truthset_is_upset : forall M φ, forall w, ((fun (x : @nodes (@pre M)) => forces M x φ) w) ->
            forall y, @reachable (@pre M) w y -> ((fun (x : @nodes (@pre M)) => forces M x φ) y).
  Proof.
  intros. simpl in H. simpl. apply Persistence with (w:=w) ; auto.
  Qed.

  Instance truthset_upset (M : model) φ: upset (@pre M) :=
      {|
        uset := (fun (x : @nodes pre) => forces M x φ);
        is_upset := truthset_is_upset M φ
      |}.

  Lemma inter_conj : forall M u0 u1 w, (@uset (@pre M) (@inter_upset _ u0 u1)) w ->
          ((@uset (@pre M) u0) w) /\ ((@uset (@pre M) u1) w).
  Proof.
  intros. unfold uset in *. unfold inter_upset in H. auto.
  Qed.

  (* i preserves identity on sets. *)

  Lemma i_id_uset_preserv : forall M u0 u1, (forall w, (@uset (@pre M) u0) w <-> (@uset (@pre M) u1) w) ->
          (forall w, (@uset (@pre M) (i u0)) w <-> (@uset pre (i u1)) w).
  Proof.
  intros. assert (@uset _ u0 = @uset _ u1). apply Extensionality_Ensembles ; split ; intros A HA ; apply H ; auto.
  pose (upset_prf_irrel _ _ _ H0). split ; intro ; rewrite e in * ; auto.
  Qed.

  (* i preserves the subset relation. *)

  Lemma i_subset_uset_mon : forall M u0 u1, (forall w, (@uset (@pre M) u0) w -> (@uset (@pre M) u1) w) ->
          (forall w, (@uset (@pre M) (i u0)) w -> (@uset pre (i u1)) w).
  Proof.
  intros.
  assert (@uset _ (inter_upset _ u0 u1) = @uset _ u0).
  apply Extensionality_Ensembles. split ; intros x Hx ; unfold In in * ; unfold uset in * ; auto.
  unfold inter_upset in * ; auto. destruct Hx ; auto. split ; auto. apply H ; auto.
  apply upset_prf_irrel in H1.
  assert (@uset _  (inter_upset _ (i u0) (i u1)) w).
  rewrite <- i_inter ; rewrite H1 ; auto.
  destruct H2 ; auto.
  Qed.

  (* A world w forces Box φ iff it is in the interior of the truth set of φ. *)

  Lemma force_Box_interior_truthset : forall φ M w, forces M w (Box φ) <-> (@uset (@pre M) (i (truthset_upset M φ))) w.
  Proof.
  intros. split ; intro.
  - simpl in H. apply H. intros ; split ; intros ; auto.
  - simpl. intros ; auto.
    assert (forall w, (@uset (@pre M) (truthset_upset M φ)) w <-> (@uset pre u) w).
    split ; intros ; apply H0 ; auto.
    pose (i_id_uset_preserv M _ _ H1). apply i0 ; auto.
  Qed.

  Lemma force_truthset : forall φ M w, forces M w φ <-> (@uset (@pre M) (truthset_upset M φ)) w.
  Proof.
  intros. split ; intro.
  - simpl in H. apply H.
  - simpl. intros ; auto.
  Qed.

End TopologicalSemantics.
