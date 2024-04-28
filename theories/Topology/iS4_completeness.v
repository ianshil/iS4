Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import iS4_Syntax.
Require Import iS4H.
Require Import iS4H_logic.
Require Import iS4H_properties.
Require Import iS4_enum.
Require Import iS4_topol_sem.
Require Import iS4_Lindenbaum_lem.


Section Completeness.

(* We first create the canonical preord_set. *)

Class Canon_worlds Γ : Type :=
  { world : @Ensemble form ;
    wInclClos : Included _ world (Clos Γ) ;
    wNotDer : ~ iS4H_prv (world, Bot) ;
    wClosed : restr_closed (Clos Γ) world ;
    wPrime : quasi_prime world
  }.

Definition Canon_rel Γ (P0 P1 : Canon_worlds Γ) : Prop :=
  Included _ (@world _ P0) (@world _ P1).

Lemma C_R_refl Γ u : Canon_rel Γ u u.
Proof.
unfold Canon_rel. intro. auto.
Qed.

Lemma C_R_trans Γ u v w: Canon_rel Γ u v -> Canon_rel Γ v w -> Canon_rel Γ u w.
Proof.
intros. unfold Canon_rel.
intro. intros. unfold Canon_rel in H0. unfold Canon_rel in H.
apply H0. apply H. auto.
Qed.

Instance CPre Γ : preord_set :=
      {|
        nodes := Canon_worlds Γ ;

        reachable := Canon_rel Γ ;
        reach_refl := C_R_refl Γ ;
        reach_tran := C_R_trans Γ ;
      |}.

(* As expected, we can create canonical worlds using our
   Lindenbaum lemma. *)

Lemma Lindenbaum_world Γ ψ Δ :
  In _ (Clos Γ) ψ ->
  Included _ Δ (Clos Γ) ->
  ~ iS4H_prv (Δ, ψ) ->
  exists w : Canon_worlds Γ, Included _ Δ world /\ ~ In _ world ψ.
Proof.
  intros. pose (Lindenbaum _ _ _ H H0 H1).
  destruct e as (Δm & H2 & H3 & H4 & H5 & H6).
  unshelve eexists.
  - apply (Build_Canon_worlds Γ Δm); intuition ; simpl. apply H6.
    apply MP with (ps:=[(Δm, Bot --> ψ);(Δm, Bot)]). 2: apply MPRule_I.
    intros. inversion H8 ; subst. apply Ax. apply AxRule_I. left. apply IA9_I.
    eexists ; auto. inversion H9 ; subst ; auto. inversion H10.
  - intuition. apply H6. apply Id. apply IdRule_I ; auto.
Qed.

(* Then we create interior operator for the canonical preord_set. *)

Definition Theories Γ φ : Ensemble (@nodes (CPre Γ)) :=
  fun x => In _ (@world Γ x) φ.

Lemma Theories_upset : forall Γ φ,
  forall (w : @nodes (CPre Γ)), ((Theories Γ φ) w) ->
            forall y, @reachable (CPre Γ) w y -> ((Theories Γ φ) y).
Proof.
intros. unfold Theories, In in *. unfold reachable in H0. simpl in H0. apply H0 ; auto.
Qed.

Instance upTheories Γ φ : (upset (CPre Γ)) :=
      {|
        uset := Theories Γ φ;
        is_upset := Theories_upset Γ φ
      |}.

(* Note that the next definition outputs the entire type X in the case
    where l is nil. Else, it behaves as a normal finite intersection. *)

Definition Finite_Intersection {X : Type} (l : list (Ensemble X)) : Ensemble X :=
  fun x => forall y, List.In y l -> In _ y x.

(* Next is the usual infinite union. *)

Definition Inf_Union {X : Type} (E : Ensemble (Ensemble X)) : Ensemble X :=
  fun x => exists S, In _ E S /\ In _ S x.

 (* We define the function Ci, the interior function on the canonical model.  *)

Definition Ci_uset Γ (u : upset (CPre Γ)) : Ensemble (@nodes (CPre Γ)) :=
   Inf_Union (fun x => exists (l: list form),
     (Included _ (fun y => List.In y (map BoxOne l)) (Clos Γ)) /\ (* All formulae in Box l are in Clos Γ. *)
      Included _ (Finite_Intersection (map (Theories Γ) l)) (@uset _ u) /\
      x = Finite_Intersection (map (Theories _) (map BoxOne l))).

Lemma Ci_upset : forall Γ (u : upset (CPre Γ)),
  forall (w : @nodes (CPre Γ)), ((Ci_uset Γ u) w) ->
            forall y, @reachable (CPre Γ) w y -> ((Ci_uset Γ u) y).
Proof.
intros. unfold Ci_uset, Inf_Union in *. destruct H. destruct H.
unfold In in H. destruct H as ( l & H2 & H3 & H4). subst.
unfold In ; simpl.
exists (Finite_Intersection (map (Theories Γ) (map BoxOne l))).
repeat split.
- exists l. repeat split.
  + intros A HA. unfold In in HA. apply in_map_iff in HA. destruct HA. destruct H ; subst.
     apply H2. unfold In ; simpl. apply in_map_iff ; exists x ; auto.
  + intros A HA. unfold In. unfold In in HA. unfold Finite_Intersection in *. unfold In in *.
     apply H3. unfold In. intros. apply in_map_iff in H. destruct H. destruct H ; subst.
     unfold Theories. apply HA. apply in_map_iff.
     exists x. unfold Theories. split ; auto.
- unfold Finite_Intersection in *. unfold In in *. intros. apply in_map_iff in H. destruct H.
  destruct H ; subst. unfold Theories. unfold In. apply in_map_iff in H4. destruct H4.
  destruct H ; subst. apply H0. apply H1 ; simpl. apply in_map_iff. exists (BoxOne x0).
  split. unfold Theories. auto. apply in_map_iff ; exists x0 ; auto.
Qed.

Instance Ci Γ (u : upset (CPre Γ)) : (upset (CPre Γ)) :=
      {|
        uset := Ci_uset Γ u;
        is_upset := Ci_upset Γ u
      |}.

  (* Then, we proceed to show that Ci is indeed an interior operator. *)

Lemma Ci_unit Γ : Ci Γ (unit_upset (CPre Γ)) = (unit_upset (CPre Γ)).
Proof.
apply upset_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA ; auto.
unfold In. unfold uset. simpl ; auto. unfold In in *. unfold uset in * ; simpl in *.
unfold Ci_uset. unfold Inf_Union. exists (fun x => True). unfold In ; simpl. repeat split ; auto.
exists []. simpl ; repeat split ; auto. intros B HB. inversion HB. unfold Finite_Intersection.
simpl. apply Extensionality_Ensembles. split ; intros B HB ; simpl in *. unfold In in HB.
unfold In. intros. inversion H. unfold In ; auto.
Qed.

Lemma Ci_inter Γ : forall u0 u1, @uset _ (Ci  Γ (inter_upset (CPre Γ) u0 u1)) = @uset _ (inter_upset (CPre Γ) (Ci Γ u0) (Ci Γ u1)).
Proof.
intros. unfold uset ; simpl. unfold Ci_uset ; simpl.
unfold Inf_Union ; simpl. apply Extensionality_Ensembles. split ; intros A HA ; auto.
- unfold In in *. destruct HA. destruct H. destruct H. destruct H. destruct H1 ; subst. split.
  + exists (Finite_Intersection (map (Theories Γ) (map BoxOne x0))). split ; auto.
     exists x0. repeat split ; auto. intros B HB. unfold In in *. unfold uset ; simpl.
     apply H1. unfold In. auto.
  + exists (Finite_Intersection (map (Theories Γ) (map BoxOne x0))). split ; auto.
     exists x0. repeat split ; auto. intros B HB. unfold In in *. unfold uset ; simpl.
     apply H1. unfold In. auto.
- unfold In in *. destruct HA. destruct H. destruct H. destruct H. destruct H. destruct H2. subst.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H4 ; subst.
  exists (Finite_Intersection (map (Theories Γ) ((map BoxOne x0) ++ (map BoxOne x1)))). split ; auto.
  + exists (x0 ++ x1). repeat split ; auto.
     * intros B HB. unfold In in *. apply in_map_iff in HB. destruct HB.
       destruct H5 ; subst. apply in_app_or in H6. destruct H6. apply H ; unfold In.
       apply in_map_iff ; exists x ; split ; auto. apply H0 ; apply in_map_iff ; exists x ; split ; auto.
     * unfold In in *. apply H2. unfold In. unfold Finite_Intersection in *. intros. unfold In in *.
       apply in_map_iff in H6. destruct H6. destruct H6 ; subst. unfold Theories. unfold In in *. apply H5.
       apply in_map_iff. exists x2. split ; auto. apply in_or_app ; auto.
     * unfold In in *. apply H4. unfold In. unfold Finite_Intersection in *. intros. unfold In in *.
       apply in_map_iff in H6. destruct H6. destruct H6 ; subst. unfold Theories. unfold In in *. apply H5.
       apply in_map_iff. exists x2. split ; auto. apply in_or_app ; auto.
     * repeat rewrite map_app ; auto.
  + unfold Finite_Intersection in *. intros. unfold In in *. apply in_map_iff in H5. destruct H5. destruct H5 ; subst. unfold Theories.
     apply in_app_or in H6. destruct H6. apply in_map_iff in H5. destruct H5. destruct H5 ; subst. unfold In. apply H1.
     apply in_map_iff. exists (BoxOne x2). split ; auto. apply in_map_iff ; exists x2 ; split ; auto.
     apply H3 ; auto. apply in_map_iff in H5. destruct H5. destruct H5 ; subst.
     apply in_map_iff. exists (BoxOne x2). split ; auto. apply in_map_iff ; exists x2 ; split ; auto.
Qed.

Lemma Ci_T Γ :forall u, Included _ (@uset (CPre Γ) (Ci Γ u)) (@uset (CPre Γ) u).
Proof.
intros u A HA. unfold In in *. unfold uset in *. simpl in *. unfold Ci_uset in HA. unfold Inf_Union in HA.
destruct HA. unfold In in H. destruct H. destruct H. destruct H. destruct H1 ; subst.
unfold Finite_Intersection in * ; simpl in *. unfold In in *.
apply H1. unfold In. intros. apply in_map_iff in H2. destruct H2. destruct H2 ; subst. unfold Theories.
unfold In. apply wClosed.
eapply MP with [_;(_, BoxOne x)]. 2: apply MPRule_I.
intros. inversion H2 ; subst. apply T_BoxOne.
inversion H4 ; subst. 2: inversion H5. apply Id. apply IdRule_I.
unfold In. apply H0. apply in_map_iff. exists (BoxOne x) ; split ; auto.
apply in_map_iff. exists x ; split ; auto.
assert ((Clos Γ) (BoxOne x)). apply H. unfold In. apply in_map_iff. exists x ; split ; auto.
apply Incl_ClosSubform_Clos. unfold In. exists (BoxOne x) ; split ; auto.
destruct x ; simpl in * ; auto.
Qed.

Lemma Ci_4 Γ : forall u, Included _ (@uset (CPre Γ) (Ci Γ u)) (@uset (CPre Γ) (Ci Γ (Ci Γ u))).
Proof.
intros u w Hw. unfold In in *. unfold uset in *. simpl in *. unfold Ci_uset in Hw. unfold Inf_Union in Hw.
unfold In in *. destruct Hw. destruct H as (H0 & H1). destruct H0 as (l & H2 & H3 & H4) ; subst.
unfold Finite_Intersection in *. simpl in *. unfold In in *.
unfold Ci_uset. unfold Inf_Union. simpl ; unfold In.
exists (Finite_Intersection (map (Theories Γ) (map BoxOne l))). split ; auto.
exists (map BoxOne l) ; repeat split ; auto.
  + intros A HA. unfold In in *. apply in_map_iff in HA. destruct HA. destruct H ; subst.
     apply in_map_iff in H0. destruct H0. destruct H ; subst. apply H2. unfold In.
     apply in_map_iff. exists x0 ; split ; auto. destruct x0 ; simpl ; auto.
  + intros v Hv. unfold In in *. unfold Finite_Intersection in *. unfold In in *.
     unfold Ci_uset. unfold Inf_Union. unfold In ; simpl.
     exists (Finite_Intersection (map (Theories Γ) (map BoxOne l))). split ; auto.
     exists l ; repeat split ; auto.
  + rewrite <- map_double_BoxOne ; auto.
Qed.

(* We define the canonical valuation. *)

Definition Canon_val Γ (q : nat) : upset (CPre Γ) := upTheories Γ (# q).

Lemma C_val_persist : forall Γ u v, Canon_rel Γ u v -> forall p, In _ (@uset _ (Canon_val Γ p)) u -> In _ (@uset _ (Canon_val Γ p)) v.
Proof.
intros. unfold In in *. apply H ; auto.
Qed.

(* Finally we can define the canonical model. *)

Instance CM Γ : model :=
      {|
        pre := CPre Γ ;

        i := Ci Γ ;
        i_unit := Ci_unit Γ ;
        i_inter := Ci_inter Γ ;
        i_T := Ci_T Γ ;
        i_4 := Ci_4 Γ ;

        val := Canon_val Γ
      |}.

  (* To prove strong completeness, we require the strength of classical
      logic. For this, we declare LEM as an axiom. *)

Axiom LEM : forall P, P \/ ~ P.

Lemma LEM_prime Δ :
  quasi_prime Δ  -> prime Δ .
Proof.
  intros H1 A B H2.
  apply H1 in H2 ; auto. destruct (LEM (Δ  A)) ; auto.
  destruct (LEM (Δ  B)) ; auto. exfalso. apply H2.
  intro. destruct H3 ; auto.
Qed.

(* Stepping stone for the truth lemma. *)

Lemma K_finite_intersection : forall Γ l0 l1,
  Included _ (fun y => List.In y (map BoxOne l0)) (Clos Γ) ->
  Included _ (fun y => List.In y (map BoxOne l1)) (Clos Γ) ->
  Included _ (Finite_Intersection (map (Theories Γ) l0)) (Finite_Intersection (map (Theories Γ) l1)) ->
  Included _ (Finite_Intersection (map (Theories Γ) (map BoxOne l0))) (Finite_Intersection (map (Theories Γ) (map BoxOne l1))).
Proof.
intros. intros w Hw. unfold In in *. unfold Finite_Intersection in *. unfold In in *.
intros. apply in_map_iff in H2. destruct H2. destruct H2 ; subst. apply in_map_iff in H3.
destruct H3. destruct H2 ; subst. unfold Theories in *. simpl in *. unfold In in *.
enough (iS4H_rules ((fun x => List.In x (map BoxOne l0)), BoxOne x0)).
- apply wClosed. eapply (iS4H_monot (_,_) H2). simpl in *. intros A HA. unfold In in *.
  apply Hw. apply in_map_iff. exists A ; split ; auto. apply H0. apply in_map_iff. eexists ; split ; auto.
- enough (iS4H_prv (fun x : form => List.In x l0, x0)).
  + apply K_BoxOne_rule in H2. apply (iS4H_monot _ H2) ; simpl ; intros A HA.
     unfold In in * ; simpl. destruct HA. destruct H4 ; subst ; auto. apply in_map_iff.
     exists x ; split ; auto.
  + destruct (LEM (iS4H_prv (fun x : form => List.In x l0, x0))) ; auto. exfalso.
     assert (J0: In form (Clos Γ) x0). apply Incl_ClosSubform_Clos. exists (BoxOne x0). split ; auto. apply H0.
     unfold In. apply in_map_iff. exists x0 ; auto. destruct x0 ; simpl ; auto ; right ; simpl ; auto.
     assert (J1: Included form (fun x : form => List.In x l0) (Clos Γ)).
     intros A HA. apply Incl_ClosSubform_Clos. exists (BoxOne A). split ; auto.
     apply H. simpl ; apply in_map_iff. eexists ; auto. destruct A ; simpl ; auto ; right ; simpl ; auto.
     pose (Lindenbaum_world _ _ _ J0 J1 H2). destruct e. destruct H4.
     pose (H1 x). unfold In in *. apply H5. apply i.
     intros. apply in_map_iff in H6. destruct H6. destruct H6 ; subst. apply H4. auto.
     apply in_map_iff. exists x0. split ; auto.
Qed.

Lemma truth_lemma Γ : forall ψ (cp : Canon_worlds Γ),
  (Clos Γ ψ) ->
  (forces (CM Γ) cp ψ) <-> (In _ (@world _ cp) ψ).
Proof.
induction ψ ; intros ; split ; intros ; simpl ; try simpl in H1 ; auto.
(* Bot *)
- inversion H0.
- apply wNotDer. apply Id. apply IdRule_I ; auto.
(* And ψ1 ψ2 *)
- destruct H0. apply IHψ1 in H0 ; auto. apply IHψ2 in H1 ; auto. unfold In in *.
  apply wClosed ; auto.
  apply MP with (ps:=[(world, ψ1 --> (And ψ1 ψ2));(world, ψ1)]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(world, (ψ1 --> ψ2) --> (ψ1 --> (And ψ1 ψ2)));(world, (ψ1 --> ψ2))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MP with (ps:=[(world, (ψ1 --> ψ1) --> (ψ1 --> ψ2) --> (ψ1 --> (And ψ1 ψ2)));(world, (ψ1 --> ψ1))]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Ax. apply AxRule_I. left.
  apply IA8_I. repeat eexists ; auto. inversion H5.
  subst. 2: inversion H6. apply imp_Id_gen. inversion H4. subst. 2: inversion H5.
  apply MP with (ps:=[(world, ψ2 --> (ψ1 --> ψ2));(world, ψ2)]).
  2: apply MPRule_I. intros. inversion H5. subst. apply Thm_irrel.
  inversion H6. subst. 2: inversion H7. apply Id. apply IdRule_I. assumption.
  inversion H3. subst. apply Id. apply IdRule_I. assumption. inversion H4.
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∧ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∧ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∧ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∧ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  split.
  apply IHψ1 ; auto. apply wClosed ; auto.
  apply MP with (ps:=[(world, (And ψ1 ψ2) --> ψ1);(world, (And ψ1 ψ2))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. left.
  apply IA6_I. repeat eexists ; auto. inversion H2. 2: inversion H3.
  subst. apply Id. apply IdRule_I ; auto.
  apply IHψ2 ; auto. apply wClosed; auto.
  apply MP with (ps:=[(world, (And ψ1 ψ2) --> ψ2);(world, (And ψ1 ψ2))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. left.
  apply IA7_I. repeat eexists ; auto. inversion H2. 2: inversion H3.
  subst. apply Id. apply IdRule_I ; auto.
(* Or ψ1 ψ2 *)
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∨ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∨ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  destruct H0.
  apply IHψ1 in H0 ; auto. apply wClosed ; auto.
  apply MP with (ps:=[(world, Imp ψ1 (Or ψ1 ψ2));(world, ψ1)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. left.
  apply IA3_I. repeat eexists ; auto. inversion H2. 2: inversion H3.
  subst. apply Id. apply IdRule_I ; auto.
  apply IHψ2 in H0 ; auto. apply wClosed ; auto.
  apply MP with (ps:=[(world, Imp ψ2 (Or ψ1 ψ2));(world, ψ2)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. left.
  apply IA4_I. repeat eexists ; auto. inversion H2. 2: inversion H3.
  subst. apply Id. apply IdRule_I ; auto.
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∨ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∨ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  pose (LEM_prime _  wPrime). apply p in H0 ; auto. destruct H0.
  left. apply IHψ1 ; auto.
  right. apply IHψ2 ; auto.
(* Imp ψ1 ψ2 *)
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 --> ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 --> ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  destruct (LEM (In form world (ψ1 --> ψ2))) ; auto. exfalso.
  assert (iS4H_rules (Union _ world (Singleton _ ψ1), ψ2) -> False).
  intro. apply iS4H_Deduction_Theorem with (A:=ψ1) (B:=ψ2) (Γ:=world) in H2 ; auto.
  apply H1. apply wClosed ; auto.
  assert (Included form (Union form world (Singleton form ψ1)) (Clos Γ)).
  intros A HA. inversion HA ; subst. apply wInclClos ; auto. inversion H3 ; subst ;  auto.
  pose (Lindenbaum_world _ _ _ Jψ2 H3 H2). destruct e as [w [Hw1 Hw2]].
  assert (J2: Canon_rel _ cp w). unfold Canon_rel.
  intros A HA. apply Hw1. apply Union_introl. auto. simpl in H0.
  pose (H0 _ J2). apply Hw2. apply IHψ2 ; auto. apply f. apply IHψ1 ; auto.
  apply wClosed ; auto. apply Id. apply IdRule_I. apply Hw1.
  apply Union_intror ; apply In_singleton.
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 --> ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 --> ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  intros.
  apply IHψ1 in H2 ; auto. unfold Canon_rel in H1. apply H1 in H0.
  apply IHψ2 ; auto.
  assert (iS4H_rules (world, ψ2)).
  apply MP with (ps:=[(world, ψ1 --> ψ2);(world, ψ1)]). 2: apply MPRule_I.
  intros. inversion H3. subst. apply Id. apply IdRule_I. auto.
  inversion H4. 2: inversion H5. subst. apply Id. apply IdRule_I. auto.
  apply wClosed ; auto.
(* Box ψ *)
- assert (Jψ: Clos Γ ψ).
  apply Incl_ClosSubform_Clos. unfold In. exists (Box ψ). split ; simpl ; auto. right.
  destruct ψ ; simpl ; auto.
  simpl in H0.
  assert (In _ (Ci_uset Γ (upTheories Γ ψ)) cp).
  { apply H0. intros. split ; intros ; auto. apply IHψ in H1; auto. apply IHψ ; auto. }
  unfold In in *.
  unfold Ci_uset in H1. unfold Inf_Union in H1. destruct H1. unfold In in *.
  destruct H1. destruct H1. destruct H1. destruct H3 ; subst.
  assert (Included form (fun y : form => List.In y [BoxOne ψ]) (Clos Γ)).
  intros A HA. inversion HA ; subst ; auto. apply In_Clos_BoxOne ; auto. inversion H4.
  assert (Included nodes (Finite_Intersection (map (Theories Γ) x0)) (Finite_Intersection (map (Theories Γ) [ψ]))). 
  intros A HA. unfold In in *. unfold Finite_Intersection in *. intros.
  simpl in *. destruct H5 ; unfold In in * ; subst. unfold Theories. unfold In. apply H3 ; auto.
  inversion H5.
  pose (K_finite_intersection _ _ [ψ] H1 H4 H5).
  pose (i _ H2). unfold In in *.
  apply wClosed ; auto.
  eapply MP with [_;(_,BoxOne ψ)]. 2: apply MPRule_I.
  intros. inversion H6 ; subst. destruct ψ ; simpl.
  1-5: apply imp_Id_gen. apply Ax. apply AxRule_I ; right ; apply MA4_I ; eexists ; reflexivity.
  inversion H7 ; subst. unfold Finite_Intersection in i0.
  apply i0. apply in_map_iff. exists (BoxOne ψ). split ; auto.
  apply Extensionality_Ensembles ; split ; intros A HA ; unfold In in *. unfold Theories in HA.
  apply Id. apply IdRule_I ; auto. apply wClosed ; auto. apply In_Clos_BoxOne ; auto.
  apply in_map_iff. exists ψ ; split ; auto. apply in_eq. inversion H8.
- assert (Jψ: Clos Γ ψ).
  apply Incl_ClosSubform_Clos. unfold In. exists (Box ψ). split ; simpl ; auto. right.
  destruct ψ ; simpl ; auto.
  intros. unfold Ci_uset. unfold Inf_Union. unfold In in *. simpl in *.
  exists (Finite_Intersection [(Theories Γ (BoxOne ψ))]). split ; auto.
  + exists [ψ] ; repeat split ; simpl ; auto.
     intros A HA. inversion HA ; subst ; auto. apply In_Clos_BoxOne ; auto. inversion H2.
     intros A HA. apply H1. unfold In in *. unfold Finite_Intersection in HA. unfold In in *.
     apply IHψ ; auto. apply HA. unfold Theories. simpl. auto.
  + unfold Finite_Intersection. unfold Theories ; unfold In in * ; simpl. intros.
     destruct H2 ; subst ; try contradiction. apply wClosed ; auto.
     eapply MP with [_;(_,Box ψ)]. 2: apply MPRule_I.
     intros. inversion H2 ; subst. destruct ψ ; simpl. 1-5: apply imp_Id_gen.
     apply Ax. apply AxRule_I ; right ; apply MAT_I ; eexists ; reflexivity.
     inversion H3 ; [subst | inversion H4]. apply Id ; apply IdRule_I ; auto.
     apply In_Clos_BoxOne ; auto.
Qed.

Theorem QuasiCompleteness : forall s,
    (iS4H_rules s -> False) -> ((loc_conseq (fst s) (snd s)) -> False).
Proof.
intros s WD H. destruct s ; simpl in *.
apply Lindenbaum_world with (Γ:=Union _ e (Singleton _ f)) in WD ; auto.
- destruct WD as (w & H1 & H2).
  assert ((forall A, In _ e A -> forces (CM _) w A)). intros. apply truth_lemma. 2: auto.
  apply wInclClos ; auto. apply H in H0. apply truth_lemma in H0 ; auto.
  unfold Clos. unfold ClosOneBox. apply Union_introl. unfold In.
  exists f. split. apply Union_intror. apply In_singleton. destruct f ; simpl ; auto.
- unfold Clos. unfold ClosOneBox. apply Union_introl. unfold In.
  exists f. split. apply Union_intror. apply In_singleton. destruct f ; simpl ; auto.
- intros A HA. unfold Clos. unfold ClosOneBox. apply Union_introl. unfold In.
  exists A. split. apply Union_introl ; auto. destruct A ; simpl ; auto.
Qed.

Theorem Completeness : forall Γ A,
    (loc_conseq Γ A) -> iS4H_rules (Γ, A).
Proof.
intros Γ A LC. pose (QuasiCompleteness (Γ, A)).
destruct (LEM (iS4H_rules (Γ, A))) ; auto. exfalso.
apply f ; assumption.
Qed.

End Completeness.


  
