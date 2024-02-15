Require Import List.
Export ListNotations.

Require Import PeanoNat.

Require Import Ensembles.
Require Import iS4_Syntax.
Require Import iS4H.

Lemma subst_Ax : forall A f, (Axioms A) -> (Axioms (subst f A)).
Proof.
intros A f Ax. destruct Ax. 
+ destruct H ; left.
  - destruct H. destruct H. subst. apply IA1_I.
    exists (subst f x). exists (subst f x0). reflexivity.
  - destruct H. destruct H. destruct H. subst. apply IA2_I.
    exists (subst f x). exists (subst f x0). exists (subst f x1). reflexivity.
  - destruct H. destruct H. subst. apply IA3_I.
    exists (subst f x). exists (subst f x0). reflexivity.
  - destruct H. destruct H. subst. apply IA4_I.
    exists (subst f x). exists (subst f x0). reflexivity.
  - destruct H. destruct H. destruct H. subst. apply IA5_I.
    exists (subst f x). exists (subst f x0). exists (subst f x1). reflexivity.
  - destruct H. destruct H. subst. apply IA6_I.
    exists (subst f x). exists (subst f x0). reflexivity.
  - destruct H. destruct H. subst. apply IA7_I.
    exists (subst f x). exists (subst f x0). reflexivity.
  - destruct H. destruct H. destruct H. subst. apply IA8_I.
    exists (subst f x). exists (subst f x0). exists (subst f x1). reflexivity.
  - destruct H. subst. apply IA9_I.
    exists (subst f x). reflexivity.
+ destruct H ; right.
  - destruct H. destruct H. subst. apply MAK_I.
    exists (subst f x). exists (subst f x0). reflexivity.
  - destruct H. subst. apply MAT_I. exists (subst f x). reflexivity.
  - destruct H. subst. apply MA4_I. exists (subst f x). reflexivity.
Qed.

Theorem iS4H_monot : forall s,
          (iS4H_prv s) ->
          (forall Γ1, (Included _ (fst s) Γ1) ->
          (iS4H_prv (Γ1, (snd s)))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros Γ1 incl. inversion H. subst. apply Id. apply IdRule_I. simpl. apply incl.
  assumption.
(* Ax *)
- intros Γ1 incl. inversion H. subst. apply Ax. apply AxRule_I. assumption.
(* MP *)
- intros Γ1 incl. inversion H1. subst. simpl. apply MP with (ps:=[(Γ1, A --> B); (Γ1, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1 Γ1). apply i. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 Γ1). apply i. auto. inversion H4. apply MPRule_I.
(* Nec *)
- intros Γ1 incl. inversion H1. subst. simpl. apply Nec with (ps:=[(Empty_set _, A)]).
  intros. inversion H2. subst. auto. inversion H3. apply NecRule_I.
Qed.

Theorem iS4H_comp : forall s,
          (iS4H_prv s) ->
          (forall Γ,  (forall A, ((fst s) A) -> iS4H_prv (Γ, A)) ->
          iS4H_prv (Γ, (snd s))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros Γ derall. inversion H. subst. pose (derall A). apply i. auto.
(* Ax *)
- intros Γ derall. inversion H. subst. apply Ax. apply AxRule_I. assumption.
(* MP *)
- intros Γ derall. inversion H1. subst. apply MP with (ps:=[(Γ, A --> B); (Γ, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ0, A --> B) [(Γ0, A --> B); (Γ0, A)]). apply in_eq.
  pose (H0 (Γ0, A --> B) J1 Γ). apply i. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ0, A) [(Γ0, A --> B); (Γ0, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ0, A) J2 Γ). apply i. auto. inversion H4. apply MPRule_I.
(* Nec *)
- intros Γ derall. inversion H1. subst. simpl. apply Nec with (ps:=[(Empty_set _, A)]).
  intros. inversion H2. subst. auto. inversion H3. apply NecRule_I.
Qed.

Theorem iS4H_struct : forall s,
          (iS4H_prv s) ->
          (forall (f : nat -> form),
          (iS4H_prv ((fun y => (exists A, prod ((fst s) A) (y = (subst f A)))), (subst f (snd s))))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros f. inversion H. subst. simpl. apply Id. apply IdRule_I.
  exists A. auto.
(* Ax *)
- intros f. inversion H. subst. apply Ax. apply AxRule_I. 
  apply subst_Ax with (f:=f). assumption.
(* MP *)
- intros f. inversion H1. subst. apply MP with (ps:=[((fun y : form =>
  exists A0 : form, prod (Γ A0) (y = subst f A0)), (subst f A) --> (subst f B)); ((fun y : form =>
  exists A0 : form, prod (Γ A0) (y = subst f A0)), (subst f A))]). simpl.
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1 f). apply i. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 f). apply i. auto. inversion H4. apply MPRule_I.
(* Nec *)
- intros f. inversion H1. subst. apply Nec with (ps:=[(Empty_set _, (subst f A))]).
  intros. inversion H2. subst. assert (J1: List.In (Empty_set form, A) [(Empty_set form, A)]). apply in_eq.
  pose (H0 (Empty_set form, A) J1 f). simpl in i.
  assert ((fun y : form => exists A : form,
  prod (Empty_set _ A) (y = subst f A)) = Empty_set _).
  { apply Extensionality_Ensembles. split. intro. intro. inversion H3. destruct H4.
    inversion e. intro. intro. inversion H3. } rewrite H3 in i. apply i. simpl. auto.
  inversion H3. apply NecRule_I.
Qed.

Theorem iS4H_finite : forall s,
          (iS4H_prv s) ->
          (exists (Γ : Ensemble _), prod (Included _ Γ (fst s))
                                     (prod (iS4H_prv (Γ, snd s))
                                     (exists (l : list form), (forall A, ((Γ A) -> List.In A l) * (List.In A l -> (Γ A)))))).
Proof.
intros s D0. induction D0.
(* Id *)
- inversion H. subst. simpl. exists (fun x => x = A).
  repeat split. intro. intro. unfold In. inversion H1. assumption.
  apply Id. apply IdRule_I. auto. unfold In. auto.
  exists [A]. intro. split. intro. subst. apply in_eq. intro. inversion H1.
  subst. auto. inversion H2.
(* Ax *)
- inversion H. subst. simpl. exists (Empty_set _).
  repeat split. intro. intro. unfold In. inversion H1.
  apply Ax. apply AxRule_I. auto.
  exists []. intro. split. intro. subst. inversion H1. intro. inversion H1.
(* MP *)
- inversion H1. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1). destruct e. destruct H2. destruct p. destruct e.
  assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). destruct e. destruct H3. destruct p. destruct e.
  exists (Union _ x x1). repeat split. intro. intro. simpl. inversion H4.
  subst. apply i. assumption. apply i1. assumption. simpl.
  apply MP with (ps:=[(Union _ x x1, A --> B); (Union _ x x1, A)]).
  intros. inversion H4. subst.
  assert (J3: Included _ (fst (x, A --> B)) (Union _ x x1)). intro. simpl. intro.
  apply Union_introl. assumption. pose (@iS4H_monot (x, A --> B) i0 (Union _ x x1) J3). assumption.
  inversion H5. subst. assert (J4: Included _ (fst (x1, A)) (Union _ x x1)). intro. simpl. intro.
  apply Union_intror. assumption. pose (@iS4H_monot (x1, A) i2 (Union _ x x1) J4). assumption.
  inversion H6. apply MPRule_I.
  exists (x0 ++ x2). intro. split. intro. inversion H4. subst. pose (H2 A0).
  destruct p. apply in_or_app. apply i3 in H5. auto. subst. pose (H3 A0).
  destruct p. apply i3 in H5. apply in_or_app. auto. intro. apply in_app_or in H4.
  destruct H4. apply Union_introl. apply H2. assumption. apply Union_intror.
  apply H3. assumption.
(* Nec *)
- inversion H1. subst. exists (Empty_set _). repeat split.
  intro. intro. simpl. inversion H2. apply Nec with (ps:=[(Empty_set _, A)]).
  assumption. apply NecRule_I. exists []. intro. split. intro. inversion H2.
  intro. inversion H2.
Qed.
