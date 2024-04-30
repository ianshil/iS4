Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import iS4_Syntax.
Require Import iS4H.
Require Import iS4H_logic.
Require Import iS4H_properties.
Require Import iS4_enum.


Section Sets_of_forms.

Definition SubTheory (Γ Δ : @Ensemble form) (Incl: Included _ Δ Γ) := forall φ, (iS4H_prv (Δ, φ) /\ In _ Γ φ) -> In _ Δ φ.

Definition restr_closed Γ Δ :=
  forall φ, iS4H_rules (Δ, φ) -> Γ φ -> Δ φ.

Definition prime (Γ : @Ensemble form) :=
  forall φ ψ, Γ (Or φ ψ) -> Γ φ \/ Γ ψ.

Definition quasi_prime (Γ : @Ensemble form) :=
  forall φ ψ, Γ (Or φ ψ) -> ~ ~ (Γ φ \/ Γ ψ).

End Sets_of_forms.








Section Prime.

Definition choice_form Γ Δ ψ φ: Ensemble form :=
fun x => (In _ Δ x) \/ ((In _ Γ x) /\ ~ (iS4H_prv ((Union _ Δ (Singleton _ x)), ψ)) /\ φ = x).

(* For any natural number, check if it is the encoding of a formula, and if it is and this
   formula happens to be a disjunction and derivable from the set, then pick one of the disjuncts. *)

Definition choice_code Γ Δ ψ (n :nat) : @Ensemble form := (choice_form Γ Δ ψ (form_enum n)).

Fixpoint nLind_theory Γ Δ ψ n : @Ensemble form :=
match n with
| 0 => choice_code Γ Δ ψ 0
| S m => choice_code Γ (nLind_theory Γ Δ ψ m) ψ (S m)
end.

Definition Lind_theory Γ Δ ψ : @Ensemble form :=
  fun x => (exists n, In _ (nLind_theory Γ Δ ψ n) x).

End Prime.









Section PrimeProps.

(* The Lindenbaum theory is an extension of the initial set of formulas. *)

Lemma nLind_theory_extens : forall n Γ Δ ψ φ,
    In _ Δ φ -> In _ (nLind_theory Γ Δ ψ n) φ.
Proof.
induction n.
- simpl. intros. unfold In. unfold choice_code. unfold choice_form. auto.
- simpl. intros. pose (IHn Γ Δ ψ φ H). unfold choice_code.
  unfold choice_form. simpl. unfold In ; auto.
Qed.

Lemma nLind_theory_extens_le : forall m n Γ Δ ψ φ,
    In _ (nLind_theory Γ Δ ψ n) φ -> (le n m) -> In _ (nLind_theory Γ Δ ψ m) φ.
Proof.
induction m.
- intros. simpl. inversion H0. subst. simpl in H. auto.
- intros. inversion H0.
  + subst. auto.
  + subst. simpl. unfold In. apply IHm in H ; auto. unfold choice_code.
     unfold choice_form. unfold In ; auto.
Qed.

Lemma Lind_theory_extens : forall Γ Δ ψ φ,
    In _ Δ φ -> In _ (Lind_theory Γ Δ ψ) φ.
Proof.
intros. unfold Lind_theory. unfold In. exists 0. unfold nLind_theory.
unfold choice_code. unfold choice_form ; auto.
Qed.

Lemma incl_nLind_theory : forall n Γ Δ ψ,
    Included _ Δ Γ ->
    Included _ (nLind_theory Γ Δ ψ n) Γ.
Proof.
induction n.
- simpl. intros. intros φ H0. unfold In in *.
  unfold choice_code in H0. unfold choice_form in H0. destruct H0 ; auto.
  apply H ; auto. destruct H0 ; auto.
- simpl. intros. intros φ H0. pose (IHn Γ Δ ψ H φ).
  unfold choice_code in H0. unfold choice_form in H0.
  destruct H0 ; auto. destruct H0 ; auto.
Qed.

Lemma incl_Lind_theory : forall Γ Δ ψ,
    Included _ Δ Γ ->
    Included _ (Lind_theory Γ Δ ψ) Γ.
Proof.
intros Γ Δ ψ H φ H0. unfold Lind_theory in H0. unfold In in *.
destruct H0. apply incl_nLind_theory in H0 ; auto.
Qed.

(* The Lindenbaum theory preserves derivability from the initial set of formulas. *)

Lemma der_nLind_theory_mLind_theory_le : forall n m Γ Δ ψ φ,
  (iS4H_rules (nLind_theory Γ Δ ψ n, φ)) -> (le n m) ->
    (iS4H_rules (nLind_theory Γ Δ ψ m, φ)).
Proof.
intros.
pose (iS4H_monot (nLind_theory Γ Δ ψ n, φ) H (nLind_theory Γ Δ ψ m)).
simpl in i. apply i. intro. intros. apply nLind_theory_extens_le with (n:=n) ; auto.
Qed.

Lemma der_Lind_theory_nLind_theory : forall s, (iS4H_rules s) ->
 (forall Γ Δ ψ φ, (Lind_theory Γ Δ ψ = fst s) ->
                                        (φ = snd s) ->
                                        (exists n, (iS4H_rules (nLind_theory Γ Δ ψ n, φ)))).
Proof.
intros s D. induction D ; intros.
- inversion H. subst. simpl in H0. subst. simpl. unfold Lind_theory in H2. destruct H2.
  exists x. apply Id. apply IdRule_I. auto.
- inversion H. subst. simpl in H0. subst. simpl. exists 0. apply Ax. apply AxRule_I.
  auto.
- inversion H1. subst. simpl in H2. subst.
  assert (J1: List.In (Lind_theory Γ Δ ψ, A --> B) [(Lind_theory Γ Δ ψ, A --> B); (Lind_theory Γ Δ ψ, A)]).
  apply in_eq. pose (H (Lind_theory Γ Δ ψ, A --> B) J1).
  assert (J2: List.In (Lind_theory Γ Δ ψ, A) [(Lind_theory Γ Δ ψ, A --> B); (Lind_theory Γ Δ ψ, A)]).
  apply in_cons. apply in_eq. pose (H (Lind_theory Γ Δ ψ, A) J2).
  assert (J3: Lind_theory Γ Δ ψ = Lind_theory Γ Δ ψ). auto.
  assert (J4: A --> B = A --> B). auto.
  pose (H0 (Lind_theory Γ Δ ψ, A --> B) J1 Γ Δ ψ (A --> B) J3 J4). destruct e. clear J4.
  clear i. clear J1.
  assert (J5: A = A). auto.
  pose (H0 (Lind_theory Γ Δ ψ, A) J2 Γ Δ ψ A J3 J5). destruct e. clear J5.
  clear J3. clear i0. clear J2.
  exists (max x x0). simpl.
  apply MP with (ps:=[(nLind_theory Γ Δ ψ (Init.Nat.max x x0), A --> B);(nLind_theory Γ Δ ψ (Init.Nat.max x x0), A)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  pose (der_nLind_theory_mLind_theory_le x (Init.Nat.max x x0) _ _ _ _ H2). apply i.
  lia. inversion H5. 2: inversion H6. subst. clear H4. clear H5.
    pose (der_nLind_theory_mLind_theory_le x0 (Init.Nat.max x x0) _ _ _ _ H3). apply i. lia.
- subst. inversion H1. subst. simpl in H2. subst.
  assert (J1: List.In (Empty_set (form), A) [(Empty_set (form), A)]). apply in_eq.
  pose (H (Empty_set (form), A) J1). simpl. exists 0. apply Nec with (ps:=[(Empty_set (form), A)]).
  2: apply NecRule_I. intros. inversion H2. subst. auto. inversion H3.
Qed.

(* Each step of the construction preserves underivability of the formula ψ. *)

Lemma Under_nLind_theory : forall n Γ Δ ψ,
  Included _ Δ Γ ->
  ~ (iS4H_prv (Δ, ψ)) ->
  ~ (iS4H_prv (nLind_theory Γ Δ ψ n, ψ)).
Proof.
induction n.
- intros Γ Δ ψ Incl H H0. apply H. unfold nLind_theory in H0. unfold choice_code in H0. unfold choice_form in H0.
  apply iS4H_monot with (Γ1:= Δ) in H0. simpl in H0 ; auto.
  simpl. intros a Ha. simpl in Ha. unfold In in Ha.
  destruct Ha ; auto. destruct H1 ; destruct H2 ; subst. exfalso. apply H2.
  assert ((fun x : form => In form Δ x \/ In form Γ x /\ ~ iS4H_prv (Union form Δ (Singleton form x), ψ) /\ form_enum 0 = x) = 
  Union form Δ (Singleton form (form_enum 0))). apply Extensionality_Ensembles.
  split ; intros b Hb ; unfold In in * ; auto. destruct Hb ; auto. apply Union_introl ; auto.
  destruct H3 ; destruct H4 ; auto. rewrite H5 ; apply Union_intror ; apply In_singleton.
  inversion Hb ; subst ; auto. inversion H3 ; subst ; auto. rewrite <- H3 ; auto.
- intros Γ Δ ψ Incl H. specialize (IHn _ _ _ Incl H). intro.
  apply iS4H_monot with (Γ1:=nLind_theory Γ Δ ψ n) in H0. simpl in H0. auto.
  intros a Ha. simpl in Ha. unfold choice_code in Ha.
  simpl in H0. unfold choice_code in H0. unfold In. unfold choice_form in Ha.
  unfold choice_form in H0. unfold In in Ha. destruct Ha ; auto.
  destruct H1 ; destruct H2 ; subst ; auto.
  assert ((fun x : form => In form (nLind_theory Γ Δ ψ n) x \/ In form Γ x /\ ~ iS4H_prv (Union form (nLind_theory Γ Δ ψ n) (Singleton form x), ψ) /\ form_enum (S n) = x) =
  Union form (nLind_theory Γ Δ ψ n) (Singleton form (form_enum (S n)))). apply Extensionality_Ensembles.
  split ; intros b Hb ; unfold In in * ; auto. destruct Hb ; auto. apply Union_introl ; auto.
  destruct H3 ; destruct H4 ; subst ; auto. apply Union_intror ; apply In_singleton.
  inversion Hb ; subst ; auto. inversion H3 ; subst ; auto. exfalso ; apply H2 ; rewrite <- H3 ; auto.
Qed.

(* The Lindenbaum theory does not derive ψ. *)

Lemma Under_Lind_theory: forall Γ Δ ψ,
  Included _ Δ Γ ->
  ~ iS4H_prv (Δ, ψ) ->
  ~ iS4H_prv (Lind_theory Γ Δ ψ, ψ).
Proof.
intros Γ Δ ψ Incl H H0.
epose (der_Lind_theory_nLind_theory _ H0). simpl in e.
assert (Lind_theory Γ Δ ψ = Lind_theory Γ Δ ψ). auto.
assert (ψ = ψ). auto.
pose (e _ _ _ _ H1 H2). destruct e0. clear e.
pose (Under_nLind_theory x _ _ _ Incl H). apply n. auto.
Qed.

(* The Lindenbaum theory is closed under derivation. *)

Lemma restr_closeder_Lind_theory : forall Γ Δ ψ,
  Included _ Δ Γ ->
  ~ iS4H_prv (Δ, ψ) ->
  restr_closed Γ (Lind_theory Γ Δ ψ).
Proof.
intros Γ Δ ψ Incl H. intros A H0. unfold Lind_theory. exists (form_index A). unfold In.
remember (form_index A) as n. unfold nLind_theory. pose (form_enum_index A). destruct n.
- unfold choice_form. right. repeat split ; auto.
  intro. pose (Under_Lind_theory _ _ _ Incl H). apply n.
  pose (iS4H_comp _ H2 (Lind_theory Γ Δ ψ)). simpl in i. apply i.
  intros. inversion H3 ; subst. apply Id. apply IdRule_I. exists 0 ; auto.
  simpl. unfold choice_code. unfold choice_form. unfold In ; auto.
  inversion H4 ; subst ; auto. rewrite <- Heqn in e. rewrite e ; auto.
- right. repeat split ; auto.
  intro. pose (Under_Lind_theory _ _ _ Incl H). apply n0.
  pose (iS4H_comp _ H2 (Lind_theory Γ Δ ψ)). simpl in i. apply i.
  intros. inversion H3 ; subst. apply Id. apply IdRule_I. exists (S n) ; auto.
  simpl. unfold choice_code. unfold choice_form. unfold In ; auto.
  inversion H4 ; subst ; auto. rewrite <- Heqn in e. rewrite e ; auto.
Qed.

(* Not in Lind_theory does not derive *)

Lemma not_In_Lind_theory_deriv : forall Γ Δ ψ,
  Included _ Δ Γ ->
  ~ iS4H_prv (Γ, ψ) ->
  forall A, Γ A -> ~ (Lind_theory Γ Δ ψ A) ->
    ~~ iS4H_prv (Union _ (Lind_theory Γ Δ ψ) (Singleton _ A), ψ).
Proof.
intros Γ Δ ψ Incl H A HA H0 H1. apply H0. exists (form_index A).
unfold nLind_theory. simpl. unfold In.
remember (form_index A) as n. pose (form_enum_index A). destruct n.
-  unfold choice_code. unfold choice_form. right ; repeat split ; auto. intro.
   apply iS4H_monot with (Γ1:=Union form (Lind_theory Γ Δ ψ) (Singleton form A)) in H2 ; auto.
   intro. simpl ; intros. inversion H3 ; subst. apply Union_introl. apply Lind_theory_extens ; auto.
   apply Union_intror. rewrite <- Heqn in e. auto.
   rewrite Heqn ; auto.
-  right ; repeat split ; auto.
  intro.
  apply iS4H_monot with (Γ1:=Union form (Lind_theory Γ Δ ψ) (Singleton form A)) in H2 ; auto.
  intro. simpl ; intros. inversion H3 ; subst. apply Union_introl.
  exists (S n) ; auto. simpl. unfold choice_code. unfold choice_form. left ; auto.
  apply Union_intror. auto.
  rewrite Heqn ; auto.
Qed.

(* The Lindenbaum theory is quasi-prime. *)

Lemma quasi_prime_Lind_theory: forall Γ Δ ψ,
  Included _ Δ (Clos Γ) ->
  ~ iS4H_prv (Δ, ψ) ->
  quasi_prime (Lind_theory (Clos Γ) Δ ψ).
Proof.
intros Γ Δ ψ Incl H0 a b Hor H1. remember (Clos Γ) as CΓ.

apply H1. left. exists (form_index a).
remember (form_index a) as n. destruct n ; simpl.
- unfold choice_code. unfold choice_form. unfold In.
  right. repeat split. 3: rewrite Heqn ; apply form_enum_index.
  subst. apply Incl_ClosSubform_Clos. exists (a ∨ b). split ; auto.
  apply incl_Lind_theory in Hor ; auto.
  simpl. right ; apply in_or_app ; left ; destruct a ; simpl ; auto.
  intro. apply H1. right. exists (form_index b).
  remember (form_index b) as m. destruct m ; simpl.
  + rewrite Heqm in Heqn. apply form_index_inj in Heqn.
     subst. exfalso.
     pose (Under_Lind_theory (Clos Γ) Δ ψ Incl H0). apply n.
    apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (Or a a) --> ψ);
    (Lind_theory (Clos Γ) Δ ψ, (Or a a))]). 2: apply MPRule_I. intros. inversion H2 ; subst.
    apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (a --> ψ) --> (Or a a --> ψ));
    (Lind_theory (Clos Γ) Δ ψ, (a --> ψ))]). 2: apply MPRule_I. intros. inversion H3 ; subst.
    apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (a --> ψ) --> (a --> ψ) --> (Or a a --> ψ));
    (Lind_theory (Clos Γ) Δ ψ, (a --> ψ))]). 2: apply MPRule_I. intros. inversion H4 ; subst.
    apply Ax. apply AxRule_I. left. apply IA5_I. exists a. exists a. exists ψ. auto.
    inversion H5 ; subst. 2: inversion H6.
    apply iS4H_Deduction_Theorem.
    apply iS4H_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form a)) in H ; auto.
    simpl ; intros c Hc. inversion Hc ; subst. apply Union_introl. apply Lind_theory_extens ; auto.
    inversion H6 ; subst ; apply Union_intror ; apply In_singleton.
    inversion H4 ; subst. 2: inversion H5.
    apply iS4H_Deduction_Theorem.
    apply iS4H_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form a)) in H ; auto.
    simpl ; intros c Hc. inversion Hc ; subst. apply Union_introl. apply Lind_theory_extens ; auto.
    inversion H5 ; subst ; apply Union_intror ; apply In_singleton.
    inversion H3 ; subst. 2: inversion H4. apply Id. apply IdRule_I ; auto.
  + subst. unfold choice_code. unfold choice_form. unfold In. right. repeat split.
     subst. apply Incl_ClosSubform_Clos. exists (a ∨ b). split ; auto.
     apply incl_Lind_theory in Hor ; auto.
     simpl. right ; apply in_or_app ; right ; destruct b ; simpl ; auto.
     2: rewrite Heqm ; apply form_enum_index. intro.
     pose (Under_Lind_theory (Clos Γ) Δ ψ Incl H0). apply n.
     apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (Or a b) --> ψ);
     (Lind_theory (Clos Γ) Δ ψ, (Or a b))]). 2: apply MPRule_I. intros. inversion H3 ; subst.
     apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (b --> ψ) --> (Or a b --> ψ));
     (Lind_theory (Clos Γ) Δ ψ, (b --> ψ))]). 2: apply MPRule_I. intros. inversion H4 ; subst.
     apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (a --> ψ) --> (b --> ψ) --> (Or a b --> ψ));
     (Lind_theory (Clos Γ) Δ ψ, (a --> ψ))]). 2: apply MPRule_I. intros. inversion H5 ; subst.
     apply Ax. apply AxRule_I. left. apply IA5_I. exists a. exists b. exists ψ. auto.
     inversion H6 ; subst. 2: inversion H7.
     apply iS4H_Deduction_Theorem.
     apply iS4H_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form a)) in H ; auto.
     simpl ; intros c Hc. inversion Hc ; subst. apply Union_introl. apply Lind_theory_extens ; auto.
     inversion H7 ; subst ; apply Union_intror ; apply In_singleton.
     inversion H5 ; subst. 2: inversion H6.
     apply iS4H_Deduction_Theorem.
     apply iS4H_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form b)) in H2 ; auto.
     simpl ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In. exists m ; auto.
     inversion H6 ; subst ; apply Union_intror ; apply In_singleton.
     inversion H4 ; subst. 2: inversion H5. apply Id. apply IdRule_I ; auto.
- unfold choice_code. unfold choice_form. unfold In.
  right. repeat split. 3: rewrite Heqn ; apply form_enum_index.
  subst. apply Incl_ClosSubform_Clos. exists (a ∨ b). split ; auto.
  apply incl_Lind_theory in Hor ; auto.
  simpl. right ; apply in_or_app ; left ; destruct a ; simpl ; auto.
  intro. apply H1. right. exists (form_index b).
  remember (form_index b) as m. destruct m ; simpl.
  + subst. unfold choice_code. unfold choice_form. unfold In. right. repeat split.
     subst. apply Incl_ClosSubform_Clos. exists (a ∨ b). split ; auto.
     apply incl_Lind_theory in Hor ; auto.
     simpl. right ; apply in_or_app ; right ; destruct b ; simpl ; auto.
     2: rewrite Heqm ; apply form_enum_index. intro.
     pose (Under_Lind_theory (Clos Γ) Δ ψ Incl H0). apply n0.
     apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (Or a b) --> ψ);
     (Lind_theory (Clos Γ) Δ ψ, (Or a b))]). 2: apply MPRule_I. intros. inversion H3 ; subst.
     apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (b --> ψ) --> (Or a b --> ψ));
     (Lind_theory (Clos Γ) Δ ψ, (b --> ψ))]). 2: apply MPRule_I. intros. inversion H4 ; subst.
     apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (a --> ψ) --> (b --> ψ) --> (Or a b --> ψ));
     (Lind_theory (Clos Γ) Δ ψ, (a --> ψ))]). 2: apply MPRule_I. intros. inversion H5 ; subst.
     apply Ax. apply AxRule_I. left. apply IA5_I. exists a. exists b. exists ψ. auto.
     inversion H6 ; subst. 2: inversion H7.
     apply iS4H_Deduction_Theorem.
     apply iS4H_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form a)) in H ; auto.
     simpl ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In ; exists n ; auto.
     inversion H7 ; subst ; apply Union_intror ; apply In_singleton.
     inversion H5 ; subst. 2: inversion H6.
     apply iS4H_Deduction_Theorem.
     apply iS4H_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form b)) in H2 ; auto.
     simpl ; intros c Hc. inversion Hc ; subst. apply Union_introl. apply Lind_theory_extens ; auto.
     inversion H6 ; subst ; apply Union_intror ; apply In_singleton.
     inversion H4 ; subst. 2: inversion H5. apply Id. apply IdRule_I ; auto.
  + subst. unfold choice_code. unfold choice_form. unfold In. right. repeat split.
     subst. apply Incl_ClosSubform_Clos. exists (a ∨ b). split ; auto.
     apply incl_Lind_theory in Hor ; auto.
     simpl. right ; apply in_or_app ; right ; destruct b ; simpl ; auto.
     2: rewrite Heqm ; apply form_enum_index. intro.
     pose (Under_Lind_theory (Clos Γ) Δ ψ Incl H0). apply n0.
     apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (Or a b) --> ψ);
     (Lind_theory (Clos Γ) Δ ψ, (Or a b))]). 2: apply MPRule_I. intros. inversion H3 ; subst.
     apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (b --> ψ) --> (Or a b --> ψ));
     (Lind_theory (Clos Γ) Δ ψ, (b --> ψ))]). 2: apply MPRule_I. intros. inversion H4 ; subst.
     apply MP with (ps:=[(Lind_theory (Clos Γ) Δ ψ, (a --> ψ) --> (b --> ψ) --> (Or a b --> ψ));
     (Lind_theory (Clos Γ) Δ ψ, (a --> ψ))]). 2: apply MPRule_I. intros. inversion H5 ; subst.
     apply Ax. apply AxRule_I. left. apply IA5_I. exists a. exists b. exists ψ. auto.
     inversion H6 ; subst. 2: inversion H7.
     apply iS4H_Deduction_Theorem.
     apply iS4H_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form a)) in H ; auto.
     simpl ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In. exists n ; auto.
     inversion H7 ; subst ; apply Union_intror ; apply In_singleton.
     inversion H5 ; subst. 2: inversion H6.
     apply iS4H_Deduction_Theorem.
     apply iS4H_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form b)) in H2 ; auto.
     simpl ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In. exists m ; auto.
     inversion H6 ; subst ; apply Union_intror ; apply In_singleton.
     inversion H4 ; subst. 2: inversion H5. apply Id. apply IdRule_I ; auto.
Qed.

(* The Lindenbaum theory is consistent. *)

Lemma Consist_nLind_theory : forall n Γ Δ ψ,
  Included _ Δ Γ ->
  ~ iS4H_prv (Δ, ψ) ->
  ~ iS4H_rules (nLind_theory Γ Δ ψ n, Bot).
Proof.
intros n Γ Δ ψ Incl H H0. pose (Under_nLind_theory n Γ Δ ψ Incl H).
apply n0.
apply MP with (ps:=[(nLind_theory Γ Δ ψ n, Bot --> ψ);(nLind_theory Γ Δ ψ n, Bot)]).
2: apply MPRule_I. intros. inversion H1 ; subst. apply EFQ. inversion H2 ; subst ; auto.
inversion H3.
Qed.

Lemma Consist_Lind_theory : forall Γ Δ ψ,
  Included _ Δ Γ ->
  ~ iS4H_prv (Δ, ψ) ->
  ~ iS4H_prv (Lind_theory Γ Δ ψ, Bot).
Proof.
intros Γ Δ ψ H H0 H1.
pose (Under_Lind_theory Γ Δ ψ H H0). apply n.
apply MP with (ps:=[(Lind_theory Γ Δ ψ, Bot --> ψ);(Lind_theory Γ Δ ψ, Bot)]).
2: apply MPRule_I. intros. inversion H2 ; subst. apply EFQ. inversion H3 ; subst ; auto.
inversion H4.
Qed.

End PrimeProps.




Section Lindenbaum_lemma.

(* Lindenbaum lemma. *)

Lemma Lindenbaum Γ Δ ψ :
  In _ (Clos Γ) ψ ->
  Included _ Δ (Clos Γ) ->
  ~ iS4H_prv (Δ, ψ) ->
  exists Δm, Included _ Δ Δm
           /\ Included _ Δm (Clos Γ)
           /\ restr_closed (Clos Γ) Δm
           /\ quasi_prime Δm
           /\ ~ iS4H_prv (Δm, ψ).
Proof.
intros.
exists (Lind_theory (Clos Γ) Δ ψ).
repeat split.
- intro. apply Lind_theory_extens.
- apply incl_Lind_theory ; auto.
- apply restr_closeder_Lind_theory ; auto.
- pose quasi_prime_Lind_theory ; auto.
- intro. apply Under_Lind_theory with (Γ:=(Clos Γ)) in H1 ; auto.
Qed.

End Lindenbaum_lemma.




