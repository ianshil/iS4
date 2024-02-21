Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Declare Scope My_scope.
Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

(* Definitions Language *)

(* First, let us define the propositional formulas we use here. *)

Inductive form : Type :=
 | Var : nat -> form
 | Bot : form
 | And : form -> form -> form
 | Or : form -> form -> form
 | Imp : form -> form -> form
 | Box : form -> form.

(* We define negation. *)

Definition Neg (A : form) := Imp A (Bot).
Definition Top := Imp Bot Bot.

(* We use the following notations for modal formulas. *)

Notation "# p" := (Var p) (at level 1) : My_scope.
Notation "A --> B" := (Imp A B) (at level 16, right associativity) : My_scope.
Notation "A ∨ B" := (Or A B) (at level 16, right associativity) : My_scope.
Notation "A ∧ B" := (And A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.
Notation "¬ A" := (A --> ⊥) (at level 42) : My_scope.

(* Next, we define the set of subformulas of a formula, and
    extend this notion to lists of formulas. *)

Fixpoint subform (φ : form) : Ensemble form :=
match φ with
| Var p => Singleton _ (Var p)
| Bot => Singleton _ Bot
| ψ ∧ χ => Union _ (Singleton _ (ψ ∧ χ)) (Union _ (subform ψ) (subform χ))
| ψ ∨ χ => Union _ (Singleton _ (ψ ∨ χ)) (Union _ (subform ψ) (subform χ))
| ψ --> χ => Union _ (Singleton _ (ψ --> χ)) (Union _ (subform ψ) (subform χ))
| Box ψ => Union _ (Singleton _ (Box ψ)) (subform ψ)
end.

Fixpoint subformlist (φ : form) : list form :=
match φ with
| Var p => (Var p) :: nil
| Bot => [Bot]
| ψ ∧ χ => (ψ ∧ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ ∨ χ => (ψ ∨ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ --> χ => (Imp ψ χ) :: (subformlist ψ) ++ (subformlist χ)
| Box ψ => (Box ψ) :: (subformlist ψ)
end.

Lemma subform_trans : forall φ ψ χ, List.In φ (subformlist ψ) ->
  List.In χ (subformlist φ) -> List.In χ (subformlist ψ).
Proof.
intros φ ψ χ. revert ψ χ φ. induction ψ.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
  apply in_app_or in H ; destruct H. right. apply in_or_app ; left.
  apply IHψ1 with (φ:=φ) ; auto. right. apply in_or_app ; right.
  apply IHψ2 with (φ:=φ) ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
  apply in_app_or in H ; destruct H. right. apply in_or_app ; left.
  apply IHψ1 with (φ:=φ) ; auto. right. apply in_or_app ; right.
  apply IHψ2 with (φ:=φ) ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
  apply in_app_or in H ; destruct H. right. apply in_or_app ; left.
  apply IHψ1 with (φ:=φ) ; auto. right. apply in_or_app ; right.
  apply IHψ2 with (φ:=φ) ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto. right.
  apply IHψ with (φ:=φ) ; auto.
Qed.

Lemma eq_dec_form : forall x y : form, {x = y}+{x <> y}.
Proof.
repeat decide equality.
Qed.

Fixpoint subst (σ : nat -> form) (φ : form) : form :=
match φ with
| # p => (σ p)
| Bot => Bot
| ψ ∧ χ => (subst σ ψ) ∧ (subst σ χ)
| ψ ∨ χ => (subst σ ψ) ∨ (subst σ χ)
| ψ --> χ => (subst σ ψ) --> (subst σ χ)
| Box ψ => Box (subst σ ψ)
end.

Fixpoint list_Imp (A : form) (l : list form) : form :=
match l with
 | nil => A
 | h :: t => h --> (list_Imp A t)
end.

Definition Box_list (l : list form) : list form := map Box l.

Lemma In_form_dec : forall l (A : form), {List.In A l} + {List.In A l -> False}.
Proof.
induction l ; simpl ; intros ; auto.
destruct (IHl A) ; auto.
destruct (eq_dec_form a A) ; auto.
right. intro. destruct H ; auto.
Qed.

Definition BoxOne φ : form :=
  match φ with
  | Box ψ => Box ψ
  | _ => Box φ
  end.

Definition BoxTwo φ : form :=
  match φ with
  | Box ψ => match ψ with
                   | Box χ => φ
                   | _ => Box φ
                   end
  | _ => Box (Box φ)
  end.

Definition UnBox φ : form :=
  match φ with
  | Box ψ => ψ
  | _ => φ
  end.

Definition ClosOneBox Γ : Ensemble form := Union _ Γ (fun φ => exists ψ, In _ Γ ψ /\ φ = BoxOne ψ).

Definition ClosTwoBox Γ : Ensemble form := Union _ Γ (fun φ => exists ψ, In _ Γ ψ /\ φ = BoxTwo ψ).

Definition ClosOneTwoBox Γ : Ensemble form :=
  Union _ Γ (Union _ (fun φ => exists ψ, In _ Γ ψ /\ φ = BoxOne ψ) (fun φ => exists ψ, In _ Γ ψ /\ φ = BoxTwo ψ)).

Definition ClosSubform Γ : Ensemble form := fun φ => exists ψ, In _ Γ ψ /\ List.In φ (subformlist ψ).

Definition Clos Γ : Ensemble form := ClosOneTwoBox (ClosSubform Γ).

Definition Clos' Γ : Ensemble form := ClosOneBox (ClosSubform Γ).

Lemma Incl_Set_ClosSubform : forall Γ, Included _ Γ (ClosSubform Γ).
Proof.
intros Γ φ Hφ. unfold In. exists φ ; split ; auto. destruct φ ; simpl ; auto.
Qed.

Lemma Incl_ClosSubform_Clos : forall Γ, Included _ (ClosSubform (Clos Γ)) (Clos Γ).
Proof.
intros Γ φ Hφ. unfold In in *. unfold Clos in *. unfold ClosOneTwoBox in *.
unfold ClosSubform in *. destruct Hφ. destruct H. unfold In in H. inversion H.
- subst. inversion H1. destruct H2. apply Union_introl. unfold In. exists x0. split ; auto.
  apply subform_trans with (φ:=x) ; auto.
- subst. unfold In in H1. inversion H1 ; subst.
  + unfold In in H2. destruct H2. destruct H2 ; subst. destruct H2. destruct H2 ; subst.
     destruct x0 ; simpl in * ; destruct H0 ; auto.
     apply Union_intror. unfold In. apply Union_introl. unfold In. exists (# n).
     split ; auto. exists x ; auto. destruct H0 ; subst.
     apply Union_introl. unfold In. exists x ; auto. inversion H0.
     apply Union_intror. unfold In. apply Union_introl. unfold In. exists Bot.
     split ; auto. exists x ; auto. destruct H0 ; subst.
     apply Union_introl. unfold In. exists x ; auto. inversion H0.
     apply Union_intror. unfold In. apply Union_introl. unfold In. exists (x0_1 ∧ x0_2).
     split ; auto. exists x ; auto. destruct H0 ; subst.
     apply Union_introl. unfold In. exists x ; auto.
     apply Union_introl. unfold In. exists x ; split ; auto.
     apply subform_trans with (φ:=x0_1 ∧ x0_2) ; auto. simpl ; auto.
     apply Union_intror. unfold In. apply Union_introl. unfold In. exists (x0_1 ∨ x0_2).
     split ; auto. exists x ; auto. destruct H0 ; subst.
     apply Union_introl. unfold In. exists x ; auto.
     apply Union_introl. unfold In. exists x ; split ; auto.
     apply subform_trans with (φ:=x0_1 ∨ x0_2) ; auto. simpl ; auto.
     apply Union_intror. unfold In. apply Union_introl. unfold In. exists (x0_1 --> x0_2).
     split ; auto. exists x ; auto. destruct H0 ; subst.
     apply Union_introl. unfold In. exists x ; auto.
     apply Union_introl. unfold In. exists x ; split ; auto.
     apply subform_trans with (φ:=x0_1 --> x0_2) ; auto. simpl ; auto.
     apply Union_intror. unfold In. apply Union_introl. unfold In. exists (Box x0).
     split ; auto. exists x ; auto.
     apply Union_introl. unfold In. exists x ; split ; auto.
     apply subform_trans with (φ:=Box x0) ; auto. simpl ; auto.
  + unfold In in H2. destruct H2. destruct H2 ; subst. destruct H2. destruct H2 ; subst.
     destruct x0 ; simpl in *. 1-5: destruct H0 ; subst ; auto.
     destruct H0 ; subst. apply Union_intror. unfold In. apply Union_introl. unfold In. exists (# n).
     split ; auto. exists x ; auto. destruct H0 ; subst. 2: inversion H0.
     apply Union_introl. unfold In. exists x ; auto.
     destruct H0 ; subst. apply Union_intror. unfold In. apply Union_introl. unfold In. exists Bot.
     split ; auto. exists x ; auto. destruct H0 ; subst. 2: inversion H0.
     apply Union_introl. unfold In. exists x ; auto.
     destruct H0 ; subst. apply Union_intror. unfold In. apply Union_introl. unfold In. exists (x0_1 ∧ x0_2).
     split ; auto. exists x ; auto. destruct H0 ; subst.
     apply Union_introl. unfold In. exists x ; auto.
     apply Union_introl. unfold In. exists x ; split ; auto.
     apply subform_trans with (φ:=x0_1 ∧ x0_2) ; auto. simpl ; auto.
     destruct H0 ; subst. apply Union_intror. unfold In. apply Union_introl. unfold In. exists (x0_1 ∨ x0_2).
     split ; auto. exists x ; auto. destruct H0 ; subst.
     apply Union_introl. unfold In. exists x ; auto.
     apply Union_introl. unfold In. exists x ; split ; auto.
     apply subform_trans with (φ:=x0_1 ∨ x0_2) ; auto. simpl ; auto.
     destruct H0 ; subst. apply Union_intror. unfold In. apply Union_introl. unfold In. exists (x0_1 --> x0_2).
     split ; auto. exists x ; auto. destruct H0 ; subst.
     apply Union_introl. unfold In. exists x ; auto.
     apply Union_introl. unfold In. exists x ; split ; auto.
     apply subform_trans with (φ:=x0_1 --> x0_2) ; auto. simpl ; auto.
     { destruct x0  ; simpl in *. 1-5: destruct H0 ; subst ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=(Box # n)) ; auto. simpl ; auto. inversion H0.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=(Box Bot)) ; auto. simpl ; auto. inversion H0.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=(Box (x0_1 ∧ x0_2))) ; auto. simpl ; auto.
       apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=(Box (x0_1 ∧ x0_2))) ; auto. simpl ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=(Box (x0_1 ∨ x0_2))) ; auto. simpl ; auto.
       apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=(Box (x0_1 ∨ x0_2))) ; auto. simpl ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=(Box (x0_1 --> x0_2))) ; auto. simpl ; auto.
       apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=(Box (x0_1 --> x0_2))) ; auto. simpl ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; auto.
       destruct H0 ; subst. apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=Box (Box x0)) ; auto. simpl ; auto.
       apply Union_introl. unfold In. exists x ; split ; auto.
       apply subform_trans with (φ:=Box (Box x0)) ; auto. simpl ; auto. }
Qed.

Lemma Incl_ClosSubform_Clos' : forall Γ, Included _ (ClosSubform (Clos' Γ)) (Clos' Γ).
Proof.
intros Γ φ Hφ. unfold In in *. unfold Clos' in *. unfold ClosOneBox in *.
unfold ClosSubform in *. destruct Hφ. destruct H. unfold In in H. inversion H.
- subst. inversion H1. destruct H2. apply Union_introl. unfold In. exists x0. split ; auto.
  apply subform_trans with (φ:=x) ; auto.
- subst. unfold In in H1. inversion H1 ; subst.
  unfold In in H2. destruct H2. destruct H2 ; subst. destruct H2.
  destruct x0 ; simpl in * ; destruct H0 ; auto.
  apply Union_intror. unfold In. exists (# n).
  split ; auto. exists x1 ; auto. destruct H0 ; subst.
  apply Union_introl. unfold In. exists x1 ; auto. inversion H0.
  apply Union_intror. unfold In. exists Bot.
  split ; auto. exists x1 ; auto. destruct H0 ; subst.
  apply Union_introl. unfold In. exists x1 ; auto. inversion H0.
  apply Union_intror. unfold In. exists (x0_1 ∧ x0_2).
  split ; auto. exists x1 ; auto. destruct H0 ; subst.
  apply Union_introl. unfold In. exists x1 ; auto.
  apply Union_introl. unfold In. exists x1 ; split ; auto.
  apply subform_trans with (φ:=x0_1 ∧ x0_2) ; auto. simpl ; auto.
  apply Union_intror. unfold In. exists (x0_1 ∨ x0_2).
  split ; auto. exists x1 ; auto. destruct H0 ; subst.
  apply Union_introl. unfold In. exists x1 ; auto.
  apply Union_introl. unfold In. exists x1 ; split ; auto.
  apply subform_trans with (φ:=x0_1 ∨ x0_2) ; auto. simpl ; auto.
  apply Union_intror. unfold In. exists (x0_1 --> x0_2).
  split ; auto. exists x1 ; auto. destruct H0 ; subst.
  apply Union_introl. unfold In. exists x1 ; auto.
  apply Union_introl. unfold In. exists x1 ; split ; auto.
  apply subform_trans with (φ:=x0_1 --> x0_2) ; auto. simpl ; auto.
  apply Union_intror. unfold In. exists (Box x0).
  split ; auto. exists x1 ; auto.
  apply Union_introl. unfold In. exists x1 ; split ; auto.
 apply subform_trans with (φ:=Box x0) ; auto. simpl ; auto.
Qed.

Lemma Box_UnBox_BoxOne_id : forall l, map Box (map UnBox (map BoxOne l)) = map BoxOne l.
Proof.
induction l ; simpl ; intuition.
destruct a ; simpl ; subst ; auto. 1-5: rewrite IHl ; auto.
destruct a ; simpl ; auto. 1-6: rewrite IHl ; auto.
Qed.

Lemma Box_UnBox_BoxTwo_id : forall l, map Box (map UnBox (map BoxTwo l)) = map BoxTwo l.
Proof.
induction l ; simpl ; intuition.
destruct a ; simpl ; subst ; auto. 1-5: rewrite IHl ; auto.
destruct a ; simpl ; auto. 1-6: rewrite IHl ; auto.
Qed.

Lemma UnBox_BoxOne : forall φ, BoxOne φ = Box (UnBox φ).
Proof.
induction φ ; simpl ; auto.
Qed.

Lemma UnBox_BoxTwo : forall φ, BoxTwo φ = Box (Box (UnBox (UnBox φ))).
Proof.
induction φ ; simpl ; auto.
destruct φ ; simpl ; auto.
Qed.

Lemma BoxOne_UnBox_fixpoint : forall φ, BoxOne φ = Box (UnBox (BoxOne φ)).
Proof.
induction φ ; simpl ; auto.
Qed.

Lemma BoxTwo_UnBox_fixpoint : forall φ, BoxTwo φ = Box (UnBox (BoxTwo φ)).
Proof.
induction φ ; simpl ; auto.
destruct φ ; simpl ; auto.
Qed.

Lemma In_Clos_not_box : forall Γ φ, ((exists ψ, φ = Box ψ) -> False) -> (Clos Γ) φ -> (ClosSubform Γ) φ.
Proof.
intros. destruct H0 ; auto. destruct H0 ; auto. destruct H0. destruct H0 ; subst.
exfalso. apply H. exists (UnBox x0). apply UnBox_BoxOne. destruct H0.
destruct H0 ; subst. exfalso ; apply H. exists (Box (UnBox (UnBox x0))).
apply UnBox_BoxTwo.
Qed.

Lemma In_Clos'_not_box : forall Γ φ, ((exists ψ, φ = Box ψ) -> False) -> (Clos' Γ) φ -> (ClosSubform Γ) φ.
Proof.
intros. destruct H0 ; auto. destruct H0 ; auto. destruct H0. destruct H0 ; subst.
exfalso. apply H. exists (UnBox x0). apply UnBox_BoxOne.
Qed.

Lemma In_Clos_BoxTwo : forall Γ φ, (Clos Γ) φ -> (Clos Γ) (BoxTwo φ).
Proof.
induction φ.
1-5: intros ; apply Union_intror ; apply Union_intror ; eexists ; split ; auto ; apply In_Clos_not_box ; auto.
1-5: intro H0 ; destruct H0 ; inversion H0.
intros. destruct φ ; simpl in * ; auto.
1-5: apply IHφ ; apply Incl_ClosSubform_Clos.
exists (Box (# n)). simpl ; split ; auto.
exists (Box Bot). simpl ; split ; auto.
exists (Box (φ1 ∧ φ2)). simpl ; split ; auto.
exists (Box (φ1 ∨ φ2)). simpl ; split ; auto.
exists (Box (φ1 --> φ2)). simpl ; split ; auto.
Qed.

Lemma In_Clos'_BoxOne : forall Γ φ, (Clos' Γ) φ -> (Clos' Γ) (BoxOne φ).
Proof.
induction φ.
1-5: intros ; apply Union_intror ; eexists ; split ; auto ; apply In_Clos'_not_box ; auto.
1-5: intro H0 ; destruct H0 ; inversion H0.
intros. destruct φ ; simpl in * ; auto.
Qed.



