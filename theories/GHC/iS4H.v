Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Require Import general_export.

Require Import iS4_Syntax.

(* We define here the intuitionistic axioms. *)

Definition IA1 (A B : form) : form := A --> (B --> A).
Definition IA2 (A B C : form) : form := (A --> (B --> C)) --> ((A --> B) --> (A --> C)).
Definition IA3 (A B : form) : form := A --> (Or A B).
Definition IA4 (A B : form) : form := B --> (Or A B).
Definition IA5 (A B C : form) : form := (A --> C) --> ((B --> C) --> ((Or A B) --> C)).
Definition IA6 (A B : form) : form := (And A B) --> A.
Definition IA7 (A B : form) : form := (And A B) --> B.
Definition IA8 (A B C : form) : form := (A --> B) --> ((A --> C) --> (A --> (And B C))).
Definition IA9 (A : form) : form := Bot --> A.

Inductive IAxioms (A : form) : Prop :=
 | IA1_I : (exists B C, A = (IA1 B C)) -> IAxioms A
 | IA2_I : (exists B C D, A = (IA2 B C D)) -> IAxioms A
 | IA3_I :  (exists B C, A = (IA3 B C)) -> IAxioms A
 | IA4_I :  (exists B C, A = (IA4 B C)) -> IAxioms A
 | IA5_I : (exists B C D, A = (IA5 B C D)) -> IAxioms A
 | IA6_I :  (exists B C, A = (IA6 B C)) -> IAxioms A
 | IA7_I :  (exists B C, A = (IA7 B C)) -> IAxioms A
 | IA8_I : (exists B C D, A = (IA8 B C D)) -> IAxioms A
 | IA9_I : (exists B, A = (IA9 B)) -> IAxioms A.

(* We then define the modal axioms. *)

Definition MAK (A B : form) : form := Box (A --> B) --> (Box A --> Box B).
Definition MAT (A : form) : form := Box A --> A.
Definition MA4 (A : form) : form := Box A --> Box (Box A).

Inductive MAxioms (A : form) : Prop :=
 | MAK_I : (exists B  C, A = (MAK B C)) -> MAxioms A
 | MAT_I : (exists B, A = (MAT B)) -> MAxioms A
 | MA4_I :  (exists B, A = (MA4 B)) -> MAxioms A.

Definition Axioms (A : form) : Prop := IAxioms A \/ MAxioms A.

(* We can separately define the rules which constitute our calculus. 
   We gather them in a calculus in a definition appearing later. *)

Inductive IdRule : rls ((Ensemble form) * form) :=
  | IdRule_I : forall A (Γ : Ensemble _),
                  (In _ Γ A) -> IdRule [] (Γ , A).

Inductive AxRule : rls ((Ensemble form) * form) :=
  | AxRule_I : forall Γ (A : form),
          (Axioms A) -> AxRule [] (Γ , A).

Inductive MPRule : rls ((Ensemble form) * form) :=
  | MPRule_I : forall A B Γ,
          MPRule [(Γ , A --> B); (Γ , A)]
                    (Γ , B).

Inductive NecRule : rls ((Ensemble form) * form) :=
  | NecRule_I : forall (A : form) Γ,
          NecRule [(Empty_set form , A)]
                                     (Γ , Box A).

(* At last we can define our calculus iS4H. *)

Inductive iS4H_rules (s : ((Ensemble _) * form)) : Prop :=
  | Id : IdRule [] s -> iS4H_rules s
  | Ax : AxRule [] s -> iS4H_rules s
  | MP : forall ps, (forall prem, List.In prem ps -> iS4H_rules prem) -> MPRule ps s -> iS4H_rules s
  | Nec : forall ps, (forall prem, List.In prem ps -> iS4H_rules prem) -> NecRule ps s -> iS4H_rules s
.

(* Then, we define a macro for provability. *)

Definition iS4H_prv s := iS4H_rules s.
