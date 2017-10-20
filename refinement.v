Require Export cd.

Require Export String ListSet List Arith Bool. 
Open Scope nat_scope.
Open Scope type_scope.
Open Scope string_scope.
Open Scope list_scope.
Import ListNotations.

Parameter R : Class -> Class -> Class -> list Assoc.
Parameter CA : Class -> Class -> assocKind -> Assoc.

Print AsEnd.

Definition CreateAsEnd (c : Class) :=
  BAsEnd "_" c (Nat 0) Star.

Print Assoc.

Definition CreateAssoc (n : NamedElement) (c1 c2 : Class) :=
  BAssoc n none (CreateAsEnd c1, CreateAsEnd c2).


Inductive refineone : SimpleUML -> SimpleUML -> Prop :=
| import:  forall c' ci cj C T P S G,
    not (set_In c' C) -> 
    set_In ci C /\ set_In cj C ->
    let C' := (c':: C) in
    let S' := set_union eqAssoc_dec (R ci cj c') S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
| dec1: forall c' ci C T P S G,
    not (set_In c' C) -> 
    set_In ci C ->
    let C' := (c':: C) in
    let G' := (BGen ci c') :: G in 
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S G')
| dec2 : forall c' ci C T P S G,
    not (set_In c' C) ->
    set_In ci C ->
    let C' := (c' :: C) in
    let S' := (CA c' ci composite) :: S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
| dec3 : forall c' ci C T P S G,
    not (set_In c' C) ->
    set_In ci C ->
    let C' := (c' :: C) in
    let S' := (CA c' ci aggregate) :: S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
| intro1 : forall c' ci C T P S G,
    not (set_In c' C) ->
    set_In ci C ->
    let C' := (c' :: C) in
    let S' := (CA c' ci none) :: S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
| intro2 : forall c' ci C T P S G,
    not (set_In c' C) ->
    set_In ci C ->
    let C' := (c' :: C) in
    let S' := (CA c' ci directed) :: S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
.


Inductive refine : SimpleUML -> SimpleUML -> Prop :=
| one : forall m1 m2, 
    refineone m1 m2 -> refine m1 m2
| reflex : forall m, 
    refine m m
| trans : forall m1 m2 m3, 
    refine m1 m2 -> refine m2 m3 -> refine m1 m3
.

Theorem wellFormed_preserve :
  forall m1 m2, WellFormed m1 -> refineone m1 m2 ->
           WellFormed m2.
Proof.
  intros m1 m2 H1 H2.
  inversion H1. unfold UniqueClass in H.
  inversion H2; subst; simpl in H.
Admitted.

Require Import Relations.

Theorem refine_refl :
   reflexive _  refine.
Proof.
  unfold reflexive. 
  intro x. apply reflex.
Qed.


Theorem refine_trans :
  transitive _ refine.
Proof.
  unfold transitive.
  intros x y z. apply trans.
Qed.


Theorem class_preserve :
  forall c m1 m2, 
    refineone m1 m2 ->
    set_In c (MClass_Instance m1) ->
    set_In c (MClass_Instance m2).
Proof.
  intros c m1 m2 H.
  induction H; intros H1; simpl;
    simpl in H1; right; assumption.
Qed.


Theorem gen_preserve :
  forall sub super m1 m2, 
    refineone m1 m2 ->
    set_In (BGen super sub) (MGen_Instance m1) ->
    set_In (BGen super sub) (MGen_Instance m2).
Proof.
  intros sub super m1 m2 H.
  induction H; intros H1; simpl in H1; simpl; try assumption.
  - right; assumption.
Qed.