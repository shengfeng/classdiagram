Require Export cd.
Require Export od.

Print NamedElement.
Require Import Coq.Lists.List.
Import ListNotations.

(* named element *)
Definition EleState : NamedElement := 
  BNamedElement 0 "State".
Definition EleInitState : NamedElement := 
  BNamedElement 1 "InitState".
Definition EleTransition : NamedElement := 
  BNamedElement 2 "Transition".
Definition EleFinalState : NamedElement :=
  BNamedElement 3 "FinalState".

Definition EleIsActive : NamedElement :=
  BNamedElement 4 "isActive".
Definition EleLabel : NamedElement :=
  BNamedElement 5 "label".

Definition EleString : NamedElement :=
  BNamedElement 6 "String".
Definition EleBoolean : NamedElement :=
  BNamedElement 7 "Boolean".

Definition EleOutTransition : NamedElement :=
  BNamedElement 8 "OutTransition".
Definition EleInTransition : NamedElement :=
  BNamedElement 9 "InTransition".

(* classifier *)
Definition CString : Classifier := 
  BClassifier EleString.
Definition CBoolean : Classifier := 
  BClassifier EleBoolean.
Definition CInitState : Classifier := 
  BClassifier EleInitState.
Definition CState : Classifier := 
  BClassifier EleState.
Definition CTransition : Classifier := 
  BClassifier EleTransition.
Definition CFinalState : Classifier := 
  BClassifier EleFinalState.

(* types *)

Definition DString := 
  BDataType CString.
Definition DBoolean :=
  BDataType CBoolean.

(* attribute and class *)
Definition isActive : Attribute := 
  BAttribute EleIsActive CBoolean.
Definition label : Attribute := 
  BAttribute EleLabel CString.

Definition State : Class := 
  BClass CState true [isActive].
Definition Transition : Class := 
  BClass CTransition false [label].
Definition InitState : Class := 
  BClass CInitState false [].
Definition FinalState : Class := 
  BClass CFinalState false [].

(* generalization *)
Definition State_InitState : Gen := 
  BGen State InitState.

Definition State_FinalState : Gen :=
  BGen State FinalState.

(* association end*)
Definition source : AsEnd := 
  BAsEnd "source" State (Nat 1) (Nat 1).
Definition out : AsEnd := 
  BAsEnd "out" Transition Star Star.

Definition target : AsEnd :=
  BAsEnd "target" State Star Star.
Definition tin : AsEnd :=
  BAsEnd "in" Transition Star Star.

(* association *)
Definition outTransition : Assoc := 
  BAssoc EleOutTransition none (source, out).
Definition inTransition : Assoc :=
  BAssoc EleInTransition none (target, tin).

(* record *)

Print SimpleUML.

Definition auto : SimpleUML := mkSimpleUML 
    [State;InitState;Transition;FinalState]
    [isActive;label]
    [DString; DBoolean]
    [outTransition;inTransition]
    [State_InitState;State_FinalState].

(* proof *)

Print UniqueClass.
Print List.NoDup.
(*
Inductive NoDup (A : Type) : list A -> Prop :=
  NoDup_nil : List.NoDup [] 
| NoDup_cons : forall (x : A) (l : list A), ~ List.In x l -> List.NoDup l -> List.NoDup (x :: l)
*)

Lemma auto_unique_class:
  UniqueClass auto.
Proof.
  unfold UniqueClass. unfold auto; simpl.
  apply List.NoDup_cons. 
  simpl; intros contra.
  destruct contra; inversion H.
  inversion H0.
  inversion H0.
  inversion H1.
  apply H1.

  apply List.NoDup_cons. 
  simpl; intros contra.
  destruct contra; inversion H.
  inversion H0.
  apply H0.

  apply List.NoDup_cons. 
  simpl; intros contra.
  destruct contra; inversion H.

  apply List.NoDup_cons.
  simpl; intros contra.
  inversion contra.
  apply List.NoDup_nil.
Qed.


(* object *)
Definition s1 : Object := BObject "s1".
Definition s2 : Object := BObject "s2".
Definition s3 : Object := BObject "s3".
Definition a : Object := BObject "a".
Definition b : Object := BObject "b".
Definition c : Object := BObject "c".

Definition r1 : Link := BLink "r1".
Definition r2 : Link := BLink "r2".
Definition r3 : Link := BLink "r3".
Definition r4 : Link := BLink "r4".
Definition r5 : Link := BLink "r5".
Definition r6 : Link := BLink "r6".


Print VObject.
Open Scope type_scope.

Definition o1 : VObject := (InitState, [s1]).
Definition o2 : VObject := (State, [s1;s2;s3]). 
Definition o3 : VObject := (FinalState, [s3]).
Definition o4 : VObject := (Transition, [a;b;c]).


Definition l1 : VLink := (inTransition, [r1;r3;r5]).
Definition l2 : VLink := (outTransition, [r2;r4;r6]).

Definition e1 : VEnd := (r1, s1, a).
Definition e2 : VEnd := (r2, a, s2).
Definition e3 : VEnd := (r3, s2, c).
Definition e4 : VEnd := (r4, c, s3).
Definition e5 : VEnd := (r5, s2, b).
Definition e6 : VEnd := (r6, b, s2).


Definition st :=
  mkState
    [s1; s2; s3; a; b; c]
    [r1; r2; r3; r4; r5; r6]
    [o1; o2; o3; o4]
    [l1; l2]
    [e1; e2; e3; e4; e5; e6].

Check st.

Theorem proof_test :
  Sat_class InitState st.
Proof.
  unfold Sat_class, st.
  simpl. left; auto.
Qed.

Theorem classes_satisfaction:
  forall c: Class, In c (MClass_Instance auto) ->
  Sat_class c st.
Proof.
  intros. simpl in H.
  unfold Sat_class, st.
  inversion H; subst; clear H. 
  - simpl. auto.
  - inversion H0; subst; clear H0; simpl; auto.
    inversion H; subst; clear H; simpl; auto.
    inversion H0; subst; clear H0; simpl; auto.
Qed.

Eval simpl in ((mapObject (Gen_dest State_InitState) (vobjects st))).
Eval simpl in ((mapObject (Gen_src State_InitState) (vobjects st))).


Print Sat_gen.
Theorem proof_test2 :
  Sat_gen State_InitState st.
Proof.
  unfold Sat_gen, st.
  simpl. intros.
  destruct H; auto.
Qed.

Theorem gen_satisfaction:
    forall g: Gen, In g (MGen_Instance auto) ->
    Sat_gen g st.
Proof.
  intros. simpl in H.
  unfold Sat_gen, st.
  inversion H; subst; clear H. 
  - intros. simpl in *.
    destruct H; auto.
  - intros. destruct H0. rewrite <- H0 in *.
    simpl in *. auto. inversion H0.
Qed.


Compute (mapLink inTransition (vlinks st)).
Compute (links_objects_dest (mapLink inTransition (vlinks st)) (vends st)).

Lemma proof_test4 :
  Sat_assoc1 inTransition st.
Proof.
  unfold Sat_assoc1, st.
  simpl; intros.

  destruct H.
  unfold VEnd_src, e1 in H. simpl in H.
  left; assumption.

  destruct H.
  unfold VEnd_src, e2 in H. simpl in H.
  right. left; assumption.

  destruct H.
  unfold VEnd_src, e5 in H. simpl in H.
  right. left; assumption.

  auto.
Qed.

Lemma proof_test5 :
  Sat_assoc2 inTransition st.
Proof.
  unfold Sat_assoc2, st.
  simpl; intros.

  destruct H.
  left; assumption.

  destruct H.
  do 2 right. left. assumption.

  destruct H.
  right. left; assumption.

  auto.
Qed.


(* ----- refinement ------ *)
Definition EleExitAction : NamedElement := 
  BNamedElement 11 "ExitAction".
Definition EleEntryAction : NamedElement := 
  BNamedElement 12 "EntryAction".
Definition EleAction : NamedElement := 
  BNamedElement 13 "Action".
Definition EleAssocExitAction : NamedElement :=
  BNamedElement 14 "exit_Action".
Definition EleAssocEntryAction : NamedElement :=
  BNamedElement 15 "entry_Action".

Definition CExitAction : Classifier :=
  BClassifier EleExitAction.
Definition CEntryAction: Classifier :=
  BClassifier EleEntryAction.
Definition CAction : Classifier :=
  BClassifier EleAction.

Definition ExitAction : Class := 
  BClass CExitAction false [].
Definition Action : Class :=
  BClass CAction true [].
Definition EntryAction : Class :=
  BClass CEntryAction false [].

Definition rstate: AsEnd := 
  BAsEnd "state" State (Nat 1) Star.
Definition exitAction : AsEnd :=
  BAsEnd "exitAction" ExitAction (Nat 1) (Nat 1).
Definition exit_Action : Assoc :=
  BAssoc EleAssocExitAction none (rstate,exitAction).

Definition rstate2 : AsEnd :=
  BAsEnd "state" State (Nat 1) Star.
Definition entryAction : AsEnd :=
  BAsEnd "entryAction" EntryAction (Nat 1) (Nat 1).
Definition entry_Action : Assoc :=
  BAssoc EleAssocEntryAction none (rstate2,entryAction).

Definition Action_ExitAction :=
  BGen Action ExitAction.
Definition Action_EntryAction :=
  BGen Action EntryAction.

Definition auto3 : SimpleUML := mkSimpleUML
  [State;InitState;FinalState;Transition;ExitAction;EntryAction;Action]
  [isActive;label]
  [DString;DBoolean]
  [outTransition;inTransition;exit_Action;entry_Action]
  [State_InitState;State_FinalState;Action_EntryAction;Action_ExitAction].

