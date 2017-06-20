(** @Name Formalization of class diagrams
    @version 1.1
    @domains 
    @authors Feng sheng 
    @date 30/03/2017
    @description class and object diagrams (Coq v8.2)
**)

Require Import List.
Require Import String.
Require Import ListSet.
Require Import Arith.
Require Import Nat.
Require Import Peano_dec.

Import ListNotations.

Open Scope list_scope.

(** ##### the structute of metamodel of class diagram #### **)
(** ----- basic element ----- **)
Inductive NamedElement : Set :=
| BNamedElement (oid: nat) (name : string).

(** ----- classifier ----- **)
Inductive Classifier : Set :=
| BClassifier (super : NamedElement).

(** ----- operation ----- **)
Inductive Operation : Set :=
| BOperation : NamedElement -> list string -> Operation.

(** ----- attribute, primitive data type, class ----- **)
Inductive Attribute : Set :=
| BAttribute (super : NamedElement) (type : Classifier)
with DataType : Set :=
| BDataType (super : Classifier)
with Class : Set :=
| BClass (super : Classifier) (abstract : bool) (attribute : list Attribute).

(** ----- generalization ----- **)
Inductive Gen : Set :=
| BGen (super : Class) (sub : Class).

(** ----- association end ----- **)
Inductive Natural :=
| Nat : nat -> Natural
| Star : Natural.

Inductive AsEnd : Set :=
| BAsEnd (name:string) (attached:Class) (lower: Natural) (upper: Natural).

(** ----- association ----- **)
Inductive assocKind : Set :=
| none : assocKind       | directed : assocKind
| aggregate : assocKind  | composite : assocKind.

Inductive Assoc : Set :=
| BAssoc: NamedElement -> assocKind -> (AsEnd * AsEnd) -> Assoc.

Inductive AlterAssoc : Set :=
| BAAssoc (super : NamedElement) (kind: assocKind) (ends: AsEnd * AsEnd).

(** ------------------------------- **)
(** -------- Source Model --------- **)
Record SimpleUML : Set :=
  mkSimpleUML {
      MClass_Instance : list Class;
      MAttr_Instance : list Attribute;
      MDataType_Instance : list DataType;
      MAssoc_Instance : list Assoc;
      MGen_Instance : list Gen
    }.


Definition eqClassifier_dec : forall x y: Classifier, {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Definition beqClassifier c c' :=
  match eqClassifier_dec c c' with
  | left _ => true
  | right _ => false
  end.

Definition eqAttribute_dec : forall x y: Attribute, {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Definition beqAttribute a a' :=
  match eqAttribute_dec a a' with
  | left _ => true
  | right _ => false
  end.

Definition eqAssoc_dec : forall x y: Assoc, {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Definition beqAssoc a a' :=
  match eqAssoc_dec a a' with
  | left _ => true
  | right _ => false
  end.

Definition eqAsEnd_dec : forall x y: AsEnd, {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Definition beqAsEnd a a' :=
  match eqAsEnd_dec a a' with
  | left _ => true
  | right _ => false
  end.

Definition eqOperation_dec : forall x y: Operation, {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Definition beqOperation o o' :=
  match eqOperation_dec o o' with
  | left _ => true
  | right _ => false
  end.

Fixpoint eqClass_dec (x y : Class) : {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Definition beqClass c c' :=
  match eqClass_dec c c' with
  | left _ => true
  | right _ => false
  end.

Fixpoint eqGen_dec (x y : Gen) : {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Definition beqGen g g' :=
  match eqGen_dec g g' with
  | left _ => true
  | right _ => false
  end.

(** ------------------projection--------------------- **)

(** ----- get named element oid ----- **)
Definition NamedElement_oid (o : NamedElement) : nat :=
  match o with
    | (BNamedElement o _ ) => o
  end.


(** ----- get named element name ----- **)
Definition NamedElement_name (o : NamedElement) : string :=
  match o with
    | (BNamedElement _ n) => n
  end.

(** ------ get the basis of attribute ----- **)
Definition Attribute_super (a : Attribute) : NamedElement :=
  match a with
    | BAttribute s _ => s
  end.

(** ------ get the classifier of attribute ----- **)
Definition Attribute_type (a : Attribute) : Classifier :=
  match a with
    | BAttribute _ c => c
  end.

(** ----- get the basis of class ------ **)
Definition Class_super (c : Class) : Classifier :=
  match c with
    | BClass c _ _  => c
  end.


(** ----- get the abstract of class ----- **)
Definition Class_abstract (c : Class) : bool :=
  match c with 
    | BClass _ a _ => a 
  end.


(** ----- get the attributes of class ----- **)
Definition Class_attribute (c : Class) : list Attribute :=
  match c with
    | BClass _ _ a  => a
  end.

(** ----- get the basis (name, abstract) of classifier ----- **)
Definition Classifier_super (c : Classifier) : NamedElement :=
  match c with
    | BClassifier s => s
  end.

(** ----- get the classifier of primitive data type ------ **)
Definition DataType_super (p : DataType) : Classifier :=
  match p with
    | BDataType s => s
  end.

(** ----- get the super class of generalization ----- **)
Definition Gen_src (g : Gen) : Class :=
  match g with
    | BGen s _ => s
  end.

(** ----- get the sub class of generalization ----- **)
Definition Gen_dest (g : Gen) : Class :=
  match g with
    | BGen _ sub => sub
  end.


(** ------ get the name of association end ----- **)
Definition AsEnd_name (a : AsEnd) : string :=
  match a with
  | BAsEnd n _ _ _ => n
  end.

(** ------ get the attached class of association end ----- **)
Definition AsEnd_class (a : AsEnd) : Class :=
  match a with
  | BAsEnd  _ c _ _ => c
  end.

(** ------ get the multipy of association ----- **)
Definition AsEnd_lower (a : AsEnd) : Natural:=
  match a with
    | BAsEnd _ _ l _ => l
  end.


Definition AsEnd_upper (a : AsEnd) : Natural:=
  match a with
    | BAsEnd _ _ _ u => u
  end.

(** ----- get the name of association ------ **)
Definition Assoc_super (a : Assoc) : NamedElement :=
  match a with
    | BAssoc s _ _ => s
  end.


Definition Assoc_kind (a : Assoc) : assocKind :=
  match a with
  | BAssoc _ k _ => k
  end.


(** ----- Get the ends of association ----- *)
Definition Assoc_node (a : Assoc) : AsEnd * AsEnd :=
  match a with
    | BAssoc _ _ k => k
  end.

(** ----- get the class of association ends ----- **)
Definition Assoc_src (a : Assoc) : Class :=
  AsEnd_class (fst (Assoc_node a)).

Definition Assoc_dest (a : Assoc) : Class :=
  AsEnd_class (snd (Assoc_node a)).


(** ----------------Derived Projections------------------- **)

Definition Classifier_name (c : Classifier) : string :=
  NamedElement_name (Classifier_super c).

Definition Classifier_oid (c : Classifier) :=
  NamedElement_oid (Classifier_super c).

Definition Attribute_name (a : Attribute) : string :=
  NamedElement_name (Attribute_super a).

Definition Attribute_oid (a : Attribute) : nat :=
  NamedElement_oid (Attribute_super a).

Definition DataType_name (c : DataType) : string :=
  Classifier_name (DataType_super c).

Definition DataType_oid (c : DataType) : nat :=
  Classifier_oid (DataType_super c).

Definition Class_name (c : Class) : string :=
  Classifier_name (Class_super c).

Definition Class_oid (c : Class) : nat :=
  Classifier_oid (Class_super c).

Definition Assoc_name (a : Assoc) : string :=
  NamedElement_name (Assoc_super a).

Definition Assoc_oid (a : Assoc) : nat :=
  NamedElement_oid (Assoc_super a).

(** ---------Structural Constraints--------- *)

Definition Class_Instances (model : SimpleUML) :=
  MClass_Instance model.

Definition DataType_Instances (model : SimpleUML) :=
  MDataType_Instance model.

Definition Assoc_Instances (model : SimpleUML) :=
  MAssoc_Instance model.

Definition Attribute_Instances (model : SimpleUML) :=
  MAttr_Instance model.

Definition Gen_Instances (model : SimpleUML) :=
  MGen_Instance model.

(** ###### well-formed rules ##### **)

Definition lstClassOid (model : SimpleUML) : list nat :=
  map Class_oid (Class_Instances model).

Definition lstAttrOid (model : SimpleUML) : list nat :=
  map Attribute_oid (Attribute_Instances model).

Definition lstDataOid (model : SimpleUML) : list nat :=
  map DataType_oid (DataType_Instances model).

Definition lstAssocOid (model : SimpleUML) : list nat :=
  map Assoc_oid (Assoc_Instances model).


Definition UniqueOid (model : SimpleUML) : Prop :=
  NoDup (lstClassOid model ++ lstAttrOid model ++ lstDataOid model ++ lstAssocOid model).

Definition UniqueClass (model : SimpleUML) : Prop :=
  NoDup (Class_Instances model).

Definition UniqueDataType (model : SimpleUML) : Prop :=
  NoDup (DataType_Instances model).

Definition UniqueAttribute (model : SimpleUML) : Prop :=
  NoDup (Attribute_Instances model).

Definition UniqueAttrInClass (model : SimpleUML) : Prop :=
  forall o: Class,  (In o (Class_Instances model)) ->
    NoDup (Class_attribute o).


(** ##### Non-structural Contraints ##### **)

Definition nsc_AttributeUniqueness (model : SimpleUML) : Prop :=
  forall o : Class, (In o (Class_Instances model)) ->
                    NoDup (map Attribute_name (Class_attribute o)).

Definition nsc_ClassUniqueness (model : SimpleUML) : Prop :=
  NoDup (map Class_name (Class_Instances model)).

Definition nsc_DataTypeUniquenss (model : SimpleUML) : Prop :=
  NoDup (map DataType_name (DataType_Instances model)).

Definition nsc_AssocUniqueness (model : SimpleUML) : Prop :=
  NoDup (map Assoc_name (Assoc_Instances model)).

Definition NotSelfGenralization (model : SimpleUML) : Prop :=
  forall g: Gen, (In g (Gen_Instances model)) ->
    beqClass (Gen_src g) (Gen_dest g) = false.


(** ----- well formed ----- **)
(** 
Definition WellFormed (s : SimpleUML) :  Prop :=
  UniqueClass s /\ UniqueAttribute s /\  UniqueDataType s /\
  UniqueAttrInClass s /\ nsc_AttributeUniqueness s /\ nsc_ClassUniqueness s /\
  nsc_DataTypeUniquenss s /\ NotSelfGenralization s.
**)



