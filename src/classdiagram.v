(** @Name Formalization of class diagrams
    @version 1.1
    @domains 
    @authors Feng sheng 
    @date 30/03/2019
    @description class and object diagrams (Coq v8.9)
**)

Require Import List.
Require Import String.
Require Import ListSet.
Require Import Arith.
Require Import Peano_dec.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Lists.List.

Import ListNotations.

Open Scope list_scope.

(** ##### the structute of metamodel of class diagram #### **)


(* ----- class(classid, classname, isAbstract) ----- *)
Inductive class : Set :=
| BClass : string -> bool -> class.


(* ----- attribute(attrid, attrname, attrtype, classid)  ----- *)
Inductive ctype :=
| cclass : class -> ctype
| cint : ctype
| cboolean : ctype
| cstring : ctype.


Inductive visibility :=
| public | private | protected.


Inductive attribute : Set :=
| BAttribute : string -> visibility -> ctype -> class -> attribute.


(* ----- parameter(pod, pname, ptype) ------ *)
Inductive parameter :=
| BParameter : string -> ctype -> parameter.


(* ----- operation(opid, opname, [parameter], classid) ----- *)
Inductive operation : Set :=
| BOperation : string -> visibility -> list parameter -> class -> operation.


(* ----- association(associd, classAid, classBid, assoctype) ----- *)
Inductive assoctype : Set :=
| bidirect : assoctype
| direct : assoctype
| aggregate : assoctype
| composite : assoctype.


Inductive association : Set :=
| BAssoc: nat -> string -> list class -> assoctype -> association.


(* ----- rolename(roleid, nameA, nameB, associd) ----- *)
Inductive rolename : Set :=
| BRole: nat -> list string -> association -> rolename.


(* ----- multiplicity(multid, classid, lower, upper, associd) ----- *)
Inductive natural :=
| Nat : nat -> natural
| Star : natural.


Inductive multiplicity : Set :=
| BMulti : nat -> class -> natural -> natural -> association -> multiplicity.


(* ----- generalization(genid, superid, subid) ----- *)
Inductive generalization : Set :=
| BGen : class -> class -> generalization.


(** ------------------------------- **)
(** -------- Source Model --------- **)
Record SimpleUML : Set :=
  mkSimpleUML {
      mclass : list class;
      mattribute : list attribute;
      moperation : list operation;
      massociation : list association;
      mrolename : list rolename;
      mmultiplicity : list multiplicity;
      mgeneralization : list generalization
    }.


(* ------------------projection--------------------- *)

(* ----- projection of class  ----- *)
Definition class_name (c : class) : string :=
  match c with
  | (BClass s _) => s
  end.


Definition is_abstract (c : class) : bool :=
  match c with
  | (BClass _ a) => a
  end.


(* ----- projection of attribute ----- *)
Definition attr_name (a : attribute) : string :=
  match a with
  | (BAttribute n _ _ _) => n
  end.


Definition attr_visibility (a : attribute) : visibility :=
  match a with
  | BAttribute _ v _ _ => v
  end.


Definition attr_type (a : attribute) : ctype :=
  match a with
  | (BAttribute _ _ t _) => t
  end.


Definition attr_class (a : attribute) : class :=
  match a with
  | (BAttribute _ _ _ c) => c
  end.


(* ----- projection of operation ----- *)
Definition op_name (o : operation) : string :=
  match o with
  | BOperation n _ _ _ => n
  end.


Definition op_visibility (o : operation) : visibility :=
  match o with
  | BOperation _ v _ _ => v
  end.


Definition op_parameters (o : operation) : list parameter :=
  match o with
  | BOperation _ _ l _ => l
  end.


Definition op_class (o : operation) : class :=
  match o with
  | BOperation _ _ _ c => c
  end.


(* ----- projection of parameter ----- *)
Definition param_name (p : parameter) :=
  match p with
  | BParameter n _ => n
  end.


Definition param_type (p : parameter) :=
  match p with
  | BParameter _ t => t
  end.

(* ----- projection of association ----- *)
Definition assoc_id (a : association) : nat :=
  match a with
  | BAssoc n _ _ _  => n
  end.


Definition asscoc_name (a : association) : string :=
  match a with
  | BAssoc _ n _ _ => n
  end.


Definition assoc_classes (a : association) : list class :=
  match a with
  | BAssoc _ _ s _  => s
  end.


Definition assoc_type (a : association) : assoctype :=
  match a with
  | BAssoc _ _ _ t => t
  end.


(* ----- projection of rolename ----- *)

Definition rolename_id (r : rolename) : nat :=
  match r with
  | BRole n _ _ => n
  end.


Definition rolename_names (r : rolename) : list string :=
  match r with
  | BRole _ s _ => s
  end.


Definition rolename_association (r : rolename) : association :=
  match r with
  | BRole _ _ a => a
  end.


(* ----- projection of multiplicity ----- *)

Definition multi_id (r : multiplicity) : nat :=
  match r with
  | BMulti n _ _ _ _ => n
  end.


Definition multi_class (r : multiplicity) : class :=
  match r with
  | BMulti _ c _ _ _ => c
  end.


Definition multi_lower (r : multiplicity) : natural :=
  match r with
  |  BMulti _ _ l _ _ => l
  end.


Definition multi_upper (r : multiplicity) : natural :=
  match r with
  |  BMulti _ _ _ u _ => u
  end.


Definition multi_assoc (r : multiplicity) : association :=
  match r with
  |  BMulti _ _ _ _ a => a
  end.


(* ----- projection of generalization ----- *)
Definition gener_sub (r : generalization) : class :=
  match r with
  |  BGen sub _ => sub
  end.


Definition gener_super (r : generalization) : class :=
  match r with
  |  BGen _ super => super
  end.


(* --------- the set of each concept--------- *)

Definition classes (model : SimpleUML) :=
  mclass model.

Definition attributes (model : SimpleUML) :=
  mattribute model.

Definition operations (model : SimpleUML) :=
  moperation model.

Definition associations (model : SimpleUML) :=
  massociation model.

Definition rolenames (model : SimpleUML) :=
  mrolename model.

Definition multiplicities (model : SimpleUML) :=
  mmultiplicity model.

Definition generalizations (model : SimpleUML) :=
  mgeneralization model.


(* ----- Equality Judgement ----- *)
Definition eqclass_dec : 
  forall x y: class, {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Definition beq_class c c' :=
  match eqclass_dec c c' with
  | left _ => true
  | right _ => false
  end.


Definition eqassociation_dec : 
  forall x y: association, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


Definition beq_association c c' :=
  match eqassociation_dec c c' with
  | left _ => true
  | right _ => false
  end.


Definition eqmultiplicity_dec : 
  forall x y: multiplicity, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


Definition beq_multiplicity c c' :=
  match eqmultiplicity_dec c c' with
  | left _ => true
  | right _ => false
  end.


(* ---------- Functions --------- *)

(** --- get all parents --- **)

(** remove the duplicate class **)
Fixpoint deduplicate (ls : list class) :=
  match ls with
  | [] => []
  | x :: [] => [x]
  | x :: xs
    => if leb (count_occ eqclass_dec ls x) 1
       then x :: deduplicate xs
       else deduplicate xs
  end.


Fixpoint parents' (l : list generalization) (c : class) :=
match l with
| [] => []
| (BGen p c') :: l' => if beq_class c c' 
                       then [p]
                       else parents' l' c
end.

Definition parents_step (l : list generalization) (cs : list class) :=
  deduplicate (cs ++ List.flat_map (parents' l) cs).


Fixpoint all_parents' (l : list generalization) (cs : list class) (fuel : nat) :=
  match fuel with
  | 0 => cs
  | S fuel'
    => all_parents' l (parents_step l cs) fuel'
  end.


Definition parents (l : list generalization) (c : class) :=
  deduplicate (all_parents' l (parents' l c) (List.length l)).


(** ----- children ----- **)
Fixpoint children' (l : list generalization) (c : class) :=
match l with
| [] => []
| (BGen c' p) :: l' => if beq_class c' c 
                       then [p] ++ children' l' c
                       else children' l' c
end.


Definition children_step (l : list generalization) (cs : list class) :=
  deduplicate (cs ++ List.flat_map (children' l) cs).


Fixpoint all_children' (l : list generalization) (cs : list class) (fuel : nat) :=
  match fuel with
  | 0 => cs
  | S fuel'
    => all_children' l (children_step l cs) fuel'
  end.


Definition children (l : list generalization) (c : class) :=
  deduplicate (all_children' l (children' l c) (List.length l)).


(* ----- get all attributes ----- *)
Fixpoint get_attributes (c : class) (attrs : list attribute) :=
  match attrs with
  | [] => []
  | a :: attr' => if beq_class c (attr_class a)
                   then a :: get_attributes c attr'
                   else get_attributes c attr'
  end.


(** ###### Structural Constraints ##### **)

Definition lst_assoc_id (model : SimpleUML) : list nat :=
  map assoc_id (associations model).

Definition lst_rolename_id (model : SimpleUML) : list nat :=
  map rolename_id (rolenames model).

Definition lst_multi_id (model : SimpleUML) : list nat :=
  map multi_id (multiplicities model).

Definition Unique_id (model : SimpleUML) : Prop :=
  NoDup  (lst_assoc_id model ++
          lst_rolename_id model ++
          lst_multi_id model).



Definition unique_class (model : SimpleUML) : Prop :=
  NoDup (classes model).

Definition unique_attribute (model : SimpleUML) : Prop :=
  NoDup (attributes model).

Definition unique_attr_names (model : SimpleUML) : Prop :=
  NoDup (map attr_name (attributes model)).


(** ##### Non-structural Contraints ##### **)

Definition nsc_AttributeUniqueness (model : SimpleUML) : Prop :=
  forall o : class, 
    In o (classes model) -> 
    NoDup (map attr_name (get_attributes o (attributes model))).


Definition nsc_ClassUniqueness (model : SimpleUML) : Prop :=
  NoDup (map class_name (classes model)).


Definition NotSelfGenralization (model : SimpleUML) : Prop :=
  forall g: generalization, 
    In g (generalizations model) ->
    let sub := gener_sub g in ~ In sub (parents (generalizations model) sub).

(** ----- well formed ----- **)

Definition WellFormed (s : SimpleUML) :  Prop :=
  unique_class s /\ unique_attribute s /\  unique_attr_names s /\
  nsc_AttributeUniqueness s /\ nsc_ClassUniqueness s /\ NotSelfGenralization s.