(** @name Formalization of class diagrams
   @version 1.0
   @domains 
   @authors Feng sheng 
   @date 30/03/2019
   @description object diagrams (Coq v8.9)
**)

Require Import List.
Require Import String.
Require Import ListSet.
Require Import Arith.
Require Import Peano_dec.
Require Import classdiagram.
Import ListNotations.


(* ----- object(objid, objname, classid) ------ *)
Inductive object := 
| BObject: string -> class -> object.


(* ----- link(linkid, objAid, objBid, associd) ------ *)
Inductive link_rel :=
| rel_assoc : association -> link_rel
| rel_gen : generalization -> link_rel.

Inductive link :=
| BLink: list object -> link_rel -> link.


(* ------ attrval(attrvalid, attrid, value, objid) ---- *)
Inductive atype :=
| AT : class -> atype
| AInt : nat -> atype
| ABool : bool -> atype
| AString : string -> atype.

Inductive attrval : Set :=
| BAttrval : attribute -> atype -> object -> attrval.


(* ---- Equality Judgement -----*)
Definition eqobject_dec :
  forall x y: object, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


Definition beq_object o o' :=
  match eqobject_dec o o' with
  | left _ => true
  | right _ => false
  end.


Definition eqLink_dec : forall x y: link, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


Definition beq_link l l' :=
  match eqLink_dec l l' with
  | left _ => true
  | right _ => false
  end.


Definition eqAttrval_dec : forall x y: attrval, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


Definition beq_attrval l l' :=
  match eqAttrval_dec l l' with
  | left _ => true
  | right _ => false
  end.


Definition eqRel_dec : forall x y: link_rel, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


Definition beq_link_rel l l' :=
  match eqRel_dec l l' with
  | left _ => true
  | right _ => false
  end.


Open Scope type_scope.

(** ----- pair (class, objects) ----- *)

Record State : Set :=
  mkState {
      mobjects : list object;
      mlinks : list link;
      mattrvals : list attrval
  }.


(* ----- projections ------ *)

(* ----- projects of objects -----*)
Definition object_name (o : object) : string :=
  match o with
  | BObject n _  => n
  end.


Definition object_class (o : object) :=
  match o with
  | BObject _ c => c
  end.


(* ----- projects of links -----*)
Definition link_objects (l : link) :=
  match l with
  | BLink s _  => s
  end.


Definition link_assoc (l : link) :=
  match l with
  | BLink _ a  => a
  end.


(* ----- projections of attrval ----- *)
Definition attrv_attribute (a : attrval) :=
  match a with
  | BAttrval attr _ _ => attr
  end.


Definition attrv_type (a : attrval) :=
  match a with
  | BAttrval _ t _ => t
  end.


Definition attrv_object (a : attrval) :=
  match a with
  | BAttrval _ _ ob => ob
  end.


(* ---- projections of states ----- *)
Definition objects (state : State) :=
  mobjects state.


Definition links (state : State) :=
  mlinks state.


Definition attrvals (state : State) :=
  mattrvals state.


(* ----- Component ----- *)
Inductive component : Type :=
| cclass : class -> component
| cattribute : attribute -> component
| cassociation : association -> component
| cgeneralization : generalization -> component
| cabstract : list class -> component
| cnonabstract : list class -> component.


(** every object o in s is the instance of a class c **)
Definition Sat_class (c: class) (s : State) : Prop :=
  In c (map object_class (objects s)).


(** get the objects of class c in l **)
Fixpoint get_objects_of_class (l : list object) (c : class) :=
  match l with
  | [] => []
  | o :: l' => if beq_class c (object_class o)
               then o :: get_objects_of_class l' c
               else get_objects_of_class l' c
  end.


(* (** get the links of association a **)
Fixpoint get_links_of_assoc (l : list link) (a : association) :=
  match l with
  | [] => []
  | o :: l' => if beq_association a (link_assoc o)
               then o :: get_links_of_assoc l' a
               else get_links_of_assoc l' a
  end. *)


Definition sat_object_class model state : Prop :=
  forall o : object, In o (mobjects state) ->
  exists c : class, In c (classes model) /\ c = object_class o.


(** Check parents. **)

Definition domain lg lo c :=
  flat_map (get_objects_of_class lo) (children lg c ++ [c]).


Definition sat_domain model state : Prop :=
  forall (c1 c2 : class),
    In (BGen c2 c1) (generalizations model) ->
  forall o : object, 
  let lg := generalizations model in
  let lo := mobjects state in
  In o (domain lg lo c1) -> In o (domain lg lo c1).


Definition sat_abstract_class_domain model state :=
  forall c : class, In c (classes model) /\ is_abstract c = true -> 
  let lg := generalizations model in
  let lo := mobjects state in
  domain lg lo c = flat_map (domain lg lo) (children lg c).

(** the multiplicity defined in M denotes a range of possible links between objects of these
   classes. Moreover, structural propertoes expressed on the metamodel as OCL contraints 
   and behavioural properties will be taken into account in future work **)

(** extend the associationEnd as an list to model (semantics) **)


(** #### Sat(M, I) -> Bool #### **)

(** Definition Sat (model : SimpleUML) (ins : InstanceModel) :=
   Sat_class model ins /\ Sat_assoc model ins /\ Sat_exists model ins. **)



