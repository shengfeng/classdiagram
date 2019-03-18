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
| BObject: nat -> string -> class -> object.


(* ----- link(linkid, objAid, objBid, associd) ------ *)
Inductive link :=
| BLink: nat -> object -> object -> association -> link.


(* ------ attrval(attrvalid, attrid, value, objid) ---- *)
Inductive atype :=
| AT : class -> atype
| AInt : nat -> atype
| ACBool : bool -> atype
| AString : string -> atype.

Inductive attrval : Set :=
| BAttrval : nat -> attribute -> atype -> object -> attrval.


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
Definition object_id (o : object) :=
  match o with
  | BObject n _ _  => n
  end.


Definition object_name (o : object) : string :=
  match o with
  | BObject _ n _  => n
  end.


Definition object_class (o : object) :=
  match o with
  | BObject _ _ c => c
  end.


(* ----- projects of links -----*)
Definition link_id (l : link) :=
  match l with
  | BLink n _ _ _  => n
  end.


Definition link_source_object (l : link) :=
  match l with
  | BLink _ s _ _  => s
  end.


Definition link_target_object (l : link) :=
  match l with
  | BLink _ _ t _  => t
  end.


Definition link_assoc (l : link) :=
  match l with
  | BLink _ _ _ a  => a
  end.


(* ----- projections of attrval ----- *)
Definition attrv_id (a : attrval) :=
  match a with
  | BAttrval n _ _ _ => n
  end.


Definition attrv_attribute (a : attrval) :=
  match a with
  | BAttrval _ attr _ _ => attr
  end.


Definition attrv_type (a : attrval) :=
  match a with
  | BAttrval _ _ t _ => t
  end.


Definition attrv_object (a : attrval) :=
  match a with
  | BAttrval _ _ _ ob => ob
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
Fixpoint get_objects_of_class (c : class) (l : list object) :=
  match l with
  | [] => []
  | o :: l' => if beq_class c (object_class o)
               then o :: get_objects_of_class c l'
               else get_objects_of_class c l'
  end.


(** get the links of association a **)
Fixpoint get_links_of_assoc (a : association) (l : list link) :=
  match l with
  | [] => []
  | o :: l' => if beq_association a (link_assoc o)
               then o :: get_links_of_assoc a l'
               else get_links_of_assoc a l'
  end.



(** only direct Generalization **)
Definition Sat_gen (g: Gen) (s : State) :=
  forall p : Object, 
  let sub := Gen_dest g in 
    In p (mapObject sub (vobjects s)) ->
  let super := Gen_src g in 
    In p (mapObject super (vobjects s)).



(** get subset **)
Fixpoint unionSet (sub: list Class) (l : list VObject) :=
  match sub with
  | nil => nil
  | c :: sub' => set_union eqObject_dec (mapObject c l) (unionSet sub' l)
  end.


Definition csabstract (c : Class) :=
  Class_abstract c = true.

Definition Sat_abstract (c : Class) (sub : list Class) (s : State) :=
  csabstract c -> 
  mapObject c (vobjects s) = unionSet sub (vobjects s).

Definition ncsabstract (c : Class) :=
  Class_abstract c = false.

Definition dom (st : State) (a : Assoc) :=
  let lks := mapLink a (vlinks st) in
  links_objects_src lks (vends st).

Definition ran (st : State) (a : Assoc) :=
  let lks := mapLink a (vlinks st) in
  links_objects_dest lks (vends st).


Definition Sat_assoc1 (a : Assoc) (s : State) :=
  forall o, In o (dom s a) ->
       In o (mapObject (Assoc_src a) (vobjects s)).

Definition Sat_assoc2 (a : Assoc) (s : State) :=
  forall o, In o (ran s a) ->
       In o (mapObject (Assoc_dest a) (vobjects s)).


Definition blt_eq (n : nat) (m : Natural) : bool :=
  match m with
  | Star => true
  | Nat x => if leb n x then true else false
  end.


Compute (blt_eq 2 Star).
Compute (blt_eq 2 (Nat 4)).
Compute (blt_eq 2 (Nat 2)).
Compute (blt_eq 2 (Nat 1)).

(** the multiplicity defined in M denotes a range of possible links between objects of these
   classes. Moreover, structural propertoes expressed on the metamodel as OCL contraints 
   and behavioural properties will be taken into account in future work **)

(** extend the associationEnd as an list to model (semantics) **)


(** #### Sat(M, I) -> Bool #### **)

(** Definition Sat (model : SimpleUML) (ins : InstanceModel) :=
   Sat_class model ins /\ Sat_assoc model ins /\ Sat_exists model ins. **)



