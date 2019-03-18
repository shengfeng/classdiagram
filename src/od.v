(** @name Formalization of class diagrams
   @version 1.0
   @domains 
   @authors Feng sheng 
   @date 30/03/2017
   @description object diagrams (Coq v8.2)
**)

Require Import List.
Require Import String.
Require Import ListSet.
Require Import Arith.
Require Import Peano_dec.

Require Import cd.


Import ListNotations.


Inductive Object := 
| BObject: string -> Object.


Inductive Link :=
| BLink: string -> Link.


Definition eqObject_dec :
  forall x y: Object, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


Definition beqObject o o' :=
  match eqObject_dec o o' with
  | left _ => true
  | right _ => false
  end.


Definition eqLink_dec : forall x y: Link, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


Definition beqLink l l' :=
  match eqLink_dec l l' with
  | left _ => true
  | right _ => false
  end.


Open Scope type_scope.

(** ----- pair (class, objects) ----- *)
Definition VObject: Set := Class * list Object.

Definition VLink: Set := Assoc * list Link.

Definition VEnd: Set := Link * Object * Object.

Record State : Set :=
  mkState {
      objects : list Object;
      links : list Link;
      vobjects : list VObject;
      vlinks : list VLink;
      vends : list VEnd
  }.


Definition VObject_object (o : VObject) := snd o.


Definition VObject_class (o : VObject) := fst o.


Definition VLink_link (o : VLink) := snd o.


Definition VLink_assoc (o : VLink) := fst o.


Definition VEnd_src (o : VEnd) : Object := snd (fst o).


Definition VEnd_dest (o : VEnd) : Object := snd o.


Definition VEnd_link (o : VEnd) := fst (fst o).


(* ----- Component ----- *)
Inductive Component : Type :=
| cclass : Class -> Component
| cattribute : Attribute -> Component
| cassociation : Assoc -> Component
| cgeneralization : Gen -> Component
| cabstract : Class -> list Class -> Component
| cnonabstract : Class -> list Class -> Component.



(** every object o in s is the instance of a class c **)
Definition Sat_class (c: Class) (s : State) : Prop :=
  In c (map VObject_class (vobjects s)).


(** get the objects of class c in l **)
Fixpoint mapObject (c : Class) (l : list VObject) : list Object :=
  match l with
  | nil => nil
  | o :: l' => if beqClass c (VObject_class o)
               then VObject_object o
               else mapObject c l'
  end.


(*
Definition obj_domain (c : class) (lg : list generalization) (lo : list VObject) :=
  (mapObject c lo) ++ List.flat_map (oid lo) (children lg c).
*)

(** get the links of association a **)
Fixpoint mapLink (a : Assoc) (l : list VLink) : list Link :=
  match l with
  | nil => nil
  | o :: l' => if beqAssoc a (VLink_assoc o)
               then VLink_link o
               else mapLink a l'
  end.


(** ----- get the objects according to link ----- *)
Fixpoint mapVend_src (l : list VEnd) (r : Link) : list Object :=
  match l with
  | nil => nil
  | v :: l' => if beqLink (VEnd_link v) r
               then VEnd_src v :: mapVend_src l' r 
               else mapVend_src l' r
  end.


Fixpoint mapVend_dest (l :list VEnd) (r : Link) : list Object :=
  match l with
  | nil => nil
  | v :: l' => if beqLink (VEnd_link v) r
               then VEnd_dest v :: mapVend_dest l' r
               else mapVend_dest l' r
  end.


Fixpoint links_objects_src (ll: list Link) (lr : list VEnd) :=
  match ll with
  | nil => nil
  | l :: ll' => app (mapVend_src lr l) (links_objects_src ll' lr)
  end.


Fixpoint links_objects_dest (ll: list Link) (lr : list VEnd) :=
  match ll with
  | nil => nil
  | l :: ll' => app (mapVend_dest lr l) (links_objects_dest ll' lr)
  end.

Print parents.

Section GExample.

  Variable c1 c2 c3 c4 c5 : Class.

  Definition G1 : Gen := BGen c1 c2.
  Definition G2 : Gen := BGen c1 c3.
  Definition G3 : Gen := BGen c2 c4.
  Definition G4 : Gen := BGen c3 c5.

  Definition G := [G1; G2; G3; G4].

  Eval simpl in (Gen_dest G1).
  Eval simpl in (Gen_src G1).

  (* Compute (parents' G c4). *)
  (* Compute (parents G c4). *)

End GExample.


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



