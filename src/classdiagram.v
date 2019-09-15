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
Open Scope string_scope.

(** ##### the structute of metamodel of class diagram #### **)

Definition class := string.


(* attribute  *)
Inductive ptype :=
| TClass : class -> ptype
| TInteger : ptype
| TBoolean : ptype
| TString : ptype.

Inductive type :=
| t1 : ptype -> type
| t2 : list ptype -> type.

Inductive attribute : Set :=
| BAttribute : string ->  class -> type -> attribute.

(** ----- operation(opid, opname, [parameter], classid) ----- **)
Inductive operation : Set :=
| BOperation : string  -> class -> list type -> operation.

(* ----- association(associd, classAid, classBid, assoctype) ----- *)
Definition assoc := string.

Inductive assoctype : Set :=
| bidirect : assoctype
| direct : assoctype
| aggregate : assoctype
| composite : assoctype.

Inductive associates : Set :=
| BAssoc: assoc -> list class -> assoctype -> associates.

(* ----- rolename(roleid, nameA, nameB, associd) ----- *)
Inductive role : Set :=
| BRole: assoc -> list string -> role.

(* ----- multiplicity(multid, classid, lower, upper, associd) ----- *)
Inductive natural :=
| Nat : nat -> natural
| Star : natural.

Inductive multiplicity : Set :=
| BMulti : assoc -> list (natural * natural) -> multiplicity.


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
      massoc : list assoc;
      massociates : list associates;
      mrolename : list role;
      mmultiplicity : list multiplicity;
      mgeneralization : list generalization
    }.

(* ------------------projection--------------------- *)

(* ----- projection of attribute ----- *)
Definition attr_name (a : attribute) : string :=
  match a with
  | (BAttribute n _ _) => n
  end.


Definition attr_class (a : attribute) : class :=
  match a with
  | (BAttribute _ c _) => c
  end.


Definition attr_type (a : attribute) : type :=
  match a with
  | (BAttribute _ _ t) => t
  end.


(* ----- projection of operation ----- *)
Definition op_name (o : operation) : string :=
  match o with
  | BOperation n _ _ => n
  end.


Definition op_class (o : operation) : class :=
  match o with
  | BOperation _ c _ => c
  end.


Definition op_parameters (o : operation) : list type :=
  match o with
  | BOperation _ _ l => l
  end.


(* ----- projection of association ----- *)
Print associates.

Definition assoc_name (a : associates) : assoc :=
  match a with
  | BAssoc n _ _ => n
  end.


Definition assoc_classes (a : associates) : list class :=
  match a with
  | BAssoc _ s _  => s
  end.


Definition assoc_type (a : associates) : assoctype :=
  match a with
  | BAssoc _ _ t => t
  end.


(* ----- projection of rolename ----- *)
Definition role_assoc (r : role) : assoc :=
  match r with
  | BRole a _ => a
  end.

Definition role_names (r : role) : list string :=
  match r with
  | BRole _ s => s
  end.

(* ----- projection of multiplicity ----- *)
Definition multi_assoc (r : multiplicity) : assoc :=
  match r with
  | BMulti a _ => a
  end.


Definition multi_naturals (r : multiplicity) :=
  match r with
  |  BMulti _ l => l
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

Definition assocs (model : SimpleUML) :=
  massoc model.

Definition associatess (model : SimpleUML) :=
  massociates model.

Definition roles (model : SimpleUML) :=
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

Definition beq_class x y :=
  if eqclass_dec x y then true else false.


Definition eqassoc_dec : 
  forall x y: assoc, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


Definition beq_assoc c c' :=
  match eqassoc_dec c c' with
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

Fixpoint participating (c : class) (l: list associates) :=
  match l with
  | [] => []
  | h :: l' =>
    if 0 <? List.count_occ eqclass_dec  (assoc_classes h) c 
    then (assoc_name h) :: participating c l' else participating c l'
  end.


Fixpoint navends_aux (a : assoc) (l : list role) :=
  match l with
  | [] => []
  | h :: l' =>
    if beq_assoc (role_assoc h) a
    then role_names h else navends_aux a l'
  end.

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
| (BGen c' p) :: l' => if beq_class c c' 
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
Fixpoint children (l : list generalization) (c : class) :=
match l with
| [] => []
| (BGen p c') :: l' =>
  if beq_class c' c then [p] else children l' c
end.


Definition children_step (l : list generalization) (cs : list class) :=
  deduplicate (cs ++ List.flat_map (children l) cs).


Fixpoint all_children (l : list generalization) (cs : list class) (fuel : nat) :=
  match fuel with
  | 0 => cs
  | S fuel' => all_children l (children_step l cs) fuel'
  end.


Definition get_children (l : list generalization) (c : class) :=
  deduplicate (all_children l (children l c) (List.length l)).


(* ----- get all attributes ----- *)
Fixpoint get_attributes (c : class) (attrs : list attribute) :=
  match attrs with
  | [] => []
  | a :: attr' => if beq_class c (attr_class a)
                   then a :: get_attributes c attr'
                   else get_attributes c attr'
  end.


Fixpoint get_multiplicities (a : assoc) (ml : list multiplicity) :=
  match ml with
  | [] => []
  | m  :: l =>
    if beq_assoc a (multi_assoc m)
    then m :: get_multiplicities a l
    else get_multiplicities a l
  end.



(** ###### Structural Constraints ##### **)
Definition unique_class (model : SimpleUML) : Prop :=
  NoDup (classes model).

Definition unique_attribute (model : SimpleUML) : Prop :=
  NoDup (attributes model).

Definition unique_attr_names (model : SimpleUML) : Prop :=
  NoDup (map attr_name (attributes model)).


(** ##### Non-structural Contraints ##### **)

Definition nsc_attribute_unique (model : SimpleUML) : Prop :=
  forall o : class, 
    In o (classes model) -> 
    NoDup (map attr_name (get_attributes o (attributes model))).


Definition nsc_nselfgen (model : SimpleUML) :=
  forall c : class, In c (classes model) -> 
    ~ In c (get_children (generalizations model) c).


Definition natural_eq_n (m : natural) (n : nat) :=
  match m with
  | Nat m' => beq_nat m' n
  | Star => false
  end.

(*
Definition multi_lower_eq_n (m : multiplicity) (n : nat) :=
  natural_eq_n (multi_lower m) n.

Definition multi_upper_eq_n (m : multiplicity) (n : nat) :=
  natural_eq_n (multi_upper m) n.
*)
(*
Definition nsc_assoc (model : SimpleUML) :=
  forall a : assoc,
    In a (associations model) /\
    (assoc_type a = composite \/ assoc_type a = aggregate) ->
    forall m : multiplicity,
      In m (get_multiplicities a (multiplicities model)) ->
      multi_lower_eq_n m 1 = true /\ multi_upper_eq_n m 1 = true.                  
*)   


(** ----- well formed ----- **)