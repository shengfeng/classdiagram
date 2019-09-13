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


(** example **)
Definition Branch : class := "Branch".
Definition Car : class := "Car".
Definition CarGroup : class := "CarGroup".
Definition Check_ : class := "Check".
Definition Customer : class := "Customer".
Definition Employee : class := "Employee".
Definition Person : class := "Person".
Definition Rental : class := "Rental".
Definition SeriveDepot : class := "Serivedepot".

Definition car_class :=
  [Branch;Car;CarGroup;Check_;Customer;Employee;Person;Rental;SeriveDepot].


(* attribute  *)
Inductive ptype :=
| TClass : class -> ptype
| Integer : ptype
| Boolean : ptype
| String : ptype.


Inductive type :=
| t1 : ptype -> type
| t2 : list ptype -> type.


Inductive attribute : Set :=
| BAttribute : string ->  class -> type -> attribute.


(** Example **)
Definition firstname :=
  BAttribute "firstname" Person (t1 String).
Definition lastname :=
  BAttribute "lastname" Person (t1 String).
Definition age :=
  BAttribute "age" Person (t1 Integer).
Definition isMarried :=
  BAttribute "isMarried" Person (t1 Boolean).
Definition email :=
  BAttribute "email" Person (t2 [String]).


Definition car_attibute :=
  [firstname;lastname;age;isMarried;email].


(** ----- operation(opid, opname, [parameter], classid) ----- **)
Inductive operation : Set :=
| BOperation : string  -> class -> list type -> operation.


(** Example **)
Definition description :=
  BOperation "description" Car [(t1 String)].
Definition rentalForDay :=
  BOperation "rentalForDay" Branch [(t1 String);(t2 [TClass Rental])].
Definition raiseSalary :=
  BOperation "raiseSalary" Employee [(t1 Integer);(t1 Integer)].

Definition car_operation :=
  [description;rentalForDay;raiseSalary].


(* ----- association(associd, classAid, classBid, assoctype) ----- *)
Definition assoc := string.

Inductive assoctype : Set :=
| bidirect : assoctype
| direct : assoctype
| aggregate : assoctype
| composite : assoctype.

Inductive associates : Set :=
| BAssoc: assoc -> list class -> assoctype -> associates.


(** example **)
Definition Assignment : assoc := "Assignment".
Definition Booking : assoc := "Booking".
Definition Classification : assoc := "Classification".
Definition Employment : assoc := "Employment".
Definition Fleet : assoc := "Fleet".
Definition Maintenance : assoc := "Maintenance".
Definition Management : assoc := "Management".
Definition Offer : assoc := "Offer".
Definition Provider : assoc := "Provider".
Definition Quality : assoc := "Quality".
Definition Reservation : assoc := "Reservation".


Definition car_assoc :=
  [Assignment;Booking;Classification;Employment;Fleet;
     Maintenance;Management;Offer;Provider;Quality;Reservation].

Definition a1 :=
  BAssoc Assignment [Rental;Car] bidirect.
Definition a2 :=
  BAssoc Booking [Rental;Customer] bidirect.
Definition a3 :=
  BAssoc Classification [CarGroup;Car] bidirect.
Definition a4 :=
  BAssoc Employment [Branch;Employee] bidirect.
Definition a5 :=
  BAssoc Fleet  [Branch;Car] bidirect.
Definition a6 :=
  BAssoc Maintenance [SeriveDepot;Check_;Car] bidirect.
Definition a7 :=
  BAssoc Management [Branch;Employee] bidirect.
Definition a8 :=
  BAssoc Offer [Branch;CarGroup] bidirect.
Definition a9 :=
  BAssoc Provider [Rental;Branch] bidirect.
Definition a10 :=
  BAssoc Quality [CarGroup;CarGroup] bidirect.
Definition a11 :=
  BAssoc Reservation [Rental;CarGroup] bidirect.

Definition car_associates :=
  [a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11].


(* ----- rolename(roleid, nameA, nameB, associd) ----- *)
Inductive role : Set :=
| BRole: assoc -> list string -> role.


(** example **)
Definition r1 :=
  BRole Assignment ["rental";"car"].
Definition r2 :=
  BRole Booking ["rental";"customer"].
Definition r3 :=
  BRole Classification ["carGroup";"car"].
Definition r4 :=
  BRole Employment ["employer";"employee"].
Definition r5 :=
  BRole Fleet ["branch";"car"].
Definition r6 :=
  BRole Maintenance ["seriveDepot";"check";"car"].
Definition r7 :=
  BRole Management ["managedBranch";"manager"].
Definition r8 :=
  BRole Offer ["branch";"carGroup"].
Definition r9 :=
  BRole Provider ["rental";"branch"].
Definition r10 :=
  BRole Quality ["lower";"high"].
Definition r11 :=
  BRole Reservation ["rental";"carGroup"].


Definition car_roles :=
  [r1;r2;r3;r4;r5;r6;r7;r8;r9;r10;r11].



(* ----- multiplicity(multid, classid, lower, upper, associd) ----- *)
Inductive natural :=
| Nat : nat -> natural
| Star : natural.


Inductive multiplicity : Set :=
| BMulti : assoc -> class -> natural -> natural -> multiplicity.


(* ----- generalization(genid, superid, subid) ----- *)
Inductive generalization : Set :=
| BGen : class -> class -> generalization.


(** example **)
Definition g1 := BGen Customer Person.
Definition g2 := BGen Employee Person.


Definition car_generalization :=
  [g1; g2].


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

Definition asscoc_name (a : associates) : assoc :=
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
  |  BMulti a _ _ _ => a
  end.

Definition multi_class (r : multiplicity) : class :=
  match r with
  | BMulti _ c _ _  => c
  end.


Definition multi_lower (r : multiplicity) : natural :=
  match r with
  |  BMulti _ _ l _ => l
  end.


Definition multi_upper (r : multiplicity) : natural :=
  match r with
  |  BMulti _ _ _ u => u
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
    then h :: participating c l' else participating c l'          
  end.


Compute (participating Car car_associates).



Fixpoint navends_aux (a : assoc) (l : list role) :=
  match l with
  | [] => []
  | h :: l' =>
    if beq_assoc (role_assoc h) a
    then role_names h else navends_aux a l'
  end.


Compute (navends_aux Maintenance car_roles).


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


Compute (parents car_generalization Customer).
Compute (parents car_generalization Employee).


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


Compute (get_children car_generalization Person).


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

Definition nsc_AttributeUniqueness (model : SimpleUML) : Prop :=
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


Definition multi_lower_eq_n (m : multiplicity) (n : nat) :=
  natural_eq_n (multi_lower m) n.

Definition multi_upper_eq_n (m : multiplicity) (n : nat) :=
  natural_eq_n (multi_upper m) n.

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