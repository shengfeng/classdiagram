Require Import Coq.Lists.List. 
Import ListNotations.
Require Import Coq.Sorting.Mergesort. 
Require Export classdiagram.
Require Import String.
Require Import CpdtTactics.
Open Scope string_scope.


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


Definition firstname :=
  BAttribute "firstname" Person (t1 TString).
Definition lastname :=
  BAttribute "lastname" Person (t1 TString).
Definition age :=
  BAttribute "age" Person (t1 TInteger).
Definition isMarried :=
  BAttribute "isMarried" Person (t1 TBoolean).
Definition email :=
  BAttribute "email" Person (t2 [TString]).
Definition salary :=
  BAttribute "salary" Employee (t1 TInteger).
Definition location :=
  BAttribute "location" Branch (t2 [TString]).

Definition car_attibute :=
  [firstname;lastname;age;isMarried;email;salary;location].

Definition description :=
  BOperation "description" Car [(t1 TString)].
Definition rentalForDay :=
  BOperation "rentalForDay" Branch [(t1 TString);(t2 [TClass Rental])].
Definition raiseSalary :=
  BOperation "raiseSalary" Employee [(t1 TInteger);(t1 TInteger)].

Definition car_operation :=
  [description;rentalForDay;raiseSalary].
  
  
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
  
  
(* example *)
Definition m1 :=
  BMulti Assignment [(Nat 0, Nat 1);(Nat 0, Nat 1)].
Definition m2 :=
  BMulti Booking [(Nat 0, Star);(Nat 1, Nat 1)].
Definition m3 :=
  BMulti Classification [(Nat 1, Nat 1);(Nat 0, Star)].
Definition m4 :=
  BMulti Employment [(Nat 1, Nat 1);(Nat 0, Star)].
Definition m5 :=
  BMulti Fleet [(Nat 1, Nat 1);(Nat 0, Star)].
Definition m6 :=
  BMulti Maintenance [(Nat 0, Nat 1);(Nat 0, Star);(Nat 0, Star)].
Definition m7 :=
  BMulti Management [(Nat 0, Star);(Nat 1, Nat 1)].
Definition m8 :=
  BMulti Offer [(Nat 0, Star);(Nat 0, Star)].
Definition m9 :=
  BMulti Provider [(Nat 0, Star);(Nat 1, Nat 1)].
Definition m10 :=
  BMulti Quality [(Nat 0, Nat 1);(Nat 0, Nat 1)].
Definition m11 :=
  BMulti Reservation [(Nat 0, Star);(Nat 1, Nat 1)].

Definition car_multiplicity :=
  [m1;m2;m3;m4;m5;m6;m7;m8;m9;m10;m11].
  
  
(** example **)
Definition g1 := BGen Customer Person.
Definition g2 := BGen Employee Person.

Definition car_generalization := [g1; g2].


Definition car_rental := mkSimpleUML
  car_class car_attibute car_operation car_assoc car_associates
  car_roles car_multiplicity car_generalization.

Compute (participating Car car_associates).

Compute (navends_aux Maintenance car_roles).

Compute (parents car_generalization Customer).
Compute (parents car_generalization Employee).

Compute (get_children car_generalization Person).



(** Proof **)
Example wlf_rule1:
  unique_class car_rental.
Proof.
  unfold car_rental, car_class, unique_class; crush.
  repeat constructor; crush; try inversion H0; try inversion H.
Qed.


Example wlf_rule2:
  nsc_attribute_unique car_rental.
Proof.
  unfold car_rental, car_attibute, nsc_attribute_unique; crush; 
  repeat constructor; crush.
Qed.

Example wlf_rule3:
  nsc_nselfgen car_rental.
Proof.
  unfold car_rental, nsc_nselfgen; crush; inversion H.
Qed.


Example wlf_rule4:
  nsc_assoc car_rental.
Proof.
  unfold car_rental, nsc_assoc.
Admitted.


Require Import objectdiagram.

(* object diagrams *)
Definition b1 := BObject Branch "b1".
Definition e1 := BObject Employee "e1".
Definition e2 := BObject Employee "e2".

Definition car_objects := [b1;e1;e2].

Definition v1 := BAttrval location b1 (AString "Berlin").
Definition v2 := BAttrval firstname e1 (AString "John").
Definition v3 := BAttrval lastname e1 (AString "Clark").
Definition v4 := BAttrval age e1 (AInteger 47).
Definition v5 := BAttrval isMarried e1 (ABoolean true).
Definition v6 := BAttrval salary e1 (AInteger 72).
Definition v7 := BAttrval firstname e2 (AString "Frank").
Definition v8 := BAttrval lastname e2 (AString "Barnes").
Definition v9 := BAttrval age e2 (AInteger 23).
Definition v10 := BAttrval isMarried e2 (ABoolean false).
Definition v11 := BAttrval salary e2 (AInteger 38).

Definition car_attrivals := [v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11].


Definition l1 := BLink Management [b1;e1].
Definition l2 := BLink Employment [b1;e1].
Definition l3 := BLink Employment [b1;e2].

Definition car_links := [l1;l2;l3].


Definition car_rental_state :=
  mkState car_objects car_attrivals car_links.


Example sat_rule1:
  sat_object_class car_rental car_rental_state.
Proof.
  unfold car_rental, car_rental_state, sat_object_class; crush.
  + exists Branch; crush.
  + exists Employee; crush.
  + exists Employee; crush.
Qed.


Example sat_rule2:
  sat_domain car_rental car_rental_state.
Proof.
  unfold car_rental, car_rental_state, sat_domain; crush.
Qed.


Example sat_rule3:
  sat_abstract_class_domain car_rental car_rental_state.
Proof.
  unfold car_rental, car_rental_state, sat_abstract_class_domain; crush.
  + unfold car_generalization, car_objects, domain; simpl.
Qed.