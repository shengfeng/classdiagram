Add LoadPath "~/Desktop/classdiagram/src".

Require Import Coq.Lists.List. 
Import ListNotations.
Require Import Coq.Sorting.Mergesort.
Require Export classdiagram.
Require Import String.
Require Import CpdtTactics.
Open Scope string_scope.


(** example **)
Definition Customer : class := "Customer".
Definition Order : class := "Order".
Definition Payment : class := "Payment".
Definition Cash : class := "Cash".
Definition Check_ : class := "Check_".
Definition Credit : class := "Credit".
Definition OrderDetail : class := "OrderDetail".
Definition Item : class := "Item".

Definition order_class :=
  [Customer;Order;Payment;Cash;Check_;Credit;OrderDetail;Item].


Definition firstname :=
  BAttribute "firstname" Customer TString.
Definition lastname :=
  BAttribute "lastname" Customer TString.
Definition email :=
  BAttribute "email" Customer TString.
Definition address :=
  BAttribute "address" Customer TString.
Definition date :=
  BAttribute "date" Order TString.
Definition status :=
  BAttribute "status" Order TString.
Definition amount :=
  BAttribute "amount" Payment TInteger.
Definition cashTendered :=
  BAttribute "cashTendered" Cash TInteger.
Definition name :=
  BAttribute "name" Check_ TString.
Definition bankID :=
  BAttribute "bankID" Cash TInteger.
Definition number :=
  BAttribute "number" Credit TString.
Definition credittype :=
  BAttribute "type" Credit TString.
Definition expDate :=
  BAttribute "expDate" Credit TString.
Definition quanity :=
  BAttribute "quanity" OrderDetail TInteger.
Definition tax :=
  BAttribute "tax" OrderDetail TInteger.
Definition shippingWeight :=
  BAttribute "shippingWeight" Item TInteger.
Definition description :=
  BAttribute "description" OrderDetail TString.

Definition order_attibute :=
  [firstname;lastname;email;address;date;status;amount;cashTendered;
   name;bankID;number;credittype;expDate;quanity;tax;shippingWeight;description].

Definition calcTax :=
  BOperation "calcTax" Order [TInteger].
Definition calcTotal :=
  BOperation "calcTotal" Order [TInteger].
Definition calcTotalWeight :=
  BOperation "calcTotalWeight" Order [TInteger].

Definition order_operation :=
  [calcTax;calcTotal;calcTotalWeight].


(** example **)
Definition Generate : assoc := "Generate".
Definition Pay : assoc := "Pay".
Definition Has : assoc := "Has".
Definition Contain : assoc := "Contain".


Definition order_assoc :=
  [Generate;Pay;Has;Contain].

Definition a1 :=
  BAssoc Generate [Customer;Order] bidirect.
Definition a2 :=
  BAssoc Pay [Payment;Order] bidirect.
Definition a3 :=
  BAssoc Has [Order;OrderDetail] composite.
Definition a4 :=
  BAssoc Contain [OrderDetail;Item] direct.

Definition order_associates :=
  [a1;a2;a3;a4].



(** example **)
Definition r1 :=
  BRole Generate ["customer";"order"].
Definition r2 :=
  BRole Pay ["payment";"order"].
Definition r3 :=
  BRole Has ["order";"orderDetail"].
Definition r4 :=
  BRole Contain ["orderDetail";"item"].

Definition order_roles :=
  [r1;r2;r3;r4].


(* example *)
Definition m1 :=
  BMulti Generate [(Nat 1, Nat 1);(Nat 0, Star)].
Definition m2 :=
  BMulti Pay [(Nat 1, Star);(Nat 1, Nat 1)].
Definition m3 :=
  BMulti Has [(Nat 1, Nat 1);(Nat 1, Star)].
Definition m4 :=
  BMulti Contain [(Nat 0, Star);(Nat 1, Nat 1)].

Definition order_multiplicity :=
  [m1;m2;m3;m4].


(** example **)
Definition g1 := BGen Cash Payment.
Definition g2 := BGen Check_ Payment.
Definition g3 := BGen Credit Payment.

Definition order_generalization := [g1; g2; g3].


Definition order_model := mkSimpleUML
  order_class order_attibute order_operation order_assoc order_associates
  order_roles order_multiplicity order_generalization.

Compute (participating Order order_associates).

Compute (navends Order a1 order_roles).
Compute (navends Order a2 order_roles).
Compute (navends Order a3 order_roles).

Compute (navs Order order_associates order_roles).

Compute (parents order_generalization Cash).
Compute (parents order_generalization Payment).

Compute (get_children order_generalization Payment).



(** Proof **)
Example wlf_rule1:
  unique_class order_model.
Proof.
  unfold order_model, order_class, unique_class; crush.
  repeat constructor; crush; try inversion H0; try inversion H.
Qed.


Example wlf_rule2:
  nsc_attribute_unique order_model.
Proof.
  unfold order_model, order_attibute, nsc_attribute_unique; crush;
  repeat constructor; crush.
Qed.

Example wlf_rule3:
  nsc_nselfgen order_model.
Proof.
  unfold order_model, nsc_nselfgen; crush; inversion H.
Qed.


Example wlf_rule4:
  nsc_role order_model.
Proof.
  unfold order_model, nsc_role; crush.
Qed.


Example wlf_rule4:
  nsc_assoc order_model.
Proof.
  unfold order_model, nsc_assoc; crush.
Qed.


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