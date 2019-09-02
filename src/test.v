Require Import Coq.Lists.List. 
Import ListNotations.
Require Import Coq.Sorting.Mergesort. 
Require Export classdiagram.
Require Import String.


(** Example of Order Payment  **)

Definition c1 := BClass "Customer" false.
Definition c2 := BClass "Order" false.
Definition c3 := BClass "OrderDetail" false.
Definition c4 := BClass "Item" false.
Definition c5 := BClass "Payment" true.
Definition c6 := BClass "Cash" false.
Definition c7 := BClass "Check" false.
Definition c8 := BClass "Credit" false.


Definition a1 := BAttribute "name" private cstring c1.
Definition a2 := BAttribute "address" private cstring c1.
Definition a3 := BAttribute "date" private cstring c2.
Definition a4 := BAttribute "status" private cstring c2.
Definition a5 := BAttribute "quantity" private cint c3.
Definition a6 := BAttribute "taxStatus" private cstring c3.
Definition a7 := BAttribute "shippingWeight" private cint c4.
Definition a8 := BAttribute "description" private cstring c4.
Definition a9 := BAttribute "amount" private cint c5.
Definition a10 := BAttribute "cashTendered" private cint c6.
Definition a11 := BAttribute "name" private cstring c7.
Definition a12 := BAttribute "bankID" private cstring c7.
Definition a13 := BAttribute "number" private cstring c8.
Definition a14 := BAttribute "type" private cstring c8.
Definition a15 := BAttribute "expDate" private cstring c8.



Definition o1 := BOperation "calcSubTotal" public [] c2.
Definition o2 := BOperation "calcTax" public [] c2.
Definition o3 := BOperation "calcTotal" public [] c2.
Definition o4 := BOperation "calcTotalWeight" public [] c2.
Definition o5 := BOperation "calcSubTotal" public [] c3.
Definition o6 := BOperation "calcWeight" public [] c3.
Definition o7 := BOperation "calcTax" public [] c3.
Definition o8 := BOperation "getPriceFromQuantity" public [] c4.
Definition o9 := BOperation "getTax" public [] c4.
Definition o10 := BOperation "inStock" public [] c4.
Definition o11 := BOperation "authorized" public [] c7.
Definition o12 := BOperation "authorized" public [] c8.


(** Associations **)
Definition s1 : association :=
  BAssoc 1 "" [c1;c2] bidirect.
Definition s2 : association :=
  BAssoc 2 "compose" [c2; c3] composite.
Definition s3 : association :=
  BAssoc 3 "" [c3;c4] direct.
Definition s4 : association :=
  BAssoc 4 "" [c2;c5] bidirect.


Definition r1 :=
  BRole 5 ["customer";"order"] c1.
