Require Import Coq.Lists.List. 
Import ListNotations.
Require Import Coq.Sorting.Mergesort. 
Require Export classdiagram.
Require Export objectdiagram.
Require Import String.
Open Scope string_scope.

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
Definition a6 := BAttribute "tax" private cint c3.
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
  BRole 5 ["customer";"order"] s1.
Definition r2 :=
  BRole 6 ["line";"item"] s2.
Definition r3 :=
  BRole 7 ["orderDetail";"item"] s3.
Definition r4 :=
  BRole 8 ["oder";"payment"] s4.


Definition m1 :=
  BMulti 9 c1 (Nat 1) (Nat 1) s1.
Definition m2 :=
  BMulti 9 c2 (Nat 0) Star s1.
Definition m3 :=
  BMulti 10 c2 (Nat 1) (Nat 1) s2.
Definition m4 :=
  BMulti 11 c3 (Nat 1) Star s2.
Definition m5 :=
  BMulti 12 c3 (Nat 0) Star s3.
Definition m6 :=
  BMulti 13 c4 (Nat 1) (Nat 1) s3.
Definition m7 :=
  BMulti 14 c2 (Nat 1) (Nat 1) s4.
Definition m8 :=
  BMulti 15 c5 (Nat 1) Star s4.


Definition g1 : generalization := 
  BGen c6 c5.
Definition g2 : generalization := 
  BGen c7 c5.
Definition g3 : generalization := 
  BGen c8 c5.

Definition order_payment := mkSimpleUML 
    [c1;c2;c3;c4;c5;c6;c7;c8] 
    [a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15]
    [o1;o2;o3;o4;o5;o6;o7;o8;o9;o10;o11;o12] 
    [s1;s2;s3;s4]
    [r1;r2;r3;r4]
    [m1;m2;m3;m4;m5;m6;m7;m8]
    [g1;g2;g3].



(* object diagrams *)
Definition b1 := BObject "c" c1.
Definition b2 := BObject "o1" c2.
Definition b3 := BObject "o2" c2.
Definition b4 := BObject "od1" c3.
Definition b5 := BObject "od2" c3.
Definition b6 := BObject "od1" c3.
Definition b7 := BObject "p1" c6.
Definition b8 := BObject "p2" c8.


Definition l1 := BLink [b1; b2] (rel_assoc s1).
Definition l2 := BLink [b1; b3] (rel_assoc s1).
Definition l3 := BLink [b2; b4] (rel_assoc s2).
Definition l4 := BLink [b3; b5] (rel_assoc s2).
Definition l5 := BLink [b3; b6] (rel_assoc s2).
Definition l6 := BLink [b2; b7] (rel_assoc s4).
Definition l7 := BLink [b2; b8] (rel_assoc s4).


Definition v1 := BAttrval a1 (AString "Alen") b1.
Definition v2 := BAttrval a2 (AString "New York") b1.
Definition v3 := BAttrval a3 (AString "20190904") b2.
Definition v4 := BAttrval a4 (AString "prepaid") b2.
Definition v5 := BAttrval a3 (AString "20190831") b3.
Definition v6 := BAttrval a4 (AString "prepaid") b3.
Definition v7 := BAttrval a5 (AInt 1) b4.
Definition v8 := BAttrval a6 (AInt 7) b4.
Definition v9 := BAttrval a5 (AInt 2) b5.
Definition v10 := BAttrval a6 (AInt 5) b5.
Definition v11 := BAttrval a5 (AInt 3) b6.
Definition v12 := BAttrval a6 (AInt 7) b6.
Definition v13 := BAttrval a9 (AInt 30) b7.
Definition v14 := BAttrval a10 (AInt 12) b7.
Definition v15 := BAttrval a9 (AInt 190) b8.
Definition v16 := BAttrval a13 (AString "63527631") b8.
Definition v17 := BAttrval a14 (AString "credit card") b8.
Definition v18 := BAttrval a15 (AString "2029/08/21") b8.


Definition order_instance := mkState
  [b1;b2;b3;b4;b5;b6;b7;b8]
  [l1;l2;l3;l4;l5;l6;l7]
  [v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11;v12;v13;v14;v15;v16;v17;v18].