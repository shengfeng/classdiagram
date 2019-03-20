Require Export classdiagram.
Require Import List.
Require Import String.
Require Import ListSet.
Import ListNotations.
Require Import CpdtTactics.

(* ------ example ------ *)

Definition c1 := 
  BClass 0 "Vehicle" false. 
Definition c2 := 
  BClass 1 "Car" false. 
Definition c3 := 
  BClass 2 "Motorcycle" false. 
Definition c4 := 
  BClass 3 "Company" false. 
Definition c5 := 
  BClass 4 "RentalStation" false. 
Definition c6 := 
  BClass 5 "Person" false.
Definition c7 := 
  BClass 6 "Date" false.

Definition a1 := 
  BAttribute 7 "registration" cstring c1.
Definition a2 := 
  BAttribute 8 "numWheels" cint c1.
Definition a3 := 
  BAttribute 9 "category" cint c2.
Definition a4 := 
  BAttribute 10 "numSaddles" cint c3.
Definition a5 := 
  BAttribute 11 "cc" cint c3.
Definition a6 := 
  BAttribute 12 "name" cstring c4.
Definition a7 := 
  BAttribute 13 "numEmployees" cint c4.
Definition a8 := 
  BAttribute 14 "location" cstring c5.
Definition a9 := 
  BAttribute 15 "firstname" cstring c6.
Definition a10 := 
  BAttribute 16 "lastname" cstring c6.
Definition a11 := 
  BAttribute 17 "age" cint c6.
Definition a12 := 
  BAttribute 18 "isMarried" cboolean c6.

Definition p1 := 
  BParameter 19 "d" (cclass c7).

Definition o1 := 
  BOperation 20 "stockPrice" [] c4.
Definition o2 := 
  BOperation 21 "income" [p1] c6.


Definition s1 := 
  BAssoc 22 c5 c6 none.
Definition s2 := 
  BAssoc 23 c1 c4 none.
Definition s3 := 
  BAssoc 24 c4 c5 none.
Definition s4 := 
  BAssoc 25 c5 c6 none.


Definition r1 := 
  BRole 26 "employee" "employer" s1.
Definition r2 := 
  BRole 27 "vehicle" "company" s2.
Definition r3 := 
  BRole 28 "company" "rentalstation" s3.
Definition r4 := 
  BRole 29 "manager" "managedStation" s4.


Definition m1 := 
  BMulti 30 c1 (Nat 0) (Nat 1) s2.
Definition m2 := 
  BMulti 31 c4 (Nat 0) Star s2.
Definition m3 := 
  BMulti 32 c4 (Nat 1) Star s3.
Definition m4 := 
  BMulti 33 c5 (Nat 0) Star s1.
Definition m5 := 
  BMulti 34 c5 (Nat 1) (Nat 1) s3.
Definition m6 := 
  BMulti 35 c5 (Nat 1) (Nat 1) s4.
Definition m7 := 
  BMulti 36 c6 (Nat 0) (Nat 1) s1.
Definition m8 := 
  BMulti 37 c6 (Nat 0) (Nat 1) s4.


Definition g1 := 
  BGen 38 c1 c2.
Definition g2 := 
  BGen 39 c1 c3.


Definition carRental : SimpleUML := mkSimpleUML 
    [c1;c2;c3;c4;c5;c6;c7] 
    [a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12]
    [o1;o2] 
    [s1;s2;s3;s4]
    [r1;r2;r3;r4]
    [m1;m2;m3;m4;m5;m6;m7;m8]
    [g1;g2].


Compute (parents [g1;g2] c3).
Compute (children [g1;g2] c1).


Require Import objectdiagram.

Definition ob1 :=
  BObject 40 "p1" c6.
Definition ob2 :=
  BObject 41 "p2" c6.
Definition ob3 :=
  BObject 42 "c1" c4.
Definition ob4 :=
  BObject 43 "r1" c5.
Definition ob5 :=
  BObject 44 "v1" c2.
Definition ob6 := 
  BObject 45 "v2" c2.
Definition ob7 :=
  BObject 46 "v3" c3.


Definition l1 :=
  BLink 47 ob1 ob4 s1.
Definition l2 :=
  BLink 48 ob2 ob4 s4.
Definition l3 :=
  BLink 49 ob3 ob4 s3.
Definition l4 :=
  BLink 50 ob3 ob5 s2.
Definition l5 :=
  BLink 51 ob3 ob6 s2.
Definition l6 :=
  BLink 52 ob3 ob7 s2.


Definition v1 :=
  BAttrval 53 a9 (AString "Oliver") ob1.
Definition v2 :=
  BAttrval 54 a10 (AString "Queen") ob1.
Definition v3 :=
  BAttrval 55 a11 (AInt 34) ob1.
Definition v4 :=
  BAttrval 56 a12 (ABool false) ob1.
Definition v5 :=
  BAttrval 57 a9 (AString "Jane") ob2.
Definition v6 :=
  BAttrval 58 a10 (AString "Quinn") ob2.
Definition v7 :=
  BAttrval 59 a11 (AInt 23) ob2.
Definition v8 :=
  BAttrval 60 a12 (ABool false) ob2.
Definition v9 :=
  BAttrval 61 a6 (AString "Ford") ob3.
Definition v10 :=
  BAttrval 62 a7 (AInt 3000) ob3.
Definition v11 :=
  BAttrval 63 a8 (AString "New York") ob4.
Definition v12 :=
  BAttrval 64 a1 (AString "VC1") ob5.
Definition v13 :=
  BAttrval 65 a2 (AInt 4) ob5.
Definition v14 :=
  BAttrval 66 a3 (AInt 1) ob5.
Definition v15 :=
  BAttrval 67 a1 (AString "VC2") ob6.
Definition v16 :=
  BAttrval 68 a2 (AInt 4) ob6.
Definition v17 :=
  BAttrval 69 a3 (AInt 2) ob7.
Definition v18 :=
  BAttrval 70 a1 (AString "VM1") ob7.
Definition v19 :=
  BAttrval 71 a2 (AInt 2) ob7.
Definition v20 :=
  BAttrval 72 a4 (AInt 2) ob7.
Definition v21 :=
  BAttrval 73 a5 (AInt 2) ob7.


Definition list_obj := [ob1;ob2;ob3;ob4;ob5;ob6;ob7].
Definition list_link := [l1;l2;l3;l4;l5;l6].
Definition list_value := 
  [v1;v2;v3;v4;v5;v6;v7;v8;
   v9;v10;v11;v12;v13;v14;v15;
   v16;v17;v18;v19;v20;v21].

Definition st : State := 
  mkState list_obj list_link list_value.


Lemma unique_class_company:
  unique_class carRental.
Proof.
  unfold carRental, unique_class;
  unfold c1, c2, c3, c4, c5, c6, c7.
  repeat constructor; crush.
Qed.


Ltac exists_class c :=
  exists c; firstorder; subst; reflexivity.

Theorem class_satisfaction :
  sat_object_class carRental st.
Proof.
  unfold sat_object_class, carRental, st; intros.
  simpl in *; firstorder.
  - exists_class c6.
  - exists_class c6.
  - exists_class c4.
  - exists_class c5.
  - exists_class c2.
  - exists_class c2.
  - exists_class c3.
Qed.


Compute (children [g1;g2] c1).
Compute (children [g1;g2] c2).
Compute (children [g1;g2] c3).

Compute (domain [g1;g2] list_obj c1).
Compute (domain [g1;g2] list_obj c2).
Compute (domain [g1;g2] list_obj c3).


Compute (flat_map (domain [g1;g2] list_obj) (children [g1;g2] c1)).


Theorem domain_satisfaction :
  sat_domain carRental st.
Proof.
  unfold sat_domain, carRental, st, list_obj; intros.
  simpl in *; firstorder.
  - rewrite H in *; crush.
Admitted.

