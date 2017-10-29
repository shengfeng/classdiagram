Require Export classdiagram.
Require Import List.

Import ListNotations.

(* ----- classes ----- *)
Definition c1 : class := (Id 1, "Branch", false).
Definition c2 : class := (Id 2, "Car", false).
Definition c3 : class := (Id 3, "CarGroup", false).
Definition c4 : class := (Id 4, "Check", false).
Definition c5 : class := (Id 5, "Customer", false).
Definition c6 : class := (Id 6, "Employee", false).
Definition c7 : class := (Id 7, "Person", false).
Definition c8 : class := (Id 8, "Rental", false).
Definition c9 : class := (Id 9, "ServiceDepot", false).


Definition class_list := 
  [c1; c2; c3; c4; c5; c6; c7; c8; c9].

(* ----- attributes ------ *)
Definition a1 : attribute := (Id 21, "firstname", string_, c7).
Definition a2 : attribute := (Id 22, "lastname", string_, c7).
Definition a3 : attribute := (Id 23, "age", integer, c7).
Definition a4 : attribute := (Id 24, "isMarried", boolean, c7).
Definition a5 : attribute := (Id 25, "email", string_, c7).
Definition a6 : attribute := (Id 26, "address", string_, c5).
Definition a7 : attribute := (Id 27, "salary", real, c6).
Definition a8 : attribute := (Id 28, "location", string_, c1).
Definition a9 : attribute := (Id 29, "fromDay", string_, c8).
Definition a10 : attribute := (Id 30, "untilDay", string_, c8).
Definition a11 : attribute := (Id 31, "id", integer, c2).
Definition a12 : attribute := (Id 32, "kind", string_, c3).
Definition a13 : attribute := (Id 33, "description", string_, c4).
Definition a14 : attribute := (Id 34, "location", string_, c9).

Definition attr_list :=
  [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14].

(* ------ operations ------ *)
Definition o1 : operation := (Id 41, "raiseSalary", [], c6).
Definition o2 : operation := (Id 42, "rentalDorDate", [], c1).
Definition o3 : operation := (Id 43, "description", [], c2).

Definition op_list :=
  [o1; o2; o3].


(* ----- association ----- *)
Definition s1 : association := (Id 61, "Assignment", [c8;c2]).
Definition s2 : association := (Id 62, "Booking", [c8;c5]).
Definition s3 : association := (Id 63, "Classification", [c3;c2]).
Definition s4 : association := (Id 64, "Employment", [c1;c6]).
Definition s5 : association := (Id 65, "Fleet", [c1;c2]).
Definition s6 : association := (Id 66, "Maintenance", [c9;c4;c2]).
Definition s7 : association := (Id 67, "Managerment", [c1;c6]).
Definition s8 : association := (Id 68, "Offer", [c1;c3]).
Definition s9 : association := (Id 69, "Provider", [c8;c1]).
Definition s10 : association := (Id 70, "Quality", [c3;c3]).
Definition s11 : association := (Id 71, "Reservation", [c8;c3]).

Definition assoc_list := 
  [s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11].

Eval simpl in (partipating c2 assoc_list).
Compute (map assoc_name (partipating c2 assoc_list)).

Eval simpl in (pos c2 (assoc_class s6) 0).


(* ----- multiplicity ----- *)
Definition m1 : multiplicity := (Id 101, c8, Nat 0, Nat 1, s1).
Definition m2 : multiplicity := (Id 102, c2, Nat 0, Nat 1, s1).
Definition m3 : multiplicity := (Id 103, c5, Nat 1, Nat 1, s2).
Definition m4 : multiplicity := (Id 104, c8, Nat 0, Star, s2).
Definition m5 : multiplicity := (Id 105, c3, Nat 1, Nat 1, s3).
Definition m6 : multiplicity := (Id 106, c2, Nat 0, Star, s3).
Definition m7 : multiplicity := (Id 107, c1, Nat 1, Nat 1, s4).
Definition m8 : multiplicity := (Id 108, c6, Nat 0, Star, s4).
Definition m9 : multiplicity := (Id 109, c1, Nat 1, Nat 1, s5).
Definition m10 := (Id 110, c2, Nat 0, Nat 1, s5).
Definition m11 := (Id 111, c9, Nat 0, Nat 1, s6).
Definition m12 := (Id 112, c4, Nat 0, Star, s6).
Definition m13 := (Id 113, c2, Nat 0, Star, s6).
Definition m14 := (Id 114, c1, Nat 0, Nat 1, s7).
Definition m15 := (Id 115, c6, Nat 1, Nat 1, s7).
Definition m16 := (Id 116, c1, Nat 0, Star, s8).
Definition m17 := (Id 117, c3, Nat 0, Star, s8).
Definition m18 := (Id 118, c8, Nat 0, Star, s9).
Definition m19 := (Id 119, c1, Nat 1, Nat 1, s9).
Definition m20 := (Id 120, c3, Nat 0, Nat 1, s10).
Definition m21 := (Id 121, c3, Nat 0, Nat 1, s10).
Definition m22 := (Id 122, c8, Nat 0, Star, s11).
Definition m23 := (Id 123, c3, Nat 1, Nat 1, s11).

Definition multip_list :=
  [m1; m2; m3; m4; m5; m6; m7; m8; m9;
   m10; m11; m12; m13; m14; m15; m16; m17;
   m18; m19; m20; m21; m22; m23].


(* ----- rolenames ------ *)
Definition r1 : rolename := (Id 81, ["rental"; "car"], s1).
Definition r2 : rolename := (Id 82, ["rental"; "customer"], s2).
Definition r3 : rolename := (Id 83, ["carGroup"; "car"], s3).
Definition r4 : rolename := (Id 84, ["employer"; "employee"], s4).
Definition r5 : rolename := (Id 85, ["branch"; "car"], s5).
Definition r6 : rolename := (Id 86, ["serviceDepot"; "check"; "car"], s6).
Definition r7 : rolename := (Id 87, ["managedBranch"; "manager"], s7).
Definition r8 : rolename := (Id 88, ["branch"; "carGroup"], s8).
Definition r9 : rolename := (Id 89, ["rental"; "branch"], s9).
Definition r10 : rolename := (Id 90, ["lower"; "higher"], s10).
Definition r11 : rolename := (Id 91, ["rental"; "carGroup"], s11).

Definition role_list :=
  [r1; r2; r3; r4; r5; r6; r7; r8; r9; r10; r11].

Compute (find_assoc s6 role_list).
Check navends.
Compute (navends c2 s6 role_list).
Compute (navends c2 s3 role_list).
Compute (navends c2 s10 role_list).

Compute (all_navends c2 (partipating c2 assoc_list) role_list).



(* ----- generalization ------ *)
Definition g1 : generalization := (Id 130, c7, c5).
Definition g2 : generalization := (Id 131, c7, c6).

Definition gen_list :=
  [g1; g2].


Eval simpl in (children gen_list c7).
Compute (children gen_list c7).

Eval simpl in (parents gen_list c5).
Compute (parents gen_list c5).


Definition carModel :=
  mkCD class_list attr_list assoc_list role_list multip_list gen_list.


Lemma unique_class :
  UniqueClass carModel.
Proof.
  unfold UniqueClass. simpl.
  unfold c1, c2, c3, c4, c5, c6, c7, c8, c9.
  apply NoDup_cons.
  simpl in *.
Admitted.  


(* ----- objects ------ *)
Definition ob1 : object := (Id 201, "b1", c1).
Definition ob2 : object := (Id 202, "e1", c6).
Definition ob3 : object := (Id 203, "e2", c6).

Definition ob4 := (Id 204, "c7", c7).

Definition ob_list := [ob1; ob2; ob3; ob4].

Compute (obj_domain c7 gen_list ob_list).

Compute (obj_domain c6 gen_list ob_list).


Eval simpl in oid ob_list c1.
Eval simpl in oid ob_list c6.

(* ----- link ----- *)
Definition l1 : link := (Id 111, [ob1; ob2], s7).
Definition l2 : link := (Id 112, [ob1; ob2], s4).
Definition l3 : link := (Id 113, [ob1; ob3], s4).


Definition link_list :=
  [l1; l2; l3].


Eval simpl in (lid s4 link_list).
Eval simpl in (lid s7 link_list).
Eval simpl in (lid s1 link_list).


Definition atval1 : attrval := (Id 200, a14, "Berlin", ob1).
Definition atval2 : attrval := (Id 201, a1, "John", ob2).
Definition atval3 : attrval := (Id 202, a2, "Clark", ob2).
Definition atval4 : attrval := (Id 203, a3, "47", ob2).
Definition atval5 : attrval := (Id 204, a4, "true", ob2).


Definition attrval_list :=
  [atval1; atval2; atval3; atval4; atval5].

Definition carInstance :=
  mkObj ob_list link_list attrval_list.



