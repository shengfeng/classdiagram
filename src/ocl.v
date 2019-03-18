(* @name Formalization of OCL
   @version 1.0
   @domains 
   @authors Feng sheng 
   @date 22/05/2017
   @description object diagrams (Coq v8.5)
*)

Require Import List.
Require Import ZArith.
Require Import String.
Require Import Reals.
Require Export cd.

Import ListNotations.

(* use natural numbers as identifiers *)
Inductive id : Set := Id : nat -> id.

(* a state represents the current values of all the variables *)
Definition state := id -> nat.

Definition varname := string.

Inductive OclClassifier :=
| OCLAny : OclClassifier
| OCLMessage : string -> OclClassifier
| OCLVoid : OclClassifier
| OCLInvalid : OclClassifier
| OCLInt : option nat -> OclClassifier
| OCLString : option string -> OclClassifier
| OCLBoolean : option bool -> OclClassifier
| OCLClass : Class -> OclClassifier
| OCLSet : OclClassifier
| OCLOrdSet : OclClassifier
| OCLBag : OclClassifier
| OCLSeq : OclClassifier
.

Inductive oclexpr :=
| CIF : boolexpr -> oclexpr -> oclexpr -> oclexpr
| VAR : varname -> oclexpr
| LET : varname -> oclexpr -> oclexpr -> oclexpr
| MSG : string -> oclexpr
| LIT : OclClassifier -> oclexpr
| ITER : oclexpr -> list OclClassifier -> oclexpr
| BOOL : boolexpr -> oclexpr
| LOOP : varname -> list oclexpr -> oclexpr
with
boolexpr :=
| True : boolexpr
| False : boolexpr 
| lesser : oclexpr -> oclexpr -> boolexpr
| greater : oclexpr -> oclexpr -> boolexpr
| lseq : oclexpr -> oclexpr -> boolexpr
| greq : oclexpr -> oclexpr -> boolexpr
| eq : oclexpr -> oclexpr -> boolexpr.

(*
Inductive oclexpr :=
| IFExpr : ifexpr -> oclexpr
| VAR : varname -> oclexpr
| LETExpr : letexpr -> oclexpr
| MSGExpr : string -> oclexpr
| LITExpr : OclClassifier -> oclexpr
| ITERExpr : iterexpr -> oclexpr
| BOOLExpr : boolexpr -> oclexpr
| TYPEExpr : loopexpr -> oclexpr
with
ifexpr :=
| CIF : boolexpr -> oclexpr -> oclexpr -> ifexpr
with
letexpr :=
| LET : varname -> oclexpr -> oclexpr -> letexpr
with
iterexpr :=
| ITER : oclexpr -> list OclClassifier -> iterexpr
with
loopexpr :=
| LOOP : varname -> list oclexpr -> loopexpr
with
boolexpr :=
| True : boolexpr
| False : boolexpr 
| lesser : oclexpr -> oclexpr -> boolexpr
| greater : oclexpr -> oclexpr -> boolexpr
| lseq : oclexpr -> oclexpr -> boolexpr
| greq : oclexpr -> oclexpr -> boolexpr
| eq : oclexpr -> oclexpr -> boolexpr
.

Print oclexpr_rect.
(* *)
 *)
Inductive ConstraintType :=
| Inv    | Pre
| Post   | Guard.


Inductive Constraint := 
| CONS : OclClassifier -> ConstraintType -> oclexpr -> Constraint.


Definition OCLConstraints := list Constraint.

Section Example.

  Print string.

  Open Scope string_scope.

  Definition active : string := "isActive".

  Definition oe1 : oclexpr :=
    BOOL (eq (VAR active) (LIT (OCLBoolean (Some false)))).

  Parameter Customer : Class.

  Definition c1 : Constraint :=
    CONS (OCLClass Customer) Inv oe1.

  Definition lstOcl := [c1].

End Example.


(* definitions for arithmetic expression and boolean expression *)
Inductive aexp : Type := 
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BGt : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr : bexp -> bexp -> bexp
  | BImp : bexp -> bexp -> bexp.

(* evaluation functions for arithmetic expression and boolean expression *)
Fixpoint aeval (st : state) (e : aexp) {struct e} : nat :=
  match e with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => plus (aeval st a1) (aeval st a2)
  | AMinus a1 a2  => minus (aeval st a1) (aeval st a2)
  | AMult a1 a2 => mult (aeval st a1) (aeval st a2)
  end.


Fixpoint ble_nat (n m : nat) {struct n} : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Fixpoint bgt_nat (n m : nat) {struct n} : bool :=
  match m with
  | O => true
  | S m' =>
      match n with
      | O => false
      | S n' => ble_nat m' n'
      end
  end.

Fixpoint beval (st : state)(e : bexp) {struct e} : bool :=
  match e with 
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BGt a1 a2 => bgt_nat (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  | BOr b1 b2 => orb (beval st b1) (beval st b2)
  | BImp b1 b2 => orb (negb (beval st b1)) (beval st b2)
  end.


