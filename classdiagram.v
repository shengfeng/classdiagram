(**
 
 @Name Formalization of class diagrams
 @version 1.4
 @domains 
 @authors Feng sheng 
 @date 24/10/2017
 @description class and object diagrams (Coq v8.7)

**)


Require Import Arith.
Require Import List.
Require Import String.

Open Scope nat_scope.
Open Scope type_scope.
Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.


Definition name := string.


Inductive id : Set := 
  | Id : nat -> id.


Definition beq_id x y :=
  match x, y with
    | Id n1, Id n2 => if beq_nat n1 n2 then true else false
  end.


Definition class := id * name * bool.


Inductive PrimitiveType :=
| pinteger : PrimitiveType
| pstring : PrimitiveType
| pfloat : PrimitiveType
| preal : PrimitiveType
| pboolean : PrimitiveType
.


Definition attribute := 
  id * name * PrimitiveType * class.


Definition parameter_ := 
  id * name * PrimitiveType.


Definition operation :=
  id * name * list parameter_ * class.


Definition association :=
  id * name * list class.


Definition rolename :=
  id * list name * association.


Inductive Natural :=
| Nat : nat -> Natural
| Star : Natural.


Definition multiplicity :=
  id * class * Natural * Natural * association.


Definition generalization :=
  id * class * class.


Record CD : Set := 
  mkCD {
    classes : list class;
    attributes : list attribute;
    associations : list association;
    rolenames : list rolename;
    multiplities : list multiplicity;
    generalizations : list generalization
  }.


(* ========== Equality Judgement ========== *)
Definition class_dec : forall (a b : class), {a = b} + {a <> b}.
  repeat decide equality.
Defined.


Definition beqClass_dec a b :=
  match class_dec a b with
    | left _ => true
    | right _ => false
  end.


Definition attribute_dec :
  forall (a b : attribute), {a = b} + {a <> b}.
  repeat decide equality.
Defined.


Definition operation_dec :
  forall (a b : operation), {a = b} + {a <> b}.
  repeat decide equality.
Defined.

Definition association_dec :
  forall (a b : association), {a = b} + {a <> b}.
  repeat decide equality.
Defined.


Definition rolename_dec :
  forall (a b : rolename), {a = b} + {a <> b}.
  repeat decide equality.
Defined.


Definition mulplicity_dec :
  forall (a b : multiplicity), {a = b} + {a <> b}.
  repeat decide equality.
Defined.


Definition generalization_dec :
  forall (a b : generalization), {a = b} + { a <> b}.
  repeat decide equality.
Defined.


(* ----- projections ----- *)
Definition class_id (c : class) : id := fst (fst c).

Definition class_name (c : class) : name := snd (fst c).

Definition class_abstract (c : class) : bool := snd c.


Definition attribute_id (a : attribute) : id := fst (fst (fst a)).

Definition attribute_name (a : attribute) : name := snd (fst (fst a)).

Definition attribute_type (a : attribute) : PrimitiveType := snd (fst a).

Definition attribute_class (a : attribute) : class := snd a.


Definition operation_id (o : operation) : id := fst (fst (fst o)).

Definition operation_name (o : operation) : name := snd (fst (fst o)).

Definition operation_params (o : operation) := snd (fst o).

Definition operation_class (o : operation) := snd o.


Definition assoc_id (a : association) : id := fst (fst a).

Definition assoc_name (a : association) : string := snd (fst a).

Definition assoc_class (a : association) : list class := snd a.


Definition rolename_id (r : rolename) : id := fst (fst r).

Definition rolename_name (r : rolename) : list name := snd (fst r).

Definition rolename_assoc (r : rolename) : association := snd r.


Definition gen_id (g : generalization) : id := fst (fst g).

Definition gen_super (g : generalization) : class := snd (fst g).

Definition gen_sub (g : generalization) : class := snd g.


Definition mult_id (m : multiplicity) : id := fst (fst (fst (fst m))).

Definition mult_class (m : multiplicity) : class := snd (fst (fst (fst m))).

Definition mult_lower (m : multiplicity) : Natural := snd (fst (fst m)).

Definition mult_upper (m : multiplicity) : Natural := snd (fst m).

Definition mult_assoc (m : multiplicity) : association := snd m.


(* ----- Fuctions ----- *)
Print count_occ.


Fixpoint in_class (c : class) (l : list class) : bool :=
match count_occ class_dec l c with
| 0 => false
| _ => true
end.


Fixpoint partipating (c : class) (l : list association) :=
match l with
| [] => []
| x :: h => if in_class c (assoc_class x) 
            then x :: partipating c h
            else partipating c h
end.


Fixpoint find_assoc (a : association) (l : list rolename) :=
match l with
| [] => []
| x :: h => if association_dec a (rolename_assoc x)
            then rolename_name x
            else find_assoc a h
end.


Fixpoint pos (c : class) (l : list class) (n : nat) :=
match l with
| [] => None
| x :: h => if class_dec x c 
            then Some n
            else pos c h (S n)
end.


Fixpoint remove_nth (l : list name) (n : nat) {struct l} :=
match n, l with
| 0, [] => []
| 0, x :: h => h
| S n', [] => [] 
| S n', x :: h => x :: remove_nth h n'
end.


Definition navends (c : class) (a : association) (l : list rolename) :=
match (pos c (assoc_class a) 0) with
| None => find_assoc a l
| Some n => remove_nth (find_assoc a l) n
end.


Fixpoint all_navends (c : class) (la : list association) (lr : list rolename) :=
match la with
| [] => []
| x :: h => app (navends c x lr) (all_navends c h lr)
end.


Fixpoint class_attribute (c : class) (l : list attribute) := 
match l with
| [] => []
| x :: h => if class_dec c (attribute_class x)
            then x :: class_attribute c h
            else class_attribute c h
end.


Fixpoint children (l : list generalization) (c : class) :=
  match l with
    | [] => []
    | g :: h => if class_dec c (gen_super g)
                then (gen_sub g) :: children h c
                else children h c
  end.


Fixpoint parents (l : list generalization) (c : class) :=
  match l with
    | [] => []
    | g :: h => if class_dec c (gen_sub g)
                then (gen_super g) :: parents h c
                else parents h c
  end.


Definition class_ids (l : list class) :=
  map class_id l.

Check class_ids.


Definition attribute_ids (l : list attribute) :=
  map attribute_id l.


Definition operation_ids (l : list operation) :=
  map operation_id l.


Definition assoc_ids (l : list association) :=
  map assoc_id l.


Definition role_ids (l : list rolename) :=
  map rolename_id l.


Definition mult_ids (l : list multiplicity) :=
  map mult_id l.


Definition gen_ids (l : list generalization) :=
  map gen_id l.

  
(* ----- Rules ----- *)

Definition UniqueClass (model : CD) :=
  NoDup (map class_name (classes model)).


Definition UniqueAttribute (model : CD) :=
  forall c : class,  In c (classes model) ->
      NoDup (map attribute_name (class_attribute c (attributes model))).


Fixpoint deduplicate (l : list class) :=
  match l with
    | [] => []
    | x :: h => if leb (count_occ class_dec l x) 1
                then x :: deduplicate h
                else deduplicate h
  end.


Definition parents_step (l : list generalization) (cs : list class) :=
  deduplicate (cs ++ List.flat_map (parents l) cs).


Fixpoint all_parents' (l : list generalization) (cs : list class) (fuel : nat) :=
  match fuel with
  | 0 => cs
  | S fuel'=> all_parents' l (parents_step l cs) fuel'
  end.


Definition all_parents (l : list generalization) (c : class) :=
  deduplicate (all_parents' l (parents l c) (List.length l)).


(* object diagrams *)

Definition object :=
  id * name * class.

Definition link :=
  id * list object * association.


Print PrimitiveType.
(*
Inductive PrimitiveType : Type :=
    pinteger : PrimitiveType
  | pstring : PrimitiveType
  | pfloat : PrimitiveType
  | preal : PrimitiveType
  | pboolean : PrimitiveType
*)


Inductive TB :=
| Integer : option nat -> TB
| Real : option nat -> TB
| Boolean : option bool -> TB
| String : option string -> TB
.

(*

(* we ignore the value of object *)
Definition value := intepret_pt.

*)

Definition attrval :=
  id * attribute * TB * object.


(* ----- Equation Judgement ----- *)
Definition object_dec :
  forall (a b : object), {a = b} + {a <> b}.
  repeat decide equality.
Defined.


Definition link_dec :
  forall (a b : link), {a = b} + {a <> b}.
  repeat decide equality.
Defined.


(* ----- projections ----- *)

Definition object_id (o : object) : id := fst (fst o).


Definition object_name (o : object) : name := snd (fst o).


Definition object_class (o : object) : class := snd o.


Definition link_id (l : link) : id := fst (fst l).

Definition link_objects (l : link) : list object := snd (fst l).

Definition link_assoc (l : link) : association := snd l.


(* ----- functions ------ *)

Fixpoint oid (l : list object) (c : class) :=
  match l with
    | [] => []
    | x :: h => if class_dec c (object_class x)
                then x :: oid h c
                else oid h c
  end.


(* ##### the domain of a class #### *)
Print children.

Print List.flat_map.


Definition obj_domain (c : class) (lg : list generalization) (lo : list object) :=
  (oid lo c) ++ List.flat_map (oid lo) (children lg c).


Print obj_domain.


Fixpoint lid (a : association) (l : list link) :=
  match l with
    | [] => []
    | x :: h => if association_dec a (link_assoc x)
                then x :: lid a h
                else lid a h
  end.


Record obj : Set :=
  mkObj{
      objects : list object;
      links : list link;
      attrvals : list attrval
    }.


(* ----- Rules ----- *)

Lemma Generalization_Subst :
  forall (c1 c2 : class) (g : generalization),
    c1 = gen_super g /\ c2 = gen_sub g ->
	forall (o : object) (lg : list generalization) (lo : list object), 
        In o (obj_domain c2 lg lo) -> In o (obj_domain c1 lg lo).
Proof.
  intros.
Admitted.


(* ----- OCL ----- *)

(* ----- Functions ----- *)

Open Scope nat_scope.


Fixpoint ocl_andb (b1 b2: option bool) : option bool :=
match b1, b2 with
| Some false, Some false => Some false
| Some false, Some true => Some false
| Some true, Some false => Some false
| Some true, Some true => Some true
| Some false, None => Some false
| Some true, None => None
| None, Some false => Some false
| _, _ => None
end.


Fixpoint ocl_orb (b1 b2: option bool) : option bool :=
match b1, b2 with
| Some false, Some false => Some false
| Some false, Some true => Some true
| Some true, Some false => Some true
| Some true, Some true => Some true
| Some false, None => None
| Some true, None => Some true
| None, Some false => None
| None, Some true => Some true
| _, _ => None
end.


Fixpoint ocl_xorb (b1 b2: option bool) : option bool :=
match b1, b2 with
| Some false, Some false => Some false
| Some false, Some true => Some true
| Some true, Some false => Some true
| Some true, Some true => Some false
| _, _ => None
end.


Fixpoint ocl_implies (b1 b2: option bool) : option bool :=
match b1, b2 with
| Some false, Some false => Some true
| Some false, Some true => Some true
| Some true, Some false => Some false
| Some true, Some true => Some true
| Some false, None => Some true
| Some true, None => None
| None, Some false => None
| None, Some true => Some true
| _, _ => None
end.


Fixpoint ocl_not (b1 : option bool) : option bool :=
match b1 with
| Some false => Some true
| Some true => Some false
| _ => None
end.


Fixpoint ocl_oadd (a1 a2 : option nat) : option nat :=
  match a1, a2 with
    | Some n1, Some n2 => Some (n1 + n2)
    | _, _ => None
  end.


(* ----- TODO ------ *)


(* ----- Expression ------ *)
Inductive OCLExp :=
| Basic : TB -> OCLExp
| OSet : OCLExp -> OCLExp
| OSeq : OCLExp -> OCLExp
| OBag : OCLExp -> OCLExp
| OCol : OCLExp -> OCLExp
| Any : OCLExp.






