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
  Id : nat -> id.


Definition class := id * name * bool.


Inductive PrimitiveType :=
| integer : PrimitiveType
| string_ : PrimitiveType
| float : PrimitiveType
| real : PrimitiveType
| boolean : PrimitiveType
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



Definition attribute_dec : forall (a b : attribute), {a = b} + {a <> b}.
  repeat decide equality.
Defined.

Definition operation_dec : forall (a b : operation), {a = b} + {a <> b}.
  repeat decide equality.
Defined.

Definition association_dec : forall (a b : association), {a = b} + {a <> b}.
  repeat decide equality.
Defined.

Definition rolename_dec : forall (a b : rolename), {a = b} + {a <> b}.
  repeat decide equality.
Defined.

Definition mulplicity_dec : forall (a b : multiplicity), {a = b} + {a <> b}.
  repeat decide equality.
Defined.


Definition generalization_dec : forall (a b : generalization), {a = b} + { a <> b}.
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

Definition assoc_id (a : association) : id := fst (fst a).

Definition assoc_name (a : association) : string := snd (fst a).

Definition assoc_class (a : association) : list class := snd a.

Definition rolename_id (r : rolename) : id := fst (fst r).

Definition rolename_name (r : rolename) : list name := snd (fst r).

Definition rolename_assoc (r : rolename) : association := snd r.


Definition gen_id (g : generalization) : id := fst (fst g).


Definition gen_super (g : generalization) : class := snd (fst g).


Definition gen_sub (g : generalization) : class := snd g.

(* ----- Fuctions ----- *)
Check count_occ.

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



(* ----- Rules ----- *)

Definition UniqueClass (model : CD) :=
  NoDup (map class_name (classes model)).


Definition UniqueAttribute (model : CD) :=
  forall c : class,  In c (classes model) ->
      NoDup (map attribute_name (class_attribute c (attributes model))).


(* object diagrams *)

Definition object :=
  id * name * class.

Definition link :=
  id * list object * association.


(* ----- Equation Judgement ----- *)
Definition object_dec : forall (a b : object), {a = b} + {a <> b}.
  repeat decide equality.
Defined.


Definition link_dec : forall (a b : link), {a = b} + {a <> b}.
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


Check oid.
Check lid.


Print PrimitiveType.
(*
Inductive PrimitiveType : Type :=
    integer : PrimitiveType
  | string_ : PrimitiveType
  | float : PrimitiveType
  | real : PrimitiveType
  | boolean : PrimitiveType
 *)

(*
Inductive value : PrimitiveType -> Type -> Set :=
| vInterger : value integer nat
| vString : value string_ string
| vFloat : value float  nat
| vReal : value real nat
| vBoolean : value boolean bool
.
*)

(* we ignore the value of object *)
Definition value := string.


Definition attrval :=
  id * attribute * value * object.


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

Inductive basic_type :=
| Integer : nat -> basic_type
| Real : nat -> basic_type
| Boolean : bool -> basic_type
| String : string -> basic_type
.

(* ----- Functions ----- *)

Fixpoint andb (b1 b2: option bool) : option bool :=
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


Fixpoint orb (b1 b2: option bool) : option bool :=
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


Fixpoint xorb (b1 b2: option bool) : option bool :=
match b1, b2 with
| Some false, Some false => Some false
| Some false, Some true => Some true
| Some true, Some false => Some true
| Some true, Some true => Some false
| _, _ => None
end.


Fixpoint implies (b1 b2: option bool) : option bool :=
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


Fixpoint not (b1 : option bool) : option bool :=
match b1 with
| Some false => Some true
| Some true => Some false
| _ => None
end.