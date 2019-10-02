Add LoadPath "~/Desktop/classdiagram/src".

Require Export classdiagram.
Require Export String ListSet List Arith Bool.
Open Scope nat_scope.
Open Scope type_scope.
Open Scope string_scope.
Open Scope list_scope.
Import ListNotations.


Definition refine_class :=  list (class * class).

Definition refine_assoc := list (assoc * assoc).

Definition refine_multiplicity :=
  list (multiplicity * multiplicity).

Definition refine_t :=
  refine_class * refine_assoc * refine_multiplicity.


(** ----- projections ----- **)
(* \u83b7\u53d6\u7cbe\u5316\u5173\u7cfb\u4e2d\u7684\u62bd\u8c61\u7c7b *)
Fixpoint get_refinement_aclass (ref : refine_class) (c : class) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_class (fst h) c
                 then Some (snd h)
                 else get_refinement_aclass ref' c
  end.

(* \u83b7\u53d6\u7cbe\u5316\u5173\u7cfb\u4e2d\u7684\u5177\u4f53\u7c7b *)
Fixpoint get_refinement_cclass (ref : refine_class) (a : class) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_class (snd h) a
                 then Some (fst h)
                 else get_refinement_cclass ref' a
  end.



Fixpoint get_refinement_aassoc (ref : refine_assoc) (c : assoc) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_assoc (fst h) c
                 then Some (snd h)
                 else get_refinement_aassoc ref' c
  end.



Fixpoint get_refinement_cassoc (ref : refine_assoc) (a : assoc) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_assoc (snd h) a
                 then Some (fst h)
                 else get_refinement_aassoc ref' a
  end.


Fixpoint get_refinement_amulti (ref : refine_multiplicity) (c : multiplicity) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_multiplicity (fst h) c
                 then Some (snd h)
                 else get_refinement_amulti ref' c
  end.


Fixpoint get_refinement_cmulti (ref : refine_multiplicity) (c : multiplicity) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_multiplicity (snd h) c
                 then Some (fst h)
                 else get_refinement_amulti ref' c
  end.



Definition natural_nat (n : natural) :=
  match n with
  | Nat m => Some m
  | Star => None
  end.


Definition lattice (n m : natural) :=
  match n, m with
  | Star, Star => true
  | Star, Nat _ => false
  | Nat _, Star => true
  | Nat a, Nat b => Nat.leb a b
  end.


(** ----- rules ----- **)
Definition b1 (C0 A0 : SimpleUML) (R0 : refine_class) :=
  forall (c : class), In c (classes C0) ->
    exists! a, In a (classes A0) /\ 
    Some a = get_refinement_aclass R0 c.



Definition b2 (C1 A1 : SimpleUML) (R1 : refine_assoc) :=
  forall c, In c (assocs C1) ->
    exists! a, In a (assocs A1) /\ 
    Some a = get_refinement_aassoc R1 c.


Definition b3 (C1 A1 : SimpleUML) (R0 : refine_class) (R1 : refine_assoc) :=
  forall c, In c (assocs C1) ->
    forall a, In a (assocs A1) ->
      Some a = get_refinement_aassoc R1 c.



Definition b4 (C1 A1 : SimpleUML) (R0 : refine_class) :=
  forall a1 a2, In (BGen a1 a2) (generalizations A1) ->
    exists c1 c2,
      Some c1 = get_refinement_cclass R0 a1 /\
      Some c2 = get_refinement_cclass R0 a2 /\
      In (BGen c1 c2) (generalizations C1).


Definition b5 (C2 A2 : SimpleUML) (R2 : refine_multiplicity) :=
  forall c a : multiplicity, 
    In c (multiplicities C2) /\ In a (multiplicities A2) ->
    Some a = get_refinement_amulti R2 c /\ 
    lattice (multi_lower a) (multi_lower c) = true /\
    lattice (multi_upper c) (multi_upper a) = true.