Require Export classdiagram.

Require Export String ListSet List Arith Bool.
Open Scope nat_scope.
Open Scope type_scope.
Open Scope string_scope.
Open Scope list_scope.
Import ListNotations.


Definition refine_class := 
  list (class * class).

Definition refine_association :=
  list (association * association).

Definition refine_multiplicity :=
  list (multiplicity * multiplicity).


Definition refine_t :=
  refine_class * refine_association * refine_multiplicity.



(** ----- projections ----- **)
Fixpoint get_refinement_aclass (ref : refine_class) (c : class) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_class (fst h) c
                 then Some (snd h)
                 else get_refinement_aclass ref' c
  end.


Fixpoint get_refinement_cclass (ref : refine_class) (a : class) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_class (snd h) a
                 then Some (fst h)
                 else get_refinement_cclass ref' a
  end.



Fixpoint get_refinement_aassoc (ref : refine_association) (c : association) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_association (fst h) c
                 then Some (snd h)
                 else get_refinement_aassoc ref' c
  end.



Fixpoint get_refinement_cassoc (ref : refine_association) (a : association) :=
  match ref with
  | [] => None
  | h :: ref' => if beq_association (snd h) a
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


Print le.
(*
Inductive natural :=
| Nat : nat -> natural
| Star : natural.
*)


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

(**
Inductive lattice (n : natural) : natural -> Prop :=
| la_Star : lattice n Star
| la_Succ : forall m, Some m = natural_nat n -> lattice m n.
**)

(** ----- rules ----- **)

Definition b1 (C A : SimpleUML) (ref : refine_class) :=
  forall (c : class), In c (classes C) ->
    exists! a, In a (classes A) /\ 
    Some a = get_refinement_aclass ref c.



Definition b2 (C A : SimpleUML) (ref : refine_association) :=
  forall c, In c (associations C) ->
    exists! a, In a (associations A) /\ 
    Some a = get_refinement_aassoc ref c.



Definition b4 (C A : SimpleUML) (ref : refine_class) :=
  forall a1 a2 n, In (BGen n a1 a2) (generalizations A) ->
    exists n' c1 c2,
      Some c1 = get_refinement_cclass ref a1 /\
      Some c2 = get_refinement_cclass ref a2 /\
      In (BGen n' c1 c2) (generalizations C).


Definition b5 (C A : SimpleUML) (ref : refine_multiplicity) :=
  forall c a : multiplicity, 
    In c (multiplicities C) /\ In a (multiplicities A) ->
    Some a = get_refinement_amulti ref c /\ 
    lattice (multi_lower a) (multi_lower c) = true /\
    lattice (multi_upper c) (multi_upper a) = true.