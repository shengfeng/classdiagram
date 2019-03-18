Require Import Coq.Lists.List. 
Import ListNotations.
Require Import Coq.Sorting.Mergesort. 
Import NatSort.

Scheme Equality for nat.

Print sort.
Print iter_merge.

Inductive Gen : Set :=
| BGen : nat -> nat -> Gen.

Definition g1 := BGen 1 2.
Definition g2 := BGen 2 3.


Fixpoint parents (l : list Gen) (c : nat) :=
  match l with
  | [] => []
  | (BGen p c') :: l' => if nat_beq c c'
                         then [p]
                         else parents l' c
  end.

Fixpoint deduplicate' (ls : list nat) :=
  match ls with
  | [] => []
  | x :: [] => [x]
  | x :: ((y :: ys) as xs)
    => if nat_beq x y
       then deduplicate' xs
       else x :: deduplicate' xs
  end.

Definition deduplicate (ls : list nat) := deduplicate' (sort ls).

Definition parents_step (l : list Gen) (cs : list nat) :=
  deduplicate (cs ++ List.flat_map (parents l) cs).

Fixpoint all_parents' (l : list Gen) (cs : list nat) (fuel : nat) :=
  match fuel with
  | 0 => cs
  | S fuel'
    => all_parents' l (parents_step l cs) fuel'
  end.

Definition all_parents (l : list Gen) (c : nat) :=
  deduplicate (all_parents' l (parents l c) (List.length l)).

Definition gs := (g1::g2::nil).