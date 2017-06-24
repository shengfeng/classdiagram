Require Export cd.
Require Import List.
Require Import String.
Require Import ListSet.
Import ListNotations.

Parameter R : Class -> Class -> Class -> list Assoc.
Parameter CA : Class -> Class -> assocKind -> Assoc.

Inductive refineone : SimpleUML -> SimpleUML -> Prop :=
| import:  forall c' ci cj C T P S G,
    not (set_In c' C) -> 
    set_In ci C /\ set_In cj C ->
    let C' := (c':: C) in
    let S' := set_union eqAssoc_dec (R ci cj c') S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
| dec1: forall c' ci C T P S G,
    not (set_In c' C) -> 
    set_In ci C ->
    let C' := (c':: C) in
    let G' := set_add eqGen_dec (BGen ci c') G in 
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S G')
| dec2 : forall c' ci C T P S G,
    not (set_In c' C) ->
    set_In ci C ->
    let C' := (c' :: C) in
    let S' := (CA c' ci composite) :: S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
| dec3 : forall c' ci C T P S G,
    not (set_In c' C) ->
    set_In ci C ->
    let C' := (c' :: C) in
    let S' := (CA c' ci aggregate) :: S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
| intro1 : forall c' ci C T P S G,
    not (set_In c' C) ->
    set_In ci C ->
    let C' := (c' :: C) in
    let S' := (CA c' ci none) :: S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
| intro2 : forall c' ci C T P S G,
    not (set_In c' C) ->
    set_In ci C ->
    let C' := (c' :: C) in
    let S' := (CA c' ci directed) :: S in
    refineone (mkSimpleUML C T P S G) (mkSimpleUML C' T P S' G)
.
