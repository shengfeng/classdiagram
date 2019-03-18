
(* Copyright (c), Department of Computer Science and Engineering
 * East China Normal University, Shanghai, China.
 * All rights reserved.
 * Author: Feng Sheng
 * Email: fsheng1990@163.com
 * Description: Mechanized Semantics of UML sequence diagram
     and Refinement Relation
*)

Require Export String Bool ListSet List Arith Permutation.

Open Scope type_scope.


(* ======== Definition of Semantics Model of Sequence Diagrams ========= *)

(* The definition specifies the kind of a event *)

Inductive kd : Set :=
| Send : kd
| Receive : kd.


Notation "!" := Send (at level 40).
Notation "?" := Receive (at level 40).

(* The definition specifies the signal and lifeline *)
Definition sg := string.
Definition lf := string.

(* An event is defined as a signal send between two lifelines with kind *) 
Definition evt := kd * sg * lf * lf.

(* The definition specifies the syntax of condition *)
Inductive id : Type := Id : nat -> id.

Inductive cnd : Type :=
| Bvar : id -> cnd
| Btrue : cnd 
| Bfalse : cnd
| Bnot : cnd -> cnd
| Band : cnd -> cnd -> cnd 
| Bor : cnd -> cnd -> cnd
| Bimp : cnd -> cnd -> cnd.


(* Inductive type for event with guard(condition)*)
Inductive tk : Type :=
| ev : evt -> tk
| cd : cnd -> tk.

(* A trace is a list of event and condition *)
Definition tr := list tk.

(* An obligation is a set of trace *)
Definition ob := set tr.

(* A model is a set of obligation *)
Definition mo := set ob.

(* The definition of state *)
Definition state := id -> bool.


(*Shorthands for variables*)
Definition P : id := Id 0.
Definition Q : id := Id 1.
Definition R : id := Id 2.

Definition empty_state : state := fun _ => true. 

(*===========Equality Judgement============*)
Definition kd_dec : forall (a b : kd), {a = b} + {a <> b}.
    repeat decide equality.
Defined.

Definition sg_dec : forall (a b : sg) ,{a = b} + {a <> b}.
   exact string_dec.
Defined.

Definition lf_dec : forall (a b : lf) ,{a = b} + {a <> b}.
   exact string_dec.
Defined.

Definition evt_dec : forall (a b : evt) ,{a = b} + {a <> b}.
   repeat decide equality.
Defined.

Definition id_dec : forall (a b : id) ,{a = b} + {a <> b}.
  repeat decide equality. 
Defined.

Definition cnd_dec : forall (a b : cnd) ,{a = b} + {a <> b}.
   repeat decide equality. 
Defined.

Definition tk_dec : forall (a b : tk) ,{a = b} + {a <> b}.
   repeat decide equality. 
Defined.

Definition tr_dec : forall (a b : tr) ,{a = b} + {a <> b}.
   repeat decide equality. 
Defined.

Definition ob_dec : forall (a b : ob) ,{a = b} + {a <> b}.
   repeat decide equality. 
Defined.

Definition mo_dec : forall (a b : mo) ,{a = b} + {a <> b}.
   repeat decide equality. 
Defined.


(*===========Functions for Equality Judgement ============*)

Definition beq_kd (k1 k2 : kd) : bool :=
match k1,k2 with
 |!, ! => true
 |?, ? => true
 |_, _ => false
end.


Definition string_eq_bool (s1 s2 : string) : bool :=
  andb (prefix s1 s2) 
       (beq_nat (String.length s1) (String.length s2)).

Definition beq_sg (s1 : sg)(s2 : sg) : bool :=
   string_eq_bool s1 s2.

Definition beq_lf (l1 : lf)(l2 : lf) : bool :=
   string_eq_bool l1 l2.

Definition beq_evt (e1 : evt)(e2 : evt) : bool :=
match e1,e2 with 
(k1, s1, tr1, re1), (k2, s2, tr2, re2) =>
    andb (andb (beq_kd k1 k2) (beq_sg s1 s2)) 
         (andb (beq_lf tr1 tr2) (beq_lf re1 re2))
end.


(* Evaluate a condition in the state and reduce it to boolean value *)
Fixpoint beval (st : state)(c : cnd) : bool :=
  match c with 
  | Bvar i => st i
  | Btrue => true
  | Bfalse => false
  | Bnot b1 => negb (beval st b1)
  | Band b1 b2 => andb (beval st b1) (beval st b2)
  | Bor b1 b2 => orb (beval st b1) (beval st b2)
  | Bimp b1 b2 => orb (negb (beval st b1)) (beval st b2)
  end.


Definition beq_cnd (st : state)(be1 : cnd)(be2 : cnd) : bool :=
  eqb (beval st be1) (beval st be2).


Definition beq_tk (st : state)(ce1 : tk)(ce2 : tk) : bool :=
match ce1, ce2 with
|ev e1, ev e2 => beq_evt e1 e2
|ev e, cd c => false
|cd c, ev e => false
|cd c1, cd c2 => beq_cnd st c1 c2
end.

Fixpoint beq_tr (st : state)(t1 : tr)(t2 : tr) : bool :=
match t1, t2 with
|nil, nil => true
|t1::tail1, t2::tail2 => if (beq_tk st t1 t2) 
                           then (beq_tr st tail1 tail2) 
                           else false
|_, _ => false
end.

Fixpoint beq_ob (st : state)(t1 : set tr)(t2 : set tr) : bool :=
match t1, t2 with
|nil, nil => true
|t1::tail1, t2::tail2=> if (beq_tr st t1 t2) 
                          then (beq_ob st tail1 tail2) 
                          else false
|_, _ => false
end.

Fixpoint beq_mo (st : state)(t1 : set (set tr))(t2 : set (set tr)) : bool :=
match t1, t2 with
|nil, nil => true
|t1::tail1, t2::tail2 => if (beq_ob st t1 t2) 
                           then (beq_mo st tail1 tail2) 
                           else false
|_, _ => false
end.

Fixpoint evtMem (e : evt) (se :list evt) : bool :=
match se with
|nil => false
|t::tail => if beq_evt e t then true else (evtMem e tail)
end.


(*==========Syntax of Sequence Diagram===============*)
Inductive sd : Set :=
|Dtau : sd
|De : evt -> sd
|Dstrict : sd -> sd -> sd
|Dopt : cnd -> sd -> sd
|Dalt : cnd -> sd -> sd -> sd
|Dpar : sd -> sd -> sd
|DSeq : sd -> sd -> sd
|Dloop : cnd -> nat -> sd -> sd.

(* Get events from a sequence diagram *)
Fixpoint getEvts (d : sd) : set evt :=
match d with
|Dtau => nil
|De e => e :: nil
|Dstrict SD1 SD2 => set_union evt_dec (getEvts SD1) (getEvts SD2)
|Dopt c SD => getEvts SD
|Dalt c SD1 SD2 => set_union evt_dec (getEvts SD1) (getEvts SD2)
|Dpar SD1 SD2 => set_union evt_dec (getEvts SD1)  (getEvts SD2)
|DSeq SD1 SD2 => set_union evt_dec (getEvts SD1)  (getEvts SD2)
|Dloop c n SD => getEvts SD
end.


(* Functional Scheme getEvts_ind :=
   Induction for getEvts Sort Prop. *)

(*=====Auxiliary functions, used in Weak Sequence=======*)

(* get kind from event *)
Definition getKd (e : evt) : kd := fst (fst (fst e)).

(* get transmitter's lifeline from event *)
Definition getTrLf(e : evt) : lf := (snd (fst e)).

(* get receiver's lifeline from event *)
Definition getReLf(e : evt) : lf := snd e.

(* get the lifeline set from a sequence diagram *)
Fixpoint getLfs (d : sd) : set lf :=
match d with
|Dtau => nil
|De e => snd(e) :: snd(fst e) ::nil
|Dstrict SD1 SD2 => set_union lf_dec (getLfs SD1) (getLfs SD2)
|Dopt c SD => getLfs SD
|Dalt c SD1 SD2 => set_union lf_dec (getLfs SD1) (getLfs SD2)
|Dpar SD1 SD2 => set_union lf_dec (getLfs SD1) (getLfs SD2)
|DSeq SD1 SD2 => set_union lf_dec (getLfs SD1)  (getLfs SD2)
|Dloop c n SD => getLfs SD
end.

(* Functional Scheme getLfs_ind :=
   Induction for getLfs Sort Prop. *)

(*--get related events from event set in particular lifeline*)
Fixpoint projLf (l : lf) (se : set evt) : set evt :=
match se with
|nil =>nil
|e :: tail => match e with
  |(!,_,t,r) => if (beq_lf t l) then e :: (projLf l tail) 
                else (projLf l tail)
  |(?,_,t,r) => if (beq_lf r l) then e :: (projLf l tail) 
                else (projLf l tail)
  end
end.

(*=====Auxiliary functions,used in Weak Sequence, End=======*)
(* test cases *)
(* d=(e1 Strict e2) Strict (e3 Strict e4) *)
Open Scope string_scope.
Definition e1Event : evt := (!, "calle", "l1", "l2").
Definition e2Event : evt := (?, "calle", "l1", "l2").
Definition e3Event : evt := (!, "return", "l1", "l2").
Definition e4Event : evt := (?, "return", "l1", "l2").
Definition d := Dstrict (Dstrict (De e1Event) (De e2Event)) 
                   (Dstrict (De e3Event) (De e4Event)).
Eval compute in evtMem e1Event (e1Event :: e2Event :: nil).
Eval compute in getEvts(d).

Open Scope list_scope.
(*======Auxiliary Functions for Denotational Semantics======*)

(*------1.Strict-------*)
Fixpoint strict{A B C : Type}(f : A -> B -> C)(l1 : list A)(l2 : list B)
 : list C :=
match l1 with 
|nil => nil
|a :: tail => (map (fun b => f a b) l2) ++ strict f tail l2
end.

(* Functional Scheme strict_ind := Induction for strict Sort Prop. *)

Definition strictOb (s1 s2: set tr) : set tr :=
   strict (@app _) s1 s2.

Definition strictMo (s1 s2 : set (set tr)) : set (set tr) :=
   strict (@strictOb) s1 s2.

(*------2.Alt-------*)
Fixpoint addCndOb (st : state)(c : cnd)(s : set tr) : set tr :=
match s with
|nil => nil
|a :: tail=> if (beq_tr st a nil) then (nil::(addCndOb st c tail))
              else ((cd c) :: a) :: (addCndOb st c tail)
end.

(* Functional Scheme addCndOb_ind := Induction for addCndOb Sort Prop. *)

Fixpoint addCndToMo (st : state)(c : cnd)(s : set (set tr)) : set (set tr) :=
match s with
|nil => nil
|a :: tail=> (addCndOb st c a) :: (addCndToMo st c tail)
end.

(* Functional Scheme addCndToMo_ind := Induction for addCndToMo Sort Prop. *)

Fixpoint altMoAux2 (st1 : set tr)(s2 : set (set tr)) :=
match s2 with
|nil => nil
|a :: tail =>  (st1 ++ a) :: altMoAux2 st1 tail
end.

(* Functional Scheme altMoAux2_ind := Induction for altMoAux2 Sort Prop. *)

Fixpoint altMoaux (s1 s2: set (set tr)) :=
match s1 with 
|nil => nil
|a :: tail => altMoAux2 a s2 ++ altMoaux tail s2
end.

(* Functional Scheme altMoaux_ind := Induction for altMoaux Sort Prop. *)

Definition altMo (st : state)(c : cnd)(s1 s2: set (set tr)): set (set tr) :=
if (beq_mo st s1 s2) then s1
   else altMoaux (addCndToMo st c s1) (addCndToMo st (Bnot c) s2).

(* Functional Scheme altMo_ind := Induction for altMo Sort Prop. *)

(*------3.Opt-------*)
Definition optMo (st : state)(c : cnd)(s : set (set tr)) : set (set tr) :=
match s with
|(nil :: nil) :: nil => (nil :: nil) :: nil
| _ =>  set_union ob_dec (addCndToMo st c s) ((nil :: nil) :: nil)
end.

(* Functional Scheme optMo_ind := Induction for optMo Sort Prop. *)

(*------4.Par---------*)
Fixpoint combListAuxAux (o1 : set tr)(l : set (set tr)) : set (set tr):=
match o1 with
|nil => nil
|t :: tail => (map (set_add tr_dec t ) l) ++ (combListAuxAux tail l)
end.

(* Functional Scheme combListAuxAux_ind := Induction for combListAuxAux Sort Prop. *)

Fixpoint combList (l : set (set tr)) : set (set tr) :=
match l with 
|nil => nil :: nil
|o1 :: tail=> combListAuxAux o1 (combList tail)
end.

(* Functional Scheme combList_ind := Induction for combList Sort Prop. *)

(* add event to obligation *)
Fixpoint addEvtOb (e : tk) (o : set tr) : set tr :=
match o with
| nil => nil
| t :: R => (e :: t) :: (addEvtOb e R)
end.

Fixpoint intlev (t1 : tr) {struct t1}: tr -> set tr :=
match t1 with
| nil => fun t2 => (t2 :: nil)
| x :: u => fix aux (t2 : tr) {struct t2} : (set tr) :=
           match t2 with
           | nil => (t1 :: nil)
           | y :: v => set_union tr_dec
                      (addEvtOb x (intlev u t2))
                         (addEvtOb y (aux v))
           end
end.

Fixpoint intlevObAux2 (t1 : tr) (s2 : set tr) : set ob :=
match s2 with
| nil => nil
| t2 :: tail2 => (intlev t1 t2) :: (intlevObAux2 t1 tail2)
end. 

Fixpoint intlevObAux (s1 s2 : set tr) : set ob :=
match s1 with
| nil => nil
| t1::tail1 => set_union ob_dec (intlevObAux2 t1 s2) (intlevObAux tail1 s2)
end.

(* Functional Scheme intlevObAux2_ind := Induction for intlevObAux2 Sort Prop.
Functional Scheme intlevObAux_ind := Induction for intlevObAux Sort Prop. *)

Definition intlevOb (s1 s2: set tr) : set (set tr) :=
   combList (intlevObAux s1 s2).

Fixpoint parMoAux (t1 : set tr)(s2 : set (set tr)) : set (set tr) :=
match s2 with
| nil => nil
| t2 :: tail2 => set_union ob_dec (intlevOb t1 t2) (parMoAux t1 tail2)
end.

(* Functional Scheme parMoAux_ind := Induction for parMoAux Sort Prop. *)

Fixpoint parMo(s1 s2 : set (set tr)) : set (set tr) :=
match s1 with
| nil => nil
| t1 :: tail1 => set_union ob_dec (parMoAux  t1 s2) (parMo tail1 s2)
end.

(* Functional Scheme parMo_ind := Induction for parMo Sort Prop. *)

(*----------5.Weak Sequence-------*)
Fixpoint filter (evs : set evt) (t : tr) {struct t} : tr :=
match t with
|nil=> nil
|ev e :: tail=> 
  if (evtMem e evs) then (ev e)::(filter evs tail)
  else (filter evs tail)
|cd c :: tail => (filter evs tail)
end.

Fixpoint isWek (st : state)(es : set evt)(h1 h2 t: tr)(ls : set lf)
  : bool :=
match ls with
|nil => true
|l :: tail =>
(andb 
 (beq_tr st (filter (projLf l es) t) 
 ((filter (projLf l es) h1) ++ (filter (projLf l es) h2)))
 (isWek st es h1 h2 t tail))
end.

Fixpoint weakSeq (st : state)(es : set evt)(ls : set lf)(h1 : tr)(h2 : tr)(ts : set tr):set tr:=
match ts with
|nil => nil
|h :: tail => if (isWek st es h1 h2 h ls) 
             then h :: (weakSeq st es ls h1 h2 tail) 
             else (weakSeq st es ls h1 h2 tail)
end.

Fixpoint seqAux2 (st : state)(es : set evt)(ls : set lf)(t1 : tr)(s2 : set tr)(s : set tr) : set tr :=
match s2 with
|nil => nil
|t2 :: tail2 =>set_union tr_dec (weakSeq st es ls t1 t2 s) (seqAux2 st es ls t1 tail2 s)
end.

Fixpoint seqAux (st : state)(es : set evt)(ls : set lf)(s1 s2 s : set tr){struct s1}
 : set tr :=
match s1 with
|nil => nil
|t1 :: tail1 => set_union tr_dec (seqAux2 st es ls t1 s2 s)  (seqAux st es ls tail1 s2 s)
end. 

Fixpoint seqObAux (st : state)(es : set evt)(ls : set lf)(s1 s2 : set tr)(s : set (set tr)) :=
match s with 
|nil => nil
|t :: tail => set_add ob_dec (seqAux st es ls s1 s2 t) (seqObAux st es ls s1 s2 tail)
end.

(* Functional Scheme seqObAux_ind:= Induction for seqObAux Sort Prop. *)

(*based on seqObAux and intlevOb*)
Definition seqOb (st : state)(se : set evt)(ls : set lf)(s1 s2 : set tr) :set (set tr ) :=
  seqObAux st se ls s1 s2 (intlevOb s1 s2).

(* Functional Scheme seqOb_ind := Induction for seqOb Sort Prop. *)

Fixpoint seqMoAux (st : state)(se : set evt)(ls : set lf)(t1 : set tr)(s2 : set (set tr))
 : set (set tr) :=
match s2 with
|nil => nil
|t2 :: tail2 => set_union ob_dec (seqOb st se ls t1 t2) (seqMoAux st se ls t1 tail2)
end.

(* Functional Scheme seqMoAux_ind := Induction for seqMoAux Sort Prop. *)

Fixpoint seqMo (st : state)(se : set evt)(ls : set lf)(s1 s2: set (set tr))
 : set (set tr) :=
match s1 with
|nil => nil
|t1 :: tail1 => set_union ob_dec (seqMoAux st se ls t1 s2) (seqMo st se ls tail1 s2)
end.

(* Functional Scheme seqMo_ind := Induction for seqMo Sort Prop. *)

(*------6.Loop-------*)
Open Scope nat_scope.

Fixpoint getEvtsTr (t : tr) {struct t}  : set evt :=
match t with
| nil => nil
| a :: tail => match a with
  |(cd c1) => getEvtsTr tail
  |(ev e1) => set_union evt_dec (e1 :: nil) (getEvtsTr tail)
  end
end.

Fixpoint getEvtsOb (o : set tr) : set evt :=
match o with
|nil => nil
|a :: tail => set_union evt_dec (getEvtsTr a) (getEvtsOb tail)
end.

Fixpoint getEvtsMo (m : set (set tr)) : set evt :=
match m with
|nil => nil
|a :: tail => set_union evt_dec (getEvtsOb a) (getEvtsMo tail)
end.

Definition unionEvts (m1 m2 : set (set tr)) : set evt :=
 set_union evt_dec (getEvtsMo m1) (getEvtsMo m2).

Fixpoint getLfsTr (t : tr) {struct t}  : set lf :=
match t with
| nil => nil
| a :: tail => match a with
  |(cd c1) => getLfsTr tail
  |(ev e1) => set_add lf_dec (getReLf e1) 
               (set_add lf_dec (getTrLf e1) (getLfsTr tail))
  end
end.

Fixpoint getLfsOb (o : set tr) : set lf :=
match o with
|nil => nil
|a :: tail => set_union lf_dec (getLfsTr a) (getLfsOb tail)
end.

Fixpoint getLfsMo (m : set (set tr)) : set lf :=
match m with
|nil => nil
|a :: tail => set_union lf_dec (getLfsOb a) (getLfsMo tail)
end.

Definition unionLfs (m1 m2 : set (set tr)) : set lf :=
 set_union lf_dec (getLfsMo m1) (getLfsMo m2).


Fixpoint loopMo (st : state)(c : cnd)(n : nat)(s : set (set tr)){struct n} 
 : set (set tr) :=
match n, s with
|0, _ => (nil :: nil) :: nil
|S p, _ => set_union ob_dec
             (addCndToMo st c 
               (seqMo st (unionEvts s (loopMo st c p s))
                (unionLfs s (loopMo st c p s)) s (loopMo st c p s)) )                
          ((nil :: nil) :: nil)
                                  
end.


(*test case*)
Eval compute in loopMo empty_state Btrue 3 ((nil::nil)::nil).


(* Functional Scheme loopMo_ind := Induction for loopMo Sort Prop. *)

(*-----Definition of Denotational Functions--*)
Fixpoint interp (st : state)(d : sd) {struct d} : mo :=
match d with
|Dtau => ((nil) :: nil) :: nil
|De e => ((ev e :: nil) :: nil) :: nil
|Dstrict SD1 SD2 => strictMo (interp st SD1) (interp st SD2)
|Dopt c SD  => optMo st c (interp st SD) 
|Dalt c SD1 SD2 => altMo st c (interp st SD1) (interp st SD2)
|Dpar SD1 SD2 => parMo (interp st SD1) (interp st SD2)
|DSeq SD1 SD2 => seqMo st (getEvts (DSeq SD1 SD2))
                (getLfs (DSeq SD1 SD2))
                (interp st SD1) (interp st SD2)
|Dloop c n SD  => loopMo st c n (interp st SD)
end.

(* Functional Scheme interp_ind := Induction for interp Sort Prop. *)

(*test cases of interp*)
Definition f1 := (!, "m", "l1", "l2").
Definition f2 := (?, "m", "l1", "l2").
Definition f3 := (!, "n", "l1", "l2").
Definition f4 := (?, "n", "l1", "l2").
Definition d1 : sd := Dstrict (De f1) (De f2).
Definition d2 : sd := Dstrict (De f3) (De f4).
Definition e0 : evt := (!, "call", "l1", "l2").
Definition d3 : sd := De e0.
Definition d4 : sd := Dtau.

Eval compute in interp empty_state d1 .
(*result: ((f1 :: f2 :: nil) :: nil) :: nil*)
Eval compute in interp empty_state d2 .
(*result: ((f3 :: f4 :: nil) :: nil) :: nil*)
Eval compute in interp empty_state d3 .
Eval compute in interp empty_state d4 .

Eval compute in interp empty_state (Dloop Btrue 2 d1).
Eval compute in interp empty_state (DSeq d1 d2).


(*1.strict*)
Definition dstrict := (Dstrict d1 d2).
Eval compute in interp empty_state dstrict .
(*result:((f1 :: f2 :: f3 :: f4 :: nil) :: nil) :: nil *)

(*2.alt*)
Definition dalt := Dalt (Band (Bvar P) (Bvar Q)) d1 d3.
Eval compute in interp empty_state dalt .
Definition dalt2 := Dalt (Band (Bvar P) (Bvar Q)) d3 d3.
Eval compute in interp empty_state dalt2.
(*result: ((e0 :: nil) :: nil) :: nil*)
Definition dalt3 := Dalt (Band (Bvar P) (Bvar Q)) d1 d3.
Eval compute in interp empty_state dalt3.

(*3.opt*)
Definition dopt := Dopt (Band (Bvar P) (Bvar Q)) d4.
Eval compute in interp empty_state dopt.
Definition dopt2 := Dopt (Band (Bvar P) (Bvar Q)) d2.
Eval compute in interp empty_state dopt2.
Definition dopt3 := Dopt (Band (Bvar P) (Bvar Q)) Dtau.
Eval compute in interp empty_state dopt3.

(*4.par*)
Definition dpar := (Dpar d1 d2).
Eval compute in interp empty_state dpar.
(*result:(((f1 :: f2 :: f3 :: f4 :: nil) :: nil)
               ((f1 :: f3 :: f2 :: f4 :: nil) :: nil)
                 ((f1 :: f3 :: f4 :: f2 :: nil) :: nil)
                   ((f3 :: f4 :: f1 :: f2 :: nil) :: nil)
                     ((f3 :: f1 :: f4 :: f2 :: nil) :: nil)
                       ((f3 :: f1 :: f2 :: f4 :: nil) :: nil)) :: nil
*)

(*6.seq*)
Definition dseq:=(DSeq d1 d2).
Eval compute in interp empty_state dseq  .
(*result:(((f1::f2::f3::f4::nil)::nil)::((f1::f3::f2::f4))::nil)::nil *)

(*7.loop*)
Definition dloop := Dloop (Btrue) 2 d1.
Eval compute in interp empty_state dloop.


Definition f:=(?,"f","l1","l2").
Definition g:=(?,"g","l1","l2").
Definition h:=(?,"h","l1","l2").
Eval compute in interp empty_state (Dalt Btrue (De f) (De g)).
(*((cd Btrue :: ev (?, "f", "l1", "l2") :: nil) )
       :: ((cd (BNot BTrue) :: ev (?, "g", "l1", "l2") :: nil) :: nil) :: nil*)
Eval compute in interp empty_state (De h).
(*((ev (?, "h", "l1", "l2") :: nil) :: nil) :: nil*)
Eval compute in interp empty_state (Dpar (Dalt Btrue (De f) (De g)) (De h)).


(*test cases of interp: a full example*)
Definition sid := (!, "id", "client", "server").
Definition rid := (?, "id", "client", "server").
Definition spwd := (!, "pwd", "client", "server").
Definition rpwd := (?, "pwd", "client", "server").
Definition rloginsucc := (?, "loginsucc", "server", "client").
Definition sloginsucc := (!, "loginsucc", "server", "client").
Definition scmd := (!, "cmd", "client", "server").
Definition rcmd := (?, "cmd", "client", "server").
Definition rloginfail := (?, "loginfail", "server", "client").
Definition sloginfail := (!, "loginfail", "server", "client").

Definition flag1 : id := Id 10.
Definition flag2 : id := Id 20.

Definition LoginDiag := 
Dstrict (Dstrict (Dstrict (De sid)(De rid)) (Dstrict (De spwd)(De rpwd)))
(Dalt (Bvar flag1) (Dstrict (Dstrict (De sloginsucc) (De rloginsucc))
(Dopt (Bvar flag2) (Dstrict (De scmd) (De rcmd)))) (Dstrict (De sloginfail) (De rloginfail))).

Eval compute in interp empty_state LoginDiag.

(*====Syntax Constraints=====*)
(*if both the transmitter and the receiver lifelines of a signal are present
in a diagram, then the corresponding receive event of any transmit event must be
in the diagram , and vice versa. *)
Definition revEvt (e : evt) : evt :=
match e with
|(!, s, t, r) => (?, s, t, r)
|(?, s, t, r) => (!, s, t, r)
end.

Definition chkEvt (d : sd)(e : evt) := 
if (andb (set_mem lf_dec (getTrLf e) (getLfs d))
         (set_mem lf_dec (getReLf e) (getLfs d)))
   then set_mem evt_dec (revEvt e) (getEvts d)
   else true.

Fixpoint chkEvtAux (d : sd)(evs : set evt) : bool :=
match evs with
|nil => true
|e :: tail =>  if (chkEvt d e) then (chkEvtAux d tail) else false
end.

Definition chkEvts (D : sd) : bool :=
  chkEvtAux D (getEvts D).

Compute chkEvts (LoginDiag ).
Compute chkEvts (dseq).

(*=====Semantic Constraint on Traces====== *)
(* For all traces, if at a point in a trace we have an receive event of a signal, then up to
that point we must have had at least as many transmits of that message as receives *)
Fixpoint countKd (k : kd)(t : tr) : nat :=
match t with
|nil => 0
|ev e :: tail => if (beq_kd k (getKd e)) then (countKd k tail) +1
               else (countKd k tail)
|cd d :: tail => (countKd k tail)
end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => ble_nat n' m'
            end
  end.

Fixpoint chkTr (t1 : tr) : bool :=
match t1 with
|nil => true
|ev (?, s, t, r) :: tail => 
if (ble_nat 
(countKd Receive 
  (filter ((!, s, t, r) :: (?, s, t, r) :: nil) t1)) 
(countKd Send 
  (filter ((!, s, t, r) :: (?, s, t, r) :: nil) t1))) 
then chkTr tail
else false
|_ :: tail => chkTr tail
end.

Fixpoint chkOb (o : ob) : bool :=
match o with
|nil => true
|t :: tail => andb (chkTr (rev t)) (chkOb tail)
end.

Fixpoint chkMo (m : mo) : bool :=
match m with
|nil => true
|o :: tail => andb (chkOb o) (chkMo tail)
end.

Definition checkSd (d : sd) : bool :=
chkMo (interp empty_state d).

(*test cases*)
Compute chkTr ((ev f1)::(ev f2)::(cd Btrue)::nil).
Compute checkSd d1.
Compute checkSd dpar.
Compute checkSd dseq.
Compute checkSd LoginDiag.

(*==========Properties of semantics==============**)
Lemma setUnionEv_Nil: 
  forall l1 l2, set_union evt_dec l1 l2 = nil-> l1 = nil /\ l2 = nil.
Proof.
 intros l1 l2 H.
 induction l1; destruct l2; simpl in *.
 split; auto.
 split; auto. 
 contradict H. apply set_add_not_empty.
 inversion H.
 contradict H. apply set_add_not_empty.
Qed.

Lemma loopMoNil: forall st c n, 
 loopMo st c n ((nil :: nil) :: nil)= (nil :: nil) :: nil .
Proof.
 intros.
 induction n.
 simpl. auto.
 simpl. rewrite IHn. 
 simpl. auto.
Qed.

Lemma optMoNil:
  forall st c, optMo st c ((nil :: nil) :: nil) = (nil :: nil) :: nil.
Proof.
  intros st c.
  unfold optMo.  
  reflexivity.
Qed.

Lemma lifelineAux: forall d, getEvts d = nil -> getLfs d = nil.
Proof.
 intros d H.
 induction d; simpl; auto; try (inversion H).
 apply setUnionEv_Nil in H1.  destruct H1. apply IHd1 in H0; apply IHd2 in H1.
 rewrite H0; rewrite H1; simpl; auto.
 inversion H. apply setUnionEv_Nil in H1. destruct H1. apply IHd1 in H0; apply IHd2 in H1.
 rewrite H0; rewrite H1; simpl; auto.
 inversion H. apply setUnionEv_Nil in H1. destruct H1. apply IHd1 in H0; apply IHd2 in H1.
 rewrite H0; rewrite H1; simpl; auto.
 inversion H. apply setUnionEv_Nil in H1. destruct H1. apply IHd1 in H0; apply IHd2 in H1.
 rewrite H0; rewrite H1; simpl; auto.
Qed.


Lemma event_Nil_loopaux: forall c n d0, getEvts (Dloop c n d0) = nil ->getEvts d0 = nil.
Proof.
   intros. inversion H. auto.
Qed.

(*Lemma Event_Nil *)
Lemma eventNil : forall (st : state)(d : sd),
   getEvts d = nil -> interp st d = (nil :: nil) :: nil.
Proof.
 intros st d H.
 induction d; simpl.
(*d=Dtau*)
 reflexivity.
(*d=De e1*)
 inversion H.
(*D=Dstrict d5 d6*)
 inversion H.
 apply setUnionEv_Nil in H1. destruct H1.
 apply IHd1 in H0. apply IHd2 in H1. rewrite H0. rewrite H1.
 unfold strictMo. simpl. unfold strictOb. simpl. reflexivity.
(*D=Dopt c d0*)
 inversion H. apply IHd in H1. rewrite H1. apply optMoNil.
(*D=Dalt c d5 d6*)
 inversion H.  
 apply  setUnionEv_Nil in H1. destruct H1.
 apply IHd1 in H0. apply IHd2 in H1. rewrite H0. rewrite H1.
 unfold altMo. simpl. reflexivity.
(*D=Dpar d5 d6*)
 inversion H.
 apply setUnionEv_Nil in H1. destruct H1.
 apply IHd1 in H0.  apply IHd2 in H1. rewrite H0. rewrite H1.
 unfold strictMo. simpl. reflexivity.
(*D=Dseq d5 d6*)
 inversion H.
 apply setUnionEv_Nil in H1. destruct H1.
 rewrite H0; rewrite H1. simpl.
 apply lifelineAux in H0. apply lifelineAux in H1. 
 rewrite H0. rewrite H1.
 inversion H. apply setUnionEv_Nil in H3. destruct H3.
 apply IHd1 in H2.  apply IHd2 in H3. rewrite H2. rewrite H3.
 simpl. reflexivity.
(*D=Dloop c n d0*)
 apply event_Nil_loopaux in H. apply IHd in H. rewrite H. 
 apply loopMoNil.
Qed.


