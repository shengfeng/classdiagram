Require Export cd.
Require Export refinement.
Require Import List.
Require Import String.
Require Import ListSet.
Import ListNotations.

Open Scope list_scope.

Definition EleCustomer : NamedElement := 
  BNamedElement 100 "Customer".

Definition EleOrder : NamedElement :=
  BNamedElement 101 "Order".

Definition EleString : NamedElement := 
  BNamedElement 0 "string".

Definition EleDate : NamedElement := 
  BNamedElement 1 "date".

Definition EleFloat : NamedElement := 
  BNamedElement 2 "float".

Definition EleEnum : NamedElement := 
  BNamedElement 3 "enum".

Definition EleCustomerName : NamedElement := 
  BNamedElement 10 "CustomerName".

Definition EleCustomerAddress : NamedElement :=
  BNamedElement 11 "CustomerAddress".

Definition EleOrderDate : NamedElement := 
  BNamedElement 12 "OrderDate".

Definition EleOrderPrice : NamedElement := 
  BNamedElement 13 "OrderPrice".

Definition EleOrderType: NamedElement := 
  BNamedElement 14 "OrderType".

Definition EleOwn : NamedElement :=
  BNamedElement 51 "own".

Definition ClfCustomer : Classifier := 
  BClassifier EleCustomer.

Definition ClfOrder : Classifier := 
  BClassifier EleOrder.

Definition ClfString : Classifier := 
  BClassifier EleString.

Definition ClfDate : Classifier := 
  BClassifier EleDate.

Definition ClfFloat : Classifier := 
  BClassifier EleFloat.

Definition ClfEnum : Classifier := 
  BClassifier EleEnum.

Definition String : DataType := 
  BDataType ClfString.

Definition Date : DataType := 
  BDataType ClfDate.

Definition Float : DataType := 
  BDataType ClfFloat.

Definition Enum : DataType := 
  BDataType ClfEnum.

Definition AttrCustomerName : Attribute := 
  BAttribute EleCustomer ClfString.

Definition AttrAddress : Attribute :=
  BAttribute EleCustomerAddress ClfString.

Definition AttrOrderDate : Attribute := 
  BAttribute EleOrderDate ClfDate.

Definition AttrPrice : Attribute := 
  BAttribute EleOrderPrice ClfFloat.

Definition AttrOrderType : Attribute := 
  BAttribute EleOrderType ClfEnum.

Definition Customer : Class := 
  BClass ClfCustomer false [AttrCustomerName; AttrAddress].

Definition Order : Class := 
  BClass ClfOrder false [AttrOrderDate;AttrPrice;AttrOrderType].

Definition order2customer : AsEnd := 
  BAsEnd "orders" Order (Nat 0, Star).

Definition customer2order : AsEnd := 
  BAsEnd "customer" Order (Nat 1, Nat 1).

Definition aCustomerOrder :=
  BAssoc EleOwn none (order2customer, customer2order). 

Definition m0 := mkSimpleUML 
  [Order;Customer]
  [AttrCustomerName; AttrAddress; AttrOrderDate; AttrPrice; AttrOrderType] 
  [String; Date; Float; Enum] 
  [aCustomerOrder] [].

(* ----- refinement ------ *)
Definition ElePayment : NamedElement := 
  BNamedElement 102 "Payment".

Definition EleBankAccount : NamedElement :=
  BNamedElement 103 "BankAccount".

Definition EleCreditCard : NamedElement :=
  BNamedElement 104 "CreditCard".

Definition ElePay : NamedElement :=
  BNamedElement 200 "pay".

Definition ClfPayment : Classifier :=
  BClassifier ElePayment.

Definition ClfBankAccount : Classifier :=
  BClassifier EleBankAccount.

Definition ClfCreditCard: Classifier :=
  BClassifier EleCreditCard.

Definition Payment : Class := 
  BClass ClfPayment true [].

Definition BankAccount : Class := 
  BClass ClfBankAccount false [].

Definition CreditCard : Class := 
  BClass ClfCreditCard false [].

Definition payment2customer: AsEnd := 
  BAsEnd "payment" Payment (Nat 0, Star).

Definition customer2payment : AsEnd :=
  BAsEnd "customer" Customer (Nat 1, Nat 1).

Definition aCustomerPayment: Assoc :=
  BAssoc ElePay none (payment2customer, customer2payment).

Definition gPaymentBankAccount : Gen :=
  BGen Payment BankAccount.

Definition gPaymentCreditCard :=
  BGen Payment CreditCard.

Definition m2:= mkSimpleUML 
  [CreditCard;BankAccount;Order;Customer;Payment]
  [AttrCustomerName; AttrAddress; AttrOrderDate; AttrPrice; AttrOrderType] 
  [String; Date; Float; Enum] 
  [aCustomerOrder;aCustomerPayment] 
  [gPaymentCreditCard;gPaymentBankAccount].


(** ----- proof -----  **)

Definition m1 := mkSimpleUML
  [Order;Customer;Payment]
  [AttrCustomerName; AttrAddress; AttrOrderDate; AttrPrice; AttrOrderType] 
  [String; Date; Float; Enum] 
  [aCustomerOrder;aCustomerPayment] 
  [].

Definition m1' := mkSimpleUML
  [BankAccount;Order;Customer;Payment]
  [AttrCustomerName; AttrAddress; AttrOrderDate; AttrPrice; AttrOrderType] 
  [String; Date; Float; Enum] 
  [aCustomerOrder;aCustomerPayment] 
  [gPaymentBankAccount].

Lemma refine_m0_to_m1:
  refineone m0 m1.
Proof.
  unfold m0, m1.
Admitted.


Lemma refine_m1_to_m1':
  refineone m1 m1'.
Proof.
  unfold m1, m1'.
  eapply dec1.
  - simpl; intros contra.
    destruct contra; try inversion H; try discriminate.
    destruct H0; try discriminate. assumption.
  - simpl. right. right. left. reflexivity.
Qed.

Lemma refine_m1'_to_m2:
  refineone m1' m2.
Proof.
  unfold m1', m2.
  eapply dec1.
  - simpl; intros contra.
    destruct contra; try inversion H; try discriminate.
    destruct H0; try discriminate. inversion H0; try discriminate.
    assumption.
  - simpl. right. right. right. left. reflexivity.
Qed.


Theorem refine_m0_to_m2:
  refine m0 m2.
Proof.
  apply trans with m1.
  apply one. apply refine_m0_to_m1.
  apply trans with m1'.
  apply one; apply refine_m1_to_m1'.
  apply trans with m2.
  apply one; apply refine_m1'_to_m2.
  apply reflex.
Qed.

