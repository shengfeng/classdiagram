Require Export classdiagram.

Require Export String ListSet List Arith Bool.
Open Scope nat_scope.
Open Scope type_scope.
Open Scope string_scope.
Open Scope list_scope.
Import ListNotations.


Inductive refine_t :=
| RClass : class -> class -> refine_t
| RAssociation : association -> association -> refine_t.

Definition refinement := list refine_t.
