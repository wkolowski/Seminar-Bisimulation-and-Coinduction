(** * Schematic definitions have side effects! *)

Module Type EmptyModule.
End EmptyModule.

Module Empty : EmptyModule.
End Empty.

Module m (e : EmptyModule).

Inductive Test : Type := .

End m.

Module m1 := m Empty.
Module m2 := m Empty.

Lemma side_effects_are_evil : m1.Test = m2.Test.
Proof.
  Fail reflexivity.
Abort.

(** * W-types and M-types *)

Inductive W (A : Type) (B : A -> Type) : Type :=
    | sup : forall x : A, (B x -> W A B) -> W A B.

Arguments sup {A B} _ _.

CoInductive M (S : Type) (P : S -> Type) : Type :=
{
    shape : S;
    position : P shape -> M S P
}.

Arguments shape {S P} _.
Arguments position {S P} _ _.