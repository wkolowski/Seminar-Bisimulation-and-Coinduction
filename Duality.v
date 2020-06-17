Module ind.

Inductive nat : Type :=
    | Z : nat
    | S : nat -> nat.

Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Fixpoint len {A : Type} (l : list A) {struct l} : nat :=
match l with
    | nil => Z
    | cons _ t => S (len t)
end.

Definition pred (n : nat) : option nat :=
match n with
    | Z => None
    | S n' => Some n'
end.

Definition uncons {A : Type} (l : list A) : option (A * list A) :=
match l with
    | nil => None
    | cons h t => Some (h, t)
end.

End ind.

Module coind.

CoInductive conat : Type :=
{
    pred : option conat;
}.

CoInductive colist (A : Type) : Type :=
{
    uncons : option (A * colist A);
}.

Arguments uncons {A}.

CoFixpoint colen {A : Type} (l : colist A) : conat :=
{|
    pred :=
      match uncons l with
          | None => None
          | Some (_, t) => Some (colen t)
      end
|}.

Definition Z : conat :=
{|
    pred := None
|}.

Definition S (c : conat) : conat :=
{|
    pred := Some c
|}.

Definition nil {A : Type} : colist A :=
{|
    uncons := None
|}.

Definition cons {A : Type} (h : A) (t : colist A) : colist A :=
{|
    uncons := Some (h, t)
|}.

End coind.