Inductive nat : Type :=
    | Z : nat
    | S : nat -> nat.

Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Fixpoint len {A : Type} (l : list A) : nat :=
match l with
    | nil => Z
    | cons _ t => S (len t)
end.

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

