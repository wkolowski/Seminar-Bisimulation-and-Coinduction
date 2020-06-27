(*
Require Import Searchability.

Ltac inv H := inversion H; subst.

Lemma no_axiom :
  forall n m : conat,
    sim n omega -> le n m -> sim m omega.
Proof.
  cofix CH.
  intros n m Hsim Hle.
  destruct Hle as [[]].
    destruct Hsim as [[]].
      destruct H0. inversion H1.
      destruct H0 as (n' & m' & H1 & H2). congruence.
    destruct H as (n' & m' & H1 & H2 & H3).
      constructor. right. exists m', omega. split.
        assumption.
        split.
          cbn. reflexivity.
          apply CH with n'.
            destruct Hsim as [[]].
              destruct H. congruence.
              destruct H as (n'' & m'' & H1' & H2' & H3').
                cbn in H2'. inv H2'. rewrite H1' in H1. inv H1.
                  assumption.
            assumption.
Qed.
*)

Module Ex2.

CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.

Arguments hd {A} _.
Arguments tl {A} _.

CoInductive sim {A : Type} (s1 s2 : Stream A) : Prop :=
{
    hds : hd s1 = hd s2;
    tls : sim (tl s1) (tl s2);
}.

CoFixpoint corec
  {A X : Type} (h : X -> A) (t : X -> X) (x : X) : Stream A :=
{|
    hd := h x;
    tl := corec h t (t x);
|}.

Fixpoint nth {A : Type} (s : Stream A) (n : nat) : A :=
match n with
    | 0 => hd s
    | S n' => nth (tl s) n'
end.

Fixpoint drop {A : Type} (s : Stream A) (n : nat) : Stream A :=
match n with
    | 0 => s
    | S n' => drop (tl s) n'
end.

Lemma hd_drop :
  forall {A : Type} (n : nat) (s : Stream A),
    hd (drop s n) = nth s n.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

Lemma tl_drop :
  forall {A : Type} (n : nat) (s : Stream A),
    tl (drop s n) = drop s (S n).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.

Lemma uniqueness_sim_is_eq :
  forall {A : Type},
    (forall (X : Type) (f g : X -> Stream A) (h : X -> A) (t : X -> X),
      ((forall x : X, hd (f x) = h x /\ tl (f x) = f (t x)) ->
       (forall x : X, hd (g x) = h x /\ tl (g x) = g (t x)) ->
         forall x : X, f x = g x)) ->
    forall s1 s2 : Stream A, sim s1 s2 -> s1 = s2.
Proof.
  intros A H s1 s2 Hsim.
  eapply (H nat (drop s1) (drop s2) (nth s1) S _ _ 0).
  Unshelve.
    split; [apply hd_drop | apply tl_drop].
    split.
      2: apply tl_drop.
      revert s1 s2 Hsim. induction x as [| n']; cbn; intros.
        destruct Hsim. rewrite hds0. reflexivity.
        destruct Hsim. rewrite (IHn' _ _ Hsim). reflexivity.
Qed.

End Ex2.

Module Ex3.

Import Ex2.

CoInductive M (S : Type) (P : S -> Type) : Type :=
{
    shape : S;
    position : P shape -> M S P
}.

Arguments shape {S P}.
Arguments position {S P} _ _.

Definition transport
  {A : Type} {P : A -> Type} {x y : A} (p : x = y) (u : P x) : P y :=
match p with
    | eq_refl => u
end.

CoInductive siM {S : Type} {P : S -> Type} (m1 m2 : M S P) : Prop :=
{
    shapes : shape m1 = shape m2;
    positions :
      forall p : P (shape m1),
        siM (position m1 p) (position m2 (transport shapes p))
}.

Definition P_Stream (A : Type) : A -> Type := fun _ => unit.

Definition Stream' (A : Type) : Type := M A (P_Stream A).

CoFixpoint ff {A : Type} (s : Stream A) : Stream' A :=
{|
    shape := hd s;
    position _ := ff (tl s);
|}.

CoFixpoint gg {A : Type} (s : Stream' A) : Stream A :=
{|
    hd := shape s;
    tl := gg (position s tt);
|}.

Lemma ff_gg :
  forall {A : Type} (s : Stream A),
    sim (gg (ff s)) s.
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    apply CH.
Qed.

Lemma gg_ff :
  forall {A : Type} (s : Stream' A),
    siM (ff (gg s)) s.
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 2. cbn. reflexivity.
    destruct p. cbn. apply CH.
Qed.

End Ex3.