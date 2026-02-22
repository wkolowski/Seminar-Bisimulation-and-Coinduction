From BisimCoind Require Import Searchability.

Module Ex1.

(*
  Sadly, it's not possible to do it without the axiom. Neither is it possible
  in the original Escardó definition that uses monotone sequences of booleans.
*)

End Ex1.

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

CoFixpoint corec {A X : Type} (h : X -> A) (t : X -> X) (x : X) : Stream A :=
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
  induction n as [| n']; cbn; intros; [easy |].
  now rewrite IHn'.
Qed.

Lemma tl_drop :
  forall {A : Type} (n : nat) (s : Stream A),
    tl (drop s n) = drop s (S n).
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now rewrite IHn'; cbn.
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
  unshelve eapply (H nat (drop s1) (drop s2) (nth s1) S _ _ 0).
  - now split; [apply hd_drop | apply tl_drop].
  - split; [| now apply tl_drop].
    revert s1 s2 Hsim.
    induction x as [| n']; cbn; intros s1 s2 []; [easy |].
    now erewrite IHn'.
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

Definition transport {A : Type} {P : A -> Type} {x y : A} (p : x = y) (u : P x) : P y :=
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
  constructor; cbn; [easy |].
  now apply CH.
Qed.

Lemma gg_ff :
  forall {A : Type} (s : Stream' A),
    siM (ff (gg s)) s.
Proof.
  cofix CH.
  unshelve econstructor; [easy |].
  intros []; cbn.
  now apply CH.
Qed.

End Ex3.
