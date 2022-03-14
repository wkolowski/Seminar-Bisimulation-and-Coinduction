(** * Introduction to coinductive types in Coq *)

(** ** The basics *)

(** Conatural numbers are things that [option]ally can have a predecessor
    which is a conatural number too. Contrast this with naturals, which
    are either zero or a successor of a natural number - we see that [nat]
    and [conat] are dual. *)

CoInductive conat : Type :=
{
    pred : option conat;
}.

(** [sim] (an abbreviation of "bisimilarity") is our custom "equality" for
    conatural numbers. The ordinary equality won't do, because it is not fit
    for use with (possibly) infinite objects.

    Two conaturals are bisimilar when either they are zero or they have bisimilar
    predecessors. *)

CoInductive sim (n m : conat) : Prop :=
{
    sim' :
      (pred n = None /\ pred m = None)
        \/
      (exists n' m' : conat,
        pred n = Some n' /\ pred m = Some m' /\ sim n' m');
}.

(** Using [sim] instead of [eq] saves us from trouble when proving, but it
    doesn't save us from having to prove a lot of auxiliary lemmas... unless
    we use the axiom [sim_eq], which says that bisimilar conaturals are equal.

    Feel free to use this axiom - it is consistent with Coq's logic - but
    ideally you should avoid it. *)

Axiom sim_eq :
  forall {n m : conat}, (sim n m) = (n = m).

(** [eq_pred] is a very useful lemma - conaturals with equal predecessors are
    equal. To prove it, it suffices to [destruct] both [n] and [m] and then
    [rewrite] the hypothesis. *)

Lemma eq_pred :
  forall n m : conat, pred n = pred m -> n = m.
Proof.
  intros [] [] H.
  cbn in H.
  rewrite H.
  reflexivity.
Qed.

(** This tactic will prove very useful for you... *)

Ltac inv H := inversion H; subst; clear H; auto.

(** We prove theorems about conatural numbers (and about inhabitants of other
    coinductive types) using the [cofix] tactic. It is a very primitive tactic,
    dual to the [fix] tactic used for proofs by induction. Sadly, there just
    isn't a better way.

    Let's try to prove that [sim] is reflexive, i.e. [forall n : conat, sim n n].

    In our first proof attempt below, we start with [cofix CH], which introduces
    the coinduction hypothesis [CH : forall n : conat, sim n n] to the context.
    It looks like we are done, as we can use [CH] to finish the theorem, but this
    is a deadly trap - the command [Admitted] would fail at this point. This is because
    before we can use the coinduction hypothesis, we must produce a part of the
    result (which here is just a step of the proof), similarly to how we can apply
    the induction hypothesis only after we reduce the problem in size.

    We start our second proof attempt in the same way, by giving ourselves the
    coinduction hypothesis [CH : forall n : conat, sim n n]. This time, however,
    we use the [constructor] tactic to make make a step towards proving [sim n n].
    We have two possibilities: [n] is bisimilar to [n] either because both are
    zero (i.e. have no predecessor) or because both have bisimilar predecessors.
    To decide which case it is, we destruct [n], naming the predecessor [n'].
    In the first case ([n] has predecessor [n']), we go right, tell Coq that the
    predecessor is [n'], solve the trivial side goals, and finish the proof by
    using the coinduction hypothesis to show that the predecessor is bisimilar
    to itself (i.e. [sim n' n']). The second case ([n] has no predecessor) is
    trivial. *)

Lemma sim_refl :
  forall n : conat, sim n n.
Proof.
  cofix CH.
  exact CH.
  Fail Guarded.
Restart.
  cofix CH.
  constructor.
  destruct n as [[n' |]]; cbn.
  - right. exists n', n'. split; [| split].
    1-2: reflexivity.
    apply CH.
  - left. intuition.
Qed.

(** Heads up, coinduction is easy! Now, try some proofs by coinduction to
    see for yourself. *)

Lemma sim_sym :
  forall n m : conat, sim n m -> sim m n.
Proof.
Admitted.

Lemma sim_trans :
  forall a b c : conat, sim a b -> sim b c -> sim a c.
Proof.
Admitted.

(** We import [Setoid] so that we can [rewrite] with [sim] the same way we can
    rewrite with ordinary equality. *)

Require Import Setoid.

Instance Equivalence_sim : Equivalence sim.
Proof.
  esplit; red.
    apply sim_refl.
    apply sim_sym.
    apply sim_trans.
Defined.

(** ** Zero, successor and infinity *)

(** We can now define some basic conatural numbers and functions. [zero] is
    the conatural number that has no predecessor. The [succ]essor of [n] is
    the conatural whose [pred]ecessor is [n]. *)

Definition zero : conat :=
{|
    pred := None;
|}.

Definition succ (n : conat) : conat :=
{|
    pred := Some n;
|}.

(** But a much more interesting case is [omega], the infinite conatural number.
    It is defined as the conatural number which is its own predecessor.

    To define infinite values of coinductive types (and functions into coinductive
    types), we use the keyword [CoFixpoint]. Remember that, just like for proofs
    by coinduction, we must produce a part of the object we're defining before we
    can make any use of the corecursive call. For conaturals, this means that the
    corecursive call must occur inside of [{| pred := ... |}]. *)

CoFixpoint omega : conat :=
{|
    pred := Some omega;
|}.

(** Congratulations on reaching the end of this short tutorial - I don't have
    enough time for more explanations... in case of doubt, refer to
    https://coq.inria.fr/refman/language/core/coinductive.html
    to read a bit more about coinduction and to
    https://coq.inria.fr/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.cofix
    for a clarification on the [cofix] tactic.

    To help you learn what coinductive types are, how to do proofs by coinduction
    and how to define corecursive functions, I prepared a few exercises for you...

    Good luck!

    But beware: some of the theorems may be false, and I don't remember which ones... *)

Lemma succ_pred :
  forall n m : conat,
    n = succ m <-> pred n = Some m.
Proof.
Admitted.

Lemma zero_not_omega :
  ~ sim zero omega.
Proof.
Admitted.

Lemma sim_succ_omega :
  forall n : conat, sim n (succ n) -> sim n omega.
Proof.
Admitted.

Lemma succ_omega :
  omega = succ omega.
Proof.
Admitted.

Lemma sim_succ :
  forall n m : conat, sim n m -> sim (succ n) (succ m).
Proof.
Admitted.

Lemma sim_succ_inv :
  forall n m : conat, sim (succ n) (succ m) -> sim n m.
Proof.
Admitted.

(** ** Addition *)

(** Define addition of conatural numbers and prove its properties. *)

Axiom add : conat -> conat -> conat.

Lemma add_zero_l :
  forall n m : conat, pred n = None -> add n m = m.
Proof.
Admitted.

Lemma add_zero_r :
  forall n : conat, sim (add n zero) n.
Proof.
Admitted.

Lemma sim_add_zero :
  forall n m : conat,
    sim (add n m) zero -> n = zero /\ m = zero.
Proof.
Admitted.

Lemma add_omega_l :
  forall n : conat, sim (add omega n) omega.
Proof.
Admitted.

Lemma add_omega_r :
  forall n : conat, sim (add n omega) omega.
Proof.
Admitted.

Lemma add_succ_l :
  forall n m : conat, add (succ n) m = succ (add n m).
Proof.
Admitted.

Lemma add_succ_r :
  forall n m : conat, sim (add n (succ m)) (succ (add n m)).
Proof.
Admitted.

Lemma eq_sim :
  forall n m : conat, n = m -> sim n m.
Proof.
Admitted.

Lemma add_assoc :
  forall a b c : conat, sim (add (add a b) c) (add a (add b c)).
Proof.
Admitted.

Lemma add_succ_r'' :
  forall n m : conat,
    add n {| pred := Some m |} = succ (add n m).
Proof.
Admitted.

Lemma add_comm :
  forall n m : conat, sim (add n m) (add m n).
Proof.
Admitted.

Lemma sim_add_zero_l :
  forall n m : conat,
    sim (add n m) zero -> n = zero.
Proof.
Admitted.

Lemma sim_add_zero_r :
  forall n m : conat,
    sim (add n m) zero -> m = zero.
Proof.
Admitted.

Lemma add_zero_r' :
  forall n m : conat,
    pred m = None -> sim (add n m) n.
Proof.
Admitted.

Lemma sim_add :
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> sim (add n1 m1) (add n2 m2).
Proof.
Admitted.

(** ** Ordering *)

(** Define the ordering (named [le]) on conatural numbers and prove its properties. *)

Axiom le : conat -> conat -> Prop.

Lemma le_0_l :
  forall n : conat, le zero n.
Proof.
Admitted.

Lemma le_0_r :
  forall n : conat, le n zero -> n = zero.
Proof.
Admitted.

Lemma le_succ :
  forall n m : conat, le n m -> le (succ n) (succ m).
Proof.
Admitted.

Lemma le_succ_conv :
  forall n m : conat,
    le (succ n) (succ m) -> le n m.
Proof.
Admitted.

Lemma le_refl :
  forall n : conat, le n n.
Proof.
Admitted.

Lemma le_trans :
  forall a b c : conat, le a b -> le b c -> le a c.
Proof.
Admitted.

Lemma le_univalent :
  forall n m : conat,
    le n m -> le m n -> sim n m.
Proof.
Admitted.

Lemma le_sim :
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> le n1 m1 -> le n2 m2.
Proof.
Admitted.

Lemma le_omega_r :
  forall n : conat, le n omega.
Proof.
Admitted.

Lemma le_omega_l :
  forall n : conat, le omega n -> sim n omega.
Proof.
Admitted.

Lemma le_succ_r :
  forall n m : conat, le n m -> le n (succ m).
Proof.
Admitted.

Lemma le_add_l :
  forall a b c : conat,
    le a b -> le a (add b c).
Proof.
Admitted.

Lemma le_add_r :
  forall a b c : conat,
    le a c -> le a (add b c).
Proof.
Admitted.

Lemma le_add :
  forall n1 n2 m1 m2 : conat,
    le n1 n2 -> le m1 m2 -> le (add n1 m1) (add n2 m2).
Proof.
Admitted.

Lemma le_add_l' :
  forall n m : conat, le n (add n m).
Proof.
Admitted.

Lemma le_add_r' :
  forall n m : conat, le m (add n m).
Proof.
Admitted.

Lemma le_add_l'' :
  forall n n' m : conat,
    le n n' -> le (add n m) (add n' m).
Proof.
Admitted.

Lemma le_add_r'' :
  forall n m m' : conat,
    le m m' -> le (add n m) (add n m').
Proof.
Admitted.

(** ** Min and max *)

(** Define the functions [min] and [max] and prove their properties. *)

Axiom min max : conat -> conat -> conat.

Lemma min_zero_l :
  forall n : conat, min zero n = zero.
Proof.
Admitted.

Lemma min_zero_r :
  forall n : conat, min n zero = zero.
Proof.
Admitted.

Lemma min_omega_l :
  forall n : conat, sim (min omega n) n.
Proof.
Admitted.

Lemma min_omega_r :
  forall n : conat, sim (min n omega) n.
Proof.
Admitted.

Lemma min_succ :
  forall n m : conat,
    sim (min (succ n) (succ m)) (succ (min n m)).
Proof.
Admitted.

Lemma max_zero_l :
  forall n : conat, sim (max zero n) n.
Proof.
Admitted.

Lemma max_zero_r :
  forall n : conat, sim (max n zero) n.
Proof.
Admitted.

Lemma max_omega_l :
  forall n : conat, sim (max omega n) omega.
Proof.
Admitted.

Lemma max_omega_r :
  forall n : conat, sim (max n omega) omega.
Proof.
Admitted.

Lemma max_succ :
  forall n m : conat,
    sim (max (succ n) (succ m)) (succ (max n m)).
Proof.
Admitted.

Lemma min_assoc :
  forall a b c : conat, sim (min (min a b) c) (min a (min b c)).
Proof.
Admitted.

Lemma max_assoc :
  forall a b c : conat, sim (max (max a b) c) (max a (max b c)).
Proof.
Admitted.

Lemma min_comm :
  forall n m : conat, sim (min n m) (min m n).
Proof.
Admitted.

Lemma max_comm :
  forall n m : conat, sim (max n m) (max m n).
Proof.
Admitted.

Lemma min_le :
  forall n m : conat, le n m -> sim (min n m) n.
Proof.
Admitted.

Lemma max_le :
  forall n m : conat, le n m -> sim (max n m) m.
Proof.
Admitted.

Lemma min_diag :
  forall n : conat, sim (min n n) n.
Proof.
Admitted.

Lemma max_diag :
  forall n : conat, sim (max n n) n.
Proof.
Admitted.

Lemma min_add_l :
  forall a b c : conat,
    sim (min (add a b) (add a c)) (add a (min b c)).
Proof.
Admitted.

Lemma min_add_r :
  forall a b c : conat,
    sim (min (add a c) (add b c)) (add (min a b) c).
Proof.
Admitted.

Lemma max_add_l :
  forall a b c : conat,
    sim (max (add a b) (add a c)) (add a (max b c)).
Proof.
Admitted.

Lemma max_add_r :
  forall a b c : conat,
    sim (max (add a c) (add b c)) (add (max a b) c).
Proof.
Admitted.

Lemma sim_min_max :
  forall n m : conat,
    sim (min n m) (max n m) -> sim n m.
Proof.
Admitted.

Lemma min_max :
  forall a b : conat, sim (min a (max a b)) a.
Proof.
Admitted.

Lemma max_min :
  forall a b : conat, sim (max a (min a b)) a.
Proof.
Admitted.

Lemma min_max_distr :
  forall a b c : conat,
    sim (min a (max b c)) (max (min a b) (min a c)).
Proof.
Admitted.

Lemma max_min_distr :
  forall a b c : conat,
    sim (max a (min b c)) (min (max a b) (max a c)).
Proof.
Admitted.

(** ** Division by 2 *)

(** Define the function [div2], which halves a conatural number, and prove its
    properties. *)

Axiom div2 : conat -> conat.

Lemma div2_zero :
  sim (div2 zero) zero.
Proof.
Admitted.

Lemma div2_omega :
  sim (div2 omega) omega.
Proof.
Admitted.

Lemma div2_succ :
  forall n : conat, sim (div2 (succ (succ n))) (succ (div2 n)).
Proof.
Admitted.

Lemma div2_add :
  forall n : conat, sim (div2 (add n n)) n.
Proof.
Admitted.

Lemma le_div2_l' :
  forall n m : conat, le n m -> le (div2 n) m.
Proof.
Admitted.

Lemma le_div2_l :
  forall n : conat, le (div2 n) n.
Proof.
Admitted.

Lemma le_div2 :
  forall n m : conat, le n m -> le (div2 n) (div2 m).
Proof.
Admitted.

(** ** [Finite] and [Infinite] *)

(** Define the predicates [Finite] and [Infinite]. Prove the lemmas below. *)

Axiom Finite Infinite : conat -> Prop.

Lemma omega_not_Finite :
  ~ Finite omega.
Proof.
Admitted.

Lemma Infinite_omega :
  Infinite omega.
Proof.
Admitted.

Lemma Infinite_omega' :
  forall n : conat, Infinite n -> sim n omega.
Proof.
Admitted.

Lemma Finite_Infinite :
  forall n : conat, Finite n -> Infinite n -> False.
Proof.
Admitted.

Lemma Finite_or_Infinite :
  forall c : conat, ~ ~ (Finite c \/ Infinite c).
Proof.
Admitted.

Lemma sim_add_Finite :
  forall a b c : conat,
    Finite c -> sim (add a c) (add b c) -> sim a b.
Proof.
Admitted.

Lemma Finite_sim :
  forall n m : conat,
    sim n m -> Finite n -> Finite m.
Proof.
Admitted.

Lemma Finite_add :
  forall n m : conat,
    Finite n -> Finite m -> Finite (add n m).
Proof.
Admitted.

Lemma Finite_add_inv_l :
  forall n m : conat,
    Finite (add n m) -> Finite n.
Proof.
Admitted.

(** ** [Even] and [Odd] *)

(** Define the predicates [Even] and [Odd]. Prove the lemmas below. Bonus points
    if you use mutual coinductive types for the definition. *)

Axiom Even Odd : conat -> Prop.

Lemma Even_zero :
  Even zero.
Proof.
Admitted.

Lemma Odd_zero :
  ~ Odd zero.
Proof.
Admitted.

Lemma Even_Omega :
  Even omega.
Proof.
Admitted.

Lemma Odd_Omega :
  Odd omega.
Proof.
Admitted.

Lemma Even_Odd_Infinite :
  forall n : conat, Even n -> Odd n -> Infinite n.
Proof.
Admitted.

Lemma Even_succ :
  forall n : conat, Odd n -> Even (succ n).
Proof.
Admitted.

Lemma Odd_succ :
  forall n : conat, Even n -> Odd (succ n).
Proof.
Admitted.

Lemma Even_succ_inv :
  forall n : conat, Odd (succ n) -> Even n.
Proof.
Admitted.

Lemma Odd_succ_inv :
  forall n : conat, Even (succ n) -> Odd n.
Proof.
Admitted.

Lemma Finite_Even_Odd :
  forall n : conat, Finite n -> Even n \/ Odd n.
Proof.
Admitted.

Lemma Finite_not_both_Even_Odd :
  forall n : conat, Finite n -> ~ (Even n /\ Odd n).
Proof.
Admitted.

Lemma Even_add_Odd :
  forall n m : conat, Odd n -> Odd m -> Even (add n m).
Proof.
Admitted.

Lemma Even_add_Even :
  forall n m : conat, Even n -> Even m -> Even (add n m).
Proof.
Admitted.

Lemma Odd_add :
  forall n m : conat, Even n -> Odd m -> Odd (add n m).
Proof.
Admitted.

(** ** Multiplication *)

(** Define multiplication of conatural numbers. Formulate and prove its properties
    (hint: they are very similar to properties of natural number multiplication). *)

(** ** Naturals and conaturals *)

(** Define the function [from_nat] which transforms a natural number into its
    corresponding conatural number. *)

Axiom from_nat : nat -> conat.

Lemma Finite_from_nat :
  forall n : nat, Finite (from_nat n).
Proof.
Admitted.

(** Show that [from_nat] has no inverse. *)

Lemma no_preinverse :
  forall f : conat -> nat,
    (forall c : conat, from_nat (f c) = c) -> False.
Proof.
Admitted.