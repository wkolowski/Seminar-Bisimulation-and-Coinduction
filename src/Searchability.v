CoInductive conat : Type :=
{
    pred : option conat
}.

Class Searchable (A : Type) : Type :=
{
    search : (A -> bool) -> A;
    search_spec :
      forall p : A -> bool,
        p (search p) = true \/
        forall x : A, p x = false;
}.

Definition zero : conat :=
{|
    pred := None
|}.

Definition succ (c : conat) : conat :=
{|
    pred := Some c
|}.

CoFixpoint omega : conat :=
{|
    pred := Some omega
|}.

CoFixpoint search_conat (p : conat -> bool) : conat :=
{|
    pred := if p zero
            then None
            else Some (search_conat (fun n => p (succ n)))
|}.

Lemma eq_pred :
  forall n m : conat, pred n = pred m -> n = m.
Proof.
  destruct n, m. cbn. destruct 1. reflexivity.
Qed.

Lemma sc_eq :
  forall p : conat -> bool,
    search_conat p =
      if p zero then zero else succ (search_conat (fun n => p (succ n))).
Proof.
  intros. apply eq_pred. cbn.
  destruct (p zero) eqn: Hp; cbn; reflexivity.
Qed.

CoInductive sim (n m : conat) : Prop :=
{
    sim' :
      (pred n = None /\ pred m = None) \/
      (exists n' m' : conat,
        pred n = Some n' /\ pred m = Some m' /\ sim n' m')
}.

Lemma search_conat_spec :
  forall p : conat -> bool,
    p (search_conat p) = false -> sim (search_conat p) omega.
Proof.
  cofix CH.
  intros p H.
  constructor. cbn. destruct (p zero) eqn: Hp.
  - replace (search_conat p) with zero in H.
    + congruence.
    + apply eq_pred. cbn. rewrite Hp. reflexivity.
  - right. do 2 eexists. split; [| split].
    1-2: reflexivity.
    apply CH. rewrite sc_eq, Hp in H. assumption.
Qed.

CoInductive le (n m : conat) : Prop :=
{
    le' :
      pred n = None \/
      (exists n' m' : conat,
        pred n = Some n' /\ pred m = Some m' /\ le n' m')
}.

Lemma sc_true :
  forall (p : conat -> bool) (n : conat),
    p n = true -> le (search_conat p) n.
Proof.
  cofix CH.
  intros p n H.
  constructor. rewrite sc_eq. destruct (p zero) eqn: Hp.
  - left. cbn. reflexivity.
  - right. cbn. destruct n as [[n' |]].
    + do 2 eexists; split; [| split].
      1-2: reflexivity.
      apply CH. unfold succ. assumption.
    + unfold zero in Hp. congruence.
Qed.

Lemma le_omega_l :
  forall n : conat, le omega n -> sim n omega.
Proof.
  cofix CH.
  intros n H. destruct H as [[|]].
  - cbn in H. inversion H.
  - destruct H as (omega' & n' & H1 & H2 & H3).
    cbn in *; inversion H1; subst; clear H1.
    constructor. right. exists n', omega. cbn.
    split; [| split].
    + assumption.
    + reflexivity.
    + apply CH. assumption.
Qed.

Axiom sim_eq :
  forall n m : conat, sim n m -> n = m.

#[refine]
Instance Searchable_conat : Searchable conat :=
{
    search := search_conat;
}.
Proof.
  intro p. destruct (p (search_conat p)) eqn: H; [left; reflexivity |].
  right. intro n.
  destruct (p n) eqn: Hpn; [| reflexivity].
  assert (Heq : search_conat p = omega).
  {
    apply sim_eq.
    apply search_conat_spec.
    assumption.
  }
  assert (Heq' : n = omega).
  {
    apply sim_eq.
    apply le_omega_l.
    rewrite <- Heq.
    apply sc_true.
    assumption.
  }
  rewrite Heq in *; subst. congruence.
Defined.