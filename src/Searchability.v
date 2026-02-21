CoInductive conat : Type :=
{
  pred : option conat;
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
  pred :=
    if p zero
    then None
    else Some (search_conat (fun n => p (succ n)))
|}.

Lemma eq_pred :
  forall n m : conat,
    pred n = pred m -> n = m.
Proof.
  now intros [] []; cbn; intros ->.
Qed.

Lemma sc_eq :
  forall p : conat -> bool,
    search_conat p =
      if p zero then zero else succ (search_conat (fun n => p (succ n))).
Proof.
  intros p.
  apply eq_pred; cbn.
  now destruct (p zero); cbn.
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
    p (search_conat p) = false ->
      sim (search_conat p) omega.
Proof.
  cofix CH.
  intros p Hf.
  constructor; cbn.
  destruct (p zero) eqn: Hp.
  - replace (search_conat p) with zero in Hf; [now congruence |].
    apply eq_pred; cbn.
    now rewrite Hp.
  - right.
    do 2 eexists.
    do 2 split; [easy |].
    apply CH.
    now rewrite sc_eq, Hp in Hf.
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
  intros p n Ht.
  constructor.
  rewrite sc_eq.
  destruct (p zero) eqn: Hp; cbn; [now left |].
  right.
  destruct n as [[n' |]]; [| now unfold zero in Hp; congruence].
  do 2 eexists.
  do 2 split; [easy |].
  apply CH.
  now unfold succ.
Qed.

Lemma le_omega_l :
  forall n : conat,
    le omega n -> sim n omega.
Proof.
  cofix CH.
  intros n [[| (omega' & n' & H1 & H2 & H3)]]; cbn in *; [easy |].
  injection H1 as [= <-].
  constructor; right.
  exists n', omega.
  split; [easy |].
  split; [easy |].
  now apply CH.
Qed.

Axiom sim_eq :
  forall n m : conat,
    sim n m -> n = m.

#[refine]
Instance Searchable_conat : Searchable conat :=
{
  search := search_conat;
}.
Proof.
  intros p.
  destruct (p (search_conat p)) eqn: Hpscp; [now left |].
  right; intros n.
  destruct (p n) eqn: Hpn; [| easy].
  assert (Heq : search_conat p = omega).
  {
    now apply sim_eq, search_conat_spec.
  }
  assert (Heq' : n = omega).
  {
    apply sim_eq, le_omega_l.
    rewrite <- Heq.
    now apply sc_true.
  }
  rewrite Heq in Hpscp; subst.
  now congruence.
Defined.
