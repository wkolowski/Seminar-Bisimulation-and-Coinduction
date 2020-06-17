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
  destruct (p zero) eqn: Hp.
    cbn. reflexivity.
    cbn. reflexivity.
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
    replace (search_conat p) with zero in H.
      congruence.
      apply eq_pred. cbn. rewrite Hp. reflexivity.
    right. do 2 eexists. split; [idtac | split].
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
    left. cbn. reflexivity.
    right. cbn. destruct n as [[n' |]].
      Focus 2. unfold zero in Hp. congruence.
      do 2 eexists; split; [idtac | split].
        1-2: reflexivity.
        apply CH. rewrite <- H. f_equal.
Qed.

Lemma le_omega_l :
  forall n : conat, le omega n -> sim n omega.
Proof.
  cofix CH.
  intros n H. destruct H as [[|]].
    cbn in H. inversion H.
    destruct H as (omega' & n' & H1 & H2 & H3).
      cbn in *. inversion H1. subst.
      constructor. right. exists n', omega. cbn. split.
        assumption.
        split.
          reflexivity.
          apply CH. assumption.
Qed.

Axiom sim_eq :
  forall n m : conat, sim n m -> n = m.

#[refine]
Instance Searchable_conat : Searchable conat :=
{
    search := search_conat;
}.
Proof.
  intro p. case (p (search_conat p)) eqn: H.
    left. reflexivity.
    right. intro n.
      destruct (p n) eqn: Hpn.
        2: reflexivity.
        pose (Hpn' := Hpn). pose (H' := H).
          apply sc_true in Hpn'. apply search_conat_spec in H'.
          apply sim_eq in H'. rewrite H' in *.
          apply le_omega_l in Hpn'. apply sim_eq in Hpn'. subst.
          congruence.
Defined.

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