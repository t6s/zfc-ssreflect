(** A file that involves general list sorting with respect to a
   nonstandard specification. The proofs are not finished.  *)

Require Import List.

Set Implicit Arguments.

Section ListExtras.
Variable T:Type.

(* this is essentially lelist from the stdlib, but there are not many
   results proved about it there, so I don't know if it's worth
   switching *)
Inductive Suffix : list T -> list T -> Prop :=
| Suffix_refl: forall xs, Suffix xs xs
| Suffix_cons: forall x xs ys, Suffix ys xs -> Suffix ys (x::xs).

Lemma Suffix_lem1 : forall xs ys:list T, Suffix xs ys -> 
  exists zs, zs++xs=ys.
Proof.
  intros.
  induction ys.
  inversion H.
  exists nil.
  simpl.
  reflexivity.
  inversion H.
  exists nil.
  simpl.
  reflexivity.
  assert (IH := IHys H2).
  clear -IH.
  destruct IH as [l Hl].
  rewrite <- Hl.
  exists (a::l).
  simpl.
  reflexivity.
Qed.

Lemma Suffix_incl : forall xs ys:list T, Suffix xs ys -> 
  incl xs ys.
Proof.
  intros.
  induction ys.
  inversion H.
  red.
  auto.
  inversion H.
  red.
  auto.
  red.
  assert (IH:=IHys H2).
  clear -IH.
  red in IH.
  auto using in_cons.
Qed.

Section Sorting.

  Variable R:T->T->bool.
  
  (* sorting is taken from the CoLoR library *)
  Fixpoint insert x (l : list T) :=
    match l with
      | nil => cons x nil
      | cons y m => 
        if R x y then (cons y (insert x m)) else (cons x l)
    end.
  
  Fixpoint sort (l : list T) : list T :=
    match l with
      | nil => nil
      | cons x m => insert x (sort m)
    end.

  Lemma insert_ext : forall xs a a0, 
    a = a0 \/ In a0 xs <-> In a0 (insert a xs).
  Proof.
    induction xs.
    simpl.
    intuition.

    simpl insert.
    intros b c.
    Require Setoid.
    destruct R.
    simpl.
    rewrite <- IHxs.
    intuition.
    simpl.
    intuition.
  Qed.

  Lemma insert_sort_ext : forall xs a a0, 
    a = a0 \/ In a0 xs <-> In a0 (insert a (sort xs)).
  Proof.
    induction xs.
    simpl.
    intuition.

    simpl insert.
    intros b c.
    Require Setoid.
    simpl.
    rewrite <- insert_ext.
    rewrite <- IHxs.
    intuition.
  Qed.

  Lemma sort_ext : forall (xs:list T), 
    let ys := sort xs in
      incl xs ys /\ incl ys xs.
  Proof.
    intros xs ys.

    split.
    induction xs.
    intuition.
    unfold ys in IHxs.
    unfold ys.
    clear -IHxs.
    simpl.
    unfold incl in *.
    simpl in *.
    intros.
    firstorder using insert_sort_ext.

    induction xs.
    intuition.
    simpl in IHxs.
    unfold ys.
    clear -IHxs.
    simpl.
    unfold incl in *.
    simpl in *.
    intros.
    firstorder using insert_sort_ext.
  Qed.

  Lemma sort_suffix : 
      forall xs zs z, Suffix (z::zs) (sort xs) -> 
        forall z', In z' zs -> R z z' = true.
  Proof.
    intros xs zs z H.
    assert ({ys:list T|ys=z::zs}).
    exists (z::zs).
    reflexivity.
    destruct X as [ys Hys].
    rewrite <-Hys in H.
    replace zs with (tail ys).
    Focus 2.
    rewrite Hys; simpl; reflexivity.
    apply Suffix_lem1 in H.
    generalize dependent xs.
    generalize dependent zs.
    induction ys.
    intuition.
    simpl.
    intros.
    assert (H1 : ys=nil \/ In z' (tail ys) \/ Some z' = head ys).
    admit.
    destruct H1.
    admit.
    destruct H1.
  Admitted.

  Lemma sort_correct : forall (xs:list T),
    let ys := sort xs in
      incl xs ys /\ incl ys xs /\ 
      forall z zs, Suffix (z::zs) ys -> 
        forall z', In z' zs -> R z z' = true.
  Proof.
    intros xs ys.

    split.
    firstorder using sort_ext.
    split.
    firstorder using sort_ext.
    eauto using sort_suffix.
  Qed.

  Lemma nodup_sort : forall (xs:list T),
    NoDup xs -> NoDup (sort xs).
  Admitted.


(* I should have a look at the place where this list operations are
   used. Maybe it's possible to optimise a bit. Ex: do we compose a
   nodup with sort or vice-versa. *)

End Sorting.

Section Removing_consecutive_duplicates.

  Variable R:T->T->bool.
  Variable eqT_dec:forall x y:T, {x=y}+{x<>y}.

  (* remove _consecutive_ appearences of duplicate elements of a list *)
  Fixpoint nodup' (xs:list T) : list T :=
    match xs with
      | nil => nil
      | cons y ys => cons y
        match ys with
          | nil => nil
          | cons z zs => 
            if eqT_dec y z then (nodup' zs) else cons z (nodup' zs)
        end
    end.
  
  Definition nodup (xs:list T) : list T := nodup' (sort R xs).
  
  Lemma nodup_correct : forall xs:list T, 
    let ys := nodup xs in
      incl xs ys /\ incl ys xs /\ NoDup ys.
  Admitted.

End Removing_consecutive_duplicates.


End ListExtras.

(* Require Import Compare_dec. *)
(* Require Import Peano_dec. *)
(* Eval compute in (sort leb (1::2::1::4::3::4::nil)). *)
(* Eval compute in (nodup leb eq_nat_dec (1::2::1::4::3::4::nil)). *)
