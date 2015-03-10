(** The Cantor pairing function proved correct.

   This code is part of Russell O'Connor's formalisation of Goedel's
   Incompleteness Theorem in Coq, released into the Public Domain.

   http://r6.ca/Goedel/goedel1.html
*)
Require Import Arith.
Require Import Coq.Lists.List.
Require Import extEqualNat.
Require Import primRec.

Definition sumToN (n : nat) :=
  nat_rec (fun _ => nat) 0 (fun x y : nat => S x + y) n.

Lemma sumToN1 : forall n : nat, n <= sumToN n.
Proof.
intros.
induction n as [| n Hrecn].
auto.
simpl in |- *.
apply le_n_S.
apply le_plus_l.
Qed.

Lemma sumToN2 : forall b a : nat, a <= b -> sumToN a <= sumToN b.
Proof.
intro.
induction b as [| b Hrecb]; intros.
simpl in |- *.
rewrite <- (le_n_O_eq _ H).
simpl in |- *.
auto.
induction (le_lt_or_eq _ _ H).
apply le_trans with (sumToN b).
apply Hrecb.
apply lt_n_Sm_le.
auto.
simpl in |- *.
apply le_S.
apply le_plus_r.
rewrite H0.
auto.
Qed.

Definition cPair (a b : nat) := a + sumToN (a + b).

Section CPair_Injectivity.

Remark cPairInjHelp :
 forall a b c d : nat, cPair a b = cPair c d -> a + b = c + d.
Proof.
assert (forall a b : nat, a < b -> a + sumToN a < sumToN b).
simple induction b.
intros.
elim (lt_n_O _ H).
intros.
simpl in |- *.
assert (a <= n).
apply lt_n_Sm_le.
assumption.
induction (le_lt_or_eq a n H1).
apply lt_trans with (sumToN n).
auto.
apply le_lt_n_Sm.
apply le_plus_r.
rewrite H2.
apply lt_n_Sn.
unfold cPair in |- *.
assert
 (forall a b c d : nat,
  a <= c -> b <= d -> a + sumToN c = b + sumToN d -> c = d).
intros.
induction (le_or_lt c d).
induction (le_lt_or_eq _ _ H3).
assert (a + sumToN c < sumToN d).
apply le_lt_trans with (c + sumToN c).
apply plus_le_compat_r.
auto.
auto.
rewrite H2 in H5.
elim (lt_not_le _ _ H5).
apply le_plus_r.
auto.
assert (b + sumToN d < sumToN c).
apply le_lt_trans with (d + sumToN d).
apply plus_le_compat_r.
auto.
auto.
rewrite <- H2 in H4.
elim (lt_not_le _ _ H4).
apply le_plus_r.
intros.
eapply H0.
apply le_plus_l.
apply le_plus_l.
auto.
Qed.

Lemma cPairInj1 : forall a b c d : nat, cPair a b = cPair c d -> a = c.
Proof.
intros.
assert (a + b = c + d).
apply cPairInjHelp.
auto.
eapply plus_reg_l.
unfold cPair in H.
rewrite (plus_comm a) in H.
rewrite (plus_comm c) in H.
rewrite H0 in H.
apply H.
Qed.

Lemma cPairInj2 : forall a b c d : nat, cPair a b = cPair c d -> b = d.
Proof.
intros.
assert (a + b = c + d).
apply cPairInjHelp.
auto.
assert (a = c).
eapply cPairInj1.
apply H.
eapply plus_reg_l.
rewrite H1 in H0.
apply H0.
Qed.

End CPair_Injectivity.

Section CPair_projections.

Let searchXY (a : nat) :=
  boundedSearch (fun a y : nat => ltBool a (sumToN (S y))) a.

Definition cPairPi1 (a : nat) := a - sumToN (searchXY a).
Definition cPairPi2 (a : nat) := searchXY a - cPairPi1 a.

Lemma cPairProjectionsHelp :
 forall a b : nat, b < sumToN (S a) -> sumToN a <= b -> searchXY b = a.
Proof.
intros.
unfold searchXY in |- *.
induction (boundedSearch2 (fun b y : nat => ltBool b (sumToN (S y))) b).
rewrite H1.
induction (eq_nat_dec b a).
auto.
elim (ltBoolFalse b (sumToN (S a))).
apply (boundedSearch1 (fun b y : nat => ltBool b (sumToN (S y))) b).
rewrite H1.
induction (nat_total_order _ _ b0).
elim (lt_not_le _ _ H2).
apply le_trans with (sumToN a).
apply sumToN1.
auto.
auto.
auto.
set (c := boundedSearch (fun b y : nat => ltBool b (sumToN (S y))) b) in *.
induction (eq_nat_dec c a).
auto.
elim (ltBoolFalse b (sumToN (S a))).
apply (boundedSearch1 (fun b y : nat => ltBool b (sumToN (S y))) b).
fold c in |- *.
induction (nat_total_order _ _ b0).
elim (le_not_lt _ _ H0).
apply lt_le_trans with (sumToN (S c)).
apply ltBoolTrue.
auto.
assert (S c <= a).
apply lt_n_Sm_le.
apply lt_n_S.
auto.
apply sumToN2.
auto.
auto.
auto.
Qed.

Lemma cPairProjections : forall a : nat, cPair (cPairPi1 a) (cPairPi2 a) = a.
Proof.
assert
 (forall a b : nat, b < sumToN a -> cPair (cPairPi1 b) (cPairPi2 b) = b).
intros.
induction a as [| a Hreca].
simpl in H.
elim (lt_n_O _ H).
induction (le_or_lt (sumToN a) b).
assert (searchXY b = a).
apply cPairProjectionsHelp; auto.
unfold cPair in |- *.
replace (cPairPi1 b + cPairPi2 b) with a.
unfold cPairPi1 in |- *.
rewrite H1.
rewrite plus_comm.
rewrite <- le_plus_minus.
reflexivity.
auto.
unfold cPairPi2 in |- *.
rewrite <- le_plus_minus.
auto.
unfold cPairPi1 in |- *.
rewrite H1.
simpl in H.
apply (fun p n m : nat => plus_le_reg_l n m p) with (sumToN a).
rewrite <- le_plus_minus.
rewrite plus_comm.
apply lt_n_Sm_le.
auto.
auto.
apply Hreca.
auto.
intros.
apply H with (S a).
apply lt_le_trans with (S a).
apply lt_n_Sn.
apply sumToN1.
Qed.

Lemma cPairProjections1 : forall a b : nat, cPairPi1 (cPair a b) = a.
Proof.
intros.
unfold cPair in |- *.
unfold cPairPi1 in |- *.
replace (searchXY (a + sumToN (a + b))) with (a + b).
rewrite plus_comm.
apply minus_plus.
symmetry  in |- *.
apply cPairProjectionsHelp.
simpl in |- *.
apply le_lt_n_Sm.
apply plus_le_compat_r.
apply le_plus_l.
apply le_plus_r.
Qed.

Lemma cPairProjections2 : forall a b : nat, cPairPi2 (cPair a b) = b.
Proof.
intros.
unfold cPairPi2 in |- *.
rewrite cPairProjections1.
unfold cPair in |- *.
replace (searchXY (a + sumToN (a + b))) with (a + b).
apply minus_plus.
symmetry  in |- *.
apply cPairProjectionsHelp.
simpl in |- *.
apply le_lt_n_Sm.
apply plus_le_compat_r.
apply le_plus_l.
apply le_plus_r.
Qed.

End CPair_projections.

Section CPair_Order.

Lemma cPairLe1 : forall a b : nat, a <= cPair a b.
Proof.
intros.
unfold cPair in |- *.
apply le_plus_l.
Qed.

Lemma cPairLe1A : forall a : nat, cPairPi1 a <= a.
intros.
apply le_trans with (cPair (cPairPi1 a) (cPairPi2 a)).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
Qed.

Lemma cPairLe2 : forall a b : nat, b <= cPair a b.
Proof.
intros.
unfold cPair in |- *.
eapply le_trans.
apply le_plus_r.
apply plus_le_compat_l.
apply le_trans with (a + b).
apply le_plus_r.
apply sumToN1.
Qed.

Lemma cPairLe2A : forall a : nat, cPairPi2 a <= a.
intros.
apply le_trans with (cPair (cPairPi1 a) (cPairPi2 a)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
Qed.

Lemma cPairLe3 :
 forall a b c d : nat, a <= b -> c <= d -> cPair a c <= cPair b d.
Proof.
intros.
unfold cPair in |- *.
apply le_trans with (a + sumToN (b + d)).
apply plus_le_compat_l.
apply sumToN2.
apply le_trans with (a + d).
apply plus_le_compat_l.
auto.
apply plus_le_compat_r.
auto.
apply plus_le_compat_r.
auto.
Qed.

Lemma cPairLt1 : forall a b : nat, a < cPair a (S b).
Proof.
intros.
unfold cPair in |- *.
rewrite (plus_comm a (S b)).
simpl in |- *.
rewrite plus_comm.
simpl in |- *.
rewrite plus_comm.
unfold lt in |- *.
apply le_n_S.
apply le_plus_l.
Qed.

Lemma cPairLt2 : forall a b : nat, b < cPair (S a) b.
Proof.
intros.
unfold cPair in |- *.
simpl in |- *.
unfold lt in |- *.
apply le_n_S.
eapply le_trans.
apply le_plus_r.
apply plus_le_compat_l.
apply le_S.
eapply le_trans.
apply le_plus_l.
rewrite plus_comm.
apply le_plus_l.
Qed.

End CPair_Order.
