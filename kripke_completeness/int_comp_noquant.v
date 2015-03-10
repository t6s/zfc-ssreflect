(** Formalised proof of completeness of Intuitionistic propositional
   logic (disjunction and implication, no quantifiers) with respect to
   Kripke-style models.

   Danko Ilik, July 2009

   Normalisation examples at end of file.
*)
Require Import stdlib_Type.

Set Implicit Arguments.
Unset Strict Implicit.

(** printing <= $\le$ #&le;# *)
(** printing ||-- $\Vdash$ #⊩# *)
(** printing ||- $\Vdash$ #⊩# *)
(** printing ||+ $\Vdash_s$ #⊩<sub>s</sub># *)

Definition var : Set := nat.

(** Proof terms *)
Inductive term : Set :=
| Lam   : var -> term -> term
| Inl   : term -> term
| Inr   : term -> term
| Var   : var -> term
| App   : term -> term -> term
| Match : term -> var -> term -> var -> term -> term.

Inductive formula := 
  Atom : formula
| Imp  : formula -> formula -> formula
| Disj : formula -> formula -> formula.

Definition context := list (var*formula).
Hint Unfold context.

(** Natural deduction system *)
Inductive proof : context -> term -> formula -> Set :=
| DisjIL : forall Gamma t A B, proof Gamma t A -> proof Gamma (Inl t) (Disj A B)
| DisjIR : forall Gamma t A B, proof Gamma t B -> proof Gamma (Inr t) (Disj A B)
| ImpI   : forall Gamma x t A B, proof ((x,A)::Gamma) t B -> proof Gamma (Lam x t) (Imp A B)
| Hypo   : forall Gamma x A, In (x,A) Gamma -> proof Gamma (Var x) A
| DisjE  : forall Gamma x y e t u A B C, proof Gamma e (Disj A B) -> proof ((x,A)::Gamma) t C -> proof ((y,B)::Gamma) u C -> proof Gamma (Match e x t y u) C
| ImpE   : forall Gamma t u A B, proof Gamma t (Imp A B) -> 
  proof Gamma u A -> proof Gamma (App t u) B.

Section Abstract_Semantics.
  (** An abstract Kripke-style structure: [wle] is the preorder, [X] is
     the exploding-world predicate, [aforces] is strong forcing of
     atomic formulae. *)
  Record Kripke : Type := {
    world :> Set;
    wle : world -> world -> Type;
    wle_refl : forall w, wle w w;
    wle_trans : forall w w' w'', wle w w' -> wle w' w'' -> wle w w'';
    X : world -> formula -> Set;
    aforces : world -> Set;
    aforces_mon : forall w, aforces w -> forall w', wle w w' -> aforces w'
  }.
  Notation "w <= w'" := (wle w w').

  Variable K:Kripke.

  (** The continuations monad we will use to extend forcing to
     composite formulas *)
  Definition Kont (F:K->formula->Type)(w:K)(A:formula) := 
    forall C:formula,
      (forall w1, w <= w1 -> 
        (forall w2, w1 <= w2 -> F w2 A -> X w2 C) -> X w1 C).
  Hint Unfold Kont.

  (** Strong forcing extended to composite formulas. The expression
     [sforces w A] stands for strong forcing, while [Kont sforces w A]
     stands for (weak) forcing of A in the world w. *)
  Fixpoint sforces (w:K)(A:formula) {struct A} : Type :=
    match A with
      | Atom => aforces w
      | Imp A1 A2 => forall w', w <= w' -> Kont sforces w' A1 -> Kont sforces w' A2
      | Disj A1 A2 => sum (Kont sforces w A1) (Kont sforces w A2)
    end.

  Lemma sforces_mon : forall A w, sforces w A  -> forall w', w <= w' -> sforces w' A .
  Proof.
    induction A.
    simpl.
    intros.
    eauto using aforces_mon.

    intros w H1 w' ww'.
    simpl in *.
    eauto using wle_trans.

    intros w H1 w' ww'.
    simpl in *.
    case H1; intro H'.
    eauto using wle_trans.
    eauto using wle_trans.
  Defined.

  Definition ret {w A} : sforces w A -> Kont sforces w A.
  Proof.
    intros H.
    intros C w1 w_w1 k.
    apply k.
    apply wle_refl.
    apply sforces_mon with w.
    assumption.
    assumption.
  Defined.

  Fixpoint Kont_sforces_cxt (w:K)(Gamma:context) : Type :=
    match Gamma with
      | nil => unit
      | cons aA Gamma' => 
        prod (Kont sforces w (snd aA)) (Kont_sforces_cxt w Gamma')
    end.

  Notation " w ||- A " := (Kont sforces w A) (at level 70).
  Notation " w ||-- Gamma " := (Kont_sforces_cxt w Gamma) (at level 70).

  Lemma Kont_sforces_cxt_mon : forall Gamma w, w ||-- Gamma -> forall w', w <= w' -> w' ||-- Gamma.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros w H w' w_w'.
    destruct H.
    split; eauto using wle_trans,sforces_mon.
  Defined.

  Lemma Kont_sforces_mon : forall w A, w ||- A -> forall w', w <= w' ->  w' ||- A.
  Proof.
    intros w A H w' ww'.
    intros C w'' w'w'' k.
    apply H.
    eauto using wle_trans.
    assumption.
  Defined.

  Theorem soundness : forall Gamma t A, proof Gamma t A -> forall w, w ||-- Gamma -> w ||- A.
  Proof.
    intros Gamma t A p.
    induction p.

    intros w wGamma.
    apply ret.
    simpl.
    left; auto.

    intros w wGamma.
    apply ret.
    simpl.
    right; auto.

    intros w wGamma.
    apply ret.
    simpl in *.
    intros.
    apply IHp.    
    split; eauto using Kont_sforces_cxt_mon.

    induction Gamma.
    simpl.
    contradict i.
    simpl.
    intros w [Ha HGamma].
    simpl in i.
    destruct i.
    rewrite e in Ha.
    assumption.
    auto.

    clear p1 p2 p3.
    intros w wGamma.
    intros D w1 ww1 k.
    apply IHp1 with w.
    assumption.
    assumption.
    intros w2 w1w2 HDisj.
    simpl in HDisj.
    case HDisj.
    intro HA.
    apply IHp2 with w2.
    simpl.
    split.
    assumption.
    eauto using wle_trans,Kont_sforces_cxt_mon.
    apply wle_refl.
    eauto using wle_trans.
    intro HB.
    apply IHp3 with w2.
    simpl.
    split.
    assumption.
    eauto using wle_trans,Kont_sforces_cxt_mon.
    apply wle_refl.
    eauto using wle_trans.

    intros w wGamma.
    intros C w1 ww1 k.
    apply IHp1 with w1.
    eauto using Kont_sforces_cxt_mon.
    apply wle_refl.
    simpl sforces.
    intros w2 w1w2 HAB.
    apply HAB with w2.
    apply wle_refl.
    eauto using wle_trans,Kont_sforces_mon.
    apply wle_refl.
    intros w3 w2w3 HB.
    eauto using wle_trans,Kont_sforces_mon.
  Defined.
End Abstract_Semantics.

(** The Universal model *)
Section Universal_Model_and_Completeness.
  Definition Kworld : Set := context.
  Definition Kle (w w':Kworld) : Type := incl w w'.
  Lemma Kle_refl : forall w, Kle w w.
  Proof.
    apply incl_refl.
  Defined.

  Lemma Kle_trans : forall w w' w'', Kle w w' -> Kle w' w'' -> Kle w w''.
  Proof.
    unfold Kle.
    intros.
    intuition eauto using incl_tran.
  Defined.

  Definition Normal_term (A:formula)(Gamma:context) :=
    {t:term & proof Gamma t A}.
  Hint Unfold Normal_term.

  Definition KX (w:Kworld)(A:formula) : Set :=  Normal_term A w.
  Hint Unfold KX.

  Definition Kaforces (w:Kworld) : Set := Normal_term Atom w.

  Notation "w <= w'" := (Kle w w').

  Lemma proof_mon : forall A t w, proof w t A -> forall w', w <= w' -> proof w' t A.
  Proof.
    intros A t w p.
    induction p.

    intros.
    constructor.
    auto.

    intros.
    constructor.
    auto.

    intros.
    constructor.
    apply IHp.
    apply cons_incl_head.
    assumption.

    intros.
    constructor.
    apply X0.
    assumption.

    intros.
    apply DisjE with A B.
    auto.
    apply IHp2.
    apply cons_incl_head.
    assumption.
    apply IHp3.
    apply cons_incl_head.
    assumption.

    intros.
    apply ImpE with A.
    apply IHp1.
    assumption.
    apply IHp2.
    assumption.
  Defined.

  Lemma Kaforces_mon : forall w, Kaforces w -> forall w', Kle w w' -> Kaforces w'.
  Proof.
    intros w H.
    destruct H as [v p].
    intros w' Hle.
    exists v.
    unfold Kle in Hle.
    eauto using proof_mon.
  Defined.

  Definition K : Kripke.
  (* begin show *)
    apply Build_Kripke with Kworld Kle Kaforces.
    exact Kle_refl.
    exact Kle_trans.
    exact KX.
    exact Kaforces_mon.
  (* end show *)
  Defined.

  Let F := (@sforces K).

  (** The proof of completeness is via a reify-reflect pair. [fresh] is a fresh variable counter that is increased at every recursive call. *)
  Theorem Kcompleteness : forall A w, forall fresh:nat,
    (Kont F w A -> {t:term & proof w t A}) *
    (forall e:term, proof w e A -> Kont F w A).
  Proof.
    induction A.

    (* Atomic formula *)
    intros.
    split.

    intros c.
    apply c.
    apply wle_refl.
    simpl.
    intros w2 w_w2 H.
    apply H.

    intros e He.
    apply ret.
    simpl.
    exists e.
    assumption.

    (* Implication *)
    intro w.
    split.

    intro c.
    apply c.
    apply wle_refl.
    intros w2 le_w2 f.
    set (w' := (fresh,A1)::w2).
    simpl in f.
    assert (Hf : Kont F w' A2).
      apply f.
      unfold w'.
      red;simpl;auto.
      apply (snd (IHA1 w' (S fresh))) with (Var fresh).
      unfold w'.
      constructor.
      auto.
    apply (fst (IHA2 w' (S fresh))) in Hf.
    destruct Hf as [t' p'].
    exists (Lam fresh t').
    apply ImpI.
    unfold w' in p'; simpl in p'.
    assumption.
  
    intros e He.
    apply ret.
    simpl.
    intros w' le_w' Ha1.
    apply (fst (IHA1 w' (S fresh))) in Ha1.
    destruct Ha1 as [a1 Ha1].
    apply (snd (IHA2 w' (S fresh))) with (App e a1).
    apply ImpE with A1.
    eauto using proof_mon.
    assumption.

    (* Disjunction *)
    intro w.
    split.

    intro c.
    apply c.
    apply wle_refl.
    intros w2 ww2 Hdisj.
    simpl in Hdisj.
    destruct Hdisj as [HA1 | HA2].
    apply (fst (IHA1 _ (S fresh))) in HA1.
    destruct HA1 as [t1 Ht1].
    exists (Inl t1).
    constructor.
    assumption.
    apply (fst (IHA2 _ (S fresh))) in HA2.
    destruct HA2 as [t2 Ht2].
    exists (Inr t2).
    constructor.
    assumption.

    intros e He.
    intros C w' le_w' k.
    simpl in k.
    set (w1 := (fresh,A1)::w').
    assert (branch1 : Kont F w1 A1).
    apply (snd (IHA1 w1 (S fresh))) with (Var fresh).
    constructor.
    unfold w1.
    auto.
    set (w2 := (fresh,A2)::w').
    assert (branch2 : Kont F w2 A2).
    apply (snd (IHA2 w2 (S fresh))) with (Var fresh).
    constructor.
    unfold w2.
    auto.
    assert (w'w1 : w' <= w1).
    unfold w1.
    red;simpl;intuition.
    assert (w'w2 : w' <= w2).
    unfold w2.
    red;simpl;intuition.
    assert (t1p1 := k w1 w'w1 (inl _ branch1)).
    assert (t2p2 := k w2 w'w2 (inr _ branch2)).
    destruct t1p1 as [t1 p1].
    destruct t2p2 as [t2 p2].
    exists (Match e fresh t1 fresh t2).
    apply DisjE with A1 A2.
    apply proof_mon with w.
    assumption.
    assumption.
    assumption.
    assumption.
  Defined.
End Universal_Model_and_Completeness.

(** A lemma by which NbE below uses Kcompeteness *)
Lemma Kont_sforces_cxt_refl : forall Gamma, Kont_sforces_cxt (K:=K) Gamma Gamma.
Proof.
  induction Gamma.
  simpl.
  constructor.
  simpl.
  split.
  destruct a as [x A].
  simpl.
  apply (snd (Kcompleteness _ _ 0)) with (Var x).
  constructor.
  left;reflexivity.
  apply Kont_sforces_cxt_mon with Gamma.
  assumption.
  simpl.
  right.
  assumption.
Defined.

Definition NbE (Gamma:context)(t:term)(A:formula)(p:proof Gamma t A) : term.
Proof.
(* begin show *)
  intros.
  set (compl := fst (Kcompleteness A Gamma 0)).
  set (sndns := soundness (K:=K) p (Kont_sforces_cxt_refl Gamma)).
  exact (projT1 (compl sndns)).
(* end show *)
Defined.

(** Some tests of the normalization algorithm *)

Definition id1 : proof nil (Lam 0 (Var 0)) (Imp Atom Atom).
Proof.
  apply ImpI.
  apply Hypo.
  left; reflexivity.
Defined.

(* Eval compute in (NbE id1). *)

Definition id2 : proof nil (Lam 0 (Var 0)) (Imp (Imp Atom Atom) (Imp Atom Atom)).
Proof.
  apply ImpI.
  apply Hypo.
  left; reflexivity.
Defined.

(* Eval compute in (NbE id2). *)

Definition id3 : proof nil (Lam 0 (Var 0)) (Imp (Imp (Imp Atom Atom) (Imp Atom Atom)) (Imp (Imp Atom Atom) (Imp Atom Atom))).
Proof.
  apply ImpI.
  apply Hypo.
  left; reflexivity.
Defined.

(* Eval compute in (NbE id3). *)

Definition id4 : proof nil (Lam 0 (Var 0)) (Imp (Disj Atom Atom) (Disj Atom Atom)).
Proof.
  apply ImpI.
  apply Hypo.
  left; reflexivity.
Defined.

(* Eval compute in (NbE id4). *)

Definition id5 : proof nil (Lam 0 (Var 0)) (Imp (Imp (Disj Atom Atom) (Disj Atom Atom)) (Imp (Disj Atom Atom) (Disj Atom Atom))).
Proof.
  apply ImpI.
  apply Hypo.
  left; reflexivity.
Defined.

(* Eval compute in (NbE id5). *)

Definition id6 : proof nil (Lam 0 (Var 0)) (Imp (Imp (Disj Atom Atom) Atom) (Imp (Disj Atom Atom) Atom)).
Proof.
  apply ImpI.
  apply Hypo.
  left; reflexivity.
Defined.

(* Eval compute in (NbE id6). *)

Definition id7 : proof nil (Lam 0 (Lam 1 (Match (Var 1) 2 (App (Var 0) (Inl (Var 2))) 2 (App (Var 0) (Inr (Var 2)))))) (Imp (Imp (Disj Atom Atom) Atom) (Imp (Disj Atom Atom) Atom)).
Proof.
  apply ImpI.
  apply ImpI.
  apply DisjE with Atom Atom.
  apply Hypo.
  left; reflexivity.
  apply ImpE with (Disj Atom Atom).
  apply Hypo.
  right; right; left; reflexivity.
  constructor.
  apply Hypo.
  left; reflexivity.
  apply ImpE with (Disj Atom Atom).
  apply Hypo.
  right; right; left; reflexivity.
  constructor.
  apply Hypo.
  left; reflexivity.
Defined.

(* Eval compute in (NbE id7). *)
