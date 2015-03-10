(** Formalised proof of completeness of Classical propositional logic
   (conjunction, disjunction and implication, no quantifiers) with
   respect to Kripke-style models.

   Danko Ilik, February 2009

   Normalisation examples at end of file.
*)
Require Import stdlib_Type.

Set Implicit Arguments.
Unset Strict Implicit.

(** printing <= $\le$ #&le;# *)

Open Scope type_scope.

Parameters var_trm var_ect : Set.

(** Commands, terms, and evaluation contexts *)
Inductive cmd : Set :=
| cm : trm -> ect -> cmd
with trm : Set :=
| tvar : var_trm -> trm
| lam : var_trm -> trm -> trm
| mu : var_ect -> cmd -> trm
| injl : trm -> trm
| injr : trm -> trm
| paire : trm -> trm -> trm
with ect : Set :=
| evar : var_ect -> ect
| mut : var_trm -> cmd -> ect
| app : trm -> ect -> ect
| disj : ect -> ect -> ect
| projl : ect -> ect
| projr : ect -> ect.

Parameter var_formula : Set.

Inductive formula : Set :=
| Atom  : var_formula -> formula                                                      
| Imp : formula -> formula -> formula
| Disj  : formula -> formula -> formula
| Conj  : formula -> formula -> formula.

Let cxt_trm := list (var_trm*formula).
Let cxt_ect := list (var_ect*formula).

Reserved Notation "c : ( Gamma |- Delta ) " (at level 70).
Reserved Notation "Gamma |- ( t : A ) ; Delta" 
  (at level 70, A at next level, t at next level).
Reserved Notation "Gamma ; ( e : A ) |- Delta" 
  (at level 70, A at next level, e at next level).

(** The LK-mu-mu-tilde sequent calculus *)
Inductive proof_cmd : cmd -> cxt_trm -> cxt_ect -> Set :=
| Cut v e Gamma Delta A :
  proof_trm Gamma v A Delta ->
  proof_ect Gamma e A Delta ->
  proof_cmd (cm v e) Gamma Delta

where "c : ( Gamma |- Delta )" := (proof_cmd c Gamma Delta)

with proof_trm : cxt_trm -> trm -> formula -> cxt_ect -> Set :=
| AxR Gamma x A Delta : 
  In (x,A) Gamma -> 
  proof_trm Gamma (tvar x) A Delta

| Mu Gamma alpha c A Delta :
  proof_cmd c Gamma ((alpha,A)::Delta) ->
  proof_trm Gamma (mu alpha c) A Delta

| ImpR Gamma x t A B Delta :
  proof_trm ((x,A)::Gamma) t B Delta ->
  proof_trm Gamma (lam x t) (Imp A B) Delta

| DisjRL Gamma v A1 A2 Delta :
  proof_trm Gamma v A1 Delta ->
  proof_trm Gamma (injl v) (Disj A1 A2) Delta

| DisjRR Gamma v A1 A2 Delta :
  proof_trm Gamma v A2 Delta ->
  proof_trm Gamma (injr v) (Disj A1 A2) Delta

| ConjR Gamma v1 v2 A1 A2 Delta :
  proof_trm Gamma v1 A1 Delta ->
  proof_trm Gamma v2 A2 Delta ->
  proof_trm Gamma (paire v1 v2) (Conj A1 A2) Delta

where "Gamma |- ( t : A ) ; Delta" := (proof_trm Gamma t A Delta)
  
with proof_ect : cxt_trm -> ect -> formula -> cxt_ect -> Set :=
| AxL Gamma alpha A Delta :
  In (alpha,A) Delta ->
  proof_ect Gamma (evar alpha) A Delta

| MuT Gamma x c A Delta :
  proof_cmd c ((x,A)::Gamma) Delta ->
  proof_ect Gamma (mut x c) A Delta

| ImpL Gamma v e A B Delta :
  proof_trm Gamma v A Delta ->
  proof_ect Gamma e B Delta ->
  proof_ect Gamma (app v e) (Imp A B) Delta

| DisjL Gamma e1 e2 A1 A2 Delta :
  proof_ect Gamma e1 A1 Delta -> 
  proof_ect Gamma e2 A2 Delta ->
  proof_ect Gamma (disj e1 e2) (Disj A1 A2) Delta

| ConjLL Gamma e A1 A2 Delta :
  proof_ect Gamma e A1 Delta ->
  proof_ect Gamma (projl e) (Conj A1 A2) Delta

| ConjLR Gamma e A1 A2 Delta :
  proof_ect Gamma e A2 Delta ->
  proof_ect Gamma (projr e) (Conj A1 A2) Delta

where "Gamma ; ( e : A ) |- Delta" := (proof_ect Gamma e A Delta)
.

Section Abstract_Semantics.
  (** An abstract Kripke-style structure: [wle] is the preorder,
     [exploding] is the exploding-world predicate, [aforces] is strong
     refutation of atomic formulae. *)
  Record Kripke : Type := {
    world :> Set;
    wle : world -> world -> Type;
    wle_refl : forall w, wle w w;
    wle_trans : forall w w' w'', wle w w' -> wle w' w'' -> wle w w'';
    exploding : world -> Set;
    arefutes : world -> var_formula -> Set;
    arefutes_mon : forall w X, arefutes w X -> 
      forall w', wle w w' -> arefutes w' X
  }.

  Notation "w <= w'" := (wle w w').

  Variable K:Kripke.

  Fixpoint srefutes (w:K)(A:formula) {struct A} : Type :=
    match A with
      | Atom X => arefutes w X
      | Imp A1 A2 => prod
        (forall w', w <= w' -> srefutes w' A1 -> exploding w')
        (forall w', w <= w' -> 
          (forall w'', w' <= w'' -> srefutes w'' A2 -> exploding w'') 
          -> exploding w')
      | Disj A1 A2 => prod
        (forall w', w <= w' -> 
          (forall w'', w' <= w'' -> srefutes w'' A1 -> exploding w'') 
          -> exploding w')
        (forall w', w <= w' -> 
          (forall w'', w' <= w'' -> srefutes w'' A2 -> exploding w'') 
          -> exploding w')
      | Conj A1 A2 => sum
        (forall w', w <= w' -> 
          (forall w'', w' <= w'' -> srefutes w'' A1 -> exploding w'') 
          -> exploding w')
        (forall w', w <= w' -> 
          (forall w'', w' <= w'' -> srefutes w'' A2 -> exploding w'') 
          -> exploding w')
    end.

  Notation "w : | A ||- " := (srefutes w A) (at level 70).

  Definition forces (w:K)(A:formula) :=
    forall w':K, w <= w' -> srefutes w' A -> exploding w'.

  Notation "w : ||- A" := (forces w A) (at level 70).

  Definition refutes (w:K)(A:formula) := 
    forall w', w <= w' -> forces w' A -> exploding w'.

  Notation "w : A ||- " := (refutes w A)  (at level 70).

  Fixpoint forces_cxt (w:K)(Gamma:cxt_trm) : Type :=
    match Gamma with
      | nil => unit
      | cons xA Gamma' => prod (w:||-(snd xA)) (forces_cxt w Gamma')
    end.

  Fixpoint refutes_cxt (w:K)(Delta:cxt_ect) : Type :=
    match Delta with
      | nil => unit
      | cons aA Delta' => prod (refutes w (snd aA)) (refutes_cxt w Delta')
    end.

  Fixpoint srefutes_cxt (w:K)(Delta:cxt_ect) : Type :=
    match Delta with
      | nil => unit
      | cons aA Delta' => prod (srefutes w (snd aA)) (srefutes_cxt w Delta')
    end.

  Notation " w : ||-- Gamma" := (forces_cxt w Gamma) (at level 70).
  Notation " w : Delta ||-- "  := (refutes_cxt w Delta) (at level 70).

  (* Combined Scheme only works for sort Prop, so I have to give the
     definition by hand by adapting a copy-paste of the Prop version: *)
(*   Scheme proof_cmd_rect' := Induction for proof_cmd Sort Prop *)
(*   with proof_trm_rect' := Induction for proof_trm Sort Prop *)
(*   with proof_ect_rect' := Induction for proof_ect Sort Prop. *)
(*   Combined Scheme proof_rect'' from proof_cmd_rect', proof_trm_rect', *)
(*     proof_ect_rect'. *)
(*   Unset Printing Notations. *)
(*   Print proof_rect''. *)
(*   Set Printing Notations. *)

  Scheme proof_cmd_rect' := Induction for proof_cmd Sort Type
  with proof_trm_rect' := Induction for proof_trm Sort Type
  with proof_ect_rect' := Induction for proof_ect Sort Type.

  (** We have to make the mutual-induction predicate "by hand" since the Combined Scheme Coq command works only in sort Prop, not in Type. *)
  Definition proof_rect' := 
    fun
      (P : forall (c : cmd) (c0 : cxt_trm) (c1 : cxt_ect),
        proof_cmd c c0 c1 -> Type)
      (P0 : forall (c : cxt_trm) (t : trm) (t0 : formula) (c0 : cxt_ect),
        proof_trm c t t0 c0 -> Type)
      (P1 : forall (c : cxt_trm) (e : ect) (t : formula) (c0 : cxt_ect),
        proof_ect c e t c0 -> Type)
      (f : forall (v : trm) (e : ect) (Gamma : cxt_trm) 
        (Delta : cxt_ect) (A : formula) (p : proof_trm Gamma v A Delta),
        P0 Gamma v A Delta p ->
        forall p0 : proof_ect Gamma e A Delta,
          P1 Gamma e A Delta p0 -> P (cm v e) Gamma Delta (Cut p p0))
      (f0 : forall (Gamma : list (prod var_trm formula)) (x : var_trm) 
        (A : formula) (Delta : cxt_ect) (i : In (pair x A) Gamma),
        P0 Gamma (tvar x) A Delta (AxR (Gamma:=Gamma) (x:=x) (A:=A) Delta i))
      (f1 : forall (Gamma : cxt_trm) (alpha : var_ect) 
        (c : cmd) (A : formula) (Delta : list (prod var_ect formula))
        (p : proof_cmd c Gamma (cons (pair alpha A) Delta)),
        P c Gamma (cons (pair alpha A) Delta) p ->
        P0 Gamma (mu alpha c) A Delta (Mu p))
      (f2 : forall (Gamma : list (prod var_trm formula)) (x : var_trm) 
        (t : trm) (A B : formula) (Delta : cxt_ect)
        (p : proof_trm (cons (pair x A) Gamma) t B Delta),
        P0 (cons (pair x A) Gamma) t B Delta p ->
        P0 Gamma (lam x t) (Imp A B) Delta (ImpR p))
      (f3 : forall (Gamma : cxt_trm) (v : trm) (A1 A2 : formula) 
        (Delta : cxt_ect) (p : proof_trm Gamma v A1 Delta),
        P0 Gamma v A1 Delta p ->
        P0 Gamma (injl v) (Disj A1 A2) Delta (DisjRL A2 p))
      (f4 : forall (Gamma : cxt_trm) (v : trm) (A1 A2 : formula) 
        (Delta : cxt_ect) (p : proof_trm Gamma v A2 Delta),
        P0 Gamma v A2 Delta p ->
        P0 Gamma (injr v) (Disj A1 A2) Delta (DisjRR A1 p))
      (f5 : forall (Gamma : cxt_trm) (v1 v2 : trm) (A1 A2 : formula)
        (Delta : cxt_ect) (p : proof_trm Gamma v1 A1 Delta),
        P0 Gamma v1 A1 Delta p ->
        forall p0 : proof_trm Gamma v2 A2 Delta,
          P0 Gamma v2 A2 Delta p0 ->
          P0 Gamma (paire v1 v2) (Conj A1 A2) Delta (ConjR p p0))
      (f6 : forall (Gamma : cxt_trm) (alpha : var_ect) 
        (A : formula) (Delta : list (prod var_ect formula))
        (i : In (pair alpha A) Delta),
        P1 Gamma (evar alpha) A Delta
        (AxL Gamma (alpha:=alpha) (A:=A) (Delta:=Delta) i))
      (f7 : forall (Gamma : list (prod var_trm formula)) (x : var_trm) 
        (c : cmd) (A : formula) (Delta : cxt_ect)
        (p : proof_cmd c (cons (pair x A) Gamma) Delta),
        P c (cons (pair x A) Gamma) Delta p ->
        P1 Gamma (mut x c) A Delta (MuT p))
      (f8 : forall (Gamma : cxt_trm) (v : trm) (e : ect) 
        (A B : formula) (Delta : cxt_ect) (p : proof_trm Gamma v A Delta),
        P0 Gamma v A Delta p ->
        forall p0 : proof_ect Gamma e B Delta,
          P1 Gamma e B Delta p0 ->
          P1 Gamma (app v e) (Imp A B) Delta (ImpL p p0))
      (f9 : forall (Gamma : cxt_trm) (e1 e2 : ect) (A1 A2 : formula)
        (Delta : cxt_ect) (p : proof_ect Gamma e1 A1 Delta),
        P1 Gamma e1 A1 Delta p ->
        forall p0 : proof_ect Gamma e2 A2 Delta,
          P1 Gamma e2 A2 Delta p0 ->
          P1 Gamma (disj e1 e2) (Disj A1 A2) Delta (DisjL p p0))
      (f10 : forall (Gamma : cxt_trm) (e : ect) (A1 A2 : formula) 
        (Delta : cxt_ect) (p : proof_ect Gamma e A1 Delta),
        P1 Gamma e A1 Delta p ->
        P1 Gamma (projl e) (Conj A1 A2) Delta (ConjLL A2 p))
      (f11 : forall (Gamma : cxt_trm) (e : ect) (A1 A2 : formula) 
        (Delta : cxt_ect) (p : proof_ect Gamma e A2 Delta),
        P1 Gamma e A2 Delta p ->
        P1 Gamma (projr e) (Conj A1 A2) Delta (ConjLR A1 p)) =>
      pair (pair 
        (proof_cmd_rect' (P:=P) (P0:=P0) (P1:=P1) f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11)
        (proof_trm_rect' (P:=P) (P0:=P0) (P1:=P1) f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11))
      (proof_ect_rect' (P:=P) (P0:=P0) (P1:=P1) f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11).
  
  Lemma forces_cxt_In : forall w x A Gamma, 
    In (x, A) Gamma -> w:||--Gamma -> w:||-A.
  Proof.
    induction Gamma.
    simpl.
    intros.
    contradict H.
    simpl.
    intros H H0.
    destruct H.
    rewrite e in H0.
    intuition.
    intuition.
  Defined.

  Lemma refutes_cxt_In : forall w alpha A Delta, 
    In (alpha, A) Delta -> w:Delta||-- -> w:A||-.
  Proof.
    induction Delta.
    simpl.
    intros.
    contradict H.
    simpl.
    intros H H0.
    destruct H.
    rewrite e in H0.
    intuition.
    intuition.
  Defined.

  Lemma srefutes_mon : forall A w, w:|A||- -> forall w', w <= w' -> w':|A||-.
  Proof.
    induction A.
    simpl.
    intros.
    eauto using arefutes_mon.

    intros w H1 w' ww'.
    simpl.
    simpl in H1.
    destruct H1 as [H11 H12].
    split.
    eauto using wle_trans.
    eauto using wle_trans.

    intros w H1 w' ww'.
    simpl in *.
    destruct H1.
    split.
    eauto using wle_trans.
    eauto using wle_trans.

    intros w H1 w' ww'.
    simpl in *.
    destruct H1.
    eauto using wle_trans.
    eauto using wle_trans.
  Defined.

  Lemma forces_Imp_r : forall (w:K)(A B:formula),
    (forall w', w <= w' -> w':||-A -> w':||-B) -> w:||- (Imp A B).
  Proof.
    intros w A B H.
    unfold forces in *.
    simpl in *.
    intros w' ww' [H1 H2].
    apply H2.
    apply wle_refl.
    intros w'' w'w'' H3.
    apply H with w'.
    assumption.
    assumption.
    assumption.
    assumption.
  Defined.

  Lemma forces_Imp_l : forall (w:K)(A B:formula),
    w:||- (Imp A B) -> forall w', w <= w' -> w':||-A -> w':||-B.
  Proof.
    intros w A B H1 w' ww' H2.
    unfold forces in H1.
    unfold forces.
    intros w'' w'w'' H3.
    apply H1.
    eauto using wle_trans.
    simpl.
    split.
    intros w''' w''w''' H4.
    apply H2; eauto using wle_trans.
    intros w''' w''w''' H4.
    apply H4.
    apply wle_refl.
    eauto using wle_trans,srefutes_mon.
  Defined.

  Lemma forces_mon : forall A w, w:||-A -> forall w', w <= w' -> w':||-A.
  Proof.
    induction A.
    intros.
    unfold forces in *.
    eauto using wle_trans.

    intros w H1 w' ww'.
    unfold forces in *.
    eauto using wle_trans.

    unfold forces.
    simpl.
    intros w1 H1 w2 H2.
    intros w3 H3 H4.
    apply H1.
    eauto using wle_trans.
    destruct H4.
    intuition.

    unfold forces; simpl.
    intros w1 H1 w2 H2.
    intros w3 H3 H4.
    apply H1.
    eauto using wle_trans.
    destruct H4.
    intuition.
    intuition.
  Defined.

  Lemma forces_cxt_mon : 
    forall Gamma w, w:||--Gamma -> forall w', w <= w' -> w':||--Gamma.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros.
    destruct X.
    split; eauto using wle_trans,forces_mon.
  Defined.

  Lemma srefutes_refutes (w:K)(A:formula) : w:|A||- -> w:A||-.
  Proof.
    intros H.
    unfold refutes.
    intros w' ww' H0.
    unfold forces in H0.
    eauto using wle_refl, srefutes_mon.
  Defined.

  Lemma refutes_mon : forall A w, w:A||- -> forall w', w <= w' -> w':A||-.
  Proof.
    induction A.
    intros.
    unfold refutes in *.
    unfold forces in *.
    eauto using wle_trans.

    intros w H1 w' ww'.
    unfold refutes in *.
    unfold forces in *.
    eauto using wle_trans.

    intros w H1 w' ww'.
    unfold refutes in *.
    unfold forces in *.
    eauto using wle_trans.

    intros w H1 w' ww'.
    unfold refutes in *.
    unfold forces in *.
    eauto using wle_trans.
  Defined.

  Lemma refutes_cxt_mon : 
    forall Delta w, w:Delta||-- -> forall w', w <= w' -> w':Delta||--.
  Proof.
    induction Delta.
    simpl.
    auto.
    simpl.
    intros.
    destruct X.
    split; eauto using wle_trans,refutes_mon.
  Defined.

  Theorem soundness : 
    (forall c Gamma Delta, c:(Gamma|-Delta) -> 
      forall w, w:||--Gamma -> w:Delta||-- -> exploding w) *

    (forall Gamma t A Delta, Gamma|-(t:A);Delta -> 
      forall w, w:||--Gamma -> w:Delta||-- -> w:||-A) *

    (forall Gamma e A Delta, Gamma;(e:A)|-Delta -> 
      forall w, w:||--Gamma -> w:Delta||-- -> w:A||-).
  Proof.
    apply proof_rect'.

    (* Cut *)
    intros v e Gamma Delta A _ IH1 _ IH2.
    intros w H H0.
    apply IH2 with w; auto.
    apply wle_refl.

    (* Ax_R *)
    intros Gamma x A Delta IH1.
    intros w H H0 w' ww' H1.
    assert (H2:=forces_cxt_In IH1 H).
    auto.

    (* mu *)
    intros Gamma alpha c A Delta _ IH1 w H H0.
    intros w' ww' H1.
    apply IH1.
    eauto using forces_cxt_mon,wle_trans.
    simpl.
    split; eauto using refutes_cxt_mon,refutes_mon,wle_trans,srefutes_refutes.

    (* imp_R *)
    intros Gamma x t A B Delta _ H.
    simpl in H.
    intros w H0 H1.
    apply forces_Imp_r.
    intros w' ww' H2.
    apply H.
    split; eauto using forces_cxt_mon,forces_mon,wle_trans.
    eauto using refutes_cxt_mon,wle_trans.

    (* DisjRL *)
    intros Gamma v A1 A2 Delta _ IH1.
    intros w H H0.
    red.
    intros w' H1 H2.
    simpl in H2.
    destruct H2 as [H21 H22].
    apply H21.
    apply wle_refl.
    apply IH1;
      eauto using forces_cxt_mon,refutes_cxt_mon.

    (* DisjRR *)
    intros Gamma v A1 A2 Delta _ IH1.
    intros w H H0.
    red.
    intros w' H1 H2.
    simpl in H2.
    destruct H2 as [H21 H22].
    apply H22.
    apply wle_refl.
    apply IH1;
      eauto using forces_cxt_mon,refutes_cxt_mon.

    (* ConjR *)
    intros Gamma v1 v2 A1 A2 Delta _ IH1 _ IH2.
    intros w H H0.
    red.
    intros w' H1 H2.
    simpl in H2.
    destruct H2.
    apply e.
    apply wle_refl.
    apply IH1;
      eauto using forces_cxt_mon,refutes_cxt_mon.
    apply e.
    apply wle_refl.
    apply IH2;
      eauto using forces_cxt_mon,refutes_cxt_mon.

    (* Ax_L *)
    intros Gamma alpha A Delta IH1.
    intros w H H0.
    assert (H1 := refutes_cxt_In IH1 H0).
    assumption.

    (* mu-tilda *)
    intros Gamma x c A Delta _ IH1.
    intros w H H0.
    simpl in IH1.
    unfold refutes.
    intros w' ww' H1.
    apply IH1.
    split; eauto using wle_trans,forces_mon,forces_cxt_mon.
    eauto using wle_trans,refutes_cxt_mon.

    (* imp_L *)
    intros Gamma v e A B Delta _ IH1 _ IH2 w HGamma HDelta.
    unfold refutes.
    intros w' ww' H.
    apply H.
    apply wle_refl.
    change (forces w' A * refutes w' B).
    split;eauto using wle_trans,forces_cxt_mon,refutes_cxt_mon.

    (* DisjL *)
    intros Gamma e1 e2 A1 A2 Delta _ IH1 _ IH2.
    intros w H H0.
    red.
    intros w' H1 H2.
    apply H2.
    apply wle_refl.
    simpl.
    split.
    apply IH1.
    eauto using refutes_cxt_mon,forces_cxt_mon.
    eauto using refutes_cxt_mon,forces_cxt_mon.
    apply IH2.
    eauto using refutes_cxt_mon,forces_cxt_mon.
    eauto using refutes_cxt_mon,forces_cxt_mon.

    (* ConjLL *)
    intros Gamma e A1 A2 Delta _ IH w H H0.
    intros w' H1 H2.
    apply H2.
    apply wle_refl.
    simpl.
    left.
    apply IH;
      eauto using refutes_cxt_mon,forces_cxt_mon.

    (* ConjLR *)
    intros Gamma e A1 A2 Delta _ IH w H H0.
    intros w' H1 H2.
    apply H2.
    apply wle_refl.
    simpl.
    right.
    apply IH;
      eauto using refutes_cxt_mon,forces_cxt_mon.
  Defined.
End Abstract_Semantics.

(** The Universal model *)
Section Context_Semantics.
  Definition Kworld : Set := cxt_trm*cxt_ect.

  Definition Kle (w w':Kworld) : Type :=
    incl (fst w) (fst w') * incl (snd w) (snd w').

  Lemma Kle_refl : forall w, Kle w w.
  Proof.
    intro w.
    split;
      auto using incl_refl.
  Defined.

  Lemma Kle_trans : forall w w' w'', Kle w w' -> Kle w' w'' -> Kle w w''.
  Proof.
    unfold Kle.
    intros.
    intuition eauto using incl_tran.
  Defined.

  Definition Kexploding (w:Kworld) : Set := 
    {c:cmd & proof_cmd c (fst w) (snd w)}.

  Definition Karefutes (w:Kworld)(X:var_formula) : Set := 
    {e:ect & proof_ect (fst w) e (Atom X) (snd w)}.

  Lemma proof_weaken : 
    (forall c Gamma Delta, c:(Gamma|-Delta) -> 
      forall Gamma' Delta', incl Gamma Gamma' -> incl Delta Delta' ->
        c:(Gamma'|-Delta')) *
    (forall Gamma t A Delta, Gamma|-(t:A);Delta -> 
      forall Gamma' Delta', incl Gamma Gamma' -> incl Delta Delta' ->
        Gamma'|-(t:A);Delta') *
    (forall Gamma e A Delta, Gamma;(e:A)|-Delta ->
      forall Gamma' Delta', incl Gamma Gamma' -> incl Delta Delta' ->
        Gamma';(e:A)|-Delta').
  Proof.
    apply proof_rect'.

    (* Cut *)
    eauto using Cut.

    (* AxR *)
    eauto using AxR.

    (* Mu *)
    intros.
    apply Mu.
    apply X.
    assumption.
    red.
    intuition.
    simpl in H |- *.
    intuition.

    (* ImpR *)
    intros.
    apply ImpR.
    apply X.
    red.
    simpl.
    intuition.
    assumption.

    (* DisjRL *)
    intros.
    apply DisjRL.
    apply X.
    assumption.
    assumption.

    (* DisjRR *)
    intros.
    apply DisjRR.
    apply X.
    assumption.
    assumption.

    (* ConjR *)
    intros.
    apply ConjR.
    apply X.
    assumption.
    assumption.
    apply X0.
    assumption.
    assumption.

    (* AxL *)
    eauto using AxL.

    (* MuT *)
    intros.
    apply MuT.
    apply X.
    red;simpl;intuition.
    assumption.

    (* ImpL *)
    eauto using ImpL.

    (* DisjL *)
    intros.
    apply DisjL.
    apply X; intuition.
    apply X0; intuition.

    (* ConjLL *)
    intros.
    apply ConjLL.
    apply X; intuition.

    (* ConjLR *)
    intros.
    apply ConjLR.
    apply X; intuition.
  Defined.

  Lemma Karefutes_mon : forall w X, Karefutes w X ->
    forall w', Kle w w' -> Karefutes w' X.
  Proof.
    intros w X H.
    destruct H as [e He].
    inversion He.

    intros w' Hle.
    exists (evar alpha).
    apply AxL.
    clear -H Hle.
    destruct Hle.
    intuition.
    
    intros w' Hle.
    exists (mut x c).
    apply MuT.
    destruct Hle.
    eapply (fst (fst proof_weaken)).
    apply H.
    red;simpl;intuition.
    assumption.
  Defined.

  Definition K : Kripke.
  (* begin show *)
    apply Build_Kripke with Kworld Kle Karefutes.
    exact Kle_refl.
    exact Kle_trans.
    exact Kexploding.
    exact Karefutes_mon.
  (* end show *)
  Defined.

  Definition Neutral_trm (uA:var_trm*formula)(Gamma:cxt_trm)(Delta:cxt_ect) :=
    forall t C Gamma' Delta', incl Gamma Gamma' -> incl Delta Delta' ->
      (uA::Gamma')|-(t:C);Delta' -> Gamma'|-(t:C);Delta'.
  Hint Unfold Neutral_trm.

  Definition Neutral_ect (alphaA:var_ect*formula)(Gamma:cxt_trm)(Delta:cxt_ect) :=
    forall e C Gamma' Delta', incl Gamma Gamma' -> incl Delta Delta' ->
      Gamma';(e:C)|-(alphaA::Delta') -> Gamma';(e:C)|-Delta'.
  Hint Unfold Neutral_ect.

  Notation "w <= w'" := (Kle w w').

  Notation "w : | A ||- " := (@srefutes K w A) (at level 70).
  Notation "w : ||- A" := (@forces K w A) (at level 70).
  Notation "w : A ||- " := (@refutes K w A)  (at level 70).
  Notation " w : ||-- Gamma" := (@forces_cxt K w Gamma) (at level 70).
  Notation " w : Delta ||-- "  := (@refutes_cxt K w Delta) (at level 70).

  (** We use these variables as a supply of fresh ones. This was just a temporary solution, for total correctness I should include an explicit counter to Kcompleteness, like it is done in the other files for Kripke-style models. *)
  Parameter beta gamma delta:var_ect.
  Parameter y:var_trm.

  (** The proof of completeness is via a two pairs of reify-reflect function *)
  Theorem Kcompleteness : forall A Gamma Delta, 
    ((Gamma,Delta):||-A -> sigT (fun t:trm => Gamma|-(t:A);Delta)) *
    (forall x, Neutral_trm (x,A) Gamma Delta -> (Gamma,Delta):||-A) *
    ((Gamma,Delta):A||- -> sigT (fun e:ect => Gamma;(e:A)|-Delta)) *
    (forall alpha, Neutral_ect (alpha,A) Gamma Delta -> (Gamma,Delta):A||-).
  Proof.
    induction A.

    (* Atom type *)
    intuition.

    unfold forces in X.
    simpl in X.
    unfold Kexploding in X.
    unfold Karefutes in X.
    set (Delta' := ((beta, Atom v)::Delta)).
    assert (H : (Gamma,Delta) <= (Gamma,Delta')).
    unfold Kle.
    split.
    intuition.
    unfold Delta'.
    simpl.
    red.
    simpl.
    intuition.
    assert (X0 := X (Gamma,Delta') H).
    simpl in X0.
    clear -X0.
    assert (sigT (fun (e : ect) => Gamma; (e : Atom v)|-Delta')).
    exists (evar beta).
    apply AxL.
    unfold Delta'.
    simpl.
    intuition.
    destruct (X0 H) as [c Hc].
    exists (mu beta c).
    apply Mu.
    apply Hc.

    rename X into H.
    red in H.
    red.
    simpl.
    red.
    unfold Karefutes.
    intros w' H0 H1.
    assert (sigT (fun (Gamma':cxt_trm) => 
      sigT (fun (Delta':cxt_ect) => w'=(Gamma',Delta')))).
    exists (fst w').
    exists (snd w').
      induction w'.
      simpl.
      reflexivity.
    destruct H2 as [Gamma' [Delta' Hw']].
    rewrite Hw' in *.
    simpl in *.
    destruct H1 as [e He].
    assert (H1 := H (tvar x) (Atom v) Gamma' Delta).
    exists (cm (tvar x) e).
    apply Cut with (Atom v).
    apply (snd (fst proof_weaken)) with Gamma' Delta; destruct H0; intuition.
    apply X.
    apply incl_refl.
    apply (AxR).
    simpl;intuition.
    assumption.

    unfold refutes in X.
    simpl in X.
    unfold forces in X.
    simpl in X.
    unfold Kexploding in X.
    set (w' := ((y,(Atom v))::Gamma, Delta)).
    assert ((Gamma,Delta) <= w').
    unfold w'.
    red.
    simpl.
    intuition.
    assert (forall w'' : Kworld, w' <= w'' -> Karefutes w'' v -> 
      sigT (fun (c:cmd) => c :  (fst w'' |- snd w''))).
      clear.
      unfold Karefutes.
      intros w'' H H0.
      destruct H0 as [e He].
      exists (cm (tvar y) e).
      apply Cut with (Atom v).
      apply AxR.
      destruct H.
      unfold w' in i.
      clear -i.
      red in i.
      red.
      apply i.
      simpl.
      intuition.
      assumption.
    destruct (X w' X0 X1) as [c Hc].
    exists (mut y c).
    apply MuT.
    apply Hc.

    red in X.
    red.
    simpl.
    red.
    intro w'.
    unfold forces.
    simpl.
    unfold Karefutes, Kexploding .
    assert (sigT (fun (Gamma':cxt_trm) => 
      sigT (fun (Delta':cxt_ect) => w'=(Gamma',Delta')))).
      exists (fst w').
      exists (snd w').
      induction w'.
      simpl.
      reflexivity.
    destruct H as [Gamma' [Delta' Hw']].
    rewrite Hw' in *.
    simpl in *.
    intros.
    replace Gamma' with (fst w').
    replace Delta' with (snd w').
    Focus 2.
    rewrite Hw'; auto.
    Focus 2.
    rewrite Hw'; auto.
    apply X1.
    red.
    rewrite Hw'.
    intuition.
    exists (evar alpha).
    apply (snd proof_weaken) with Gamma Delta'.
    Focus 2.
    rewrite Hw'.
    simpl.
    destruct X0.
    intuition.
    Focus 2.
    rewrite Hw'.
    simpl.
    intuition.
    apply X.
    destruct X0.
    intuition.
    destruct X0.
    intuition.
    apply AxL.
    simpl.
    intuition.

    (* Induction case -- Imp *)
    intuition.
    unfold forces in X.
    simpl exploding in X.
    simpl wle in X.
    unfold Kexploding in X.
    set (w':=((y,A1)::Gamma,(beta,A2)::Delta)).
    assert ((Gamma,Delta) <= w').
    unfold w'.
    red.
    simpl.
    split;
      red;
        simpl;
          intuition.
    assert(H0 : w' :  | Imp A1 A2 ||-).
      simpl.
      split.
      (* prove: forces w' A1 *)
      clear -IHA1.
      destruct (IHA1 (fst w') (snd w')).
      destruct p.
      destruct p.
      unfold forces in f.
      simpl in f.
      unfold w'.
      apply f with y.
      clear.
      red.
      intros.
      apply (snd (fst proof_weaken)) with ((y, A1) :: Gamma') Delta'.
      assumption.
      red in X |- *;simpl in *;intuition.
      red in X0 |- *;simpl in *;intuition.
      (* prove: refutes w' A2 *)
      clear -IHA2.
      destruct (IHA2 (fst w') (snd w')).
      destruct p.
      destruct p.
      unfold refutes in r.
      simpl in r.
      unfold forces in r.
      simpl in r.
      unfold w'.
      apply r with beta.
      clear.
      red.
      intros.
      apply (snd proof_weaken) with Gamma' ((beta,A2)::Delta').
      assumption.
      intuition.
      clear -X0; red in X0 |- *; simpl in *; intuition.
      destruct (X w' X0 H0) as [c Hc].
      unfold w' in Hc.
    simpl in Hc.
    eexists.
    apply ImpR.
    apply Mu.
    apply Hc.

    unfold forces.
    simpl.
    intros w' H H0.
    unfold Kexploding.
    destruct H0 as [X1 X2].
    assert (H1 : w':||-A1).
    unfold forces.
    apply X1.
    assert (H2 : w':A2||-).
    unfold refutes.
    apply X2.
    assert (IH1 := fst (fst (fst (IHA1 (fst w') (snd w')))) H1).
    assert (IH2 := (snd (fst (IHA2 (fst w') (snd w')))) H2).
    clear -IH1 IH2 H X.
    destruct IH1 as [t Ht].
    destruct IH2 as [e He].
    assert (Hu : sigT (fun u:trm => fst w' |- (u:A2); snd w')).
      red in X.
      exists (mu beta (cm (tvar x) (app t e))).
      apply X.
      destruct H; intuition.
      destruct H; intuition.
      apply Mu.
      apply Cut with (Imp A1 A2).
      apply AxR.
      red; simpl; intuition.
      apply ImpL.
      apply (snd (fst proof_weaken)) with (fst w') (snd w').
      apply Ht.
      intuition.
      intuition.
      apply (snd (proof_weaken)) with (fst w') (snd w').
      assumption.
      intuition.
      intuition.
    destruct Hu as [u Hu].
    exists (cm u e). (* can this be turned into a trivial cut? 
                        -- yes, se the paper version, where we
                        don't cut with A2 but with A1->A2 *)
    apply Cut with A2.
    assumption.
    assumption.

    red in X.
    simpl in X.
    red in X.
    set (w1:=(Gamma,(beta,A1)::Delta)).
    assert ((Gamma,Delta) <= w1).
    unfold w1.
    split.
    simpl.
    intuition.
    simpl.
    intuition.
    assert (H0 : w1:||-Imp A1 A2).
      unfold forces.
      simpl.
      intros.
      destruct X0.
      assert (sigT (fun e:ect => fst w';(e:A1) |- snd w')).
      exists (evar beta).
      apply AxL.
      destruct X1 as [_ H2].
      apply H2.
      unfold w1.
      simpl; intuition.
      assert (sigT (fun t:trm => fst w' |- (t:A1);snd w')).
      destruct X2.
      assert (IH1 := (fst (fst (fst (IHA1 (fst w') (snd w'))))) k).
      apply IH1.
      destruct H0 as [t Ht].
      destruct H as [e He].
      exists (cm t e).
      apply Cut with A1.
      assumption.
      assumption.
    set (w2:=((y,A2)::Gamma,Delta)).
    assert ((Gamma,Delta) <= w2).
    unfold w2.
    split.
    simpl.
    intuition.
    simpl.
    intuition.
    assert (H2 : w2:||-Imp A1 A2).
      unfold forces.
      simpl.
      intros.
      destruct X0.
      assert (sigT (fun t:trm => fst w' |- (t:A2); snd w')).
      exists (tvar y).
      apply AxR.
      destruct X2 as [H2 _].
      apply H2.
      unfold w2.
      simpl; intuition.
      assert (sigT (fun e:ect => fst w' ; (e:A2) |- snd w')).
      destruct X3.
      assert (IH2 := (snd (fst (IHA2 (fst w') (snd w')))) k0).
      apply IH2.
      destruct H as [t Ht].
      destruct H1 as [e He].
      exists (cm t e).
      apply Cut with A2.
      assumption.
      assumption.
    destruct (X w1 X0 H0) as [c1 Hc1].
    destruct (X w2 X1 H2) as [c2 Hc2].
    unfold w1 in Hc1.
    simpl in Hc1.
    unfold w2 in Hc2.
    simpl in Hc2.
    eexists.
    apply ImpL.
    apply Mu.
    apply Hc1.
    apply MuT.
    apply Hc2.

    unfold refutes.
    simpl.
    intros.
    red.
    unfold forces in X.
    simpl exploding in X.
    simpl wle in X.
    red in X.
    set (w'' := ((y,A1)::fst w', (alpha,A2)::snd w')).
    assert (w' <= w'').
    unfold w'';simpl;red;simpl;intuition.
    assert (H2 : w'':|Imp A1 A2||-).
    simpl.
    split.
    (* forces w'' A1 *)
      assert (IH1 := snd (fst (fst (IHA1 (fst w'') (snd w''))))).
      unfold forces in IH1.
      simpl in IH1.
      apply IH1 with y.
      clear -X0.
      red.
      intros.
      apply (snd (fst proof_weaken)) with ((y,A1)::Gamma') Delta'.
      assumption.
      red in X |- *.
      simpl in *.
      intuition.
      apply incl_refl.
    (* refutes w'' A2 *)
      assert (IH2 := snd (IHA2 (fst w'') (snd w''))).
      unfold refutes in IH2.
      simpl in IH2.
      apply IH2 with alpha.
      clear -X0.
      red.
      intros.
      apply (snd proof_weaken) with Gamma' ((alpha,A2)::Delta').
      assumption.
      apply incl_refl.
      red in X1 |- *.
      simpl in *.
      intuition.
    destruct (X1 w'' X2 H2) as [c Hc].
    unfold w'' in Hc.
    simpl in Hc.
    eexists.
    apply Cut with (Imp A1 A2).
    apply ImpR.
    apply Mu.
    apply Hc.
    apply X.
    red in X0; intuition.
    red in X0; intuition.
    apply AxL.
    red; intuition.

    (* Induction case -- Disj *)
    split.
    split.
    split.

    intro H.
    unfold forces in H.
    change (forall w':K, (Gamma,Delta) <= w' -> refutes w' A1 * refutes w' A2 -> Kexploding w') in H.
      set (w' := (Gamma, (delta,A2)::(gamma,A1)::(beta,Disj A1 A2)::Delta)).
      assert (H0 : (Gamma,Delta) <= w').
      unfold w'.
      clear.
      red;simpl;split;red;simpl;intuition.
      assert (H1 : w':A1||-).
      apply (snd (IHA1 (fst w') (snd w'))) with gamma.
      unfold w'.
      simpl.
      red.
      intros.
      apply (snd proof_weaken) with Gamma' ((gamma, A1)::Delta').
      assumption.
      apply incl_refl.
      clear -X0.
      red in X0 |- *; simpl in X0 |- *;intuition.
      assert (H2 : w':A2||-).
      apply (snd (IHA2 (fst w') (snd w'))) with delta.
      unfold w'.
      simpl.
      red.
      intros.
      apply (snd proof_weaken) with Gamma' ((delta, A2)::Delta').
      assumption.
      apply incl_refl.
      clear -X0.
      red in X0 |- *; simpl in X0 |- *;intuition.
    assert (Hc := H w' H0 (H1,H2)).
    destruct Hc as [c Hc].
    unfold w' in Hc.
    simpl in Hc.
    exists (
      mu beta (
        cm (mu gamma (cm (mu delta c) (
            mut y (cm (injr (tvar y)) (evar beta))))) 
        (mut y (cm (injl (tvar y)) (evar beta))))).
    (*eexists.*)
    apply Mu.
    apply Cut with A1.
    apply Mu.
    apply Cut with A2.
    apply Mu.
    apply Hc.
      apply MuT.
      apply Cut with (Disj A1 A2).
      apply DisjRR.
      apply AxR.
      simpl;intuition.
      apply AxL.
      simpl;intuition.
      apply MuT.
      apply Cut with (Disj A1 A2).
      apply DisjRL.
      apply AxR.
      simpl;intuition.
      apply AxL.
      simpl;intuition.

    intros x H.
    unfold forces.
    change (forall w':K, (Gamma,Delta) <= w' -> refutes w' A1 * refutes w' A2 -> Kexploding w').
    intros w' H0 [H1 H2].
    change ((Gamma,Delta) <= (fst w', snd w')) in H0.
    destruct (IHA1 (fst w') (snd w')) as [[_ IH1] _].
    apply IH1 in H1.
    destruct (IHA2 (fst w') (snd w')) as [[_ IH2] _].
    apply IH2 in H2.
    destruct H1 as [e1 He1].
    destruct H2 as [e2 He2].
    eexists.
    apply Cut with (Disj A1 A2).
    apply H.
    destruct H0.
    intuition.
    destruct H0.
    intuition.
    apply AxR.
    intuition.
    apply DisjL.
    apply He1.
    apply He2.

    intro H.
    unfold refutes in H.
    unfold forces in H.
    simpl in H.
    change (forall w':K, (Gamma,Delta) <= w' -> 
      (forall w'':K, w' <= w'' -> refutes w'' A1 * refutes w'' A2 -> Kexploding w'') 
      -> Kexploding w') in H.
    set (w' := (((y,Disj A1 A2)::Gamma), Delta)).
    assert (H0 : (Gamma, Delta) <= w').
    unfold w'.
    red.
    simpl.
    intuition.
    apply H in H0.
    destruct H0 as [c Hc].
    eexists.
    apply MuT.
    unfold w' in Hc.
    simpl in Hc.
    apply Hc.
    intros w'' Hle H1.
    destruct H1 as [H1 H2].
    destruct (IHA1 (fst w'') (snd w'')) as [[_ IH1] _].
    apply IH1 in H1.
    destruct (IHA2 (fst w'') (snd w'')) as [[_ IH2] _].
    apply IH2 in H2.
    destruct H1 as [e1 He1].
    destruct H2 as [e2 He2].
    eexists.
    apply Cut with (Disj A1 A2).
    apply AxR.
    destruct Hle as [Hle _].
    apply Hle.
    unfold w'.
    simpl.
    left.
    reflexivity.
    apply DisjL.
    apply He1.
    apply He2.

    intros alpha H.
    unfold refutes.
    unfold forces.
    simpl.
    change (forall w':K, (Gamma,Delta) <= w' -> 
      (forall w'':K, w' <= w'' -> refutes w'' A1 * refutes w'' A2 -> Kexploding w'') 
      -> Kexploding w').
    intros w' H0 H1.
      set (w1 := (fst w', ((gamma,A2)::(beta,A1)::(snd w')))).
      assert (H2 : w' <= w1).
      change ((fst w',snd w') <= w1).
      unfold w1.
      red; simpl;
        intuition.
      assert (H3: w1:A1||-).
      apply (snd (IHA1 (fst w1) (snd w1))) with beta.
      unfold w1.
      clear.
      red; intros.
      simpl in *.
      apply (snd proof_weaken) with Gamma' ((beta,A1)::Delta'); intuition.
      clear -X0.
      unfold incl in *.
      simpl in *.
      intuition.
      assert (H4: w1:A2||-).
      apply (snd (IHA2 (fst w1) (snd w1))) with gamma.
      unfold w1.
      clear.
      red; intros.
      simpl in *.
      apply (snd proof_weaken) with Gamma' ((gamma,A2)::Delta'); intuition.
      clear -X0.
      unfold incl in *.
      simpl in *.
      intuition.
      destruct (H1 w1 H2 (H3,H4)) as [c Hc].
      unfold w1 in Hc.
      simpl in Hc.
    exists (cm (mu beta (cm (mu gamma c) (mut y (cm (injr (tvar y)) (evar alpha))))) (mut y (cm (injl (tvar y)) (evar alpha)))).
    (*eexists.*)
    apply Cut with A1.
    apply Mu.
    apply Cut with A2.
    apply Mu.
    apply Hc.
    apply H.
    destruct H0.
    intuition.
    destruct H0; unfold incl in *; simpl in *; intuition.
    apply MuT.
    apply Cut with (Disj A1 A2).
    apply DisjRR.
    apply AxR.
    intuition.
    apply AxL.
    intuition.
    apply H.
    destruct H0.
    intuition.
    destruct H0; unfold incl in *; simpl in *; intuition.
    apply MuT.
    apply Cut with (Disj A1 A2).
    apply DisjRL.
    apply AxR.
    intuition.
    apply AxL.
    intuition.

    (* Induction case - Conjunction *)
    split.
    split.
    split.

    intro H.
    red in H.
    change (forall w':K, (Gamma,Delta) <= w' -> refutes w' A1 + refutes w' A2 
      -> Kexploding w') in H.
    set (w1 := (Gamma, (beta,A1)::Delta)).
      assert (H11 : (Gamma,Delta) <= w1).
      unfold w1.
      clear;red;simpl;intuition.
      assert (H12 : @refutes K w1 A1).
      apply (snd (IHA1 (fst w1) (snd w1))) with beta.
      unfold w1; simpl.
      clear.
      red.
      intros.
      apply (snd (proof_weaken)) with Gamma' ((beta,A1)::Delta').
      assumption.
      intuition.
      red;simpl;intuition.
      assert (H13:Kexploding w1).
      intuition.
      destruct H13 as [c1 Hc1].
      unfold w1 in Hc1; simpl in Hc1.
    set (w2 := (Gamma, (beta,A2)::Delta)).
      assert (H21 : (Gamma,Delta) <= w2).
      unfold w2.
      clear;red;simpl;intuition.
      assert (H22 : @refutes K w2 A2).
      apply (snd (IHA2 (fst w2) (snd w2))) with beta.
      unfold w2; simpl.
      clear.
      red.
      intros.
      apply (snd (proof_weaken)) with Gamma' ((beta,A2)::Delta').
      assumption.
      intuition.
      red;simpl;intuition.
      assert (H23:Kexploding w2).
      intuition.
      destruct H23 as [c2 Hc2].
      unfold w2 in Hc2; simpl in Hc2.
    clear - Hc1 Hc2.
    eexists.
    apply ConjR.
    apply Mu.
    apply Hc1.
    apply Mu.
    apply Hc2.

    intros x H.
    change (forall w':K, (Gamma,Delta) <= w' -> refutes w' A1 + refutes w' A2 
      -> Kexploding w').
    intros w' H0 H1.
    destruct H1.
    destruct ((snd (fst (IHA1 (fst w') (snd w')))) r) as [e1 He1].
    exists (cm (mu beta (cm (tvar x) (projl (evar beta)))) (e1)).
    apply Cut with A1.
    apply H.
    destruct H0;intuition.
    destruct H0;intuition.
    apply Mu.
    apply Cut with (Conj A1 A2).
    apply AxR.
    left;reflexivity.
    apply ConjLL.
    apply AxL.
    left;reflexivity.
    apply He1.
    destruct ((snd (fst (IHA2 (fst w') (snd w')))) r) as [e2 He2].
    exists (cm (mu beta (cm (tvar x) (projr (evar beta)))) (e2)).
    apply Cut with A2.
    apply H.
    destruct H0;intuition.
    destruct H0;intuition.
    apply Mu.
    apply Cut with (Conj A1 A2).
    apply AxR.
    left;reflexivity.
    apply ConjLR.
    apply AxL.
    left;reflexivity.
    apply He2.

    intro H.
    set (w' := ((y,Conj A1 A2)::Gamma, Delta)).
    red in H.
    simpl in H.
    assert (H0 : (Gamma,Delta) <= w').
    unfold w';clear;red;simpl;intuition.
    apply H in H0.
    destruct H0 as [c Hc].
    unfold w' in Hc; simpl in Hc.
    eexists.
    apply MuT.
    apply Hc.
    change (forall w'':K, w' <= w'' -> refutes w'' A1 + refutes w'' A2 
      -> Kexploding w'').
    intros w'' H1 H2.
    destruct H2.
    assert (H2 := (snd (fst (IHA1 (fst w'') (snd w'')))) r).
    destruct H2 as [e He].
    eexists.
    apply Cut with (Conj A1 A2).
    apply AxR.
    apply H1.
    left;reflexivity.
    apply ConjLL.
    apply He.
    assert (H2 := (snd (fst (IHA2 (fst w'') (snd w'')))) r).
    destruct H2 as [e He].
    eexists.
    apply Cut with (Conj A1 A2).
    apply AxR.
    apply H1.
    left;reflexivity.
    apply ConjLR.
    apply He.

    intros alpha H.
    intros w' H0 H1.
    simpl in *.
    change (forall w'':K, w' <= w'' -> refutes w'' A1 + refutes w'' A2 
      -> Kexploding w'') in H1.
    set (w1 := (fst w', (beta,A1)::snd w')).
    assert (H11 : w' <= w1).
    unfold w1;simpl;red;simpl;intuition.
    assert (H12 : @refutes K w1 A1).
    apply (snd (IHA1 (fst w1) (snd w1))) with beta.
    unfold w1; simpl.
    clear.
      red.
      intros.
      apply (snd (proof_weaken)) with Gamma' ((beta,A1)::Delta').
      assumption.
      apply incl_refl.
      clear -X0.
      red in X0 |- *.
      simpl in *; intuition.
    set (w2 := (fst w', (beta,A2)::snd w')).
    assert (H21 : w' <= w2).
    unfold w2;simpl;red;simpl;intuition.
    assert (H22 : @refutes K w2 A2).
    apply (snd (IHA2 (fst w2) (snd w2))) with beta.
    unfold w2; simpl.
    clear.
      red.
      intros.
      apply (snd (proof_weaken)) with Gamma' ((beta,A2)::Delta').
      assumption.
      apply incl_refl.
      clear -X0.
      red in X0 |- *.
      simpl in *; intuition.
    assert (Hc1 : Kexploding w1).
    intuition.
    assert (Hc2 : Kexploding w2).
    intuition.
    destruct Hc1 as [c1 Hc1].
    destruct Hc2 as [c2 Hc2].
    unfold w1 in Hc1; simpl in Hc1. 
    unfold w2 in Hc2; simpl in Hc2.
    eexists.
    apply Cut with (Conj A1 A2).
    apply ConjR.
    apply Mu.
    apply Hc1.
    apply Mu.
    apply Hc2.
    apply H.
    destruct H0; intuition.
    destruct H0; intuition.
    apply AxL.
    left; reflexivity.
  Defined.
End Context_Semantics.

Lemma forces_cxt_id : forall Gamma Delta, @forces_cxt K (Gamma,Delta) Gamma.
Proof.
  induction Gamma.
  simpl.
  constructor.
  simpl.
  intro Delta.
  split.
  apply (snd (fst (fst (Kcompleteness (snd a) (a::Gamma) Delta)))) with (fst a).
  red.
  intros.
  apply (snd (fst proof_weaken)) with ((fst a, snd a)::Gamma') Delta'.
  assumption.
  clear -X.
  assert (In a Gamma').
  intuition.
  replace ((fst a, snd a)) with a.
  red.
  simpl.
  intuition.
  destruct a; auto.
  apply incl_refl.
  apply forces_cxt_mon with (Gamma, Delta).
  auto.
  simpl.
  red.
  simpl.
  unfold incl.
  intuition.
Defined.

Lemma refutes_cxt_id : forall Gamma Delta, @refutes_cxt K (Gamma,Delta) Delta.
Proof.
  induction Delta.
  simpl.
  constructor.
  simpl.
  split.
  apply (snd (( (Kcompleteness (snd a) Gamma (a::Delta))))) with (fst a).
  red.
  intros.
  apply (snd (proof_weaken)) with Gamma' ((fst a, snd a)::Delta').
  assumption.
  apply incl_refl.
  clear -X0.
  assert (In a Delta').
  intuition.
  replace ((fst a, snd a)) with a.
  red.
  simpl.
  intuition.
  destruct a; auto.
  apply refutes_cxt_mon with (Gamma, Delta).
  auto.
  simpl.
  red.
  simpl.
  unfold incl.
  intuition.
Defined.

Definition NbE : forall c Gamma Delta, proof_cmd c Gamma Delta ->
  {c':cmd & proof_cmd c' Gamma Delta}.
Proof.
  intros c Gamma Delta H.
  destruct c as [t e].
  inversion H.
  clear -H2 H5.
  assert (HGamma : @forces_cxt K (Gamma,Delta) Gamma).
  apply forces_cxt_id.
  assert (HDelta : @refutes_cxt K (Gamma,Delta) Delta).
  apply refutes_cxt_id.
  assert (H2' := (snd (fst (soundness K))) Gamma t A Delta H2 (Gamma,Delta) HGamma HDelta).
  assert (H5' := (snd (soundness K)) Gamma e A Delta H5 (Gamma,Delta) HGamma HDelta).
  unfold refutes in H5'.
  simpl in H5'.
  apply H5' in H2'.
  red in H2'.
  simpl in H2'.
  exact H2'.
  apply Kle_refl.
Defined.

(** Now some normalisation tests *)
Parameter o : var_formula.
Parameters x z : var_trm.

(** Example 0: a simplest possible beta-reduction *)
Definition cmd0 : cmd := cm (lam x (tvar x)) (app (tvar y) (evar beta)).
Definition Gamma0 := ((y,Atom o)::nil).
Definition Delta0 := ((beta,Atom o)::nil).
Definition proof0 : proof_cmd cmd0 Gamma0 Delta0.
Proof.
  apply Cut with (Imp (Atom o) (Atom o)).
  apply ImpR.
  apply AxR.
  left; reflexivity.
  apply ImpL.
  apply AxR.
  left; reflexivity.
  apply AxL.
  left; reflexivity.
Defined.
Definition test0 := projT1 (NbE proof0).
(* Time Eval vm_compute in test0. *)

(** Example 1: a seemingly more complex beta-reduction, which reduces to the
   same thing as example 0 *)
Definition cmd1 : cmd := cm (lam x (tvar y)) (app (tvar x) (evar beta)).
Definition Gamma1 := ((y,Atom o)::(x,Atom o)::nil).
Definition Delta1 := ((beta,Atom o)::nil).
Definition proof1 : proof_cmd cmd1 Gamma1 Delta1.
Proof.
  apply Cut with (Imp (Atom o) (Atom o)).
  apply ImpR.
  apply AxR.
  right.
  left; reflexivity.
  apply ImpL.
  apply AxR.
  right.
  left; reflexivity.
  apply AxL.
  left; reflexivity.
Defined.
Definition test1 := projT1 (NbE proof1).
(* Time Eval vm_compute in test1. *)

(** Example 2: The <mu,mu~> critical pair indicates we are indeed in
   call-by-name. To check that the CBN behaviour does not depend on the choice of a proof,
   we try it with two different proofs. *)
Definition c' : cmd := cm (tvar x) (evar gamma).
Definition c'' : cmd := cm (tvar z) (evar delta).
Definition cmd2 := cm (mu beta c') (mut y c'').
Definition proof2 : proof_cmd cmd2 ((x,Atom o)::(z,Atom o)::nil) ((gamma,Atom o)::(delta,Atom o)::nil).
Proof.
  apply Cut with (Atom o).
  apply Mu.
  apply Cut with (Atom o).
  apply AxR.
  left;reflexivity.
  apply AxL.
  right;left;reflexivity.
  apply MuT.
  apply Cut with (Atom o).
  apply AxR.
  right;right;left;reflexivity.
  apply AxL.
  right;left;reflexivity.
Defined.
Definition proof2' : proof_cmd cmd2 ((z,Atom o)::(x,Atom o)::nil) ((delta,Atom o)::(gamma,Atom o)::nil).
Proof.
  apply Cut with (Atom o).
  apply Mu.
  apply Cut with (Atom o).
  apply AxR.
  right;left;reflexivity.
  apply AxL.
  right;right;left;reflexivity.
  apply MuT.
  apply Cut with (Atom o).
  apply AxR.
  right;left;reflexivity.
  apply AxL.
  left;reflexivity.
Defined.
Definition test2 := projT1 (NbE proof2).
Definition test2' := projT1 (NbE proof2').
(* Time Eval vm_compute in test2. *)
(* Time Eval vm_compute in test2'. *)

(** Example 3: verifying reduction for implication *)
Definition cmd3 := cm (lam x (tvar z)) (app (tvar y) (evar gamma)).
Definition proof3 : proof_cmd cmd3 ((y,Atom o)::(z,Atom o)::nil) ((gamma,Atom o)::nil).
Proof.
  apply Cut with (Imp (Atom o) (Atom o)).
  apply ImpR.
  apply AxR.
  right;right;left;reflexivity.
  apply ImpL.
  apply AxR.
  left;reflexivity.
  apply AxL.
  left;reflexivity.
Defined.
Definition test3 := projT1 (NbE proof3).
(* Time Eval vm_compute in test3. *)

(** Example 4: verifying reduction for mu *)
Definition cmd4 := cm (mu gamma (cm (tvar y) (evar delta))) (evar beta).
Definition proof4 : proof_cmd cmd4 ((y,Atom o)::nil) ((beta,Atom o)::(delta,Atom o)::nil).
Proof.
  apply Cut with (Atom o).
  apply Mu.
  apply Cut with (Atom o).
  apply AxR.
  left;reflexivity.
  apply AxL.
  right;right;left;reflexivity.
  apply AxL.
  left;reflexivity.
Defined.
Definition test4 := projT1 (NbE proof4).
(* Time Eval vm_compute in test4. *)

(** Example 4': verifying reduction for mu *)
Definition cmd4' := cm (mu gamma (cm (tvar y) (evar gamma))) (evar beta).
Definition proof4' : proof_cmd cmd4' ((y,Atom o)::nil) ((beta,Atom o)::nil).
Proof.
  apply Cut with (Atom o).
  apply Mu.
  apply Cut with (Atom o).
  apply AxR.
  left;reflexivity.
  apply AxL.
  left;reflexivity.
  apply AxL.
  left;reflexivity.
Defined.
Definition test4' := projT1 (NbE proof4').
(* Time Eval vm_compute in test4'. *)

(** Example 5: verifying reduction for conjunction 1 *)
Definition cmd5 := cm (paire (tvar x) (tvar z)) (projl (evar beta)).
Definition proof5 : proof_cmd cmd5 ((x,Atom o)::(z,Atom o)::nil) ((beta,Atom o)::nil).
Proof.
  apply Cut with (Conj (Atom o) (Atom o)).
  apply ConjR.
  apply AxR.
  left;reflexivity.
  apply AxR.
  right;left;reflexivity.
  apply ConjLL.
  apply AxL.
  left;reflexivity.
Defined.
Definition test5 := projT1 (NbE proof5).
(* Time Eval vm_compute in test5. *)

(** Example 6: verifying reduction for conjunction 2 *)
Definition cmd6 := cm (paire (tvar x) (tvar z)) (projr (evar beta)).
Definition proof6 : proof_cmd cmd6 ((x,Atom o)::(z,Atom o)::nil) ((beta,Atom o)::nil).
Proof.
  apply Cut with (Conj (Atom o) (Atom o)).
  apply ConjR.
  apply AxR.
  left;reflexivity.
  apply AxR.
  right;left;reflexivity.
  apply ConjLR.
  apply AxL.
  left;reflexivity.
Defined.
Definition test6 := projT1 (NbE proof6).
(* Time Eval vm_compute in test6. *)

(** Example 7: verifying reduction for disjunction 1 *)
Definition cmd7 := cm (injl (tvar z)) (disj (evar gamma) (evar delta)).
Definition proof7 : proof_cmd cmd7 ((z,Atom o)::nil) ((gamma,Atom o)::(delta,Atom o)::nil).
Proof.
  apply Cut with (Disj (Atom o) (Atom o)).
  apply DisjRL.
  apply AxR.
  left;reflexivity.
  apply DisjL.
  apply AxL.
  left;reflexivity.
  apply AxL.
  right;left;reflexivity.
Defined.
Definition test7 := projT1 (NbE proof7).
(* Time Eval vm_compute in test7. *)

(** Example 8: verifying reduction for disjunction 2 *)
Definition cmd8 := cm (injr (tvar z)) (disj (evar gamma) (evar delta)).
Definition proof8 : proof_cmd cmd8 ((z,Atom o)::nil) ((gamma,Atom o)::(delta,Atom o)::nil).
Proof.
  apply Cut with (Disj (Atom o) (Atom o)).
  apply DisjRR.
  apply AxR.
  left;reflexivity.
  apply DisjL.
  apply AxL.
  left;reflexivity.
  apply AxL.
  right;left;reflexivity.
Defined.
Definition test8 := projT1 (NbE proof8).
(* Time Eval vm_compute in test8. *)

