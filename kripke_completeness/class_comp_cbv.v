(** Formalised proof of completeness of full Classical predicate logic
   with respect to Kripke-style models.

   Danko Ilik, January 2010

   Normalisation examples at end of file.

   Note: Soundness theorem quantifier cases need to be finished.
*)
Require Import stdlib_Type.
Require Import EqNat.
Require Import Peano_dec.

Set Implicit Arguments.
Unset Strict Implicit.

(** printing <= $\le$ #&le;# *)
(** printing ||-- $\Vdash$ #⊩# *)
(** printing ||- $\Vdash$ #⊩# *)
(** printing ||+ $\Vdash_s$ #⊩<sub>s</sub># *)

Open Scope type_scope.

Definition var_trm := nat.
Definition var_ect := nat.

(** Commands, terms, and evaluation contexts *)
Inductive cmd : Set :=
| cm : trm -> ect -> cmd
with trm : Set :=
| tvar  : var_trm -> trm
| lam   : var_trm -> trm -> trm
| injl  : trm -> trm
| injr  : trm -> trm
| paire : trm -> trm -> trm
| mu    : var_ect -> cmd -> trm
| tall  : trm -> trm
| tex   : trm -> trm
with ect : Set :=
| evar  : var_ect -> ect
| app   : trm -> ect -> ect
| disj  : ect -> ect -> ect
| projl : ect -> ect
| projr : ect -> ect
| mut   : var_trm -> cmd -> ect
| eall  : ect -> ect
| eex   : ect -> ect.

(** Abstract (decidable) sets of fresh variables, and predicate and function symbols *)
Parameter var_free : Set.
Parameter var_free_dec : forall x y:var_free, {x=y}+{~x=y}.
Parameters predicate function : Set.
Notation "x \notin L" := (In x L -> Empty_set) (at level 69).
Hypothesis fresh_fvar : forall L, sigT (fun x:var_free => x \notin L).

(** Individual terms. [bvar]s are deBruijn indices which represent bound variables, while [fvar]s are names that represent free variables *)
Inductive indiv : Set :=
  bvar : nat -> indiv
| fvar : var_free -> indiv
| func : function -> list indiv -> indiv.

Inductive typ : Set :=
  Atom : predicate -> list indiv -> typ
| Imp  : typ -> typ -> typ
| Disj : typ -> typ -> typ
| Conj : typ -> typ -> typ
| All  : typ -> typ
| Ex   : typ -> typ.

(** Substituting at de Bruijn variable k *) 

Fixpoint subst_indiv (k:nat)(a:indiv)(d:indiv) {struct a} : indiv :=
  let subst_list := fix subst_list (l:list indiv) {struct l} : list indiv :=
    match l with
      | nil => nil
      | cons a' l' => cons (subst_indiv k a' d) (subst_list l')
    end in
  match a with
    | func f ld => 
      func f (subst_list ld)
    | fvar x => fvar x
    | bvar i => if beq_nat k i then d else bvar i
  end.

Fixpoint subst (k:nat)(A:typ)(d:indiv) {struct A} : typ :=
  let subst_list := fix subst_list (l:list indiv) {struct l} : list indiv :=
    match l with
      | nil => nil
      | cons a' l' => cons (subst_indiv k a' d) (subst_list l')
    end in
  match A with
    | Ex A1      => Ex (subst (S k) A1 d) 
    | All A1     => All (subst (S k) A1 d) 
    | Conj A1 A2 => Conj (subst k A1 d) (subst k A2 d)
    | Disj A1 A2 => Disj (subst k A1 d) (subst k A2 d)
    | Imp A1 A2  => Imp (subst k A1 d) (subst k A2 d)
    | Atom P ld => 
      Atom P (subst_list ld)
  end.

Notation "A ^^ d" := (subst 0 A d) (at level 67).
Notation "A ^ x" := (subst 0 A (fvar x)).

(** A formula is [locl] ("locally closed") when all [bvar]s are bound
   by quantifiers (while there might be [fvar]s around) *)
Definition locl (A:typ) := forall k d, (subst k A d) = A.
Definition locli (d':indiv) := forall k d, (subst_indiv k d' d) = d'.

Let cxt_trm := list (var_trm*typ).
Let cxt_ect := list (var_ect*typ).

Reserved Notation "c : ( Gamma |- Delta ) " (at level 70).
Reserved Notation "Gamma |- ( t : A ) ; Delta" 
  (at level 70, A at next level, t at next level).
Reserved Notation "Gamma ; ( e : A ) |- Delta" 
  (at level 70, A at next level, e at next level).

(** The LK-mu-mu-tilde sequent calculus with cofinite quantification *)
Inductive proof_cmd : cmd -> cxt_trm -> cxt_ect -> Set :=
| Cut v e Gamma Delta A :
  proof_trm Gamma v A Delta ->
  proof_ect Gamma e A Delta ->
  proof_cmd (cm v e) Gamma Delta

where "c : ( Gamma |- Delta )" := (proof_cmd c Gamma Delta)

with proof_trm : cxt_trm -> trm -> typ -> cxt_ect -> Set :=
| AxR Gamma a A Delta : 
  In (a,A) Gamma -> 
  proof_trm Gamma (tvar a) A Delta

| Mu Gamma alpha c A Delta :
  proof_cmd c Gamma ((alpha,A)::Delta) ->
  proof_trm Gamma (mu alpha c) A Delta

| ImpR Gamma a t A B Delta :
  proof_trm ((a,A)::Gamma) t B Delta ->
  proof_trm Gamma (lam a t) (Imp A B) Delta

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

| AllR Gamma t A Delta L :
  locl (All A) ->
  (forall x, x \notin L -> proof_trm Gamma t (A^x) Delta) ->
  proof_trm Gamma (tall t) (All A) Delta

| ExR Gamma t A Delta d : locli d ->
  proof_trm Gamma t (A^^d) Delta ->
  proof_trm Gamma (tex t) (Ex A) Delta

where "Gamma |- ( t : A ) ; Delta" := (proof_trm Gamma t A Delta)
  
with proof_ect : cxt_trm -> ect -> typ -> cxt_ect -> Set :=
| AxL Gamma alpha A Delta :
  In (alpha,A) Delta ->
  proof_ect Gamma (evar alpha) A Delta

| MuT Gamma a c A Delta :
  proof_cmd c ((a,A)::Gamma) Delta ->
  proof_ect Gamma (mut a c) A Delta

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

| AllL Gamma e A Delta d : locli d ->
  proof_ect Gamma e (A^^d) Delta ->
  proof_ect Gamma (eall e) (All A) Delta

| ExL Gamma e A Delta L :
  locl (Ex A) ->
  (forall x, x \notin L -> proof_ect Gamma e (A^x) Delta) ->
  proof_ect Gamma (eex e) (Ex A) Delta

where "Gamma ; ( e : A ) |- Delta" := (proof_ect Gamma e A Delta)
.

(* (* Combined Scheme only works for sort Prop, so I have to give the *) *)
(* (*    definition by hand by adapting a copy-paste of the Prop version: *) *)
(* Scheme proof_cmd_rect' := Induction for proof_cmd Sort Prop *)
(* with proof_trm_rect' := Induction for proof_trm Sort Prop *)
(* with proof_ect_rect' := Induction for proof_ect Sort Prop. *)
(* Combined Scheme proof_rect'' from proof_cmd_rect', proof_trm_rect', *)
(*   proof_ect_rect'. *)
(* Unset Printing Notations. *)
(* Print proof_rect''. *)
(* Set Printing Notations. *)

Scheme proof_cmd_rect' := Induction for proof_cmd Sort Type
with proof_trm_rect' := Induction for proof_trm Sort Type
with proof_ect_rect' := Induction for proof_ect Sort Type.

(** We have to make the mutual-induction predicate "by hand" since the Combined Scheme Coq command works only in sort Prop, not in Type. *)
Definition proof_rect' := fun
  (P : forall (c : cmd) (c0 : cxt_trm) (c1 : cxt_ect),
       proof_cmd c c0 c1 -> Type)
  (P0 : forall (c : cxt_trm) (t : trm) (t0 : typ) (c0 : cxt_ect),
        proof_trm c t t0 c0 -> Type)
  (P1 : forall (c : cxt_trm) (e : ect) (t : typ) (c0 : cxt_ect),
        proof_ect c e t c0 -> Type)
  (f : forall (v : trm) (e : ect) (Gamma : cxt_trm) 
         (Delta : cxt_ect) (A : typ) (p : proof_trm Gamma v A Delta),
       P0 Gamma v A Delta p ->
       forall p0 : proof_ect Gamma e A Delta,
       P1 Gamma e A Delta p0 -> P (cm v e) Gamma Delta (Cut p p0))
  (f0 : forall (Gamma : list (prod var_trm typ)) (a : var_trm) 
          (A : typ) (Delta : cxt_ect) (i : In (pair a A) Gamma),
        P0 Gamma (tvar a) A Delta (AxR (Gamma:=Gamma) (a:=a) (A:=A) Delta i))
  (f1 : forall (Gamma : cxt_trm) (alpha : var_ect) 
          (c : cmd) (A : typ) (Delta : list (prod var_ect typ))
          (p : proof_cmd c Gamma (cons (pair alpha A) Delta)),
        P c Gamma (cons (pair alpha A) Delta) p ->
        P0 Gamma (mu alpha c) A Delta (Mu p))
  (f2 : forall (Gamma : list (prod var_trm typ)) (a : var_trm) 
          (t : trm) (A B : typ) (Delta : cxt_ect)
          (p : proof_trm (cons (pair a A) Gamma) t B Delta),
        P0 (cons (pair a A) Gamma) t B Delta p ->
        P0 Gamma (lam a t) (Imp A B) Delta (ImpR p))
  (f3 : forall (Gamma : cxt_trm) (v : trm) (A1 A2 : typ) 
          (Delta : cxt_ect) (p : proof_trm Gamma v A1 Delta),
        P0 Gamma v A1 Delta p ->
        P0 Gamma (injl v) (Disj A1 A2) Delta (DisjRL A2 p))
  (f4 : forall (Gamma : cxt_trm) (v : trm) (A1 A2 : typ) 
          (Delta : cxt_ect) (p : proof_trm Gamma v A2 Delta),
        P0 Gamma v A2 Delta p ->
        P0 Gamma (injr v) (Disj A1 A2) Delta (DisjRR A1 p))
  (f5 : forall (Gamma : cxt_trm) (v1 v2 : trm) (A1 A2 : typ)
          (Delta : cxt_ect) (p : proof_trm Gamma v1 A1 Delta),
        P0 Gamma v1 A1 Delta p ->
        forall p0 : proof_trm Gamma v2 A2 Delta,
        P0 Gamma v2 A2 Delta p0 ->
        P0 Gamma (paire v1 v2) (Conj A1 A2) Delta (ConjR p p0))
  (f6 : forall (Gamma : cxt_trm) (t : trm) (A : typ) 
          (Delta : cxt_ect) (L : list var_free) (l : locl (All A))
          (p : forall x : var_free,
               (In x L -> Empty_set) ->
               proof_trm Gamma t (subst O A (fvar x)) Delta),
        (forall (x : var_free) (e : In x L -> Empty_set),
         P0 Gamma t (subst O A (fvar x)) Delta (p x e)) ->
        P0 Gamma (tall t) (All A) Delta (AllR (A:=A) (L:=L) l p))
  (f7 : forall (Gamma : cxt_trm) (t : trm) (A : typ) 
          (Delta : cxt_ect) (d : indiv) (l : locli d)
          (p : proof_trm Gamma t (subst O A d) Delta),
        P0 Gamma t (subst O A d) Delta p ->
        P0 Gamma (tex t) (Ex A) Delta (ExR (A:=A) (d:=d) l p))
  (f8 : forall (Gamma : cxt_trm) (alpha : var_ect) 
          (A : typ) (Delta : list (prod var_ect typ))
          (i : In (pair alpha A) Delta),
        P1 Gamma (evar alpha) A Delta
          (AxL Gamma (alpha:=alpha) (A:=A) (Delta:=Delta) i))
  (f9 : forall (Gamma : list (prod var_trm typ)) (a : var_trm) 
          (c : cmd) (A : typ) (Delta : cxt_ect)
          (p : proof_cmd c (cons (pair a A) Gamma) Delta),
        P c (cons (pair a A) Gamma) Delta p ->
        P1 Gamma (mut a c) A Delta (MuT p))
  (f10 : forall (Gamma : cxt_trm) (v : trm) (e : ect) 
           (A B : typ) (Delta : cxt_ect) (p : proof_trm Gamma v A Delta),
         P0 Gamma v A Delta p ->
         forall p0 : proof_ect Gamma e B Delta,
         P1 Gamma e B Delta p0 ->
         P1 Gamma (app v e) (Imp A B) Delta (ImpL p p0))
  (f11 : forall (Gamma : cxt_trm) (e1 e2 : ect) (A1 A2 : typ)
           (Delta : cxt_ect) (p : proof_ect Gamma e1 A1 Delta),
         P1 Gamma e1 A1 Delta p ->
         forall p0 : proof_ect Gamma e2 A2 Delta,
         P1 Gamma e2 A2 Delta p0 ->
         P1 Gamma (disj e1 e2) (Disj A1 A2) Delta (DisjL p p0))
  (f12 : forall (Gamma : cxt_trm) (e : ect) (A1 A2 : typ) 
           (Delta : cxt_ect) (p : proof_ect Gamma e A1 Delta),
         P1 Gamma e A1 Delta p ->
         P1 Gamma (projl e) (Conj A1 A2) Delta (ConjLL A2 p))
  (f13 : forall (Gamma : cxt_trm) (e : ect) (A1 A2 : typ) 
           (Delta : cxt_ect) (p : proof_ect Gamma e A2 Delta),
         P1 Gamma e A2 Delta p ->
         P1 Gamma (projr e) (Conj A1 A2) Delta (ConjLR A1 p))
  (f14 : forall (Gamma : cxt_trm) (e : ect) (A : typ) 
           (Delta : cxt_ect) (d : indiv) (l : locli d)
           (p : proof_ect Gamma e (subst O A d) Delta),
         P1 Gamma e (subst O A d) Delta p ->
         P1 Gamma (eall e) (All A) Delta (AllL (A:=A) (d:=d) l p))
  (f15 : forall (Gamma : cxt_trm) (e : ect) (A : typ) 
           (Delta : cxt_ect) (L : list var_free) (l : locl (Ex A))
           (p : forall x : var_free,
                (In x L -> Empty_set) ->
                proof_ect Gamma e (subst O A (fvar x)) Delta),
         (forall (x : var_free) (e0 : In x L -> Empty_set),
          P1 Gamma e (subst O A (fvar x)) Delta (p x e0)) ->
         P1 Gamma (eex e) (Ex A) Delta (ExL (A:=A) (L:=L) l p)) =>
  pair 
  (pair 
    (proof_cmd_rect' (P:=P) (P0:=P0) (P1:=P1) f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
      f10 f11 f12 f13 f14 f15)
    (proof_trm_rect' (P:=P) (P0:=P0) (P1:=P1) f f0 f1 f2 f3 f4 f5 f6 f7 f8
      f9 f10 f11 f12 f13 f14 f15))
  (proof_ect_rect' (P:=P) (P0:=P0) (P1:=P1) f f0 f1 f2 f3 f4 f5 f6 f7 f8
    f9 f10 f11 f12 f13 f14 f15).

Section Abstract_Semantics.
  (** An abstract Kripke-style structure: [wle] is the preorder, [X] is
     the exploding-world predicate, [aforces] is strong forcing of
     atomic formulae. *)
  Record Kripke : Type := {
    world :> Set;
    wle : world -> world -> Type;
    wle_refl : forall w, wle w w;
    wle_trans : forall w w' w'', wle w w' -> wle w' w'' -> wle w w'';
    exploding : world -> Set;
    aforces : world -> predicate -> list indiv -> Set;
    aforces_mon : forall w P ld, @aforces w P ld -> 
      forall w', wle w w' -> @aforces w' P ld
  }.
  Notation "w <= w'" := (wle w w').

  Variable K:Kripke.

  (** The continuations monad we will use to extend forcing to
     composite formulas *)
  Definition Kont (F:K->typ->Type)(w:K)(A:typ) := 
    forall w1, w <= w1 -> 
      (forall w2, w1 <= w2 -> F w2 A -> exploding w2) -> exploding w1.
  Hint Unfold Kont.

  (** Strong forcing extended to composite formulas. The expression
     [sforces w A] stands for strong forcing, while [Kont sforces w A]
     stands for (weak) forcing of A in the world w. *)
  Fixpoint sforces' (n:nat)(w:K)(A:typ) {struct n} : Type :=
    match n with
      | O => Empty_set
      | S m => 
        match A with
          | Atom P ld  => aforces w P ld
          | Imp A1 A2  => forall w', w <= w'-> Kont (sforces' m) w' A1 -> Kont (sforces' m) w' A2
          | Disj A1 A2 => Kont (sforces' m) w A1 + Kont (sforces' m) w A2
          | Conj A1 A2 => Kont (sforces' m) w A1 * Kont (sforces' m) w A2
          | All A1     => forall w', w <= w' -> forall d, locli d -> Kont (sforces' m) w' (A1^^d)
          | Ex A1      => sigT (fun d => (locli d) * Kont (sforces' m) w (A1^^d))
        end
    end.

  Fixpoint depth (A:typ) : nat :=
    match A with
      | Atom _ _   => 1
      | Imp A1 A2  => S (max (depth A1) (depth A2))
      | Disj A1 A2 => S (max (depth A1) (depth A2))
      | Conj A1 A2 => S (max (depth A1) (depth A2))
      | All A1     => S (depth A1)
      | Ex A1      => S (depth A1)
    end.

  (** However, we can not define strong forcing as simply as when we had no quantifiers, because we need to do a recursion on the _complexity_ of a formula, not just its structure; we do that using the measure of [depth] above. *)
  Definition sforces (w:K)(A:typ) := sforces' (depth A) w A.
  Hint Unfold sforces.

  (** And now this section proves that the definition using the measure is correct *)
  Section sforces_correctness.
    Lemma depth_subst : forall A d k, depth (subst k A d) = depth A.
    Proof.
      induction A; simpl; intros.
      
      reflexivity.
      
      rewrite <- IHA1 with d k.
      rewrite <- IHA2 with d k.
      reflexivity.
      
      rewrite <- IHA1 with d k.
      rewrite <- IHA2 with d k.
      reflexivity.
      
      rewrite <- IHA1 with d k.
      rewrite <- IHA2 with d k.
      reflexivity.
      
      rewrite <- IHA with d (S k).
      reflexivity.

      rewrite <- IHA with d (S k).
      reflexivity.
    Defined.

    Lemma sforces'_S : forall n A w, le (depth A) n -> 
      (sforces' n w A <-> sforces' (S n) w A).
    Proof.
      induction n;
        intros A w Hle.

      inversion Hle.
      destruct A;
        inversion H0.

      split.

    (* Direction ==> *)
      intro H.
      simpl in H.
      hnf.
      assert (IHn1 := fun A w Hle => fst (IHn A w Hle)).
      assert (IHn2 := fun A w Hle => snd (IHn A w Hle)).
      clear IHn.
      destruct A.

      assumption.

      intros w' ww' HKA1Sn.
      intros w1 w'w1 k.
      apply H with w'.
      assumption.
      intros w2 w1w2 HA1n.
      apply HKA1Sn.
      assumption.
      intros w3 w2w3 HA1Sn.
      apply HA1n.
      assumption.
      apply IHn2.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_l.
      apply Hle.
      assumption.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn1.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_r.
      apply Hle.
      assumption.

      case H; intro H'.
      left.
      intros w1 ww1 k.
      apply H'.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn1; auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_l.
      apply Hle.
      right.
      intros w1 ww1 k.
      apply H'.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn1; auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_r.
      apply Hle.

      destruct H as [H1 H2].
      split.
      intros w1 ww1 k.
      apply H1.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn1;auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_l.
      apply Hle.
      intros w1 ww1 k.
      apply H2.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn1;auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_r.
      apply Hle.

      intros.
      intros w1 w'w1 k.
      apply H with w1 d.
      eauto using wle_trans.
      assumption.
      apply wle_refl.
      intros w2 w1w2 HA.
      apply k.
      assumption.
      apply IHn1;auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      rewrite depth_subst.
      assumption.

      destruct H as [d [H1 H2]].
      exists d.
      split; [assumption | ].
      intros w1 ww1 k.
      apply H2.
      assumption.
      intros w2 w1w2 H3.
      apply k.
      assumption.
      apply IHn1;auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      rewrite depth_subst.
      assumption.


    (* Direction <== (exact copy-past of the other direction except for
       swapping IHn1 <~> IHn2) *)
      intro H.
      simpl.
      hnf in H.
      assert (IHn1 := fun A w Hle => fst (IHn A w Hle)).
      assert (IHn2 := fun A w Hle => snd (IHn A w Hle)).
      clear IHn.
      destruct A.

      assumption.

      intros w' ww' HKA1Sn.
      intros w1 w'w1 k.
      apply H with w'.
      assumption.
      intros w2 w1w2 HA1n.
      apply HKA1Sn.
      assumption.
      intros w3 w2w3 HA1Sn.
      apply HA1n.
      assumption.
      apply IHn1.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_l.
      apply Hle.
      assumption.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn2.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_r.
      apply Hle.
      assumption.

      case H; intro H'.
      left.
      intros w1 ww1 k.
      apply H'.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn2; auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_l.
      apply Hle.
      right.
      intros w1 ww1 k.
      apply H'.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn2; auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_r.
      apply Hle.

      destruct H as [H1 H2].
      split.
      intros w1 ww1 k.
      apply H1.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn2;auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_l.
      apply Hle.
      intros w1 ww1 k.
      apply H2.
      assumption.
      intros.
      apply k.
      assumption.
      apply IHn2;auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      eapply le_trans.
      apply le_max_r.
      apply Hle.

      intros.
      intros w1 w'w1 k.
      apply H with w1 d.
      eauto using wle_trans.
      assumption.
      apply wle_refl.
      intros w2 w1w2 HA.
      apply k.
      assumption.
      apply IHn2;auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      rewrite depth_subst.
      assumption.

      destruct H as [d [H1 H2]].
      exists d.
      split; [assumption | ].
      intros w1 ww1 k.
      apply H2.
      assumption.
      intros w2 w1w2 H3.
      apply k.
      assumption.
      apply IHn2;auto.
      clear -Hle.
      simpl in *.
      apply le_S_n in Hle.
      rewrite depth_subst.
      assumption.
    Defined.

    Definition sforces'_S1 := fun n A w Hle => fst (@sforces'_S n A w Hle).
    Definition sforces'_S2 := fun n A w Hle => snd (@sforces'_S n A w Hle).

    Lemma sforces'_mon1 : forall n m, le n m -> 
      forall A, le (depth A) n -> forall w, sforces' n w A -> sforces' m w A.
    Proof.
      intros n m Hle.
      induction Hle.

      intros.
      auto.

      intros.
      apply sforces'_S1.
      eauto using le_trans.
      auto.
    Defined.

    Lemma sforces'_mon2 : forall n m, le n m -> 
      forall A, le (depth A) n -> forall w, sforces' m w A -> sforces' n w A.
    Proof.
      intros n m Hle.
      induction Hle.

      intros.
      auto.

      intros.
      apply IHHle.
      assumption.
      apply sforces'_S2.
      eauto using le_trans.
      assumption.
    Defined.

    Lemma Kont_invar : forall F1 F2:K->typ->Type, forall A,
      (forall w, F1 w A -> F2 w A) -> forall w, Kont F1 w A -> Kont F2 w A.
    Proof.
      intros F1 F2 A HF1F2.
      intros w HF1.
      intros w1 ww1 k1.
      apply HF1.
      assumption.
      intros w2 w1w2 HF1'.
      apply k1.
      assumption.
      auto.
    Defined.

    Lemma sforces_correct_Atom : forall w P ld,
      sforces w (@Atom P ld) -> aforces w P ld.
    Proof.
      unfold sforces.
      simpl.
      auto.
    Defined.

    Lemma sforces_correct_Atom' : forall w P ld,
      aforces w P ld -> sforces w (@Atom P ld).
    Proof.
      unfold sforces.
      simpl.
      auto.
    Defined.

    Lemma sforces_correct_Disj : forall w A B, sforces w (Disj A B) -> 
      Kont sforces w A + Kont sforces w B.
    Proof.
      intros w A B H.
      unfold sforces in H.
      simpl in H.
      destruct H.

      left.
      change (Kont (sforces' (depth A)) w A).
      generalize dependent k.
      apply Kont_invar.
      intros w'.
      apply sforces'_mon2.
      apply le_max_l.
      constructor.

      right.
      change (Kont (sforces' (depth B)) w B).
      generalize dependent k.
      apply Kont_invar.
      intros w'.
      apply sforces'_mon2.
      apply le_max_r.
      constructor.
    Defined.

    Lemma sforces_correct_Disj' : forall w A B, 
      Kont sforces w A + Kont sforces w B -> sforces w (Disj A B).
    Proof.
      intros w A B H.
      unfold sforces.
      simpl.
      destruct H.

      left.
      generalize dependent k.
      apply Kont_invar.
      intros w'.
      apply sforces'_mon1.
      apply le_max_l.
      constructor.

      right.
      generalize dependent k.
      apply Kont_invar.
      intros w'.
      apply sforces'_mon1.
      apply le_max_r.
      constructor.
    Defined.

    Lemma sforces_correct_Conj : forall w A B, sforces w (Conj A B) -> 
      Kont sforces w A * Kont sforces w B.
    Proof.
      intros w A B H.
      unfold sforces in H.
      simpl in H.
      destruct H as [H1 H2].
      split.

      change (Kont (sforces' (depth A)) w A).
      generalize dependent H1.
      apply Kont_invar.
      intros w'.
      apply sforces'_mon2.
      apply le_max_l.
      constructor.

      change (Kont (sforces' (depth B)) w B).
      generalize dependent H2.
      apply Kont_invar.
      intros w'.
      apply sforces'_mon2.
      apply le_max_r.
      constructor.
    Defined.

    Lemma sforces_correct_Conj' : forall w A B,  
      Kont sforces w A * Kont sforces w B -> sforces w (Conj A B).
    Proof.
      intros w A B H.
      unfold sforces.
      simpl.
      destruct H as [H1 H2].
      split.

      generalize dependent H1.
      apply Kont_invar.
      intros w'.
      apply sforces'_mon1.
      apply le_max_l.
      constructor.

      generalize dependent H2.
      apply Kont_invar.
      intros w'.
      apply sforces'_mon1.
      apply le_max_r.
      constructor.
    Defined.

    Lemma sforces_correct_Imp : forall w A B, sforces w (Imp A B) -> 
      forall w', w <= w' -> Kont sforces w' A -> Kont sforces w' B.
    Proof.
      intros w A B H.
      unfold sforces in H.
      simpl in H.
      intros w' ww' HA.

      change (Kont (sforces' (depth A)) w' A) in HA.
      change (Kont (sforces' (depth B)) w' B).

      apply Kont_invar with (sforces' (max (depth A) (depth B))).
      apply sforces'_mon2.
      apply le_max_r.
      constructor.
      apply H.
      assumption.
      generalize dependent HA.
      apply Kont_invar.
      apply sforces'_mon1.
      apply le_max_l.
      constructor.
    Defined.

    Lemma sforces_correct_Imp' : forall w A B,  
      (forall w', w <= w' -> Kont sforces w' A -> Kont sforces w' B)
        -> sforces w (Imp A B).
    Proof.
      intros w A B H.
      unfold sforces.
      simpl.
      intros w' ww' HA.

      apply Kont_invar with (sforces' (depth B)).
      intros w''.
      apply sforces'_mon1.
      apply le_max_r.
      constructor.
      apply H.
      assumption.
      generalize dependent HA.
      apply Kont_invar.
      intros w''.
      apply sforces'_mon2.
      apply le_max_l.
      constructor.
    Defined.

    Lemma sforces_correct_All : forall w A, sforces w (All A) -> 
      forall w', w <= w' -> forall d, locli d -> Kont sforces w' (A^^d).
    Proof.
      intros w A H.
      unfold sforces in H.
      simpl in H.
      intros w' ww' d Hd.

      change (Kont (sforces' (depth (A^^d))) w' (A^^d)).
      assert (H' := H w' ww' d Hd).
      generalize dependent H'.
      apply Kont_invar.
      apply sforces'_mon2.
      rewrite depth_subst.
      constructor.
      constructor.
    Defined.

    Lemma sforces_correct_All' : forall w A, 
      (forall w', w <= w' -> forall d, locli d -> Kont sforces w' (A^^d))
      -> sforces w (All A).
    Proof.
      intros w A H.
      unfold sforces.
      simpl.
      intros w' ww' d Hd.
      rewrite <- depth_subst with A d 0.
      apply H.
      assumption.
      assumption.
    Defined.

    Lemma sforces_correct_Ex : forall w A, sforces w (Ex A) -> 
      sigT (fun d => (locli d) * Kont sforces w (A^^d)).
    Proof.
      intros w A H.
      unfold sforces in H.
      simpl in H.
      destruct H as [d [Hd H]].

      exists d.
      split; [assumption|].
      change (Kont (sforces' (depth (A^^d))) w (A^^d)).
      generalize dependent H.
      apply Kont_invar.
      apply sforces'_mon2.
      rewrite depth_subst.
      constructor.
      constructor.
    Defined.

    Lemma sforces_correct_Ex' : forall w A, 
      (sigT (fun d => (locli d) * Kont sforces w (A^^d)))
      -> sforces w (Ex A).
    Proof.
      intros w A H.
      unfold sforces.
      simpl.
      destruct H as [d [Hd H]].
      exists d.
      split; [assumption|].
      rewrite <- depth_subst with A d 0.
      apply H.
    Defined.
  End sforces_correctness.

  Definition refutes (w1:K)(A:typ) :=
      forall w2:K, w1 <= w2 -> sforces w2 A -> exploding w2.

  Notation "w : ||+ A " := (sforces w A) (at level 70).
  Notation "w : A ||- " := (refutes w A)  (at level 70).
  Notation "w : ||- A " := (Kont sforces w A) (at level 70).

  Fixpoint refutes_cxt (w:K)(Delta:cxt_ect) : Type :=
    match Delta with
      | nil => unit
      | cons aA Delta' => (refutes w (snd aA)) * (refutes_cxt w Delta')
    end.

  Fixpoint forces_cxt (w:K)(Gamma:cxt_trm) : Type :=
    match Gamma with
      | nil => unit
      | cons aA Gamma' => (w : ||- (snd aA)) * (forces_cxt w Gamma')
    end.

  Notation " w : ||-- Gamma" := (forces_cxt w Gamma) (at level 70).
  Notation " w : Delta ||-- "  := (refutes_cxt w Delta) (at level 70).

  Lemma sforces_mon : forall A w, w : ||+ A  -> forall w', w <= w' -> w' : ||+ A .
  Proof.
    induction A.

    unfold sforces.
    simpl.
    intros.
    eauto using aforces_mon.
    
    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    eauto using wle_trans.
    
    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    case H1; intro H'.
    left.
    eauto using wle_trans.
    eauto using wle_trans.
    
    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    destruct H1; split; eauto using wle_trans.

    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    eauto using wle_trans.

    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    destruct H1 as [d [Hd H]].
    exists d.
    split; [assumption|].
    intros w1 w'w1 k.
    apply H.
    eauto using wle_trans.
    intros w2 w1w2 H2.
    auto.
  Defined.

  Definition ret {w A} : w : ||+ A -> w : ||- A.
  Proof.
    intros H.
    intros w1 w_w1 k.
    apply k.
    apply wle_refl.
    apply sforces_mon with w.
    assumption.
    assumption.
  Defined.

  Lemma refutes_mon : forall A w, w : A ||- -> forall w', w <= w' -> w' : A ||- .
  Proof.
    induction A;
      intros;
        unfold refutes in *;
          eauto using wle_trans.
  Defined.

  Lemma forces_mon : forall A w, w : ||- A -> forall w', w <= w' -> w' : ||- A.
  Proof.
    induction A;
      intros;
        eauto using wle_trans.
  Defined.

  Lemma refutes_cxt_mon : 
    forall Delta w, w : Delta ||-- -> forall w', w <= w' -> w' : Delta ||-- .
  Proof.
    induction Delta.
    simpl.
    auto.
    simpl.
    intros.
    destruct X.
    split; eauto using wle_trans,refutes_mon.
  Defined.

  Lemma forces_cxt_mon : 
    forall Gamma w, w : ||-- Gamma -> forall w', w <= w' -> w' : ||-- Gamma.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros.
    destruct X.
    split; eauto using wle_trans,forces_mon.
  Defined.

  Lemma refutes_cxt_In : forall w alpha A Delta, 
    In (alpha, A) Delta -> w : Delta ||-- -> w : A ||- .
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

  Lemma forces_cxt_In : forall w x A Gamma, 
    In (x, A) Gamma -> w : ||-- Gamma -> w : ||- A.
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

  Theorem soundness : 
    (forall c Gamma Delta, c:(Gamma|-Delta) -> 
      forall w, w : ||-- Gamma -> w : Delta ||-- -> exploding w) *
    
    (forall Gamma t A Delta, Gamma|-(t:A);Delta -> 
      forall w, w : ||-- Gamma -> w : Delta ||-- -> w : ||- A) *
    
    (forall Gamma e A Delta, Gamma;(e:A)|-Delta -> 
      forall w, w : ||-- Gamma -> w : Delta ||-- -> w : A ||- ).
  Proof.
    apply proof_rect'.

    (* Cut *)
    intros v e Gamma Delta A _ IH1 _ IH2.
    intros w HGamma HDelta.
    apply IH1 with w; auto.
    apply wle_refl.
    apply IH2; assumption.

    (* AxR *)
    intros.
    eauto using forces_cxt_In.

    (* Mu *)
    intros Gamma alpha c A Delta _ IH1 w H H0.
    intros w' ww' H1.
    apply IH1.
    eauto using forces_cxt_mon,wle_trans.
    simpl.
    eauto using refutes_cxt_mon,refutes_mon.

    (* ImpR *)
    intros.
    apply ret.
    apply sforces_correct_Imp'.
    simpl in *.
    eauto using refutes_cxt_mon,forces_cxt_mon.
  
    (* DisjRL *)
    intros.
    apply ret.
    apply sforces_correct_Disj'.
    eauto using refutes_cxt_mon,forces_cxt_mon.

    (* DisjRR *)
    intros.
    apply ret.
    apply sforces_correct_Disj'.
    eauto using refutes_cxt_mon,forces_cxt_mon.

    (* ConjR *)
    intros.
    apply ret.
    apply sforces_correct_Conj'.
    split;
      eauto using refutes_cxt_mon,forces_cxt_mon.

    (* AllR *)
    intros.
    apply ret.
    apply sforces_correct_All'.
    admit.

    (* ExR *)
    intros.
    apply ret.
    apply sforces_correct_Ex'.
    exists d.
    split; [assumption|].
    auto.

    (* Ax_L *)
    intros.
    eauto using refutes_cxt_In.

    (* MuT *)
    intros Gamma a c A Delta _ IH1.
    intros w H H0.
    intros w' ww' HA.
    apply IH1.
    simpl; split.
    apply ret; assumption.
    eauto using refutes_cxt_mon,forces_cxt_mon.
    eauto using refutes_cxt_mon,forces_cxt_mon.

    (* ImpL *)
    intros Gamma v e A B Delta _ IH1 _ IH2 w HGamma HDelta.
    intros w' ww' H.
    eapply sforces_correct_Imp in H.
    apply H.
    apply wle_refl.
    apply IH2;
      eauto using refutes_cxt_mon,forces_cxt_mon.
    apply wle_refl.
    eauto using forces_mon,refutes_cxt_mon,forces_cxt_mon.

    (* DisjL *)
    intros Gamma e1 e2 A1 A2 Delta _ IH1 _ IH2.
    intros w H H0.
    intros w' ww' HDisj.
    apply sforces_correct_Disj in HDisj.
    case HDisj; intro Hcase.
    apply Hcase.
    apply wle_refl.
    apply IH1; eauto using refutes_cxt_mon,forces_cxt_mon.
    apply Hcase.
    apply wle_refl.
    apply IH2; eauto using refutes_cxt_mon,forces_cxt_mon.

    (* ConjLL *)
    intros Gamma e A1 A2 Delta _ IH w H H0.
    intros w' H1 H2.
    apply sforces_correct_Conj in H2.
    destruct H2 as [H2 _].
    apply H2.
    apply wle_refl.
    apply IH; eauto using refutes_cxt_mon,forces_cxt_mon.

    (* ConjLR *)
    intros Gamma e A1 A2 Delta _ IH w H H0.
    intros w' H1 H2.
    apply sforces_correct_Conj in H2.
    destruct H2 as [_ H2].
    apply H2.
    apply wle_refl.
    apply IH; eauto using refutes_cxt_mon,forces_cxt_mon.

    (* AllL *)
    intros Gamma e A1 A2 d Hd _ IH w H H0.
    intros w' H1 H2.
    eapply sforces_correct_All in H2.
    apply H2.
    apply wle_refl.
    apply IH; eauto using refutes_cxt_mon,forces_cxt_mon.
    apply wle_refl.
    assumption.

    (* ExL *)
    intros Gamma e A Delta L Hlocl _ IH w H H0.
    intros w' H1 H2.
    admit.
  Defined.
End Abstract_Semantics.

(** Various lemmas that have to do with substitutions related to quantifier bound variables; this was the hardest part of the formalisation. *)
Section subst_lemmas.

  Lemma locli_fvar : forall x, locli (fvar x).
  Proof.
    unfold locli.
    simpl.
    reflexivity.
  Defined.

  Lemma func_wrapper1 : forall f l l', func f l = func f l' -> l = l'.
  Proof.
    intros.
    congruence.
  Defined.

  Lemma func_wrapper2 : forall f l l', l = l' -> func f l = func f l'.
  Proof.
    intros.
    congruence.
  Defined.

  Lemma Atom_wrapper1 : forall f l l', Atom f l = Atom f l' -> l = l'.
  Proof.
    intros.
    congruence.
  Defined.

  Lemma Atom_wrapper2 : forall p l l', l = l' -> Atom p l = Atom p l'.
  Proof.
    intros.
    congruence.
  Defined.

  Lemma cons_eqs : forall T a a' l l', @cons T a l = @cons T a' l' -> 
    (a=a') * (l=l').
  Proof.
    intros.
    inversion H.
    auto.
  Defined.

  Lemma eqs_cons : forall T a a' l l', 
    (a=a') * (l=l') -> @cons T a l = @cons T a' l'.
  Proof.
    intros.
    destruct H.
    rewrite e.
    rewrite e0.
    auto.
  Defined.

  Lemma subst_indiv_zero_twice : forall a d d' n', locli d ->
    subst_indiv n' (subst_indiv n' a d) d' = subst_indiv n' a d.
  Proof.
    fix 1.
    intro a.
    destruct a.

    intros.
    simpl.
    assert (H' := beq_nat_false n' n).
    destruct beq_nat.
    apply H.
    simpl.
    assert (H'' := beq_nat_true n' n).
    destruct beq_nat.
    assert (False).
    apply H'.
    reflexivity.
    apply H''.
    reflexivity.
    intuition.
    reflexivity.

    simpl.
    reflexivity.

    simpl.
    intros.
    apply func_wrapper2.
    induction l.
    reflexivity.
    apply eqs_cons.
    split.
    apply subst_indiv_zero_twice.
    assumption.

    apply IHl.
  Defined.

  Lemma locli_locli_subst : forall a m k d c, 
    (forall k c, subst_indiv (S (k+m)) a c = a) ->
      (forall k c, subst_indiv (k+m) d c = d) ->
        subst_indiv (k+m) (subst_indiv m a d) c = subst_indiv m a d.
  Proof.
    fix 1.
    destruct a.

    intros.
    simpl.
    remember (beq_nat m n).
    destruct b.
    apply H0.
    destruct k.
    simpl.
    rewrite <- Heqb.
    reflexivity.
    rewrite plus_Sn_m.
    apply H.

    simpl.
    reflexivity.

    intros.
    simpl.
    simpl in H.
    apply func_wrapper2.
    assert (H' := fun k d => func_wrapper1 (H k d)).
    clear H.
    induction l.
    reflexivity.
    apply eqs_cons.
    assert (H1 := fun k d => fst (cons_eqs (H' k d))).
    assert (H2 := fun k d => snd (cons_eqs (H' k d))).
    clear H'.
    split.
    rewrite locli_locli_subst.
    reflexivity.
    apply H1.
    assumption.
    apply IHl.
    apply H2.
  Defined.

  Lemma locl_locli_subst : forall A m, 
    (forall k d, subst (S (k + m)) A d = A) ->
    forall d, 
      (forall k d0, subst_indiv (k + m) d d0 = d) ->
      forall k' d', 
        subst (k'+m) (subst m A d) d' = subst m A d.
  Proof.
    fix 1.
    intros.
    rename H into H'.
    destruct A.

    simpl in *.
    apply Atom_wrapper2.
    assert (H'' := fun k d => Atom_wrapper1 (H' k d)).
    clear H'.
    induction l.
    reflexivity.
    assert (H1 := fun k d => fst (cons_eqs (H'' k d))).
    assert (H2 := fun k d => snd (cons_eqs (H'' k d))).
    clear H''.
    apply eqs_cons.
    split.
    rewrite locli_locli_subst.
    reflexivity.
    apply H1.
    apply H0.
    apply IHl.
    apply H2.

    simpl in *.
    rewrite locl_locli_subst.
    rewrite locl_locli_subst.
    reflexivity.
    unfold locl.
    simpl.
    intros.
    assert (H'' := H' k d0).
    congruence.
    assumption.
    unfold locl.
    simpl.
    intros.
    assert (H'' := H' k d0).
    congruence.
    assumption.

    simpl in *.
    rewrite locl_locli_subst.
    rewrite locl_locli_subst.
    reflexivity.
    unfold locl.
    simpl.
    intros.
    assert (H'' := H' k d0).
    congruence.
    assumption.
    unfold locl.
    simpl.
    intros.
    assert (H'' := H' k d0).
    congruence.
    assumption.

    simpl in *.
    rewrite locl_locli_subst.
    rewrite locl_locli_subst.
    reflexivity.
    unfold locl.
    simpl.
    intros.
    assert (H'' := H' k d0).
    congruence.
    assumption.
    unfold locl.
    simpl.
    intros.
    assert (H'' := H' k d0).
    congruence.
    assumption.

    simpl in *.
    rewrite plus_n_Sm.
    rewrite locl_locli_subst.
    reflexivity.
    intros.
    assert (H'' := H' k d0).
    rewrite <- plus_n_Sm.
    congruence.
    intros.
    rewrite <- Arith.Plus.plus_Snm_nSm.
    apply H0.

    simpl in *.
    rewrite plus_n_Sm.
    rewrite locl_locli_subst.
    reflexivity.
    intros.
    assert (H'' := H' k d0).
    rewrite <- plus_n_Sm.
    congruence.
    intros.
    rewrite <- Arith.Plus.plus_Snm_nSm.
    apply H0.
  Defined.

  Lemma locl_locli_subst' : forall A, locl (All A) ->
    forall d, locli d -> locl (A^^d).
  Proof.
    unfold locl,locli.
    simpl.
    intros.
    replace k with (plus k 0).
    apply locl_locli_subst.
    intros.
    assert (H' := H (plus k0 0) d1).
    congruence.
    intros.
    apply H0.
    apply Arith.Plus.plus_0_r.
  Defined.

  Lemma locl_locli_subst'' : forall A, locl (Ex A) ->
    forall d, locli d -> locl (A^^d).
  Proof.
    unfold locl,locli.
    simpl.
    intros.
    replace k with (plus k 0).
    apply locl_locli_subst.
    intros.
    assert (H' := H (plus k0 0) d1).
    congruence.
    intros.
    apply H0.
    apply Arith.Plus.plus_0_r.
  Defined.

  Fixpoint lsubst (T:Type)(k:nat)(l:list (T*typ))(d:indiv) :=
    match l with
      | cons aA aAs => cons (fst aA, (subst k (snd aA) d)) (lsubst k aAs d)
      | nil => nil
    end.

  Notation "l \ x" := (lsubst 0 l (fvar x)) (at level 60).

  Fixpoint fvar_swap_indiv (x:var_free)(a:indiv)(y:var_free) {struct a} : indiv :=
    let fvar_swap_list := fix fvar_swap_list 
      (l:list indiv) {struct l} : list indiv :=
      match l with 
        | nil => nil
        | cons a' l' => cons (fvar_swap_indiv x a' y) (fvar_swap_list l')
      end in
    match a with
      | func f ld => 
        func f (fvar_swap_list ld)
      | fvar z => if (var_free_dec x z) then (fvar y) else (fvar z)
      | bvar i => bvar i
    end.

  Fixpoint fvar_swap_typ (x:var_free)(A:typ)(y:var_free) {struct A} : typ :=
    let fvar_swap_list := fix fvar_swap_list 
      (l:list indiv) {struct l} : list indiv :=
      match l with 
        | nil => nil
        | cons a' l' => cons (fvar_swap_indiv x a' y) (fvar_swap_list l')
      end in
    match A with
      | Ex A1      => Ex   (fvar_swap_typ x A1 y) 
      | All A1     => All  (fvar_swap_typ x A1 y) 
      | Conj A1 A2 => Conj (fvar_swap_typ x A1 y) (fvar_swap_typ x A2 y)
      | Disj A1 A2 => Disj (fvar_swap_typ x A1 y) (fvar_swap_typ x A2 y)
      | Imp A1 A2  => Imp  (fvar_swap_typ x A1 y) (fvar_swap_typ x A2 y)
      | Atom P ld => 
        Atom P (fvar_swap_list ld)
    end.

  Fixpoint fvar_swap_cxt (T:Type)(x:var_free)(l:list (T*typ))(y:var_free) :=
    match l with
      | cons aA aAs => 
        cons (fst aA, (fvar_swap_typ x (snd aA) y)) (fvar_swap_cxt x aAs y)
      | nil => nil
    end.

  Lemma locli_fvar_swap : forall a m, 
    (forall k d, subst_indiv (plus k m) a d = a) ->
    forall x y k d, 
      subst_indiv (plus k m) (fvar_swap_indiv x a y) d = fvar_swap_indiv x a y.
  Proof.
    fix 1.
    intro a.
    destruct a.

    simpl.
    auto.

    simpl.
    intros.
    destruct var_free_dec.
    Hint Unfold locli_fvar.
    apply locli_fvar.
    apply locli_fvar.
    
    intros.
    simpl in *.
    assert (H' := fun k d => func_wrapper1 (H k d)).
    clear H.
    apply func_wrapper2.
    induction l.
    reflexivity.
    apply eqs_cons.
    assert (H1 := fun k d => fst (cons_eqs (H' k d))).
    assert (H2 := fun k d => snd (cons_eqs (H' k d))).
    clear H'.
    split.
    unfold locli in locli_fvar_swap.
    rewrite locli_fvar_swap.
    reflexivity.
    apply H1.
    apply IHl.
    apply H2.
  Defined.

  Lemma locl_fvar_swap : forall A m, 
    (forall k d, subst (plus k m) A d = A) ->
    forall x y k d, 
      subst (plus k m) (fvar_swap_typ x A y) d = fvar_swap_typ x A y.
  Proof.
    induction A.
    
    induction l.
    simpl.
    auto.
    intros m H.
    simpl in H.
    assert (H' := fun k d => cons_eqs (Atom_wrapper1 (H k d))).
    clear H.
    assert (H1 := fun k d => fst (H' k d)).
    assert (H2 := fun k d => snd (H' k d)).
    clear H'.
    intros.
    simpl.
    unfold locl.
    intros.
    simpl.
    apply Atom_wrapper2.
    apply eqs_cons.
    split.
    apply locli_fvar_swap.
    apply H1.
    simpl in IHl.
    assert (IHl' := fun m H x y k d => Atom_wrapper1 (IHl m H x y k d)).   
    clear IHl.
    assert (H2' : (forall (k : nat) (d : indiv),
      Atom p
      ((fix subst_list (l : list indiv) : list indiv :=
        match l with
          | nil => nil
          | a' :: l' => subst_indiv (plus k m) a' d :: subst_list l'
        end) l) = Atom p l)).
    intros.
    assert (H2'' := H2  k0 d0).
    congruence.
    apply IHl' with m x y k d in H2'.
    clear IHl'.
    apply H2'.

    unfold locl.
    simpl.
    intros.
    rewrite IHA1.
    rewrite IHA2.
    reflexivity.
    assert (H' := fun k d => H k d).
    intros k' d'.
    assert (H'' := H' k' d').
    congruence.
    assert (H' := fun k d => H k d).
    intros k' d'.
    assert (H'' := H' k' d').
    congruence.

    unfold locl.
    simpl.
    intros.
    rewrite IHA1.
    rewrite IHA2.
    reflexivity.
    assert (H' := fun k d => H k d).
    intros k' d'.
    assert (H'' := H' k' d').
    congruence.
    assert (H' := fun k d => H k d).
    intros k' d'.
    assert (H'' := H' k' d').
    congruence.

    unfold locl.
    simpl.
    intros.
    rewrite IHA1.
    rewrite IHA2.
    reflexivity.
    assert (H' := fun k d => H k d).
    intros k' d'.
    assert (H'' := H' k' d').
    congruence.
    assert (H' := fun k d => H k d).
    intros k' d'.
    assert (H'' := H' k' d').
    congruence.

    unfold locl.
    simpl.
    intros.
    rewrite plus_n_Sm.
    rewrite IHA.
    reflexivity.
    intros k' d'.
    rewrite <- plus_n_Sm.
    assert (H'' := H k' d').
    congruence.

    unfold locl.
    simpl.
    intros.
    rewrite plus_n_Sm.
    rewrite IHA.
    reflexivity.
    intros k' d'.
    rewrite <- plus_n_Sm.
    assert (H'' := H k' d').
    congruence.
  Defined.

  Lemma subst_fvar_swap_indiv : forall i k d x y, 
    fvar_swap_indiv x (subst_indiv k i d) y 
    = subst_indiv k (fvar_swap_indiv x i y) (fvar_swap_indiv x d y).
  Proof.
    fix 1.
    intro i.
    destruct i.

    simpl.
    intros.
    destruct beq_nat.
    reflexivity.
    reflexivity.

    simpl.
    intros.
    destruct var_free_dec.
    reflexivity.
    reflexivity.

    intros.
    simpl.
    apply func_wrapper2.
    induction l.
    reflexivity.
    apply eqs_cons.
    split.
    rewrite subst_fvar_swap_indiv.
    reflexivity.
    apply IHl.
  Defined.

  Lemma subst_fvar_swap : forall A k d x y, fvar_swap_typ x (subst k A d) y 
    = subst k (fvar_swap_typ x A y) (fvar_swap_indiv x d y).
  Proof.
    fix 1.
    intro A.
    destruct A.

    intros.
    simpl.

    apply Atom_wrapper2.
    induction l.
    reflexivity.
    apply eqs_cons.
    split.
    rewrite subst_fvar_swap_indiv.
    reflexivity.
    apply IHl.

    simpl.
    intros.
    rewrite subst_fvar_swap.
    rewrite subst_fvar_swap.
    reflexivity.

    simpl.
    intros.
    rewrite subst_fvar_swap.
    rewrite subst_fvar_swap.
    reflexivity.

    simpl.
    intros.
    rewrite subst_fvar_swap.
    rewrite subst_fvar_swap.
    reflexivity.

    simpl.
    intros.
    rewrite subst_fvar_swap.
    reflexivity.

    simpl.
    intros.
    rewrite subst_fvar_swap.
    reflexivity.
  Defined.

  Fixpoint fvar_appears_indiv (x:var_free)(a:indiv) {struct a} : bool :=
    let fvar_appears_list := 
      fix fvar_appears_list (x:var_free)(l:list indiv) {struct l} : bool :=
      match l with
        | nil => false
        | cons d l' => 
          orb (fvar_appears_indiv x d) (fvar_appears_list x l')
      end
      in match a with
           | func f ld => fvar_appears_list x ld
           | fvar z => if (var_free_dec x z) then true else false
           | bvar i => false
         end.

  Fixpoint fvar_appears_typ (x:var_free)(A:typ) {struct A} : bool :=
    let fvar_appears_list := 
      fix fvar_appears_list (x:var_free)(l:list indiv) {struct l} : bool :=
      match l with
        | nil => false
        | cons d l' => 
          orb (fvar_appears_indiv x d) (fvar_appears_list x l')
      end
      in match A with
      | Ex A1      => fvar_appears_typ x A1
      | All A1     => fvar_appears_typ x A1
      | Conj A1 A2 => orb (fvar_appears_typ x A1) (fvar_appears_typ x A2)
      | Disj A1 A2 => orb (fvar_appears_typ x A1) (fvar_appears_typ x A2)
      | Imp A1 A2  => orb (fvar_appears_typ x A1) (fvar_appears_typ x A2)
      | Atom P ld  => fvar_appears_list x ld
         end.

  Fixpoint fvar_appears_cxt (T:Type)(x:var_free)(l:list (T*typ)) : bool :=
    match l with
      | cons aA aAs => 
        orb (fvar_appears_typ x (snd aA)) (fvar_appears_cxt x aAs)
      | nil => false
    end.

  Lemma swap_appears_not_indiv : forall d x,
    fvar_appears_indiv x d = false -> forall y, fvar_swap_indiv x d y = d.
  Proof.
    fix 1.
    intro d.
    destruct d.

    simpl.
    auto.

    simpl.
    intros.
    destruct var_free_dec.
    discriminate.
    reflexivity.

    intros.
    simpl in *.
    apply func_wrapper2.
    induction l.
    reflexivity.
    apply Bool.orb_false_elim in H.
    destruct H as [H1 H2].
    apply eqs_cons.
    split.
    apply swap_appears_not_indiv.
    assumption.
    apply IHl.
    assumption.
  Defined.

  Lemma swap_appears_not_typ : forall A x,
    fvar_appears_typ x A = false -> forall y, fvar_swap_typ x A y = A.
  Proof.
    fix 1.
    intro A.
    destruct A.

    intros.
    simpl in *.
    apply Atom_wrapper2.
    induction l.
    reflexivity.
    apply Bool.orb_false_elim in H.
    destruct H as [H1 H2].
    apply eqs_cons.
    split.
    apply swap_appears_not_indiv.
    assumption.
    apply IHl.
    assumption.

    simpl.
    intros.
    apply Bool.orb_false_elim in H.
    destruct H as [H1 H2].
    rewrite swap_appears_not_typ.
    rewrite swap_appears_not_typ.
    reflexivity.
    assumption.
    assumption.

    simpl.
    intros.
    apply Bool.orb_false_elim in H.
    destruct H as [H1 H2].
    rewrite swap_appears_not_typ.
    rewrite swap_appears_not_typ.
    reflexivity.
    assumption.
    assumption.

    simpl.
    intros.
    apply Bool.orb_false_elim in H.
    destruct H as [H1 H2].
    rewrite swap_appears_not_typ.
    rewrite swap_appears_not_typ.
    reflexivity.
    assumption.
    assumption.

    simpl.
    intros.
    rewrite swap_appears_not_typ.
    reflexivity.
    assumption.

    simpl.
    intros.
    rewrite swap_appears_not_typ.
    reflexivity.
    assumption.
  Defined.

  Lemma swap_appears_not_cxt : forall T, forall GD:list (T*typ), forall x,
    fvar_appears_cxt x GD = false -> forall y, fvar_swap_cxt x GD y = GD.
  Proof.
    induction GD.

    reflexivity.

    simpl.
    intros.
    apply Bool.orb_false_elim in H.
    destruct H as [H1 H2].
    rewrite swap_appears_not_typ; auto.
    rewrite IHGD;auto.
    destruct a; auto.
  Defined.

  Fixpoint FV_indiv (d:indiv) {struct d} : list var_free :=
    let FV_indiv_list := 
      fix FV_indiv_list (l:list indiv) {struct l} : list var_free :=
      match l with
        | nil => nil
        | cons d' l' => List.app (FV_indiv d') (FV_indiv_list l')
      end in
    match d with
      | func f vl => FV_indiv_list vl
      | fvar z => (z::nil)
      | bvar i => nil
    end.

  Fixpoint FV_typ (A:typ) {struct A} : list var_free :=
    let FV_indiv_list := 
      fix FV_indiv_list (l:list indiv) {struct l} : list var_free :=
      match l with
        | nil => nil
        | cons d' l' => List.app (FV_indiv d') (FV_indiv_list l')
      end in
    match A with
      | Ex A1      => FV_typ A1
      | All A1     => FV_typ A1
      | Conj A1 A2 => (FV_typ A1) ++ (FV_typ A2)
      | Disj A1 A2 => (FV_typ A1) ++ (FV_typ A2)
      | Imp A1 A2  => (FV_typ A1) ++ (FV_typ A2)
      | Atom P vl  => FV_indiv_list vl
    end.

  Fixpoint FV_cxt (T:Type)(l:list (T*typ)) {struct l} : list var_free :=
    match l with
      | cons aA aAs => FV_typ (snd aA) ++ (FV_cxt aAs)
      | nil => nil
    end.

  Lemma notin_app : forall T:Type, forall x:T, forall L1 L2, 
    x\notin L1++L2 -> (x\notin L1)*(x\notin L2).
  Proof.
    intros.
    split.
    eauto using in_or_app.
    eauto using in_or_app.
  Defined.

  Lemma notin_FV_not_appears_indiv : forall a x, x \notin FV_indiv a ->
    fvar_appears_indiv x a = false.
  Proof.
    fix 1.
    destruct a.

    simpl.
    reflexivity.

    simpl.
    intros.
    destruct var_free_dec.
    symmetry in e.
    intuition.
    reflexivity.

    intros.
    induction l.
    reflexivity.
    simpl in *.
    apply Bool.orb_false_intro.
    apply notin_app in H.
    destruct H.
    apply notin_FV_not_appears_indiv.
    assumption.
    apply IHl.
    apply notin_app in H.
    destruct H.
    assumption.
  Defined.

  Lemma notin_FV_not_appears : forall A x, x \notin FV_typ A ->
    fvar_appears_typ x A = false.
  Proof.
    induction A.

    simpl.
    induction l.
    reflexivity.
    intros.
    apply Bool.orb_false_intro.
    apply notin_app in H.
    destruct H as [H _].
    apply notin_FV_not_appears_indiv.
    assumption.
    apply IHl.
    apply notin_app in H.
    destruct H as [_ H].
    assumption.

    simpl.
    intros.
    apply notin_app in H.
    destruct H as [H1 H2].
    apply Bool.orb_false_intro; auto.

    simpl.
    intros.
    apply notin_app in H.
    destruct H as [H1 H2].
    apply Bool.orb_false_intro; auto.

    simpl.
    intros.
    apply notin_app in H.
    destruct H as [H1 H2].
    apply Bool.orb_false_intro; auto.

    simpl.
    intros.
    auto.

    simpl.
    intros.
    auto.
  Defined.

  Lemma fvar_swap_cxt_idem : forall T:Type, forall GD:list (T*typ), 
    forall x y, x\notin FV_cxt GD ->
      fvar_swap_cxt x GD y = GD.
  Proof.
    induction GD.

    reflexivity.

    intros.
    simpl.
    rewrite IHGD.
    rewrite swap_appears_not_typ.
    destruct a; auto.
    simpl in H.
    apply notin_FV_not_appears.
    apply notin_app in H.
    apply H.
    simpl in H.
    apply notin_app in H.
    apply H.
  Defined.

  Lemma subst_fvar_swap_lem : forall A,
    forall x y, x\notin FV_typ A ->
      fvar_swap_typ x (A^x) y = A^y.
  Proof.
    intros.
    replace (A^y) with ((fvar_swap_typ x A y)^^(fvar_swap_indiv x (fvar x) y)).
    apply subst_fvar_swap.
    simpl.
    destruct var_free_dec; [idtac|congruence].
    rewrite swap_appears_not_typ.
    reflexivity.
    apply notin_FV_not_appears.
    assumption.
  Defined.

  Definition fvar_swap_proof : forall (x y:var_free),
    (forall c Gamma Delta, proof_cmd c Gamma Delta ->
      let Gamma' := fvar_swap_cxt x Gamma y in
      let Delta' := fvar_swap_cxt x Delta y in
      proof_cmd c Gamma' Delta') *
    (forall Gamma t A Delta, proof_trm Gamma t A Delta -> 
      let Gamma' := fvar_swap_cxt x Gamma y in
      let Delta' := fvar_swap_cxt x Delta y in
      let A' := fvar_swap_typ x A y in
        proof_trm Gamma' t A' Delta') *
    (forall Gamma e A Delta, proof_ect Gamma e A Delta -> 
      let Gamma' := fvar_swap_cxt x Gamma y in
      let Delta' := fvar_swap_cxt x Delta y in
      let A' := fvar_swap_typ x A y in
        proof_ect Gamma' e A' Delta').
  Proof.
    intros x y.
    apply proof_rect'.

    intros v e Gamma Delta A _ IHv _ IHe.
    apply Cut with (fvar_swap_typ x A y).
    assumption.
    assumption.

    intros Gamma a A Delta IH.
    constructor.
    clear Delta.
    induction Gamma.
    inversion IH.
    simpl in IH.
    destruct IH.
    rewrite e.
    simpl.
    auto.
    simpl.
    auto.

    intros Gamma alpha c A Delta _ IH.
    eapply Mu.
    assumption.

    intros; simpl in *; constructor; auto.

    intros; simpl in *; constructor; auto.

    intros; simpl in *; constructor; auto.

    intros; simpl in *; constructor; auto.

    intros; simpl in *.
    apply AllR with (x::L).
    replace (All (fvar_swap_typ x A y)) with (fvar_swap_typ x (All A) y);
      [idtac | reflexivity].
      unfold locl.
      intros.
      replace k with (plus k 0).
      apply locl_fvar_swap.
      intros.
      apply l.
      apply Arith.Plus.plus_0_r.
    intros x0 Hx0.
    assert (x0 \notin L).
    clear -Hx0.
    simpl in *.
    intro H.
    auto.
    replace (fvar_swap_typ x A y ^ x0) with 
            ((fvar_swap_typ x A y) ^^ (fvar_swap_indiv x (fvar x0) y)).
    rewrite <- subst_fvar_swap.
    auto.
    rewrite swap_appears_not_indiv.
    reflexivity.
    clear -Hx0.
    simpl.
    destruct var_free_dec.
    simpl in Hx0.
    assert (Hx0' := Hx0 (inl _ e)).
    inversion Hx0'.
    reflexivity.

    intros; simpl in *.
    apply ExR with (fvar_swap_indiv x d y).
    unfold locli.
    intros.
    replace k with (plus k 0).
    apply locli_fvar_swap.
    intros.
    apply l.
    apply Arith.Plus.plus_0_r.
    rewrite <- subst_fvar_swap.
    assumption.

    intros Gamma alpha A Delta IH.
    constructor.
    clear Gamma.
    induction Delta.
    inversion IH.
    simpl in IH.
    destruct IH.
    rewrite e.
    simpl.
    auto.
    simpl.
    auto.

    intros Gamma a c A Delta _ IH.
    eapply MuT.
    assumption.

    intros; simpl in *; constructor; auto.

    intros; simpl in *; constructor; auto.

    intros; simpl in *; constructor; auto.

    intros; simpl in *; constructor; auto.

    intros; simpl in *.
    apply AllL with (fvar_swap_indiv x d y).
    unfold locli.
    intros.
    replace k with (plus k 0).
    apply locli_fvar_swap.
    intros.
    apply l.
    apply Arith.Plus.plus_0_r.
    rewrite <- subst_fvar_swap.
    assumption.

    intros; simpl in *.
    apply ExL with (x::L).
    replace (Ex (fvar_swap_typ x A y)) with (fvar_swap_typ x (Ex A) y);
      [idtac | reflexivity].
      unfold locl.
      intros.
      replace k with (plus k 0).
      apply locl_fvar_swap.
      intros.
      apply l.
      apply Arith.Plus.plus_0_r.
    intros x0 Hx0.
    assert (x0 \notin L).
    clear -Hx0.
    simpl in *.
    intro H.
    auto.
    replace (fvar_swap_typ x A y ^ x0) with 
            ((fvar_swap_typ x A y) ^^ (fvar_swap_indiv x (fvar x0) y)).
    rewrite <- subst_fvar_swap.
    auto.
    rewrite swap_appears_not_indiv.
    reflexivity.
    clear -Hx0.
    simpl.
    destruct var_free_dec.
    simpl in Hx0.
    assert (Hx0' := Hx0 (inl _ e)).
    inversion Hx0'.
    reflexivity.
  Defined.

  Lemma proof_trm_quant_invar : forall Gamma Delta A,
    let L := FV_typ A ++ FV_cxt Gamma ++ FV_cxt Delta in
    (forall x, x\notin L ->
      sigT (fun t:trm => proof_trm Gamma t (A^x) Delta)) ->
    sigT (fun s:trm => forall y, y\notin L -> proof_trm Gamma s (A^y) Delta).
  Proof.
    intros.
    destruct (fresh_fvar L) as [x Hx].
    destruct (H x) as [t p].
    assumption.
    exists t.
    clear H.
    unfold L in Hx.
    apply notin_app in Hx.
    destruct Hx as [Hx1 Hx2].
    apply notin_app in Hx2.
    destruct Hx2 as [Hx2 Hx3].
    intros y Hy.
    unfold L in Hy.
    apply notin_app in Hy.
    destruct Hy as [Hy1 Hy2].
    apply notin_app in Hy2.
    destruct Hy2 as [Hy2 Hy3].
    assert (p' := (snd (fst (fvar_swap_proof x y))) _ _ _ _ p).
    simpl in p'.
    rewrite fvar_swap_cxt_idem in p'; auto.
    rewrite fvar_swap_cxt_idem in p'; auto.
    rewrite subst_fvar_swap_lem in p'; auto.
  Defined.

  Lemma proof_ect_quant_invar : forall Gamma Delta A,
    let L := FV_typ A ++ FV_cxt Gamma ++ FV_cxt Delta in
    (forall x, x\notin L ->
      sigT (fun e:ect => proof_ect Gamma e (A^x) Delta)) ->
    sigT (fun f:ect => forall y, y\notin L -> proof_ect Gamma f (A^y) Delta).
  Proof.
    intros.
    destruct (fresh_fvar L) as [x Hx].
    destruct (H x) as [e p].
    assumption.
    exists e.
    clear H.
    unfold L in Hx.
    apply notin_app in Hx.
    destruct Hx as [Hx1 Hx2].
    apply notin_app in Hx2.
    destruct Hx2 as [Hx2 Hx3].
    intros y Hy.
    unfold L in Hy.
    apply notin_app in Hy.
    destruct Hy as [Hy1 Hy2].
    apply notin_app in Hy2.
    destruct Hy2 as [Hy2 Hy3].
    assert (p' := ((snd (fvar_swap_proof x y))) _ _ _ _ p).
    simpl in p'.
    rewrite fvar_swap_cxt_idem in p'; auto.
    rewrite fvar_swap_cxt_idem in p'; auto.
    rewrite subst_fvar_swap_lem in p'; auto.
  Defined.
End subst_lemmas.

(** The Universal model *)
Section Concrete_Semantics.
  Definition Kworld : Set := cxt_trm * cxt_ect.
  
  Definition Kle (w w':Kworld) : Type :=
    (incl (fst w) (fst w')) * (incl (snd w) (snd w')).
  
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
  Hint Unfold Kexploding.

  Definition Normal_trm (A:typ)(Gamma:cxt_trm)(Delta:cxt_ect) :=
    sigT (fun t:trm => proof_trm Gamma t A Delta).
  Hint Unfold Normal_trm.

  Definition Normal_ect (A:typ)(Gamma:cxt_trm)(Delta:cxt_ect) :=
    sigT (fun e:ect => proof_ect Gamma e A Delta).
  Hint Unfold Normal_ect.

  Definition Kaforces (w:Kworld)(p:predicate)(ld:list indiv) : Set := 
    Normal_trm (@Atom p ld) (fst w) (snd w).
  Hint Unfold Kaforces.

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

    (* AllR *)
    intros.
    apply AllR with L.
    assumption.
    intros.
    apply X.
    assumption.
    assumption.
    assumption.

    (* ExR *)
    intros.
    apply ExR with d.
    assumption.
    apply X.
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

    (* AllL *)
    intros.
    apply AllL with d.
    assumption.
    apply X; auto.

    (* ExL *)
    intros.
    apply ExL with L.
    assumption.
    auto.
  Defined.

  Lemma Kaforces_mon : forall w P ld, @Kaforces w P ld ->
    forall w', Kle w w' -> @Kaforces w' P ld.
  Proof.
    intros w P ld H.
    destruct H as [v p].
    intros w' Hle.
    exists v.
    unfold Kle in Hle.
    destruct Hle.
    apply (snd (fst proof_weaken)) with (fst w) (snd w); auto.
  Defined.

  Definition K : Kripke.
  (* begin show *)
    apply Build_Kripke with Kworld Kle Kaforces.
    exact Kle_refl.
    exact Kle_trans.
    exact Kexploding.
    exact Kaforces_mon.
  (* end show *)
  Defined.
End Concrete_Semantics.

Notation "w  <=  w'" := (Kle w w').

Notation "w : ||+ A " := (@sforces K w A) (at level 70).
Notation "w : A ||- " := (@refutes K w A)  (at level 70).
Notation "w : ||- A " := (Kont (@sforces K) w A) (at level 70).
Notation " w : ||-- Gamma " := (@forces_cxt K w Gamma) (at level 70).
Notation " w : Delta ||-- "  := (@refutes_cxt K w Delta) (at level 70).

Definition cmd_to_trm : forall w A, forall alpha:var_ect,
  let w1 := (fst w, (alpha,A) :: snd w) in
  sigT (fun c:cmd => proof_cmd c (fst w1) (snd w1)) ->
  sigT (fun t:trm => proof_trm (fst w) t A (snd w)).
Proof.
  intros w A alpha w1 H.
  destruct H as [c Hc].
  exists (mu alpha c).
  constructor.
  exact Hc.
Defined.

Definition cmd_to_ect : forall w A, forall x:var_trm,
  let w1 := ((x,A) :: fst w, snd w) in
  sigT (fun c:cmd => proof_cmd c (fst w1) (snd w1)) ->
  sigT (fun e:ect => proof_ect (fst w) e A (snd w)).
Proof.
  intros w A x w1 H.
  destruct H as [c Hc].
  exists (mut x c).
  constructor.
  exact Hc.
Defined.

Definition to_cmd : forall w A,
  sigT (fun t:trm => proof_trm (fst w) t A (snd w)) ->
  sigT (fun e:ect => proof_ect (fst w) e A (snd w)) ->
  sigT (fun c:cmd => proof_cmd c (fst w) (snd w)).
Proof.
  intros w A H1 H2.
  destruct H1 as [t Ht].
  destruct H2 as [e He].
  exists (cm t e).
  apply Cut with A.
  assumption.
  assumption.
Defined.

Lemma Kle_eta_r : forall w a, Kle w (fst w, a :: snd w).
Proof.
  intros.
  split.
  destruct w.
  simpl.
  auto.
  simpl.
  auto.
Defined.

Lemma Kle_eta_l : forall w a, Kle w (a :: fst w, snd w).
Proof.
  intros.
  split.
  destruct w.
  simpl.
  auto.
  simpl.
  auto.
Defined.

(** The proof of completeness is via a reify-reflect pair, by induction on [n] i.e. by induction on the complexity of the formula [A]. [tfresh] and [efresh] are a fresh variable counters that are increased at every recursive call. *)
Theorem Kcompleteness : 
  forall (n:nat)(A:typ), le (depth A) n -> locl A ->
  forall (w:K)(tfresh:var_trm)(efresh:var_ect),
    (w : ||- A -> Normal_trm A (fst w) (snd w)) *
    (w : A ||- -> Normal_ect A (fst w) (snd w)).
Proof.
  induction n.

  intros A Hn.
  destruct A;inversion Hn.
  intros A HSn Hlocl.
  intros.
  destruct A.

  (* Atomic formulas *)
  split.

  intro H.
  apply cmd_to_trm with efresh.
  apply H.
  simpl.
  apply Kle_eta_r.
  simpl.
  intros w1 w1w2.
  unfold sforces.
  simpl.
  intro H1.
  apply to_cmd with (Atom p l).
  exact H1.
  exists (evar efresh).
  constructor.
  apply w1w2.
  simpl.
  left; reflexivity.
  intro H.
  apply cmd_to_ect with tfresh.
  apply H.
  apply Kle_eta_l.
  unfold sforces.
  simpl.
  exists (tvar tfresh).
  constructor.
  simpl.
  left; reflexivity.

  (* Implication *)
  assert (Hdepth2 : le (depth A2) n).
    clear -HSn.
    simpl in HSn.
    apply le_S_n in HSn.
    eapply le_trans.
    apply le_max_r.
    apply HSn.
  assert (Hdepth1 : le (depth A1) n).
    clear -HSn.
    simpl in HSn.
    apply le_S_n in HSn.
    eapply le_trans.
    apply le_max_l.
    apply HSn.
  assert (Hlocl1 : locl A1).
    clear -Hlocl.
    unfold locl in *.
    simpl in *.
    intros.
    assert (Hlocl' := Hlocl k d).
    congruence.
  assert (Hlocl2 : locl A2).
    clear -Hlocl.
    unfold locl in *.
    simpl in *.
    intros.
    assert (Hlocl' := Hlocl k d).
    congruence.
  split.

  intro H.
  set (w1 := (((tfresh,A1)::fst w),(snd w))).
  assert (Normal_trm A2 (fst w1) (snd w1)).
  apply cmd_to_trm with efresh.
  apply H.
  unfold w1.
  simpl.
  split.
  simpl.
  auto.
  simpl.
  auto.
  intros w3 w2w3 HImp.
  assert (HImp' := sforces_correct_Imp HImp).
  clear HImp.
  assert (HA2 : Normal_trm A2 (fst w3) (snd w3)).
  apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)).
  apply HImp'.
  apply wle_refl.
  intros w4 w3w4 HA1.
  change (w4:A1||-) in HA1. 
  apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)) in HA1.
  destruct HA1 as [t1 Ht1].
  eexists.
  apply Cut with A1.
  apply AxR.
  apply w3w4.
  apply w2w3.
  unfold w1.
  left;reflexivity.
  apply Ht1.
  destruct HA2 as [t2 Ht2].
  exists (cm (t2) (evar efresh)).
  apply Cut with A2.
  assumption.
  constructor.
  apply w2w3.
  left;reflexivity.
  destruct H0 as [t2' Ht2'].
  eexists.
  apply ImpR.
  unfold w1 in Ht2'.
  simpl in Ht2'.
  apply Ht2'.

  intro H.
  apply cmd_to_ect with tfresh.
  apply H.
  apply Kle_eta_l.
  apply sforces_correct_Imp'.
  intros w2 w1w2 HA1.
  apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)) in HA1.
  intros w3 w2w3 HA2.
  change (w3:A2||-) in HA2.
  apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)) in HA2.
  destruct HA1 as [t1 Ht1].
  destruct HA2 as [e2 He2].
  eexists.
  apply Cut with (Imp A1 A2).
  apply AxR.
  apply w2w3.
  apply w1w2.
  left;reflexivity.
  apply ImpL.
  apply (snd (fst proof_weaken)) with (fst w2) (snd w2).
  apply Ht1.
  destruct w2w3; auto.
  destruct w2w3; auto.
  apply He2.

  (* Disjunction *)
  (* the following 4 assertions are a copy-past of above; to define an Ltac? *)
  assert (Hdepth2 : le (depth A2) n).
    clear -HSn.
    simpl in HSn.
    apply le_S_n in HSn.
    eapply le_trans.
    apply le_max_r.
    apply HSn.
  assert (Hdepth1 : le (depth A1) n).
    clear -HSn.
    simpl in HSn.
    apply le_S_n in HSn.
    eapply le_trans.
    apply le_max_l.
    apply HSn.
  assert (Hlocl1 : locl A1).
    clear -Hlocl.
    unfold locl in *.
    simpl in *.
    intros.
    assert (Hlocl' := Hlocl k d).
    congruence.
  assert (Hlocl2 : locl A2).
    clear -Hlocl.
    unfold locl in *.
    simpl in *.
    intros.
    assert (Hlocl' := Hlocl k d).
    congruence.
  split.

  intro H.
  apply cmd_to_trm with efresh.
  apply H.
  apply Kle_eta_r.
  intros w2 w1w2 H2.
  apply sforces_correct_Disj in H2.
  case H2.
  intro case1.
  apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)) in case1.
  simpl.
  apply to_cmd with (Disj A1 A2).
  destruct case1 as [t1 Ht1].
  exists (injl t1).
  constructor.
  exact Ht1.
  exists (evar efresh).
  constructor.
  apply w1w2.
  simpl.
  left;reflexivity.
  intro case2.
  apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)) in case2.
  simpl.
  apply to_cmd with (Disj A1 A2).
  destruct case2 as [t2 Ht2].
  exists (injr t2).
  constructor.
  exact Ht2.
  exists (evar efresh).
  constructor.
  apply w1w2.
  simpl.
  left;reflexivity.

  intro H.
  set (w1 := ((tfresh, A1)::fst w, snd w)).
  assert (ww1 : wle w w1).
  apply Kle_eta_l.
  assert (branch1 : Normal_ect A1 (fst w1) (snd w1)).
  apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)).
  intros w' w1w' H'.
  apply H.
  eauto using wle_trans.
  apply sforces_correct_Disj'.
  left.
  apply ret.
  assumption.
  set (w2 := ((tfresh, A2)::fst w, snd w)).
  assert (ww2 : wle w w2).
  apply Kle_eta_l.
  assert (branch2 : Normal_ect A2 (fst w2) (snd w2)).
  apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)).
  intros w' w2w' H'.
  apply H.
  eauto using wle_trans.
  apply sforces_correct_Disj'.
  right.
  apply ret.
  assumption.
  destruct branch1 as [e1 He1].
  destruct branch2 as [e2 He2].
  exists (disj (mut tfresh (cm (tvar tfresh) e1)) 
               (mut tfresh (cm (tvar tfresh) e2))).
  constructor.
  constructor.
  apply Cut with A1.
  constructor.
  left;reflexivity.
  assumption.
  constructor.
  apply Cut with A2.
  constructor.
  left;reflexivity.
  assumption.

  (* Conjunction *)
  (* the following 4 assertions are a copy-past of above; to define an Ltac? *)
  assert (Hdepth2 : le (depth A2) n).
    clear -HSn.
    simpl in HSn.
    apply le_S_n in HSn.
    eapply le_trans.
    apply le_max_r.
    apply HSn.
  assert (Hdepth1 : le (depth A1) n).
    clear -HSn.
    simpl in HSn.
    apply le_S_n in HSn.
    eapply le_trans.
    apply le_max_l.
    apply HSn.
  assert (Hlocl1 : locl A1).
    clear -Hlocl.
    unfold locl in *.
    simpl in *.
    intros.
    assert (Hlocl' := Hlocl k d).
    congruence.
  assert (Hlocl2 : locl A2).
    clear -Hlocl.
    unfold locl in *.
    simpl in *.
    intros.
    assert (Hlocl' := Hlocl k d).
    congruence.
  split.

  intro H.
  assert (conj1 : Normal_trm A1 (fst w) (snd w)).
  apply cmd_to_trm with efresh.
  apply H.
  apply Kle_eta_r.
  intros w2 w1w2 H2.
  apply sforces_correct_Conj in H2.
  destruct H2 as [Ht1 _].
  apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)) in Ht1.
  destruct Ht1 as [t1 Ht1].
  exists (cm t1 (evar efresh)).
  apply Cut with A1.
  assumption.
  constructor.
  apply w1w2.
  left;reflexivity.
  assert (conj2 : Normal_trm A2 (fst w) (snd w)).
  apply cmd_to_trm with efresh.
  apply H.
  apply Kle_eta_r.
  intros w2 w1w2 H2.
  apply sforces_correct_Conj in H2.
  destruct H2 as [_ Ht2].
  apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)) in Ht2.
  destruct Ht2 as [t2 Ht2].
  exists (cm t2 (evar efresh)).
  apply Cut with A2.
  assumption.
  constructor.
  apply w1w2.
  left;reflexivity.
  destruct conj1 as [t1' Ht1'].
  destruct conj2 as [t2' Ht2'].
  exists (paire t1' t2').
  constructor.
  assumption.
  assumption.

  intro H.
  apply cmd_to_ect with (tfresh).
  apply H.
  apply Kle_eta_l.
  apply sforces_correct_Conj'.
  clear H.
  split.
  intros w2 w1w2 k.
  change (w2:A1||-) in k.
  apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)) in k.
  destruct k as [e1 He1].
  exists (cm (tvar tfresh) (projl e1)).
  apply Cut with (Conj A1 A2).
  constructor.
  apply w1w2.
  left;reflexivity.
  constructor.
  assumption.
  intros w2 w1w2 k.
  change (w2:A2||-) in k.
  apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)) in k.
  destruct k as [e2 He2].
  exists (cm (tvar tfresh) (projr e2)).
  apply Cut with (Conj A1 A2).
  constructor.
  apply w1w2.
  left;reflexivity.
  constructor.
  assumption.

  (* Universal quantifier *)
  split.

  intro H.
  set (L := FV_typ A ++ FV_cxt (fst w) ++ FV_cxt (snd w)).
  assert (H0:forall y:var_free, y \notin L -> Normal_trm (A^y) (fst w) (snd w)).
  intros.
  apply cmd_to_trm with efresh.
  apply H.
  apply Kle_eta_r.
  intros w2 w1w2 HAllA.
  assert (HAllA' := sforces_correct_All HAllA).
  clear HAllA.
  assert (Hdepth' : le (depth (A^y)) n).
    clear -HSn.
    simpl in HSn.
    rewrite depth_subst.
    apply le_S_n in HSn.
    assumption.
  assert (Hlocl' : locl (A^y)).
    apply locl_locli_subst'.
    assumption.
    apply locli_fvar.
  assert (HAd : w2  : ||- A^y).
  apply HAllA'.
  clear HAllA'.
  apply wle_refl.
  apply locli_fvar.
  apply (IHn _ Hdepth' Hlocl' _ (S tfresh) (S efresh)) in HAd.
  destruct HAd as [td Htd].
  exists (cm td (evar efresh)).
  apply Cut with (A^y).
  assumption.
  apply AxL.
  apply w1w2.
  left;reflexivity.
  apply proof_trm_quant_invar in H0.
  destruct H0 as [s Hs].
  exists (tall s).
  apply AllR with L.
  assumption.
  intros.
  apply Hs.
  assumption.

  intro H.
  apply cmd_to_ect with tfresh.
  apply H.
  apply Kle_eta_l.
  apply sforces_correct_All'.
  intros w2 w1w2 d Hd.
  intros w3 w2w3 HAd.
  change (w3:A^^d||-) in HAd.
  assert (Hdepth' : le (depth (A^^d)) n).
    clear -HSn.
    simpl in HSn.
    rewrite depth_subst.
    apply le_S_n in HSn.
    assumption.
  assert (Hlocl' : locl (A^^d)).
    apply locl_locli_subst'.
    assumption.
    assumption.
  apply (IHn _ Hdepth' Hlocl' _ (S tfresh) (S efresh)) in HAd.
  destruct HAd as [ed Hed].
  exists (cm (tvar tfresh) (eall ed)).
  apply Cut with (All A).
  constructor.
  apply w2w3.
  apply w1w2.
  left;reflexivity.
  apply AllL with d.
  assumption.
  assumption.


  (* Existential *)
  split.

  intro H.
  apply cmd_to_trm with efresh.
  apply H.
  apply Kle_eta_r.
  intros w2 w1w2 H2.
  apply sforces_correct_Ex in H2.
  destruct H2 as [d [Hd H2]].
  assert (Hdepth' : le (depth (A^^d)) n).
    clear -HSn.
    simpl in HSn.
    rewrite depth_subst.
    apply le_S_n in HSn.
    assumption.
  assert (Hlocl' : locl (A^^d)).
    apply locl_locli_subst''.
    assumption.
    assumption.
  apply (IHn _ Hdepth' Hlocl' _ (S tfresh) (S efresh)) in H2.
  destruct H2 as [t Ht].
  simpl.
  apply to_cmd with (Ex A).
  exists (tex t).
  apply ExR with d.
  assumption.
  exact Ht.
  exists (evar efresh).
  constructor.
  apply w1w2.
  simpl.
  left;reflexivity.

  intro H.

  set (w1 := fun d => ((tfresh, A^^d)::fst w, snd w)).
  assert (ww1 : forall d, wle w (w1 d)).
  intro d.
  apply Kle_eta_l.
  assert (branch1 : forall d, locli d -> Normal_ect (A^^d) (fst (w1 d)) (snd (w1 d))).
  intros d Hd.
  assert (Hdepth' : le (depth (A^^d)) n).
    clear -HSn.
    simpl in HSn.
    rewrite depth_subst.
    apply le_S_n in HSn.
    assumption.
  assert (Hlocl' : locl (A^^d)).
    apply locl_locli_subst''.
    assumption.
    assumption.
  apply (IHn _ Hdepth' Hlocl' _ (S tfresh) (S efresh)).
  intros w' w1w' H'.
  apply H.
  eauto using wle_trans.
  apply sforces_correct_Ex'.
  exists d.
  split ; [exact Hd|].
  apply ret.
  assumption.
  set (L := FV_typ A ++ FV_cxt (fst w) ++ FV_cxt (snd w)).
  assert (H0:forall y:var_free, y \notin L -> Normal_ect (A^y) (fst w) (snd w)).
  intros.
  destruct (branch1 (fvar y) (locli_fvar _)) as [e He].
  apply cmd_to_ect with tfresh.
  simpl.
  exists (cm (tvar tfresh) e).
  apply Cut with (A^y).
  constructor.
  left;reflexivity.
  simpl in He.
  assumption.
  apply proof_ect_quant_invar in H0.
  destruct H0 as [f Hf].
  exists (eex f).
  apply ExL with L.
  assumption.
  intros.
  apply Hf.
  assumption.
Defined.

(** Next: define NbE by composing soundness and completeness. The lemmas [forces_cxt_id] are [refutes_cxt_id] the places completeness is applied at. The variables [tf] and [ef] are the starting fresh variable counters. *)

Fixpoint locl_cxt_trm (Gamma:cxt_trm) : Prop :=
  match Gamma with
    | nil => True
    | cons a Gamma' => locl (snd a) /\ locl_cxt_trm Gamma'
  end.

Fixpoint locl_cxt_ect (Delta:cxt_ect) : Prop :=
  match Delta with
    | nil => True
    | cons a Delta' => locl (snd a) /\ locl_cxt_ect Delta'
  end.

Parameter tf : var_trm.
Parameter ef : var_ect.

Lemma forces_cxt_id : forall Gamma Delta, locl_cxt_trm Gamma -> locl_cxt_ect Delta -> @forces_cxt K (Gamma,Delta) Gamma.
Proof.
  induction Gamma.
  simpl.
  constructor.
  simpl.
  intros Delta [Hlocl HloclGamma] HloclDelta.
  split.
  set (w0 := (a :: Gamma, Delta)).
  intros w1 w0w1 Ha.
  simpl in w0w1.
  change (w0 <= w1) in w0w1.
  change (w1:snd a||-) in Ha. 
  simpl.
  apply (snd (@Kcompleteness (depth (snd a)) (snd a) (le_n _) Hlocl w1 tf ef)) in Ha.
  destruct Ha as [e pe].
  exists (cm (tvar (fst a)) e).
  apply Cut with (snd a).
  apply AxR.
  apply w0w1.
  simpl.
  left.
  destruct a;auto.
  assumption.
  apply forces_cxt_mon with (Gamma, Delta).
  auto.
  simpl.
  red.
  simpl.
  unfold incl.
  intuition.
Defined.

Lemma refutes_cxt_id : forall Gamma Delta, locl_cxt_trm Gamma -> locl_cxt_ect Delta -> @refutes_cxt K (Gamma,Delta) Delta.
Proof.
  induction Delta.
  simpl.
  constructor.
  simpl.
  intros HloclGamma [Hlocl HloclDelta].
  split.
  set (w0 := (Gamma, a::Delta)).
  intros w1 w0w1 Ha.
  simpl in w0w1.
  change (w0 <= w1) in w0w1.
  simpl.
  apply ret in Ha.
  apply (fst (@Kcompleteness (depth (snd a)) (snd a) (le_n _) Hlocl w1 tf ef)) in Ha.
  destruct Ha as [t pt].
  exists (cm t (evar (fst a))).
  apply Cut with (snd a).
  assumption.
  apply AxL.
  apply w0w1.
  simpl.
  left.
  destruct a;auto.
  apply refutes_cxt_mon with (Gamma, Delta).
  auto.
  simpl.
  red.
  simpl.
  unfold incl.
  intuition.
Defined.

Definition NbE : forall c Gamma Delta, 
  locl_cxt_trm Gamma -> locl_cxt_ect Delta -> proof_cmd c Gamma Delta ->
  sigT (fun (c':cmd) => proof_cmd c' Gamma Delta).
Proof.
  intros c Gamma Delta HloclGamma HloclDelta H.
  destruct c as [t e].
  inversion H.
  clear -H2 H5 HloclGamma HloclDelta.
  assert (HGamma : @forces_cxt K (Gamma,Delta) Gamma).
  apply forces_cxt_id; assumption.
  assert (HDelta : @refutes_cxt K (Gamma,Delta) Delta).
  apply refutes_cxt_id; assumption.
  assert (H2' := (snd (fst (soundness K))) Gamma t A Delta H2 (Gamma,Delta) HGamma HDelta).
  assert (H5' := (snd (soundness K)) Gamma e A Delta H5 (Gamma,Delta) HGamma HDelta).
  apply H2' in H5'.
  exact H5'.
  apply Kle_refl.
Defined.


(** And now some computational tests of normalisation. *)

Parameter P : predicate.
Parameter li : list indiv.
Let ATOM := Atom P li.
Parameter ATOMlocl : locl ATOM.

Parameters x y z : var_trm.
Parameters alpha beta gamma delta : var_ect.

(** Example 0: a simplest possible beta-reduction (for implication) *)
Definition cmd0 : cmd := cm (lam x (tvar x)) (app (tvar y) (evar beta)).
Definition Gamma0 := ((y,ATOM)::nil).
Definition Delta0 := ((beta,ATOM)::nil).
Definition proof0 : proof_cmd cmd0 Gamma0 Delta0.
Proof.
  apply Cut with (Imp ATOM ATOM).
  apply ImpR.
  apply AxR.
  left; reflexivity.
  apply ImpL.
  apply AxR.
  left; reflexivity.
  apply AxL.
  left; reflexivity.
Defined.
Definition locl00 : locl_cxt_trm Gamma0.
Proof.
  unfold Gamma0.
  simpl.
  auto using ATOMlocl.
Defined.
Definition locl01 : locl_cxt_ect Delta0.
Proof.
  unfold Delta0.
  simpl.
  auto using ATOMlocl.
Defined.
Definition test0 := projT1 (NbE locl00 locl01 proof0 ).
(* Time Eval vm_compute in test0. *)

(** Example 1: a seemingly more complex beta-reduction (for implication),
   which reduces to the same thing as example 0 *)
Definition cmd1 : cmd := cm (lam x (tvar y)) (app (tvar x) (evar beta)).
Definition Gamma1 := ((y,ATOM)::(x,ATOM)::nil).
Definition Delta1 := ((beta,ATOM)::nil).
Definition proof1 : proof_cmd cmd1 Gamma1 Delta1.
Proof.
  apply Cut with (Imp ATOM ATOM).
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
Definition locl10 : locl_cxt_trm Gamma1.
Proof.
  unfold Gamma1.
  simpl.
  auto using ATOMlocl.
Defined.
Definition locl11 : locl_cxt_ect Delta1.
Proof.
  unfold Delta1.
  simpl.
  auto using ATOMlocl.
Defined.
Definition test1 := projT1 (NbE locl10 locl11 proof1).
(* Time Eval vm_compute in test1. *)

(** Example 2: The <mu,mu~> critical pair indicates we are indeed in
   call-by-value *)
Definition c' : cmd := cm (tvar x) (evar gamma).
Definition c'' : cmd := cm (tvar z) (evar delta).
Definition cmd2 := cm (mu beta c') (mut y c'').
Definition Gamma2 := ((x,ATOM)::(z,ATOM)::nil).
Definition Delta2 := ((gamma,ATOM)::(delta,ATOM)::nil).
Definition Gamma2' := ((z,ATOM)::(x,ATOM)::nil).
Definition Delta2' := ((delta,ATOM)::(gamma,ATOM)::nil).
Definition proof2 : proof_cmd cmd2 Gamma2 Delta2.
Proof.
  apply Cut with ATOM.
  apply Mu.
  apply Cut with ATOM.
  apply AxR.
  left;reflexivity.
  apply AxL.
  right;left;reflexivity.
  apply MuT.
  apply Cut with ATOM.
  apply AxR.
  right;right;left;reflexivity.
  apply AxL.
  right;left;reflexivity.
Defined.
Definition proof2' : proof_cmd cmd2 Gamma2' Delta2'.
Proof.
  apply Cut with ATOM.
  apply Mu.
  apply Cut with ATOM.
  apply AxR.
  right;left;reflexivity.
  apply AxL.
  right;right;left;reflexivity.
  apply MuT.
  apply Cut with ATOM.
  apply AxR.
  right;left;reflexivity.
  apply AxL.
  left;reflexivity.
Defined.
Definition locl20 : locl_cxt_trm Gamma2.
Proof.
  unfold Gamma2.
  simpl.
  auto using ATOMlocl.
Defined.
Definition locl21 : locl_cxt_ect Delta2.
Proof.
  unfold Delta2.
  simpl.
  auto using ATOMlocl.
Defined.
Definition locl2'0 : locl_cxt_trm Gamma2'.
Proof.
  unfold Gamma2'.
  simpl.
  auto using ATOMlocl.
Defined.
Definition locl2'1 : locl_cxt_ect Delta2'.
Proof.
  unfold Delta2'.
  simpl.
  auto using ATOMlocl.
Defined.
Definition test2 := projT1 (NbE locl20 locl21 proof2).
Definition test2' := projT1 (NbE locl2'0 locl2'1 proof2').
(* Time Eval vm_compute in test2. *)
(* Time Eval vm_compute in test2'. *)

(** Example 4': verifying reduction for mu *)
Definition cmd4' := cm (mu gamma (cm (tvar y) (evar gamma))) (evar beta).
Definition proof4' : proof_cmd cmd4' ((y,ATOM)::nil) ((beta,ATOM)::nil).
Proof.
  apply Cut with (ATOM).
  apply Mu.
  apply Cut with (ATOM).
  apply AxR.
  left;reflexivity.
  apply AxL.
  left;reflexivity.
  apply AxL.
  left;reflexivity.
Defined.
Definition locl40 : locl_cxt_trm ((y,ATOM)::nil).
Proof.
  simpl.
  auto using ATOMlocl.
Defined.
Definition locl41 : locl_cxt_ect ((beta,ATOM)::nil).
Proof.
  simpl.
  auto using ATOMlocl.
Defined.
Definition test4' := projT1 (NbE locl40 locl41 proof4').
(* Time Eval vm_compute in test4'. *)

(** Example 5: verifying reduction for conjunction 1 *)
Definition cmd5 := cm (paire (tvar x) (tvar z)) (projl (evar beta)).
Definition proof5 : proof_cmd cmd5 ((x,ATOM)::(z,ATOM)::nil) ((beta,ATOM)::nil).
Proof.
  apply Cut with (Conj (ATOM) (ATOM)).
  apply ConjR.
  apply AxR.
  left;reflexivity.
  apply AxR.
  right;left;reflexivity.
  apply ConjLL.
  apply AxL.
  left;reflexivity.
Defined.
Definition locl50 : locl_cxt_trm ((x,ATOM)::(z,ATOM)::nil).
Proof.
  simpl.
  auto using ATOMlocl.
Defined.
Definition locl51 : locl_cxt_ect ((beta,ATOM)::nil).
Proof.
  simpl.
  auto using ATOMlocl.
Defined.
Definition test5 := projT1 (NbE locl50 locl51 proof5).
(* Time Eval vm_compute in test5. *)

(** Example 6: verifying reduction for conjunction 2 *)
Definition cmd6 := cm (paire (tvar x) (tvar z)) (projr (evar beta)).
Definition proof6 : proof_cmd cmd6 ((x,ATOM)::(z,ATOM)::nil) ((beta,ATOM)::nil).
Proof.
  apply Cut with (Conj (ATOM) (ATOM)).
  apply ConjR.
  apply AxR.
  left;reflexivity.
  apply AxR.
  right;left;reflexivity.
  apply ConjLR.
  apply AxL.
  left;reflexivity.
Defined.
Definition test6 := projT1 (NbE locl50 locl51 proof6).
(* Time Eval vm_compute in test6. *)

(** Example 7: verifying reduction for disjunction 1 *)
Definition cmd7 := cm (injl (tvar z)) (disj (evar gamma) (evar delta)).
Definition proof7 : proof_cmd cmd7 ((z,ATOM)::nil) ((gamma,ATOM)::(delta,ATOM)::nil).
Proof.
  apply Cut with (Disj (ATOM) (ATOM)).
  apply DisjRL.
  apply AxR.
  left;reflexivity.
  apply DisjL.
  apply AxL.
  left;reflexivity.
  apply AxL.
  right;left;reflexivity.
Defined.
Definition locl70 : locl_cxt_trm ((z,ATOM)::nil).
Proof.
  simpl.
  auto using ATOMlocl.
Defined.
Definition locl71 : locl_cxt_ect ((gamma,ATOM)::(delta,ATOM)::nil).
Proof.
  simpl.
  auto using ATOMlocl.
Defined.
Definition test7 := projT1 (NbE locl70 locl71 proof7).
(* Time Eval vm_compute in test7. *)

(** Example 8: verifying reduction for disjunction 2 *)
Definition cmd8 := cm (injr (tvar z)) (disj (evar gamma) (evar delta)).
Definition proof8 : proof_cmd cmd8 ((z,ATOM)::nil) ((gamma,ATOM)::(delta,ATOM)::nil).
Proof.
  apply Cut with (Disj (ATOM) (ATOM)).
  apply DisjRR.
  apply AxR.
  left;reflexivity.
  apply DisjL.
  apply AxL.
  left;reflexivity.
  apply AxL.
  right;left;reflexivity.
Defined.
Definition test8 := projT1 (NbE locl70 locl71 proof8).
(* Time Eval vm_compute in test8. *)

