(** Formalised proof of completeness of full Intuitionistic predicate
   logic with respect to Kripke-style models.

   Danko Ilik, January 2010
*)
Require Import stdlib_Type.
Require Import EqNat.

Set Implicit Arguments.
Unset Strict Implicit.

(** printing <= $\le$ #&le;# *)
(** printing ||-- $\Vdash$ #⊩# *)
(** printing ||- $\Vdash$ #⊩# *)

Open Scope type_scope.

Definition var : Set := nat.

(** Proof terms *)
Inductive term : Set :=
| Lam    : var -> term -> term
| Inl    : term -> term
| Inr    : term -> term
| Var    : var -> term
| App    : term -> term -> term
| Match  : term -> var -> term -> var -> term -> term
| QLam   : term -> term
| QApp   : term -> term
| QWit   : term -> term
| QMatch : term -> var -> term -> term.


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

Inductive formula := 
  Atom : predicate -> list indiv -> formula
| Imp  : formula -> formula -> formula
| Disj : formula -> formula -> formula
| All  : formula -> formula
| Ex   : formula -> formula.

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

Fixpoint subst (k:nat)(A:formula)(d:indiv) {struct A} : formula :=
  let subst_list := fix subst_list (l:list indiv) {struct l} : list indiv :=
    match l with
      | nil => nil
      | cons a' l' => cons (subst_indiv k a' d) (subst_list l')
    end in
  match A with
    | Ex A1      => Ex (subst (S k) A1 d) 
    | All A1     => All (subst (S k) A1 d) 
    | Disj A1 A2 => Disj (subst k A1 d) (subst k A2 d)
    | Imp A1 A2  => Imp (subst k A1 d) (subst k A2 d)
    | Atom P ld => 
      Atom P (subst_list ld)
  end.

Notation "A ^^ d" := (subst 0 A d) (at level 67).
Notation "A ^ x" := (subst 0 A (fvar x)).

(** A formula is [locl] ("locally closed") when all [bvar]s are bound
   by quantifiers (while there might be [fvar]s around) *)
Definition locl (A:formula) := forall k d, (subst k A d) = A.
Definition locli (d':indiv) := forall k d, (subst_indiv k d' d) = d'.

Definition context := list (var*formula).
Hint Unfold context.

(** Natural deduction system with cofinite quantification *)
Inductive proof : context -> term -> formula -> Set :=
| DisjIL Gamma t A B : proof Gamma t A -> proof Gamma (Inl t) (Disj A B)
  
| DisjIR Gamma t A B : proof Gamma t B -> proof Gamma (Inr t) (Disj A B)
  
| ImpI Gamma a t A B : 
  proof ((a,A)::Gamma) t B -> proof Gamma (Lam a t) (Imp A B)
  
| Hypo Gamma a A : In (a,A) Gamma -> proof Gamma (Var a) A
  
| DisjE Gamma a b e t u A B C :  
  proof Gamma e (Disj A B) -> 
  proof ((a,A)::Gamma) t C -> proof ((b,B)::Gamma) u C -> 
  proof Gamma (Match e a t b u) C
  
| ImpE Gamma t u A B : proof Gamma t (Imp A B) -> 
  proof Gamma u A -> proof Gamma (App t u) B
  
| AllI Gamma t A L : locl (All A) ->
  (forall x, x \notin L -> proof Gamma t (A^x)) ->
  proof Gamma (QLam t) (All A)
  
| AllE Gamma t A d : locli d ->
  proof Gamma t (All A) -> proof Gamma (QApp t) (A^^d)
  
| ExI Gamma t A d : locli d ->
  proof Gamma t (A^^d) -> proof Gamma (QWit t) (Ex A)
  
| ExE Gamma a e t A C L : locl (Ex A) ->
  proof Gamma e (Ex A) ->
  (forall x, x\notin L -> proof ((a,A^x)::Gamma) t C) ->
  proof Gamma (QMatch e a t) C
  .

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
    aforces : world -> predicate -> list indiv -> Set;
    aforces_mon : forall w P ld, @aforces w P ld -> forall w', wle w w' -> @aforces w' P ld
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
  Fixpoint sforces' (n:nat)(w:K)(A:formula) {struct n} : Type :=
    match n with
      | O => Empty_set
      | S m => 
        match A with
          | Atom P ld  => aforces w P ld
          | Imp A1 A2  => forall w', w <= w'-> Kont (sforces' m) w' A1 -> Kont (sforces' m) w' A2
          | Disj A1 A2 => Kont (sforces' m) w A1 + Kont (sforces' m) w A2
          | All A1     => forall w', w <= w' -> forall d, locli d -> Kont (sforces' m) w' (A1^^d)
          | Ex A1      => {d:indiv & (locli d) * Kont (sforces' m) w (A1^^d)}
        end
    end.

  Fixpoint depth (A:formula) : nat :=
    match A with
      | Atom _ _   => 1
      | Imp A1 A2  => S (max (depth A1) (depth A2))
      | Disj A1 A2 => S (max (depth A1) (depth A2))
      | All A1     => S (depth A1)
      | Ex A1      => S (depth A1)
    end.

  (** However, we can not define strong forcing as simply as when we had no quantifiers, because we need to do a recursion on the _complexity_ of a formula, not just its structure; we do that using the measure of [depth] above. *)
  Definition sforces (w:K)(A:formula) := sforces' (depth A) w A.
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
      intros C1 w1 w'w1 k.
      apply H with w'.
      assumption.
      intros C2 w2 w1w2 HA1n.
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
      intros C1 w1 ww1 k.
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
      intros C1 w1 ww1 k.
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

      intros.
      intros C1 w1 w'w1 k.
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
      intros C1 w1 ww1 k.
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
      intros C1 w1 w'w1 k.
      apply H with w'.
      assumption.
      intros C2 w2 w1w2 HA1n.
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
      intros C1 w1 ww1 k.
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
      intros C1 w1 ww1 k.
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

      intros.
      intros C1 w1 w'w1 k.
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
      intros C1 w1 ww1 k.
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

    Lemma Kont_invar : forall F1 F2:K->formula->Type, forall A,
      (forall w, F1 w A -> F2 w A) -> forall w, Kont F1 w A -> Kont F2 w A.
    Proof.
      intros F1 F2 A HF1F2.
      intros w HF1.
      intros C1 w1 ww1 k1.
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

  Notation "w ||+ A " := (sforces w A) (at level 70).
  Notation "w ||- A " := (Kont sforces w A) (at level 70).

  Fixpoint forces_cxt (w:K)(Gamma:context) : Type :=
    match Gamma with
      | nil => unit
      | cons aA Gamma' => prod (w ||- (snd aA)) (forces_cxt w Gamma')
    end.

  Notation " w ||-- Gamma" := (forces_cxt w Gamma) (at level 70).

  Lemma sforces_mon : forall A w, w ||+ A  -> forall w', w <= w' -> w' ||+ A .
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
    eauto using wle_trans.

    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    destruct H1 as [d [Hd H]].
    exists d.
    split; [assumption|].
    eauto using wle_trans.
  Defined.

  Definition ret {w A} : w ||+ A -> w ||- A.
  Proof.
    intros H.
    intros C w1 w_w1 k.
    apply k.
    apply wle_refl.
    apply sforces_mon with w.
    assumption.
    assumption.
  Defined.

  Definition bind {w A B} : (forall w', wle w w' -> w' ||+ A -> w' ||- B) -> w ||- A -> w ||- B.
  Proof.
    intros f a.
    intros C w1 ww1 k.
    apply a.
    assumption.
    intros w2 w1w2 a'.
    apply (f w2).
    eauto using wle_trans.
    exact a'.
    apply wle_refl.
    eauto using wle_trans.
  Defined.

  Lemma forces_mon : forall A w, w ||- A -> forall w', w <= w' -> w' ||- A.
  Proof.
    induction A;
      intros;
        eauto using wle_trans.
  Defined.

  Lemma forces_cxt_mon : forall Gamma w, w ||-- Gamma -> forall w', w <= w' -> w' ||-- Gamma.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros.
    destruct X0.
    split; eauto using wle_trans,forces_mon.
  Defined.

  Lemma forces_cxt_In : forall w x A Gamma, In (x, A) Gamma -> w ||-- Gamma -> w ||- A.
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

  Fixpoint lsubst (T:Type)(k:nat)(l:list (T*formula))(d:indiv) :=
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

  Fixpoint fvar_swap_typ (x:var_free)(A:formula)(y:var_free) {struct A} : formula :=
    let fvar_swap_list := fix fvar_swap_list 
      (l:list indiv) {struct l} : list indiv :=
      match l with 
        | nil => nil
        | cons a' l' => cons (fvar_swap_indiv x a' y) (fvar_swap_list l')
      end in
    match A with
      | Ex A1      => Ex   (fvar_swap_typ x A1 y) 
      | All A1     => All  (fvar_swap_typ x A1 y) 
      | Disj A1 A2 => Disj (fvar_swap_typ x A1 y) (fvar_swap_typ x A2 y)
      | Imp A1 A2  => Imp  (fvar_swap_typ x A1 y) (fvar_swap_typ x A2 y)
      | Atom P ld => 
        Atom P (fvar_swap_list ld)
    end.

  Fixpoint fvar_swap_cxt (T:Type)(x:var_free)(l:list (T*formula))(y:var_free) :=
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

  Fixpoint fvar_appears_typ (x:var_free)(A:formula) {struct A} : bool :=
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
      | Disj A1 A2 => orb (fvar_appears_typ x A1) (fvar_appears_typ x A2)
      | Imp A1 A2  => orb (fvar_appears_typ x A1) (fvar_appears_typ x A2)
      | Atom P ld  => fvar_appears_list x ld
         end.

  Fixpoint fvar_appears_cxt (T:Type)(x:var_free)(l:list (T*formula)) : bool :=
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
    rewrite swap_appears_not_typ.
    reflexivity.
    assumption.

    simpl.
    intros.
    rewrite swap_appears_not_typ.
    reflexivity.
    assumption.
  Defined.

  Lemma swap_appears_not_cxt : forall T, forall GD:list (T*formula), forall x,
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

  Fixpoint FV_typ (A:formula) {struct A} : list var_free :=
    let FV_indiv_list := 
      fix FV_indiv_list (l:list indiv) {struct l} : list var_free :=
      match l with
        | nil => nil
        | cons d' l' => List.app (FV_indiv d') (FV_indiv_list l')
      end in
    match A with
      | Ex A1      => FV_typ A1
      | All A1     => FV_typ A1
      | Disj A1 A2 => (FV_typ A1) ++ (FV_typ A2)
      | Imp A1 A2  => (FV_typ A1) ++ (FV_typ A2)
      | Atom P vl  => FV_indiv_list vl
    end.

  Fixpoint FV_cxt (T:Type)(l:list (T*formula)) {struct l} : list var_free :=
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
    auto.

    simpl.
    intros.
    auto.
  Defined.

  Lemma fvar_swap_cxt_idem : forall T:Type, forall GD:list (T*formula), 
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

  Lemma fvar_swap_typ_idem : forall C:formula, 
    forall x y, x\notin FV_typ C ->
      fvar_swap_typ x C y = C.
  Proof.
    intros.
    rewrite swap_appears_not_typ.
    reflexivity.
    apply notin_FV_not_appears.
    assumption.
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
    (forall Gamma t A, proof Gamma t A -> 
      let Gamma' := fvar_swap_cxt x Gamma y in
      let A' := fvar_swap_typ x A y in
        proof Gamma' t A').
  Proof.
    intros x y.
    apply proof_rect.

    intros; simpl in *; constructor; auto.

    intros; simpl in *; constructor; auto.

    intros; simpl in *; constructor; auto.

    intros Gamma a A IH.
    constructor.
    induction Gamma.
    inversion IH.
    simpl in IH.
    destruct IH.
    rewrite e.
    simpl.
    auto.
    simpl.
    auto.

    intros.
    simpl in *.
    apply DisjE with (fvar_swap_typ x A y) (fvar_swap_typ x B y);
      auto.

    intros; simpl in *.
    apply ImpE with (fvar_swap_typ x A y); auto.

    intros; simpl in *.
    apply AllI with (x::L).
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
    rewrite subst_fvar_swap.
    apply AllE.
    unfold locli.
    intros.
    replace k with (plus k 0).
    apply locli_fvar_swap.
    intros.
    apply l.
    apply Arith.Plus.plus_0_r.
    assumption.

    intros; simpl in *.
    rewrite subst_fvar_swap in H.
    apply ExI with (fvar_swap_indiv x d y).
    unfold locli.
    intros.
    replace k with (plus k 0).
    apply locli_fvar_swap.
    intros.
    apply l.
    apply Arith.Plus.plus_0_r.
    assumption.

    intros; simpl in *.
    apply ExE with (fvar_swap_typ x A y) (x::L).
    replace (Ex (fvar_swap_typ x A y)) with (fvar_swap_typ x (Ex A) y);
      [idtac | reflexivity].
      unfold locl.
      intros.
      replace k with (plus k 0).
      apply locl_fvar_swap.
      intros.
      apply l.
      apply Arith.Plus.plus_0_r.
    assumption.
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

  Lemma proof_trm_quant_invar : forall Gamma A,
    let L := FV_typ A ++ FV_cxt Gamma in
    (forall x, x\notin L ->
      sigT (fun t:term => proof Gamma t (A^x))) ->
    sigT (fun s:term => forall y, y\notin L -> proof Gamma s (A^y)).
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
    intros y Hy.
    unfold L in Hy.
    apply notin_app in Hy.
    destruct Hy as [Hy1 Hy2].
    assert (p' := (fvar_swap_proof x y) _ _ _ p).
    simpl in p'.
    rewrite fvar_swap_cxt_idem in p'; auto.
    rewrite subst_fvar_swap_lem in p'; auto.
  Defined.

  Lemma proof_trm_quant_invar' : forall Gamma a A C,
    let L := FV_typ C ++ FV_cxt ((a,A)::Gamma) in
    (forall x, x\notin L ->
      sigT (fun t:term => proof ((a,A^x)::Gamma) t C)) ->
    sigT (fun s:term => forall y, y\notin L -> proof ((a,A^y)::Gamma) s C).
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
    simpl in Hx2.
    apply notin_app in Hx2.
    destruct Hx2 as [Hx2 Hx3].
    intros y Hy.
    unfold L in Hy.
    apply notin_app in Hy.
    destruct Hy as [Hy1 Hy2].
    simpl in Hy2.
    apply notin_app in Hy2.
    destruct Hy2 as [Hy2 Hy3].
    assert (p' := (fvar_swap_proof x y) _ _ _ p).
    simpl in p'.
    rewrite fvar_swap_cxt_idem in p'; auto.
    rewrite (fvar_swap_typ_idem y Hx1) in p'.
    rewrite subst_fvar_swap_lem in p'; auto.
  Defined.

  Lemma proof_subst_lem1 : forall Gamma A, locl (All A) ->
    let L := FV_typ A ++ FV_cxt Gamma in
    (forall x, x\notin L -> {t:term & proof Gamma t (A^x)}) ->
    forall d, locli d -> {t:term & proof Gamma t (A^^d)}.
  Proof.
    intros Gamma A Hlocl L H d Hd.
    apply proof_trm_quant_invar in H.
    destruct H as [s Hs].
    apply AllI in Hs.
    assert (Hs' := AllE Hd Hs).
    exists (QApp (QLam s)).
    assumption.
    assumption.
  Defined.

  Lemma proof_subst_lem2 : forall Gamma A, locl (Ex A) ->
    let L := FV_typ A ++ FV_cxt Gamma in
      {d:indiv & locli d * {t:term & proof Gamma t (A^^d)}} ->
      {x:var_free & (x\notin L) * {t:term & proof Gamma t (A^x)}}.
  Proof.
    intros Gamma A Hlocl L H.
    destruct H as [d [Hd [t Ht]]].
    apply ExI in Ht.
    destruct (fresh_fvar L) as [x Hx].
    exists x.
    split.
    assumption.
  Admitted.
End subst_lemmas.

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

  Definition Kaforces (w:Kworld)(p:predicate)(ld:list indiv) : Set := 
    Normal_term (@Atom p ld) w.
  Hint Unfold Kaforces.

  Notation "w <= w'" := (Kle w w').

  Lemma proof_mon : forall A t w, proof w t A -> 
    forall w', w <= w' -> proof w' t A.
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

    intros.
    apply AllI with L.
    assumption.
    intros.
    apply X0.
    assumption.
    assumption.

    intros.
    apply AllE.
    assumption.
    apply IHp;auto.

    intros.
    apply ExI with d.
    assumption.
    apply IHp.
    assumption.

    intros.
    apply ExE with A L.
    assumption.
    auto.
    intros.
    apply X0 with x.
    assumption.
    apply cons_incl_head.
    assumption.
  Defined.

  Lemma Kaforces_mon : forall w P ld, @Kaforces w P ld ->
    forall w', Kle w w' -> @Kaforces w' P ld.
  Proof.
    intros w P ld H.
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

  Notation "w <= w'" := (Kle w w').
  Notation "w ||+ A " := (F w A) (at level 70).
  Notation "w ||- A " := (Kont F w A) (at level 70).
  Notation " w ||-- Gamma " := (@forces_cxt K w Gamma) (at level 70).

  (** The proof of completeness is via a reify-reflect pair, by induction on [n] i.e. by induction on the complexity of the formula [A]. [fresh] is a fresh variable counter that is increased at every recursive call. *)
  Theorem Kcompleteness : forall (n:nat)(A:formula), le (depth A) n -> locl A -> 
    forall (w:K)(fresh:nat),
      (Kont F w A -> {t:term & proof w t A}) *
      (forall e:term, proof w e A -> Kont F w A).
  Proof.
    induction n.

    intros A Hn.
    destruct A;inversion Hn.
    intros A HSn Hlocl.
    intros.
    destruct A.

    (* Atomic formula *****************)
    split.

    (* λc. run c *)
    intros c.
    apply c.
    apply wle_refl.
    simpl.
    intros w2 w_w2 H.
    apply H.

    (* λe. ret e *)
    intros e He.
    apply ret.
    simpl.
    exists e.
    assumption.

    (* Implication ********************)
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

    (* λc.c(λf.λx.↓² f (↑¹_(x,A1),… x) *)
    intro c.
    apply c.
    apply wle_refl.
    intros w2 le_w2 f.
    set (w' := (fresh,A1)::w2).
    assert (f' := sforces_correct_Imp f).
    clear f.
    rename f' into f.
    assert (Hf : Kont F w' A2).
      apply f.
      unfold w'.
      red;simpl;red;auto.
      apply (snd (IHn _ Hdepth1 Hlocl1 w' (S fresh))) with (Var fresh).
      unfold w'.
      constructor.
      auto.
    apply (fst (IHn _ Hdepth2 Hlocl2 w' (S fresh))) in Hf.
    destruct Hf as [t' p'].
    exists (Lam fresh t').
    apply ImpI.
    unfold w' in p'; simpl in p'.
    assumption.
  
    (* λe.ret(λa.↑² App e (↓¹ a)) *)
    intros e He.
    apply ret.
    apply sforces_correct_Imp'.
    intros w' le_w' Ha1.
    apply (fst (IHn _ Hdepth1 Hlocl1 w' (S fresh))) in Ha1.
    destruct Ha1 as [a1 Ha1].
    apply (snd (IHn _ Hdepth2 Hlocl2 w' (S fresh))) with (App e a1).
    apply ImpE with A1.
    eauto using proof_mon.
    assumption.

    (* Disjunction ************************)
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

    (* λc.c(λH.match H with inl H₁ => ↓¹ H₁ | inr H₂ => ↓² H₂ *)
    intro c.
    apply c.
    apply wle_refl.
    intros w2 ww2 Hdisj.
    unfold F in Hdisj.
    apply sforces_correct_Disj in Hdisj.
    destruct Hdisj as [HA1 | HA2].
    apply (fst (IHn _ Hdepth1 Hlocl1 _ (S fresh))) in HA1.
    destruct HA1 as [t1 Ht1].
    exists (Inl t1).
    constructor.
    assumption.
    apply (fst (IHn _ Hdepth2 Hlocl2 _ (S fresh))) in HA2.
    destruct HA2 as [t2 Ht2].
    exists (Inr t2).
    constructor.
    assumption.

    (* λc.λk. Match e x (k (inl ↑¹_(x,A₁),… x)) x (k (inr ↑²_(x,A2),… x)) *)
    intros e He.
    intros C w' le_w' k.
    simpl in k.
    assert (k' : forall w2 : Kworld, w' <= w2 -> Kont F w2 A1 + Kont F w2 A2 -> KX w2 C).
      clear -k.
      intros w2 w'w2 HDisj.
      apply sforces_correct_Disj' in HDisj.
      auto.
    clear k.
    rename k' into k.
    set (w1 := (fresh,A1)::w').
    assert (branch1 : Kont F w1 A1).
    apply (snd (IHn _ Hdepth1 Hlocl1 w1 (S fresh))) with (Var fresh).
    constructor.
    unfold w1.
    auto.
    set (w2 := (fresh,A2)::w').
    assert (branch2 : Kont F w2 A2).
    apply (snd (IHn _ Hdepth2 Hlocl2 w2 (S fresh))) with (Var fresh).
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

    (* Universal quantifier ******************************)
    split.

    intro c.
    set (L := FV_typ A ++ FV_cxt w).
    assert (H0 : forall y:var_free, y\notin L -> KX w (A^y)).
    intros y Hy.
    apply c.
    apply wle_refl.
    intros w2 ww2 HAll.
    assert (HAll':= sforces_correct_All HAll).
    clear HAll.
    simpl.
    assert (HAd : Kont F w2 (A^y)).
    apply HAll'.
    apply wle_refl.
    apply locli_fvar.
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
    apply (fst (IHn _ Hdepth' Hlocl' _ (S fresh))) in HAd.
    destruct HAd as [td Htd].
    exists td.
    assumption.
    apply proof_trm_quant_invar in H0.
    destruct H0 as [s Hs].
    exists (QLam s).
    apply AllI with L.
    assumption.
    unfold L.
    assumption.

    intros e He.
    apply ret.
    apply sforces_correct_All'.
    intros w1 ww1 d Hd.
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
    apply (snd (IHn _ Hdepth' Hlocl' _ (S fresh))) with (QApp e).
    apply AllE.
    assumption.
    apply proof_mon with w.
    assumption.
    assumption.

    (* Existential quantifier ****************************)
    split.

    intro c.
    apply c.
    apply wle_refl.
    intros w2 ww2 HEx.
    unfold F in HEx.
    apply sforces_correct_Ex in HEx.
    destruct HEx as [d [Hd HAd]].
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
    apply (fst (IHn _ Hdepth' Hlocl' _ (S fresh))) in HAd.
    destruct HAd as [t Ht].
    exists (QWit t).
    apply ExI with d.
    assumption.
    assumption.

    intros e He.
    intros C w' le_w' k.
    simpl in k.
    assert (k' : forall w2 : Kworld, w' <= w2 -> 
      sigT (fun (d:indiv) => locli d * Kont (K:=K) (sforces (K:=K)) w2 (A ^^ d))
      -> KX w2 C).
      clear -k.
      intros w2 w'w2 HEx.
      apply sforces_correct_Ex' in HEx.
      auto.
    clear k.
    rename k' into k.
    set (w1 := fun d => fun (w:@world K) => ((fresh, A^^d)::w):Kworld).
    assert (ww1 : forall d w0, wle w0 (w1 d w0)).
      intro d.
      unfold w1.
      right.
      assumption.
    assert (Hdepth' : forall d0, le (depth (A^^d0)) n).
      clear -HSn.
      intro d0.
      simpl in HSn.
      rewrite depth_subst.
      apply le_S_n in HSn.
      assumption.
    assert (Hlocl' : forall d0, locli d0 -> locl (A^^d0)).
      apply locl_locli_subst''.
      assumption.
    assert (branch1 : forall d, locli d -> Kont F (w1 d w) (A^^d)).
    intros d Hd.
    apply (snd (IHn _ (Hdepth' d) (Hlocl' d Hd) (w1 d w) (S fresh))) with (Var fresh).
    constructor.
    unfold w1.
    left; reflexivity.
    assert (H0 : {s:term & forall y : var_free,
      y \notin FV_typ C ++ FV_cxt ((fresh,A)::w') -> proof ((fresh,A^y)::w') s C}).
    apply proof_trm_quant_invar'.
    intros x Hx.
    assert ({t : term & proof (w1 (fvar x) w') t C}).
    apply k.
    apply ww1.
    exists (fvar x).
    split.
    apply locli_fvar.
    apply (snd (IHn _ (Hdepth' (fvar x)) (Hlocl' (fvar x) (locli_fvar x)) (w1 (fvar x) w') (S fresh))) with (Var fresh).
    constructor.
    unfold w1.
    left;reflexivity.
    unfold w1 in H.
    assumption.
    destruct H0 as [s Hs].
    exists (QMatch e fresh s).
    apply ExE with A (FV_typ C ++ FV_cxt ((fresh,A)::w')).
    assumption.
    apply proof_mon with w.
    assumption.
    assumption.
    clear -Hs.
    intros x Hx.
    auto.
  Defined.
End Universal_Model_and_Completeness.
