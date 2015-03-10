(** A proof that every filter F over a countable boolean algebra can
   be extended to a complete filter equiconsistent with
   F. (Ultrafilter Theorem)

   This file is used by the completeness theorem from classcomp.v, but
   it can be used in other contexts, it is a standalone module.
 *)
Require Import Ring.
Require Import List.
Require Import Compare_dec.
Require Import Setoid.
Require Import Morphisms.

Set Implicit Arguments.

(** Definition of Countable Boolean Algebra (over a setoid) *)
Module Type CBA.
  Parameter Inline B:Set.
  Parameters (meet join:B -> B -> B)(bott top:B)(compl:B -> B).
  Parameter eq_B : B  ->  B  ->  Prop.

  Notation "x == y" := (eq_B x y) (at level 70, no associativity).
  Axiom eq_B_refl  : reflexive B eq_B.
  Axiom eq_B_symm  : symmetric B eq_B.
  Axiom eq_B_trans : transitive B eq_B.

  Axiom eq_B_meet_morph : Proper (eq_B ==> eq_B ==> eq_B) meet.
  Axiom eq_B_join_morph : Proper (eq_B ==> eq_B ==> eq_B) join.

  Axiom enum : B -> nat.
  Axiom countable : forall x y, enum x = enum y -> x = y.

  Axiom meet_idem : forall x, meet x x == x.
  Axiom join_idem : forall x, join x x == x.
  Axiom meet_comm : forall x y, meet x y == meet y x.
  Axiom join_comm : forall x y, join x y == join y x.
  Axiom meet_assoc : forall x y z, meet x (meet y z) == meet (meet x y) z.
  Axiom join_assoc : forall x y z, join x (join y z) == join (join x y) z.
  Axiom meet_absorb : forall x y, meet x (join x y) == x.
  Axiom join_absorb : forall x y, join x (meet x y) == x.
  Axiom meet_distrib : forall x y z, 
    meet (join x y) z == join (meet x z) (meet y z).
  Axiom join_distrib : forall x y z, 
    join (meet x y) z == meet (join x z) (join y z).
  Axiom meet_bott : forall x, meet bott x == bott.
  Axiom join_bott : forall x, join bott x == x.
  Axiom meet_top : forall x, meet top x == x.
  Axiom join_top : forall x, join top x == top.
  Axiom meet_compl : forall x, meet x (compl x) == bott.
  Axiom join_compl : forall x, join x (compl x) == top.

  (** We also need that identity [id_B] is decidable in 1 place. Note that this is not that [id_B] is definitional equality, it has nothing to do with the equality of the setoid. *)
  Axiom id_B_dec : forall x y : B, {x = y}+{x <> y}.
  Axiom id_B_dec_right : forall (x y:B), x<>y ->
    exists H:x<>y, id_B_dec x y = right (x=y) H.
  Axiom id_B_dec_left : forall x:B, 
    exists H:x=x, id_B_dec x x = left (x<>x) H.

End CBA.

Module filter_completion (cba : CBA).
  Export cba.
  
  Add Relation B eq_B
    reflexivity proved by eq_B_refl
    symmetry proved by eq_B_symm
    transitivity proved by eq_B_trans
  as eq_B_relation.

  Add Morphism meet with signature eq_B ==> eq_B ==> eq_B as meet_morphism. 
    exact eq_B_meet_morph.
  Qed.

  Add Morphism join with signature eq_B ==> eq_B ==> eq_B as join_morphism. 
    exact eq_B_join_morph.
  Qed.

  (** A boolean algebra is also a semi-ring, useful because Coq can automatically solve equations for in such cases. *)
  Theorem CBA_semiring : semi_ring_theory bott top join meet eq_B.
  Proof.
    constructor.
    apply join_bott.
    apply join_comm.
    apply join_assoc.
    apply meet_top.
    apply meet_bott.
    apply meet_comm.
    apply meet_assoc.
    apply meet_distrib.
  Qed.

  Add Ring B_semiring : CBA_semiring.

  (** Lattice as an algebra is equivalent to a lattice as a poset, so
      we can define an ordering. *)
  Definition leq := fun x y => meet x y == x.

  Lemma leq' : forall x y, leq x y <-> join x y == y.
  Proof.
    intros.
    intuition.
    unfold leq in *.
    rewrite <- H .
    rewrite meet_comm.
    rewrite join_comm.
    apply join_absorb.
    unfold leq.
    rewrite <- H .
    apply meet_absorb.
  Qed.

  Delimit Scope B_scope with B.
  Bind Scope B_scope with B.
  Arguments Scope B [nat_scope].
  Open Scope B_scope.

  Notation "x && y" := (meet x y) (at level 40, left associativity) : B_scope.
  Notation "- x" := (compl x) (at level 35, right associativity) : B_scope.
  Notation "x || y" := (join x y) (at level 50, left associativity) : B_scope.
  Notation "x <= y" := (leq x y) : B_scope.

  (** When a subset F of B is a filter *)
  Record Filter (F:B -> Prop) : Prop := {
    nonempty : exists x:B, F x;
    upwards_closed : forall x y:B, F x -> leq x y -> F y;
    meet_closed : forall x y:B, F x -> F y -> F (meet x y)
  }.

  (** The closure of the subset X, [up X], is the least filter containing X.
     
     Conjuction of finite (but arbitrary) lenght is represented by the
     List operation fold_left. *)
  Definition up (X:B -> Prop) := fun z:B =>
    exists n:nat, exists ys:list B, length ys = n /\ 
      fold_left (fun (a:Prop)(b:B) => and a (X b)) ys True /\
      leq (fold_left meet ys top) z.

  Definition union_singl (F:B -> Prop)(x:B) := fun b:B => F b \/ b=x.

  Definition inconsistent (F:B -> Prop) := F bott.

  Definition equiconsistent (F G:B -> Prop) := inconsistent F <-> inconsistent G.

  Definition element_complete (F:B -> Prop)(x:B) := 
    equiconsistent F (up (union_singl F x)) -> F x.

  (** This notion of completeness of a filter is the key to having a constructive proof. This notion is constructivelly weaker than, but classically equivalent to, the more usual notion: either x in F, or ~x in F. *)
  Definition complete (F:B -> Prop) := forall x:B, element_complete F x.

  Lemma leq_refl : forall x:B, x <= x.
  Proof.
    intro x.
    unfold leq.
    apply meet_idem.
  Qed.

  Lemma leq_trans : forall x y z:B, leq x y -> leq y z -> leq x z.
  Proof.
    unfold leq.
    intros.
    rewrite <- H.
    ring [H0].
  Qed.

  Lemma eq_B_leq : forall x y:B, x==y -> x <= y.
  Proof.
    intros x y.
    unfold leq.
    intro H0.
    rewrite H0.
    apply meet_idem.
  Qed.

  Add Morphism leq with signature eq_B ==> eq_B ==> iff as leq_morphism. 
  Proof.
    intros x y H x0 y0 H0.
    split.
    intro.
    apply leq_trans with x.
    apply eq_B_leq.
    symmetry.
    assumption.
    apply leq_trans with x0.
    assumption.
    apply eq_B_leq.
    assumption.
    intro.
    apply leq_trans with y.
    apply eq_B_leq.
    assumption.
    apply leq_trans with y0.
    assumption.
    apply eq_B_leq.
    symmetry.
    assumption.
  Qed.

  Lemma meet_leq_compat : forall a b c d, a <= b -> c <= d -> a && c  <=  b && d.
  Proof.
    unfold leq.
    intros.
    ring [H H0].
  Qed.

  (** The next few lemmas with names "fold_left*" and "lemma*" are used to handle the representation of a finite number of conjunctions by a list. *)

  Lemma fold_left_meet_morphism : forall x y bs, x==y -> 
    fold_left meet bs x == fold_left meet bs y.
  Proof.
    intros.
    generalize dependent x.
    generalize dependent y.
    induction bs.
    auto.
    simpl.
    intros.
    apply IHbs.
    ring [H].
  Qed.

  Lemma fold_left_meet_cons : forall bs b, fold_left meet (cons b bs) top == b && (fold_left meet bs top).
  Proof.
    simpl.
    induction bs.
    simpl.
    intro.
    ring.
    intro.
    simpl.
    rewrite IHbs.
    rewrite meet_assoc.
    transitivity (fold_left meet bs (top && (b && a))).
    apply fold_left_meet_morphism.
    rewrite <- meet_assoc.
    reflexivity.
    apply IHbs.
  Qed.

  Lemma fold_left_impl : forall (X:B -> Prop)(xs:list B)(Q P:Prop), (Q -> P) -> fold_left (fun (a : Prop) (b : B) => a /\ X b) xs Q -> fold_left (fun (a : Prop) (b : B) => a /\ X b) xs P.
  Proof.
    induction xs.
    simpl.
    auto.
    simpl.
    intros.
    apply IHxs with (Q /\ X a); intuition.
  Qed.

  Lemma fold_left_app_lem : forall xs ys,
    fold_left meet (xs ++ ys) top == 
    fold_left meet xs top && fold_left meet ys top.
  Proof.
    intros xs ys.
    induction xs.
    simpl.
    ring.
    rewrite <- app_comm_cons.
    rewrite fold_left_meet_cons.
    rewrite fold_left_meet_cons.
    rewrite <-  meet_assoc.
    rewrite IHxs.
    reflexivity.
  Qed.

  Lemma up_filter : forall X:B -> Prop, Filter (up X).
  Proof.
    intro X.
    constructor.

    (* up X is nonempty, because it contains at least top *) 
    exists top.
    unfold up.
    exists 0.
    exists (@nil B).
    simpl.
    intuition.
    apply leq_refl.

    (* up X is upwards_closed, because if x \in up X and x <= y then we
        can use the same sequence of witnesses for x's membership to X
        and the transitivity of <= to conclude that y \in up X. *)
    intros.
    destruct H as [n [ys [H1 [H2 H3]]]].
    exists n.
    exists ys.
    intuition.
    apply leq_trans with x; auto.

    (* up X is meet-closed, by lemma meet_leq_compat. *)
    intros.
    unfold up in *.
    destruct H as [n [xs [H1 [H2 H3]]]].
    destruct H0 as [m [ys [H4 [H5 H6]]]].
    exists (n+m).
    exists (xs++ys).
    rewrite app_length.
    rewrite fold_left_app.
    intuition.
    apply fold_left_impl with True; auto.

    rewrite fold_left_app_lem.
    apply meet_leq_compat; assumption. 
  Qed.

  Lemma filter_top : forall F:B -> Prop, Filter F -> F top.
  Proof.
    intros.
    destruct (nonempty H) as [w Fw].
    apply upwards_closed with w; auto.
    unfold leq.
    ring.
  Qed.

  Lemma lemma3 : forall (T:Type)(Hdec:forall x y : T, {x = y} + {x <> y})(x:T)(ys:list T),
    incl ys (x :: remove Hdec x ys).
  Proof.
    intros.
    induction ys.
    simpl.
    unfold incl.
    intros.
    absurd (In a nil).
    apply in_nil.
    assumption.
    simpl.
    unfold incl in *.
    intros.
    assert (H' := in_inv H).
    case H'.
    intro Hr.
    rewrite <- Hr.
    case (Hdec x a).
    intro.
    rewrite e.
    apply in_eq.
    intro.
    apply in_cons.
    apply in_eq.
    intro.
    assert (IH:=IHys _ H0).
    case (Hdec x a).
    intro.
    assumption.
    intro.
    simpl.
    simpl in IH.
    intuition.
  Qed.
    
  Lemma lemma2 : forall A C:list B, incl A C -> 
    leq (fold_left meet C top) (fold_left meet A top).
  Proof.
    induction A.

    simpl.
    intros.
    unfold leq.
    ring.

    intros.
    rewrite fold_left_meet_cons.
    assert (IHA' := IHA C).

    (* a is in C, so foldleft C = a && foldleft C, by one rewrite <- meet_idem *)

    apply leq_trans with (a && fold_left meet C top).
    unfold incl in H.
    assert (H' := H a (in_eq a A)).
      clear -H'.
      induction C.
      absurd (In a nil); auto.
      simpl In in H'.
      case H'.
      intro Ha.
      rewrite Ha.
      rewrite fold_left_meet_cons.
      rewrite meet_assoc.
      rewrite meet_idem.
      apply leq_refl.
      intro Ca.
      rewrite fold_left_meet_cons.
      rewrite meet_assoc.
      rewrite (meet_comm a a0).
      rewrite <- meet_assoc.
      apply meet_leq_compat.
      apply leq_refl.
      auto.
    apply meet_leq_compat.
    apply leq_refl.
    apply IHA'.
    apply incl_tran with (a::A).
    apply incl_tl.
    apply incl_refl.
    assumption.
  Qed.

  (* membership in a filter is also a morphism, but how to declare as such? *)
  Lemma filter_memb_morph : forall F, Filter F -> 
    forall (x y:B), x==y -> F x -> F y.
  Proof.
    intros.
    apply upwards_closed with x; auto.
    apply eq_B_leq.
    assumption.
  Qed.

  Lemma lemma4 : forall xs F, Filter F ->
    fold_left (fun (A : Prop) (b : B) => A /\ F b) xs True ->
    F (fold_left meet xs top).
  Proof.
    intros.
    induction xs.
    simpl in *.
    apply (@filter_top F).
    assumption.
    apply filter_memb_morph with (a && fold_left meet xs top); auto.
    rewrite fold_left_meet_cons.
    reflexivity.
    simpl in H0.
    apply (@meet_closed F).
    assumption.
      induction xs.
      simpl in *.
      intuition.
      apply IHxs0.
      simpl in H0.
      apply fold_left_impl with (((True /\ F a) /\ F a0)).
      intuition.
      assumption.
      intro.
      assert (Hr := fold_left_meet_cons xs a0).
      apply upwards_closed with ((a0 && fold_left meet xs top)).
      assumption.
      apply filter_memb_morph with (fold_left meet (a0 :: xs) top).
      assumption.
      assumption.
      apply IHxs.
      apply fold_left_impl with ((True /\ F a)).
      intuition.
      assumption.
      unfold leq.
      rewrite <- meet_assoc.
      rewrite meet_idem.
      reflexivity.
    apply IHxs.
    apply fold_left_impl with ((True /\ F a)).
    intuition.
    assumption.
  Qed.

  Lemma lemma61 : forall (f:B -> Prop)(l:list B)(basecase:Prop)(P:Prop),
    fold_left (fun (R:Prop)(x:B) => R /\ (f x)) l (basecase /\ P) -> 
    (fold_left (fun (R:Prop)(x:B) => R /\ (f x)) l basecase) /\ P.
  Proof.
    induction l.
    simpl in *.
    auto.
    simpl.
    clear -IHl.
    intros.
    apply IHl.
    apply fold_left_impl with ((basecase /\ P) /\ f a).
    intro.
    intuition.
    assumption.
  Qed.

  Lemma lemma62 : forall (f:B -> Prop)(l:list B)(basecase:Prop)(P:Prop),
    (fold_left (fun (R:Prop)(x:B) => R /\ (f x)) l basecase) /\ P ->
    fold_left (fun (R:Prop)(x:B) => R /\ (f x)) l (basecase /\ P). 
  Proof.
    induction l.
    simpl in *.
    auto.
    simpl.
    clear -IHl.
    intros.
    apply fold_left_impl with ((basecase /\ f a) /\ P).
    intro.
    intuition.
    apply IHl.
    assumption.
  Qed.

  Lemma lemma5 : forall (X:B -> Prop)(ys:list B)(n:nat)
    (H:fold_left (fun (P : Prop) (x : B) => P /\ (X x \/ 
      (enum x = n /\ equiconsistent X (up (union_singl X x))))) ys True),
    fold_left (fun (P : Prop) (x : B) => P /\ X x) ys True \/
    (exists x_n : B,
      In x_n ys /\
      n = enum x_n /\
      fold_left (fun (P : Prop) (x : B) => P /\ X x) (remove id_B_dec x_n ys) True /\
      equiconsistent X (up (union_singl X x_n))
    ).
  Proof.
    fix 2.
    induction ys.
    intros.
    simpl in *.
    left.
    auto.
    intros.
    simpl in H.

    assert (H' := lemma61 _ _ _ _ H).
    destruct H' as [H'' case_a ].
    assert (H5 := lemma5 _ _ _ H'').
    clear - H5 case_a IHys.
    simpl.
    case H5.
    (* case 1*)
    intro H.
    clear H5.
    case case_a.
    intro Xa.
    left.
    apply lemma62.
    intuition.
    intro H1.
    right.
    exists a.
    split.
    left.
    reflexivity.
    split.
    symmetry.
    intuition.
    split; auto.
    assert (Hr := id_B_dec_left a).
    destruct Hr as [Hr1 Hr2].
    rewrite Hr2.
      clear -H.
      induction ys.
      simpl in *.
      auto.
      simpl in H.
      assert (H' := lemma61 _ _ _ _ H).
      destruct H' as [H'' Xa0].
      assert (IH := IHys H'').
      clear - Xa0 IH.
(* now if a=a0 then (remove id_B_dec a (a0 :: ys))=(remove id_B_dec a ys) QED *)
(* and if a<>a0 then (remove id_B_dec a (a0 :: ys))=a0::(remove id_B_dec a ys) *)
(* QED by Xa0 and IH and lemma62 *)
      simpl remove.
      case (id_B_dec a a0).
      auto.
      intro.
      simpl.
      apply lemma62.
      intuition.
      intuition.
    (* case 2 *)
    intro H.
    clear H5.
    destruct H as [xn [H1 [H2 [H3 H4]]]].
    (* subcase a \in X *)
    case case_a.
    intro Xa.
    right.
    exists xn.
    split.
    right.
    assumption.
    split; auto.
    split; auto.
    assert (Hdec := id_B_dec xn a).
    case Hdec.
    intro Hr.
    rewrite <- Hr.
    assert (Hleft := id_B_dec_left xn).
    destruct Hleft as [Hleft1 Hleft2].
    rewrite Hleft2.
    assumption.
    intro Hineq.
    assert (Hright := id_B_dec_right Hineq).
    destruct Hright as [Hright1 Hright2].
    rewrite Hright2.
    simpl.
    apply lemma62.
    split; auto.
    (* subcase a = x_n *)
    intro HH.
    destruct HH as [Henum H5].
    right.
    exists a.
    split.
    left; reflexivity.
    split.
    symmetry; intuition.
    assert (Hleft := id_B_dec_left a).
    destruct Hleft as [Hleft1 Hleft2].
    rewrite Hleft2.
    assert (a=xn).
    apply countable.
    rewrite Henum.
    rewrite <- H2.
    reflexivity.
    rewrite H.
    intuition.    
  Qed.

  Section completion.

  (** This is the hearth of the argument, a fixpoint that, starting from a filter F, builds a complete filter extending F and equiconsistent to F. *)
  Variable F:B -> Prop.

  Fixpoint F_ (n':nat) {struct n'} :=
    match n' with
      | (S n) => 
        let Fn := F_ n in
          let X := fun b:B => Fn b \/ 
            (enum b=n /\ equiconsistent Fn (up (union_singl Fn b)))
            in up X
      | O => F
    end.
  
  Definition Z := fun b:B => exists n:nat, (F_ n) b.

  Lemma lem223 : forall (X:B -> Prop) x, X x -> (up X) x.
  Proof.
    intros.
    unfold up.
    exists 1.
    exists (x::nil).
    simpl.
    intuition.
    unfold leq.
    rewrite meet_top.
    rewrite meet_idem.
    reflexivity.
  Qed.

  Lemma lem222 : forall n m, (n <= m)%nat -> forall x, (F_ n) x -> (F_ m) x.
  Proof.
    assert (lem2221 : forall k, forall x, (F_ k) x -> (F_ (S k)) x).
    intros.
    simpl.
    apply lem223.
    left; assumption.
    intros.
    (* induction on the relation <= *)
    induction H.
    assumption.
    apply lem2221.
    assumption.
  Qed.
    
  Theorem thm22 : Filter F ->
    Filter Z /\ equiconsistent F Z /\ complete Z.
  Proof.
    intros.
    assert (lem221 : forall n, Filter (F_ n)).
    intro.
    case n.
    simpl.
    assumption.
    intro m.
    simpl.
    apply up_filter.
    (* QED lem221 *)

    assert (Fn_filter : forall n:nat, Filter (F_ n)).
    intro.
    case n.
    simpl.
    assumption.
    intro.
    simpl.
    apply up_filter.
    (* QED Fn_filter *)

    (* Z is a filter 
       - Z is nonempty: it has the same witness of nonemptyness as F_0 *)
    split.
    constructor.
    assert (H1:=nonempty H).
    destruct H1 as [b Fb].
    exists b.
    exists 0.
    simpl.
    assumption.
    (* - Z is upwards closed: if x \in Z then there is a n s.t. x \in
         F_n. If nnow x <= y, since F_n is a filter, y \in F_n and so
         y\in Z.*)
    idtac.
    intros.
    destruct H0 as [n Fnx].
    exists n.
    apply upwards_closed with x; auto.
    idtac.
    (* - Z is closed under meets: if x,y \in Z, then there are n,m
         such that x \in F_n, y \in F_m. We use the fact that any F_k
         is a filter and a lemma saying that: k <= l -> F_k \subseteq
         F_l. From the decidability of inequality on nat, we conclude
         the proof. *)
    intros.
    destruct H0 as [n Fnx].
    destruct H1 as [m Fmx].
    case (le_lt_dec n m).
    intro.
    exists m.
    apply (@meet_closed (F_ m)); auto.
    apply lem222 with n;auto.
    intro.
    assert (l' := Lt.lt_le_weak _ _ l).
    exists n.
    apply (@meet_closed (F_ n)); auto.
    apply lem222 with m;auto.

    (* Some lemmas needed botth for the equiconsistency of F and Z and
       for the completeness of Z *)
    assert (lem224 : forall n, equiconsistent (F_ n) F).
    induction n.
    simpl.
    unfold equiconsistent.
    intuition.
    split.
    intro.
    unfold inconsistent in *.
    simpl F_ in H0.
    destruct H0 as [l [ys [H11 [H12 H13]]]].
    destruct IHn as [IH1 IH2].
    apply IH1.
    clear IH1 IH2.
    assert (CaseAnalysis : 
      (fold_left (fun (a : Prop) (b : B) => a /\ F_ n b) ys True) \/
      exists x_n, 
        In x_n ys /\ 
        n = enum x_n /\
        (fold_left (fun (a : Prop) (b : B) => a /\ F_ n b) (remove id_B_dec x_n ys) True) /\
        equiconsistent (F_ n) (up (union_singl (F_ n) x_n))
    ).
    apply lemma5.
    assumption.
    case CaseAnalysis.
    (* case 1 *)
    unfold inconsistent.
    intros H1.
    apply upwards_closed with (fold_left meet ys top);auto.
    clear - H1 H Fn_filter.
    apply (@lemma4 ys (F_ n)).
    auto.
    assumption.
    (* case 2 *)
    intros H1.
    clear - H1 H11 H12 H13 lem221.   
    destruct H1 as [x_n [H21 [H22 [H23 H24]]]].
    set (Y := remove id_B_dec x_n ys) in *.
    assert (A0 : leq (fold_left meet (x_n :: Y) top) bott).
    apply leq_trans with (fold_left meet ys top); auto.
    apply lemma2.
    unfold Y.
    apply lemma3.
    rewrite fold_left_meet_cons in A0.
    assert (A1 : leq (fold_left meet Y top) (compl x_n)).
     set (y:=fold_left meet Y top) in *.
     clear -A0.
     unfold leq in *.
     rewrite meet_comm in A0.
     rewrite meet_bott in A0.
     assert (A0' : bott || - x_n == x_n && y || - x_n).
     rewrite A0.
     reflexivity.
     rewrite join_bott in A0'.
     rewrite join_distrib in A0'.
     rewrite join_compl in A0'.
     rewrite meet_top in A0'.
     symmetry in A0'.
     assert (H := leq' y (- x_n)).
     unfold leq in *.
     intuition.
    assert (A2 : F_ n (fold_left meet Y top)).
    apply (@lemma4 Y (F_ n)).
    apply lem221.
    assumption.
    assert (A3 : F_ n (compl x_n)).
    apply upwards_closed with (fold_left meet Y top).
    apply lem221.
    assumption.
    assumption.
    clear - A3 H24 lem221 .
    unfold equiconsistent in H24.
    destruct H24 as [H241 H242].
    apply H242.
    clear - A3 lem221 .
    unfold inconsistent.
    assert (A4 : up (union_singl (F_ n) x_n) (- x_n)).
    apply lem223.
    unfold union_singl.
    intuition.
    assert (A5 : up (union_singl (F_ n) x_n) x_n).
    apply lem223.
    unfold union_singl.
    intuition.
    apply filter_memb_morph with (x_n && - x_n).
    apply up_filter.
    apply meet_compl.
    apply (@meet_closed (up (union_singl (F_ n) x_n))).
    apply up_filter.
    assumption.
    assumption.
    (* end of cases 1 and 2 *)
    unfold inconsistent.
    simpl.
    intro Fincon.
    destruct IHn.
    apply lem223.
    left.
    apply H1.
    assumption.
    (* QED lem224 *)
    assert (lem225 : forall n m, equiconsistent (F_ n) (F_ m)).
    intros n m.
    clear - lem224.
    firstorder.
    (* QED lem225 *)
    assert (lem226 : equiconsistent F Z).
    unfold Z.
    unfold equiconsistent.
    unfold inconsistent.
    split.
    intro Fincon.
    exists 0.
    simpl.
    assumption.
    intro Zincon.
    destruct Zincon.
    clear -H0 lem224.
    firstorder.
    (* QED lem226 *)

    split.
    (* F and Z are equiconsistent *)
    apply lem226.

    (* one more lemma needed for "Z is complete" *)
    assert (subseteq_up_mono : forall (X Y:B -> Prop)(b:B), (forall z, X z -> Y z) -> up X b -> up Y b).
    unfold up.
    intros.
    destruct H1 as [n [ys [H1 [H2]]]].
(*     intro H3. *)
    exists n.
    exists ys.
    intuition.
    clear H1 H3.
    induction ys.
    simpl in *; auto.
    simpl in H2 |- *.
    assert (H2' := lemma61 _ _ _ _ H2).
    apply lemma62.
    split.
    apply IHys.
    intuition.
    apply H0; intuition.

    (* Z is complete *)
    unfold complete.
    unfold element_complete.
    intros.
    set (n:=enum x).
    assert (Claim : equiconsistent (F_ n) (up (union_singl (F_ n) x))).
      split.
      unfold inconsistent.
      intro.
      apply lem223.
      left.
      assumption.
      unfold inconsistent.
      intro.
      assert ((up (union_singl Z x)) bott).
      apply subseteq_up_mono with (union_singl (F_ n) x).
      intros.
      unfold union_singl in H2 |- *.
      intuition.
      left.
      exists n.
      assumption.
      assumption.
      assert (Z bott).
      clear -H0 H2.
      firstorder.
      assert (forall n : nat, equiconsistent (F_ n) Z).
      clear -lem226 lem224.
      intro n.
      firstorder.
      clear -H3 H4.
      firstorder.
    exists (S n).
    simpl F_.
    apply lem223.
    right.
    auto.
  Defined.
  End completion.

  (** Some additional lemmas that are needed by classcomp.v *)
  Section additional_lemmas.
    
    Lemma lemma8 : forall (X:B -> Prop)(f:B)(ys:list B),
      fold_left (fun (a : Prop) (b : B) => a /\ (union_singl X f) b) ys True ->
      fold_left (fun (a : Prop) (b : B) => a /\ X b) ys True \/
      fold_left (fun (a : Prop) (b : B) => a /\ X b) 
      (remove id_B_dec f ys) True
      .
    Proof.
      fix 3.
      destruct ys.
      simpl.
      intuition.
      simpl.
      intro.
      apply lemma61 in H.
      destruct H.
      destruct (lemma8 _ _ _ H).
      destruct H0.
      left.
      apply lemma62.
      intuition.
      right.
      destruct (id_B_dec f b).
      (* ys is a subset of ys\{f} *)
      Focus 2.
      congruence.
      idtac.
      Focus 2.
      right.
      destruct (id_B_dec f b).
      assumption.
      idtac.
      simpl.
      apply lemma62.
      split.
      assumption.
      destruct H0.
      assumption.
      congruence.
      idtac.
      idtac.
      clear -H1.
      induction ys.
      simpl in *.
      auto.
      simpl in *.
      apply lemma61 in H1.
      destruct (id_B_dec f a).
      intuition.
      simpl.
      apply lemma62.
      intuition.
    Qed.

    Lemma leq_bott : forall x:B, leq bott x.
    Proof.
      intro x.
      unfold leq.
      ring.
    Qed.

  End additional_lemmas.

End filter_completion.

