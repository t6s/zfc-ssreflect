Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import finfun bigop finset.
Require Import Setoid.

Section BasicAxioms.

Axiom SET : Type.
Axiom membership : SET -> SET -> Prop.
Notation "x ∈ y" := (membership x y) (at level 100) : bool_scope.

Axiom Axiom_Extensionality : forall (x y: SET), (forall (z : SET), ((z ∈ x) <-> (z ∈ y))) <-> (x = y).

Axiom emptyset : SET.
Axiom Axiom_EmptySet : (forall (z: SET), ~(z ∈ emptyset)).

Axiom pair : SET -> SET -> SET.
Notation "\{ x , y \}" := (pair x y) (at level 50) : type_scope.
Axiom Axiom_Pairing : forall (x y : SET), forall (z : SET), (z ∈ \{ x , y \}) <-> (x = z) \/ (y = z).
Notation "\{} x" := (pair x x) (at level 49) : type_scope.

Axiom union : SET -> SET.
Notation "∪ x" := (union x) (at level 40) : type_scope.
Axiom Axiom_Union : forall (x : SET), forall (z : SET), (z ∈ (∪ x)) <-> (exists (y : SET), (y ∈ x) /\ (z ∈ y)).

Notation "x ∪ y" := (union (pair x y)) (at level 39) : type_scope.

Definition subset_of (x y : SET) : Prop :=
  forall (z : SET), (membership z x) -> (membership z y).
Notation "x ⊆ y" := (subset_of x y) (at level 101) : bool_scope.

Axiom P : SET -> SET.
Axiom Axiom_PowerSet : forall (x : SET), forall (z : SET), (z ⊆ x) <-> (z ∈ P x).

Axiom Axiom_Comprehension : forall (phi : SET -> SET-> Prop), forall (param : SET), forall (x : SET), exists (y : SET), forall (z : SET), (z ∈ y) <-> (z ∈ x) /\ (phi z param).


Axiom ω : SET.
Definition inductive_set (x : SET) : Prop :=
  (emptyset ∈ x) /\ forall (y : SET), (y ∈ x) -> ((y ∪ \{} y) ∈ x).
Axiom Axiom_Infinity : (inductive_set ω) /\ (forall (x : SET), (inductive_set x) -> (ω ⊆ x)).

(*=================== Axiom Definition End =========================*)

Lemma 補題_0と1は異なる : ~(emptyset = (\{}emptyset)).
Proof.
  assert (emptyset ∈ \{}emptyset) as H1.
  -  by apply Axiom_Pairing, or_introl.
  -  rewrite -Axiom_Extensionality => Habs.
     case: (Axiom_EmptySet emptyset).
     by rewrite Habs => //.
Qed.

(*-----------------------------------------------------------------*)

(*---  Kuratowski's Definition of ordered-pairs ---*)
Definition ordered_pair (x y : SET) : SET :=
  \{ \{}x , \{ x , y \} \}.
Notation "\( x , y \)" := (ordered_pair x y) (at level 35).

Lemma 補題_Singletonのequality : forall (x y z : SET), \{}x = \{y, z\} -> x = y.
Proof.
  move=> y x z Hsingleton.
  have Hxinx:( x ∈ \{x, z\} ); [apply (Axiom_Pairing x z x), or_introl|].
  reflexivity.
  have Hyinx:( x ∈ \{}y ); [rewrite Hsingleton => //|].
  have: (y = x \/ y = x); [apply (Axiom_Pairing y y x) => //|].
  case => //.
Qed.

Lemma 補題_非順序対は交換可能' x y z : (z∈\{x,y\}) -> (z∈\{y,x\}).
Proof.
  rewrite 2!Axiom_Pairing or_comm //.
Qed.  
 
Lemma 補題_非順序対は交換可能 : forall (x y : SET), \{x , y\} = \{y , x\}.
Proof.
  move=> x y.
  rewrite -(Axiom_Extensionality (\{x , y\}) (\{y , x\})) => z.
  apply conj; apply 補題_非順序対は交換可能'.
Qed.

Lemma 補題_順序対のequality : forall (x0 x1 y0 y1 : SET), (x0 = x1) /\ (y0 = y1) <-> ( \( x0, y0 \) = \(x1 , y1\) ).
Proof.
  move => x y z w.
  apply conj; [case=> Hxy Hzw; rewrite Hxy Hzw //|].
  move=>Hpair; apply conj.
  - have Hx:(\{}x ∈ \(x, z \)); [apply /Axiom_Pairing/or_introl => // |].
    have:(\{}x ∈ \(y, w\)); [rewrite -Hpair // | rewrite Axiom_Pairing].
    by case=>H; symmetry in H; move:H; apply 補題_Singletonのequality.
  - have:(\{x , z\} ∈ \(y, w \)); [rewrite -Hpair; apply /Axiom_Pairing/or_intror => // |].
    case/Axiom_Pairing => H.
    + move:(H) => /補題_Singletonのequality =>H0.
      rewrite 補題_非順序対は交換可能 in H; apply 補題_Singletonのequality in H.
      move:Hpair; rewrite -{}H0 -{}H.
      rewrite /ordered_pair 補題_非順序対は交換可能 =>/補題_Singletonのequality.
      by rewrite 補題_非順序対は交換可能 => /補題_Singletonのequality //.
    + move:H; rewrite -Axiom_Extensionality =>H.
      move:(H y); move:(H w); rewrite !Axiom_Pairing !iff_to_and => [[]] H0 _ => [[]] H1 _.
      case:H0 => //; [apply or_intror =>// | move=>H2].
      case:H1 => //; [apply or_introl =>// | move=>H3 | move=>H3 ].
      * by move:H; rewrite Axiom_Extensionality -H2 -H3 補題_非順序対は交換可能 => /補題_Singletonのequality //.
      * move:Hpair; rewrite /ordered_pair => /Axiom_Extensionality.
        set x':=\{}x; move/(_ x') => [] =>H4 _; move:H4.
        rewrite !Axiom_Pairing.
        case;
          [apply or_introl => // | | ];
          move=>H4; apply symmetry, 補題_Singletonのequality in H4; congruence.
Qed.

(*-------------------------------------------------------------------*)
Section RelationsAndFunctions.

Definition is_Relation (R : SET) : Prop :=
  forall z, (z ∈ R) -> (exists (x y :SET), z = \(x , y \)).


Definition is_WellDefined (R : SET) : Prop :=
  forall (x0 y0 x1 y1: SET), ( (\(x0 , y0 \) ∈ R) /\ (\(x1 , y1\) ∈ R) ) -> x0 = x1 -> y0 = y1.

Definition is_Function (R : SET) : Prop :=
  (is_Relation R) /\ (is_WellDefined R).

Definition is_OneToOne (R : SET) : Prop :=
  forall (x0 y0 x1 y1 : SET), ( (\(x0 , y0 \) ∈ R) /\ (\(x1 , y1\) ∈ R) ) -> y0 = y1 -> x0 = x1.

Definition is_Injection (R : SET) : Prop :=
  (is_Function R) /\ (is_OneToOne R).

(*=====================================================================*)

Definition is_Reflexive_Relation (R : SET) : Prop :=
  (is_Relation R) /\ forall (x y: SET), (\(x , y \) ∈ R) -> (\( x , x \) ∈ R).

Definition is_Symmetric_Relation (R : SET) : Prop :=
  (is_Relation R) /\ forall (x y: SET), (\(x , y\) ∈ R) -> (\(y , x\) ∈ R).

Definition is_Transitive_Relation (R : SET) : Prop :=
  (is_Relation R) /\ forall (x y z : SET), (\(x , y \) ∈ R) -> (\(y , z\) ∈ R) -> (\(x , z\) ∈ R).

Definition is_Transitive (x : SET) : Prop :=
  forall (y z : SET), (y ∈ x) -> (z ∈ y) -> (z ∈ x).

Definition ext (R : SET -> SET -> Prop) : SET -> Prop :=
  fun z =>
    exists (x y : SET), (z = \( x, y\) /\ R x y).

Definition E : SET -> Prop :=
  ext membership.

Axiom compr : (SET -> SET -> Prop) -> (SET) -> (SET) -> (SET).
Axiom ComprehensionAxiom : forall (phi : SET -> SET-> Prop), forall (param : SET), forall (x : SET), forall (z : SET), (z ∈ (compr phi param x)) <-> (z ∈ x) /\ (phi z param).

Notation "_{ * : x | phi $ p }_" := (compr phi p x) (at level 30) : type_scope.

Definition operation_cap (x : SET) (y : SET -> Prop) : SET :=
  let phi := (fun (a b : SET) => (y b)) in
  _{ * : x | (phi) $ (emptyset) }_.

Definition cap (x y : SET) : SET :=
  operation_cap x (

Axiom Axiom_Foundation : forall R : SET -> Prop, (exists (y : SET), R y) -> (\


Definition is_Ordinal : (x : SET) : Prop :=
  (is_Transitive x) /\ (is_Transitive_Relation

End RelationsAndFunctions.


End BasicAxioms.
