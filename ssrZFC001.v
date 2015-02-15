Require Import ssreflect ssrbool.
 
Axiom SET : Type.
Axiom membership : SET -> SET -> Prop.
Notation "x ∈ y" := (membership x y) (at level 100) : type_scope.
 
Axiom Extensionality : forall (x y: SET), (forall (z : SET), ((z ∈ x) <-> (z ∈ y))) <-> (x = y).
 
Axiom emptyset : SET.
Axiom EmptySetAxiom : (forall (z: SET), ~(z ∈ emptyset)).
 
Axiom pair : SET -> SET -> SET.
Notation "{ x , y }" := (pair x y) (at level 50) : type_scope.
Axiom PairingAxiom : forall (x y : SET), forall (z : SET), (z ∈ { x , y }) <-> (x = z) \/ (y = z).
Notation "{{ x }}" := (pair x x) (at level 49) : type_scope.
 
Axiom union : SET -> SET.
Notation "∪ x" := (union x) (at level 40) : type_scope.
Axiom UnionAxiom : forall (x : SET), forall (z : SET), (z ∈ (∪ x)) <-> (exists (y : SET), (z ∈ x) /\ (z ∈ y)).
 
Notation "x ∪ y" := (union (pair x y)) (at level 39) : type_scope.
 
Definition subset_of (x y : SET) : Prop :=
  forall (z : SET), (membership z x) -> (membership z y).
Notation "x ⊆ y" := (subset_of x y) (at level 101) : type_scope.
 
 
Axiom PowerSetAxiom : forall (x : SET), exists (y : SET), forall (z : SET), (z ⊆ x) -> (z ∈ y).
 
Axiom Comprehension : forall (phi : SET -> SET-> Prop), forall (param : SET), forall (x : SET), exists (y : SET), forall (z : SET), (z ∈ y) <-> (z ∈ x) /\ (phi z param).
 
 
Axiom ω : SET.
Definition inductive_set (x : SET) : Prop :=
  (emptyset ∈ x) /\ forall (y : SET), (y ∈ x) -> ((y ∪ {{ y }}) ∈ x).
Axiom InfinityAxiom : (inductive_set ω) /\ (forall (x : SET), (inductive_set x) -> (ω ⊆ x)).
 
Require Import Setoid.
Lemma 補題_0と1は異なる : ~(emptyset = {{ emptyset }}).
Proof.
  assert (emptyset ∈ {{emptyset}}) as H1.
  -  by apply PairingAxiom, or_introl.
  -  rewrite -Extensionality => Habs.
     case: (EmptySetAxiom emptyset).
     by rewrite Habs => //.
Qed.
 
 
(*---  Kuratowski's Definition of ordered-pairs ---*)
Definition ordered_pair (x y : SET) : SET :=
  { {{x}} , { x , y } }.
Notation "\( x , y \)" := (ordered_pair x y) (at level 35).
 
Lemma 補題_Singletonのequality : forall (x y z : SET), {{x}} = {y, z} -> x = y.
Proof.
  move=> y x z Hsingleton.
  have Hxinx:( x ∈ {x, z} ); [apply (PairingAxiom x z x), or_introl, eq_refl|].
  have Hyinx:( x ∈ {{y}} ); [rewrite Hsingleton => //|].
  have: (y = x \/ y = x); [apply (PairingAxiom y y x) => //|].
  case => //.
Qed.
 
Lemma 補題_非順序対は交換可能' x y z : (z∈{x,y}) -> (z∈{y,x}).
Proof.
  rewrite 2!PairingAxiom or_comm //.
Qed.  
 
Lemma 補題_非順序対は交換可能 : forall (x y : SET), {x , y} = {y , x}.
Proof.
  move=> x y.
  rewrite -(Extensionality ({x , y}) ({y , x})) => z.
  apply conj; apply 補題_非順序対は交換可能'.
Qed.
 
Lemma 補題_順序対のequality : forall (x0 x1 y0 y1 : SET), (x0 = x1) /\ (y0 = y1) <-> ( \( x0, y0 \) = \(x1 , y1\) ).
Proof.
  move => x y z w.
  apply conj; [case=> Hxy Hzw; rewrite Hxy Hzw //|].
  move=>Hpair; apply conj.
  - have Hx:({{x}} ∈ \(x, z \)); [apply /PairingAxiom/or_introl => // |].
    have:({{x}} ∈ \(y, w\)); [rewrite -Hpair // | rewrite PairingAxiom].
    by case=>H; symmetry in H; move:H; apply 補題_Singletonのequality.
  - have:({x , z} ∈ \(y, w \)); [rewrite -Hpair; apply /PairingAxiom/or_intror => // |].
    case/PairingAxiom => H.
    + move:(H) => /補題_Singletonのequality =>H0.
      rewrite 補題_非順序対は交換可能 in H; apply 補題_Singletonのequality in H.
      move:Hpair; rewrite -{}H0 -{}H.
      rewrite /ordered_pair 補題_非順序対は交換可能 =>/補題_Singletonのequality.
      by rewrite 補題_非順序対は交換可能 => /補題_Singletonのequality //.
    + move:H; rewrite -Extensionality =>H.
      move:(H y); move:(H w); rewrite !PairingAxiom !iff_to_and => [[]] H0 _ => [[]] H1 _.
      case:H0 => //; [apply or_intror =>// | move=>H2].
      case:H1 => //; [apply or_introl =>// | move=>H3 | move=>H3 ].
      * by move:H; rewrite Extensionality -H2 -H3 補題_非順序対は交換可能 => /補題_Singletonのequality //.
      * move:Hpair; rewrite /ordered_pair => /Extensionality.
        set x':={{x}}; move/(_ x') => [] =>H4 _; move:H4.
        rewrite !PairingAxiom.
        case;
          [apply or_introl => // | | ];
          move=>H4; apply symmetry, 補題_Singletonのequality in H4; congruence.
Qed.