Require Import ssreflect ssrbool ssrnat.

Definition nand_b (b0 : bool) (b1 : bool) : bool :=
  match b0 with
      | true => (~~ b1)
      | false => true
  end.

Lemma nand_lemma : forall (b0 b1 : bool), (nand_b b0 b1) = (~~(b0 && b1)).
Proof.
  move=> b0 b1.
  case b0.
    simpl; reflexivity.
    simpl; reflexivity.
Qed.

(* Software Foundation —ûK–â‘è: šš, recommended (basic_induction) *)

Lemma ƒ[ƒ‚ğŠ|‚¯‚é‚Æƒ[ƒ‚É‚È‚é : forall (n:nat), n*0 = 0.
Proof.
  move=> n.
  induction n as [| m].
  trivial. (* 0*0 == 0 *)
  rewrite mulSnr. (* m.+1 * 0 ~~~> m * 0 + 0 *)
  rewrite -> IHm. (* apply IHm : m * 0 == 0 *)
  reflexivity.
Qed.

Axiom SET : Type.
Axiom membership : SET -> SET -> Prop.
Notation "x ¸ y" := (membership x y) (at level 100) : type_scope.

Axiom Extensionality : forall (x y: SET), (forall (z : SET), ((z ¸ x) <-> (z ¸ y))) <-> (x = y).

Axiom emptyset : SET.
Axiom EmptySetAxiom : (forall (z: SET), ~(z ¸ emptyset)).

Axiom pair : SET -> SET -> SET.
Notation "{ x , y }" := (pair x y) (at level 50) : type_scope.
Axiom PairingAxiom : forall (x y : SET), forall (z : SET), (z ¸ { x , y }) <-> (x = z) \/ (y = z).
Notation "{{ x }}" := (pair x x) (at level 49) : type_scope.

Axiom union : SET -> SET.
Notation "¾ x" := (union x) (at level 40) : type_scope.
Axiom UnionAxiom : forall (x : SET), forall (z : SET), (z ¸ (¾ x)) <-> (exists (y : SET), (y ¸ x) /\ (z ¸ y)).

Notation "x ¾ y" := (union (pair x y)) (at level 39) : type_scope.

Definition subset_of (x y : SET) : Prop :=
  forall (z : SET), (membership z x) -> (membership z y).
Notation "x º y" := (subset_of x y) (at level 101) : type_scope.

Axiom P : SET -> SET.
Axiom PowerSetAxiom : forall (x : SET), forall (z : SET), (z º x) <-> (z ¸ P x).

Axiom Comprehension : forall (phi : SET -> SET-> Prop), forall (param : SET), forall (x : SET), exists (y : SET), forall (z : SET), (z ¸ y) <-> (z ¸ x) /\ (phi z param).


Axiom ƒÖ : SET.
Definition inductive_set (x : SET) : Prop :=
  (emptyset ¸ x) /\ forall (y : SET), (y ¸ x) -> ((y ¾ {{ y }}) ¸ x).
Axiom InfinityAxiom : (inductive_set ƒÖ) /\ (forall (x : SET), (inductive_set x) -> (ƒÖ º x)).


Lemma •â‘è_0‚Æ1‚ÍˆÙ‚È‚é : ~(emptyset = {{ emptyset }}).
Proof.
  assert (emptyset ¸ {{emptyset}}) as H1.
  apply PairingAxiom.
  left; exact. (* assertion succeeded. *)
  assert (~(emptyset ¸ emptyset)) as H0.
  apply EmptySetAxiom. (* assertion succeeded. *)
  rewrite <- Extensionality.
  move => Habs.
  destruct H0.
  rewrite (Habs emptyset).
  exact.
Qed.

(*-----------------------------------------------------------------*)

(*---  Kuratowski's Definition of ordered-pairs ---*)
Definition ordered_pair (x y : SET) : SET :=
  { {{x}} , { x , y } }.
Notation "\( x , y \)" := (ordered_pair x y) (at level 35).

Lemma •â‘è_Singleton‚Ìequality : forall (x y z : SET), {{x}} = {y, z} -> x = y.
Proof.
  move=> y x z; move.
  case=> Hsingleton.
  assert ( x ¸ {x, z} ) as Hxinx.
  apply (PairingAxiom x z x); left; reflexivity.
  assert ( x ¸ {{y}} ) as Hyinx.
  rewrite -> Hsingleton; exact.
  assert (y = x \/ y = x) as Htmp.
  apply (PairingAxiom y y x).
  exact.
  destruct Htmp.
  exact.
  exact.
Qed.

Lemma •â‘è_”ñ‡˜‘Î‚ÍŒğŠ·‰Â”\ : forall (x y : SET), {x , y} = {y , x}.
Proof.
  move=> x y.
  rewrite <- (Extensionality ({x , y}) ({y , x})).
  move=> z.
  move; split.
  move=> Hleft.
  apply (PairingAxiom y x z).
  assert ((x = z) \/ (y = z)).
  apply (PairingAxiom x y z); exact.
  destruct H.
  move: H; auto.
  move: H; auto.
  move=> Hleft.
  apply (PairingAxiom x y z).
  assert ((y = z) \/ (x = z)).
  apply (PairingAxiom y x z); exact.
  destruct H.
  move: H; auto.
  move: H; auto.
Qed.

Lemma •â‘è_‡˜‘Î‚Ìequality : forall (x0 x1 y0 y1 : SET), (x0 = x1) /\ (y0 = y1) <-> ( \( x0, y0 \) = \(x1 , y1\) ).
Proof.
  move => x y z w.
  (* •Ğ•û‚¸‚Â¦‚·‚±‚Æ‚Æ‚µ‚Ü‚· *)
  assert ((x = y) /\ (z = w) -> \(x, z\) = \(y, w\)) as Hright.
  case=> Hxy Hzw.
  rewrite <- Hxy; rewrite <- Hzw; exact.
  (* ‚à‚¤•Ğ•û‚Ì“ï‚µ‚¢•û‚ğ¦‚· *)
  assert ( \(x, z\) = \(y, w\) -> (x=y)/\(z=w) ) as Hleft.
  case=> Hpair. (* ‰¼’è‚Ì“±“ü *)
    (* Proof x=y Start. *)
    assert (x = y) as Hxy.
    assert ({{x}} ¸ \(x, z \)) as Hx.
    apply (PairingAxiom ({{x}}) ({x , z})).
    left; exact.
    assert ({{x}} ¸ \(y, w\)) as Hxinyw.
    rewrite <- Hpair; assumption.
    assert (({{y}} = {{x}}) \/ ({y,w} = {{x}})) as Hdicotomy.
    apply (PairingAxiom ({{y}}) ({y,w}) ({{x}})); assumption.
    destruct Hdicotomy. (* Dicotomiy‚Ìê‡•ª‚¯. *)
    (* ‚Ç‚¿‚ç‚Ìê‡‚Å‚à x=y ‚Å‚Ä—ˆ‚é‚Í‚¸ *)
    assert (y= x) as Hxeqy.
    apply (•â‘è_Singleton‚Ìequality y x x); exact.
    rewrite -> Hxeqy; reflexivity.
    assert ({{x}} = {y, w}) as Hprev.
    rewrite <- H; reflexivity.
    apply (•â‘è_Singleton‚Ìequality x y w); exact.
    (* Proof x=y End. *)
    (* Proof z=w Start. Simply a symmetric argument. *)
    assert (z = w) as Hzw.
    assert ({x , z} ¸ \(x, z \)) as Hxz.
    apply (PairingAxiom ({{x}}) ({x,z}) ({x , z})).
    right; exact.
    assert ({x , z} ¸ \(y, w \)) as Hxzinyw.
    rewrite <- Hpair; assumption.
    assert ({{y}} = ({x ,z}) \/ ({y , w} = {x , z})) as Hdicotomy.
    apply (PairingAxiom ({{y}}) ({y , w}) ({x , z})); assumption.
    destruct Hdicotomy. (* Dicotomiy‚Ìê‡•ª‚¯. *)
    (* ‚Ç‚¿‚ç‚Ìê‡‚Å‚à z=w ‚Å‚Ä—ˆ‚é‚Í‚¸ *)
    (*apply (•â‘è_Singleton‚Ìequality y x z); exact.*)
    assert ({{y}} = {z,x} ) as HH.
    rewrite -> (•â‘è_”ñ‡˜‘Î‚ÍŒğŠ·‰Â”\ z x); exact.
    assert (y = z) as Hyz.
    apply (•â‘è_Singleton‚Ìequality y z x); exact.
    assert (x = z) as Hxeqz.
    rewrite <- Hyz; exact.
    assert ({y, w} ¸ \(x , z \)) as Hyw.
    assert ({y, w} ¸ \(y , w \)). 
    apply (PairingAxiom ({{y}}) ({y , w}) ({y , w})); right; reflexivity.
    rewrite -> Hpair; exact.
    assert ({y , w} = {{x}}).
    assert (({{x}} = {y , w}) \/ ({x , z} = {y , w})).
    apply (PairingAxiom ({{x}}) ({x , z}) ({y , w})); exact.
    case: H0; auto.
    rewrite <- Hxeqz; auto.
    assert ({{x}} = {y, w}) as Hprev.
    auto.
    move: Hprev.
    rewrite <- Hxeqz.
    rewrite <- Hxy.
    move=> Hprev.
    assert (w ¸ {x , w}).
    apply (PairingAxiom x w w); right; reflexivity.
    move: H1.
    rewrite <- Hprev.
    move=> Hprev2.
    assert (x = w \/ x = w).
    apply (PairingAxiom x x w); exact.
    case H1; exact.

    assert (x = w \/ x <> w) as EMxz.
    Hypothesis EM : forall p : Prop, p \/ ~p.
    apply (EM (x = w)).
    case: EMxz.
    move=> Hxeqw.
    assert ({{x}} = {x , z}).
    rewrite <- H.
    rewrite <- Hxy.
    rewrite <- Hxeqw; reflexivity.
    assert ({{x}} = {z , x}).
    rewrite -> (•â‘è_”ñ‡˜‘Î‚ÍŒğŠ·‰Â”\ z x); exact.
    assert (x = z).
    apply (•â‘è_Singleton‚Ìequality x z x); exact.
    rewrite <- H2; exact.

    move=> Hxneqw.
    assert (w ¸ {x , z}).
    assert (w ¸ {y , w}).
    apply (PairingAxiom y w w); right; reflexivity.
    rewrite <- H; exact.
    assert ((x = w) \/ (z = w)).
    apply (PairingAxiom x z w); exact.
    case: H1.
    move=> H2.
    contradiction.
    trivial.
    
    move: Hxy Hzw; auto.
    move.
    auto.
Qed.

(*-------------------------------------------------------------------*)

Definition is_Relation (R : SET) : Prop :=
  forall z, (z ¸ R) -> (exists (x y :SET), z = \(x , y \)).


Definition is_WellDefined (R : SET) : Prop :=
  forall (x0 y0 x1 y1: SET), ( (\(x0 , y0 \) ¸ R) /\ (\(x1 , y1\) ¸ R) ) -> x0 = x1 -> y0 = y1.

Definition is_Function (R : SET) : Prop :=
  (is_Relation R) /\ (is_WellDefined R).

Definition is_OneToOne (R : SET) : Prop :=
  forall (x0 y0 x1 y1 : SET), ( (\(x0 , y0 \) ¸ R) /\ (\(x1 , y1\) ¸ R) ) -> y0 = y1 -> x0 = x1.

Definition is_Injection (R : SET) : Prop :=
  (is_Function R) /\ (is_OneToOne R).

(*=====================================================================*)

Definition is_Reflexive_Relation (R : SET) : Prop :=
  (is_Relation R) /\ forall (x y: SET), (\(x , y \) ¸ R) -> (\( x , x \) ¸ R).

Definition is_Symmetric_Relation (R : SET) : Prop :=
  (is_Relation R) /\ forall (x y: SET), (\(x , y\) ¸ R) -> (\(y , x\) ¸ R).

Definition is_Transitive_Relation (R : SET) : Prop :=
  (is_Relation R) /\ forall (x y z : SET), (\(x , y \) ¸ R) -> (\(y , z\) ¸ R) -> (\(x , z\) ¸ R).

Definition is_Transitive (x : SET) : Prop :=
  forall (y z : SET), (y ¸ x) -> (z ¸ y) -> (z ¸ x).

Definition is_Ordinal : (x : SET) : Prop :=
  (is_Transitive x) /\ (is_Transitive_Relation