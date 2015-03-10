Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import finfun bigop finset.

Axiom SET : Type.

Definition Var := nat.
Definition Term := nat.


(*
Definition equalS : nat := 0.
Definition memS : nat := 1.
Definition notS : nat := 2.
Definition orS : nat := 3.
Definition andS : nat := 4.
Definition implS : nat := 5.
Definition forallS : Term -> nat :=
  fun t => 6.
Definition existsS : Term -> nat :=
  fun t => 7.
*)

Inductive Fml : Type :=
  | equalityS : Var -> Var -> Fml
  | membershipS : Var -> Var -> Fml
  | notS : Fml -> Fml
  | orS : Fml -> Fml -> Fml
  | andS : Fml -> Fml -> Fml
  | implS : Fml -> Fml -> Fml
  | forallS : Var -> Fml -> Fml
  | existsS : Var -> Fml -> Fml.

Notation "x _=_ y" := (equalityS x y) (at level 50).
Notation "x _∈_ y" := (membershipS x y) (at level 50).
Notation "￢ x" := (notS x) (at level 51).
Notation "x ∨ y" := (orS x y) (at level 51).
Notation "x ∧ y" := (andS x y) (at level 51).
Notation "x → y" := (implS x y) (at level 51).
Notation "∀ x , y" := (forallS x y) (at level 51).
Notation "∃ x , y" := (existsS x y) (at level 51).

Definition allFml (p : Fml -> bool) f :=
  match f with
    | notS f1 => p f1
    | orS f1 f2 => p f1 && p f2
    | andS f1 f2 => p f1 && p f2
    | implS f1 f2 => p f1 && p f2
    | forallS x f1 => p f1
    | existsS x f1 => p f1
    | _ => true
  end.
                           

(* Syntactic comparison and eqType for Fml.                                *)

Fixpoint eqFml F G {struct F} :=
  match F, G with
    | equalityS m0 m1, equalityS n0 n1 => (m0 == n0) && (m1 == n1)
    | membershipS m0 m1, membershipS n0 n1 => (m0 == n0) && (m1 == n1)
    | notS F0, notS G0 => eqFml F0 G0
    | orS F0 F1, orS G0 G1 => eqFml F0 G0 && eqFml F1 G1
    | andS F0 F1, andS G0 G1 => eqFml F0 G0 && eqFml F1 G1
    | implS F0 F1, implS G0 G1 => eqFml F0 G0 && eqFml F1 G1
    | forallS m F0, forallS n G0 => (m == n) && eqFml F0 G0
    | existsS m F0, existsS n G0 => (m == n) && eqFml F0 G0
    | _, _ => false
  end.

Lemma eqFmlP : Equality.axiom eqFml.
Proof.
  move=> F G.
  apply (iffP idP); last first; [move => -> //| ].
  - elim: G => //; move=>*; by apply/andP.
(*    + move=> v v0 /=.
      by apply/andP.
    + move=> v v0 /=.
      by apply/andP.
    + move=> f H f0 H0 => /=.
      by apply/andP.
    + move=> f H f0 H0 => /=.
      by apply/andP.
    + move=> f H f0 H0 => /=.
      by apply/andP.
    + move=> v f H => /=.
      by apply/andP.
    + move=> v f H => /=.
      by apply/andP.*)

  - move: G; elim F; (move=> f H f0 H0 G E || move=> v f H G E || move => v v0 G E); move: G E;
    solve [ case=> v1 v2 //= /andP [] /eqP -> /eqP -> //
          | case=> f // /v0 -> //
          | case=> f1 f2 //= /andP [] /H -> /H0 -> //
          | case=> v0 f0 //= /andP [] /eqP -> /H -> //].
    (*case=> ? ? //= /andP; solve [elim=> /eqP -> /eqP -> // | elim=> /H -> /H0 -> // | elim=> /eqP -> /H -> //]*)
(*    + move=> v v0; case => v1 v2 //=.
      by move/andP; elim => /eqP -> /eqP ->.
    + move=> v v0; case => v1 v2 //=.
      by move/andP; elim => /eqP -> /eqP ->.
    + move=> f H; case => f0 //=.
      by move/H => ->.
    + move=> f H f0 H0; case => f1 f2 //=.
      by move/andP; elim => /H -> /H0 ->.
    + move=> f H f0 H0; case => f1 f2 //=.
      by move/andP; elim => /H -> /H0 ->.
    + move=> f H f0 H0; case => f1 f2 //=.
      by move/andP; elim => /H -> /H0 ->.
    + move=> v f H; case => v0 f0 //=.
      by move/andP; elim => /eqP -> /H ->.
    + move=> v f H; case => v0 f0 //=.
      by move/andP; elim => /eqP -> /H ->.*)
Qed.

(* See: *)
(*  Handbook of Practical Logic, 6.6 Proving tautologies by inference *)
(*  coq-8.4pl5/tactics/tauto.ml4 *)

(* propositional tautology *)
Fixpoint tautoFml F G {struct F} :=
  match F, G with
    | equalityS m0 m1, equalityS n0 n1 => (m0 == n0) && (m1 == n1)
    | membershipS m0 m1, membershipS n0 n1 => (m0 == n0) && (m1 == n1)
    | notS F0, notS G0 => eqFml F0 G0
    | orS F0 F1, orS G0 G1 => eqFml F0 G0 && eqFml F1 G1
    | andS F0 F1, andS G0 G1 => eqFml F0 G0 && eqFml F1 G1
    | implS F0 F1, implS G0 G1 => eqFml F0 G0 && eqFml F1 G1
    | forallS m F0, forallS n G0 => (m == n) && eqFml F0 G0
    | existsS m F0, existsS n G0 => (m == n) && eqFml F0 G0
    | _, _ => false
  end.



Canonical Fml_eqMixin := EqMixin eqFmlP.
Canonical Fml_eqType := Eval hnf in EqType Fml Fml_eqMixin.

Implicit Arguments eqFmlP [x y].
Prenex Implicits eqFmlP.

Lemma eqFmlE : eqFml = eq_op. Proof. by []. Qed.

Lemma Fml_irrelevance (F G : nat) (E E' : F = G) : E = E'.
Proof. exact: eq_irrelevance. Qed.

(* eqType準備ここまで *)

Definition X : Fml := 0 _=_ 0 ∧ 1 _=_ 1.

Definition is_atomic (f : Fml) : bool :=
  match f with
   | equalityS x y => true
   | membershipS x y => true
   | _ => false
  end.

Eval compute in (is_atomic (0 _=_ 0)).

Definition is_bounded_qf (f : Fml) : bool :=
  match f with
   | forallS x f0 =>
     match f0 with
       | implS f0 f1 =>
         match f0 with
           | membershipS z w => (z == x)
           | _ => false
         end
       | _ => false
     end
   | existsS x f0 =>
     match f0 with
       | implS f0 f1 =>
         match f0 with
           | membershipS z w => (z == x)
           | _ => false
         end
       | _ => false
     end
   | _ => false
end.

Eval compute in is_bounded_qf (∀1 , (1 _=_ 0)).
  (* ====> false *)
Eval compute in is_bounded_qf (∀1 , (1 _∈_ 2)).
  (* ====> false *)
Example testcase0: is_bounded_qf (∀1 , ((1 _∈_ 2) → (1 _=_ 3))).
  (* ====> true *)
Proof.
  simpl.
  reflexivity.
Qed.

Definition is_not_qf (f : Fml) : bool :=
  match f with
   | forallS x f0 => false
   | existsS x f0 => false
   | _ => true
  end.

Fixpoint is_quantifier_free (f : Fml) : bool :=
  match f with
    | forallS _ _ => false
    | existsS _ _ => false
    | _ => allFml is_quantifier_free f
  end.

Fixpoint is_quantifier_free (f : Fml) : bool :=
  match f with
   | equalityS x y => true
   | membershipS x y => true
   | notS f0 => (is_quantifier_free f0)
   | orS f0 f1 => (is_quantifier_free f0) && (is_quantifier_free f1)
   | andS f0 f1 => (is_quantifier_free f0) && (is_quantifier_free f1)
   | implS f0 f1 => (is_quantifier_free f0) && (is_quantifier_free f1)
   | forallS x f0 => false
   | existsS x f0 => false
end.

Require Import Datatypes.
Check (sum unit unit).

Definition hoge (a : bool) : (unit + unit) :=
  match a with
  | true => inl tt
  | false => inr tt
  end.


Definition bound_var (f : Fml) : (Var+unit) :=
  match f with
    | implS f0 f1 =>
      match f0 with
        | membershipS z w => inl z
        | _ => inr tt
      end
    | _ => inr tt
  end.

Definition is_membership f :=
  match f with
    | membershipS _ _ => true
    | _ => false
  end.

Fixpoint is_Σ_0 (f : Fml) : bool :=
  match f with
   | equalityS x y => true
   | membershipS x y => true
   | notS f0 => (is_Σ_0 f0)
   | orS f0 f1 => (is_Σ_0 f0) && (is_Σ_0 f1)
   | andS f0 f1 => (is_Σ_0 f0) && (is_Σ_0 f1)
   | implS f0 f1 => (is_Σ_0 f0) && (is_Σ_0 f1)
   | forallS x f0 => 
     match f0 with
       | implS f00 f01 => is_membership f00 && (is_Σ_0 f01)
       | _ => false
     end
   | existsS x f0 =>
     match f0 with
       | andS f00 f01 => is_membership f00 && (is_Σ_0 f01)
       | _ => false
     end
  end.

Axiom membership : SET -> SET -> bool.
Notation "x ∈ y" := (membership x y) (at level 20).
Axiom equality : SET -> SET -> bool.
(*
Axiom V : CLASS.
Axiom SET_Axiom : forall X : CLASS, (exists Y : CLASS, X ∈ Y) -> X ∈ V.
Axiom emptyset : CLASS.
Axiom emptyset_axiom : (emptyset ∈ V).
Axiom one : CLASS.
Axiom one_axiom : (emptyset ∈ one).
*)

Definition is_finOrdSet (x : finType) :=
  exists n : nat, x = ordinal_finType n.

Definition is_AssignOf (M : SET) (n : nat) (f : 'I_n -> SET) :=
  forall i , (f i) ∈ M.

Check {set ordinal_finType 0}.

Check [set set0] :|: [set set0].

Check FinSet [ffun x : 'I_3 => false].
Eval compute in (set_type (ordinal_finType 0)) = ordinal_finType 1.

Definition natSet_of_nat (n : nat) :=
  [set: ordinal_finType n].

Check natSet_of_nat.  

Check @Ordinal 10 11.

Check [set @Ordinal 10 1 erefl; @Ordinal 10 2 erefl].
Eval compute in (max 10 9).+1.



Check forall (x y:nat),
          let n := (maxn x.+1 y.+1) in
          (@Ordinal (maxn x.+1 y.+1) x (leq_maxl x.+1 y.+1)) = (@Ordinal (maxn x.+1 y.+1) y (leq_maxr x.+1 y.+1)).

(* sumSet x y := {x , y} of type 'I_{maxn x+1 y+1} *)
Definition sumSet (x y : Var) :=
          let n := (maxn x.+1 y.+1) in
          [set (@Ordinal (maxn x.+1 y.+1) x (leq_maxl x.+1 y.+1)) ; (@Ordinal (maxn x.+1 y.+1) y (leq_maxr x.+1 y.+1))].

Check sumSet.


Fixpoint free_VarSet (f : Fml) :=
  match f with
    | equalityS x y => sumSet x y
    | membershipS x y => sumSet x y
    | notS f0 => (free_VarSet f0)
    | orS f0 f1 => (free_VarSet f0) setU (free_VarSet f1)
    | andS f0 f1 => (free_VarSet f0) setU (free_VarSet f1)
    | implS f0 f1 => (free_VarSet f0) setU (free_VarSet f1)
    | forallS x f0 => 
      match f0 with
        | implS f00 f01 => is_membership f00 && (is_Σ_0 f01)
        | _ => false
      end
    | existsS x f0 =>
      match f0 with
        | andS f00 f01 => is_membership f00 && (is_Σ_0 f01)
        | _ => false
      end
  end.


Fixpoint satisfaction (f : Fml) (M : SET) ( : Prop :=
  match f with
   | equalityS x y => equality (s x) (s y)
   | membershipS x y => membership (nth emptyset s x) (nth one s y)
   | notS f0 => ~(satisfaction f0 M s)
   | orS f0 f1 => (satisfaction f0 M s) \/ (satisfaction f1 M s)
   | andS f0 f1 => (satisfaction f0 M s) /\ (satisfaction f1 M s)
   | implS f0 f1 => (satisfaction f0 M s) -> (satisfaction f1 M s)
   | forallS x f0 => forall y : CLASS, (y ∈ M) -> (satisfaction f0 M (set_nth emptyset s x y))
   | existsS x f0 => exists y : CLASS, (y ∈ M) /\ (satisfaction f0 M (set_nth emptyset s x y))
  end.

Notation "M |= f $ s" := (satisfaction f M s) (at level 30).

Definition transitive (M : CLASS) : Prop :=
  forall x y, (x ∈ M) -> (y ∈ x) -> (y ∈ M).


Definition seq_from (s : seq CLASS) (M : CLASS) : bool :=
  let p := (fun x => (x ∈ M)) in
      all p s.


Definition absolute_forMN (f : Fml) (M : CLASS) (N: CLASS) : Prop :=
  forall s : seq CLASS, (seq_from s M) ->
                        ((M |= f $ s) <-> (N |= f $ s)).

Definition absolute_forM (f : Fml) (M : CLASS) : Prop :=
  absolute_forMN f M V.

Lemma Absoluteness_membership : forall x y : Var, forall (M : CLASS), (transitive M) -> absolute_forM (x _∈_ y) M.
Proof.
  move=>x y M.
  move=> Htrans.
  move=> s.
  move=> HsinM.
  have: (nth emptyset s x) ∈ M.
    have: forall n : Var, (find(nth emptyset x n) ∈ M.
