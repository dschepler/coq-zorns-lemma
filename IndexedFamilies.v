Require Export Families.
Require Export Image.
Require Import ImageImplicit.

Set Implicit Arguments.

Section IndexedFamilies.

Variable A T:Type.
Definition IndexedFamily := A -> Ensemble T.
Variable F:IndexedFamily.

Inductive IndexedUnion : Ensemble T :=
  | indexed_union_intro: forall (a:A) (x:T),
    In (F a) x -> In IndexedUnion x.

Inductive IndexedIntersection : Ensemble T :=
  | indexed_intersection_intro: forall (x:T),
    (forall a:A, In (F a) x) -> In IndexedIntersection x.

End IndexedFamilies.

Section IndexedFamilyFacts.

Lemma IndexedUnion_vee : forall {A T:Type} (F:IndexedFamily A T) (a:A),
  Included (F a) (IndexedUnion F).
Proof.
intros; red; intros. exists a; trivial.
Qed.

Lemma IndexedUnion_minimal : forall {A T:Type} (F:IndexedFamily A T)
  (S:Ensemble T),
  (forall a:A, Included (F a) S) -> Included (IndexedUnion F) S.
Proof.
intros; red; intros. destruct H0 as [a]. eapply H; eassumption.
Qed.

Lemma IndexedIntersection_wedge : forall {A T:Type} (F:IndexedFamily A T)
  (a:A), Included (IndexedIntersection F) (F a).
Proof.
intros; red; intros. destruct H. trivial.
Qed.

Lemma IndexedIntersection_maximal : forall {A T:Type} (F:IndexedFamily A T)
  (S:Ensemble T),
  (forall a:A, Included S (F a)) -> Included S (IndexedIntersection F).
Proof.
intros; red; intros. constructor. intros. eapply H; eassumption.
Qed.

(* unions and intersections over subsets of the index set *)
Lemma sub_indexed_union: forall {A B T:Type} (f:A->B)
  (F:IndexedFamily B T),
  Included (IndexedUnion (fun a:A => F (f a))) (IndexedUnion F).
Proof.
intros; apply IndexedUnion_minimal. intros. apply IndexedUnion_vee.
Qed.

Lemma sub_indexed_intersection: forall {A B T:Type} (f:A->B)
  (F:IndexedFamily B T),
  Included (IndexedIntersection F) (IndexedIntersection (fun a:A => F (f a))).
Proof.
intros; apply IndexedIntersection_maximal. intros.
apply IndexedIntersection_wedge.
Qed.

Lemma empty_indexed_intersection: forall {T:Type}
  (F:IndexedFamily False T),
  IndexedIntersection F = Full_set.
Proof.
intros.
apply Extensionality_Ensembles; split.
+ constructor.
+ apply IndexedIntersection_maximal. destruct a.
Qed.

Lemma empty_indexed_union: forall {T:Type}
  (F:IndexedFamily False T),
  IndexedUnion F = Empty_set.
Proof.
intros. apply Extensionality_Ensembles; split.
+ apply IndexedUnion_minimal. destruct a.
+ auto with sets.
Qed.

End IndexedFamilyFacts.

Section IndexedFamilyToFamily.

(* relation to families of subsets of T *)
Variable T:Type.
Variable A:Type.
Variable F:IndexedFamily A T.

Definition ImageFamily : Family T :=
  Im Full_set F.

Lemma indexed_to_family_union: IndexedUnion F = FamilyUnion ImageFamily.
Proof.
apply Extensionality_Ensembles; split.
+ apply IndexedUnion_minimal. intros. apply FamilyUnion_vee.
  exists a; trivial. constructor.
+ apply FamilyUnion_minimal. destruct 1; subst. apply IndexedUnion_vee.
Qed.

Lemma indexed_to_family_intersection:
  IndexedIntersection F = FamilyIntersection ImageFamily.
Proof.
apply Extensionality_Ensembles; split.
+ apply FamilyIntersection_maximal. intros. destruct H; subst.
  apply IndexedIntersection_wedge.
+ apply IndexedIntersection_maximal. intros. apply FamilyIntersection_wedge.
  exists a; trivial. constructor.
Qed.

End IndexedFamilyToFamily.
