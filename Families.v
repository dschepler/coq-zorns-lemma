Require Export Ensembles.
Require Import EnsemblesImplicit.

Set Implicit Arguments.

Section Families.

Variable T:Type.
Definition Family := Ensemble (Ensemble T).
Variable F:Family.

Inductive FamilyUnion: Ensemble T :=
  | family_union_intro: forall (S:Ensemble T) (x:T),
    In F S -> In S x -> In FamilyUnion x.

Inductive FamilyIntersection: Ensemble T :=
  | family_intersection_intro: forall x:T,
    (forall S:Ensemble T, In F S -> In S x) ->
    In FamilyIntersection x.

Lemma FamilyUnion_vee : forall S:Ensemble T,
  In F S -> Included S FamilyUnion.
Proof.
intros; intros x ?. exists S; trivial.
Qed.

Lemma FamilyUnion_minimal : forall A:Ensemble T,
  (forall S:Ensemble T, In F S -> Included S A) ->
  Included FamilyUnion A.
Proof.
intros; intros x ?. destruct H0. exact (H S H0 x H1).
Qed.

Lemma FamilyIntersection_wedge : forall S:Ensemble T,
  In F S -> Included FamilyIntersection S.
Proof.
intros; intros x ?. destruct H0; auto.
Qed.

Lemma FamilyIntersection_maximal : forall A:Ensemble T,
  (forall S:Ensemble T, In F S -> Included A S) ->
  Included A FamilyIntersection.
Proof.
intros; intros x ?. constructor; intros. exact (H S H1 x H0).
Qed.

End Families.

Section FamilyFacts.

Variable T:Type.

Lemma empty_family_union: FamilyUnion (@Empty_set (Ensemble T)) =
                          Empty_set.
Proof.
apply Extensionality_Ensembles; split.
+ apply FamilyUnion_minimal. destruct 1.
+ intros x [].
Qed.

Lemma empty_family_intersection:
  FamilyIntersection (@Empty_set (Ensemble T)) = Full_set.
Proof.
apply Extensionality_Ensembles; split.
+ intros x ?; constructor.
+ apply FamilyIntersection_maximal. destruct 1.
Qed.

(* unions and intersections of subfamilies *)

Lemma subfamily_union: forall F G:Family T, Included F G ->
  Included (FamilyUnion F) (FamilyUnion G).
Proof.
intros. apply FamilyUnion_minimal. intros. apply FamilyUnion_vee.
auto.
Qed.

Lemma subfamily_intersection: forall F G:Family T, Included F G ->
  Included (FamilyIntersection G) (FamilyIntersection F).
Proof.
intros. apply FamilyIntersection_maximal. intros.
apply FamilyIntersection_wedge. auto.
Qed.

End FamilyFacts.
