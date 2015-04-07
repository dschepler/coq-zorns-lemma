Require Import EnsemblesUtf8.
Require Export Families.
Require Export IndexedFamilies.
Require Export EnsemblesSpec.

Lemma Complement_Empty_set {U:Type} :
  Complement (@Empty_set U) = Full_set.
Proof.
apply Extensionality_Ensembles; split; do 2 intro.
+ constructor.
+ intro. destruct H0.
Qed.

Lemma Complement_Full_set {U:Type} :
  Complement (@Full_set U) = ∅.
Proof.
apply Extensionality_Ensembles; split; do 2 intro.
+ do 2 red in H. contradict H. constructor.
+ destruct H.
Qed.

Lemma Complement_Intersection {U:Type} :
  ∀ A B:Ensemble U, Complement (A ∩ B) = Complement A ∪ Complement B.
Proof.
intros. apply Extensionality_Ensembles; split; red; intros.
+ destruct (classic (x ∈ A)).
  - right. intro. apply H. constructor; trivial.
  - left; assumption.
+ intro. destruct H0. destruct H; auto.
Qed.

Lemma Complement_Union {U:Type} :
  ∀ A B:Ensemble U, Complement (A ∪ B) = Complement A ∩ Complement B.
Proof.
intros. apply Extensionality_Ensembles; split; red; intros.
+ do 2 red in H. constructor.
  - intro. contradict H. left; trivial.
  - intro. contradict H. right; trivial.
+ intro. destruct H, H0; auto.
Qed.

Lemma Complement_FamilyIntersection {U:Type} :
  ∀ F:Family U, Complement (⋂ F) =
  ⋃ ([ S : Ensemble U | Complement S ∈ F ]).
Proof.
intros. apply Extensionality_Ensembles; split; red; intros.
+ do 2 red in H. apply NNPP; intro. contradict H. constructor.
  intros. apply NNPP; intro. contradict H0. exists (Complement S).
  - constructor. rewrite Complement_Complement; trivial.
  - assumption.
+ intro. destruct H, H0. destruct H. apply H0 in H. do 2 red in H.
  contradiction.
Qed.

Lemma Complement_FamilyUnion {U:Type} :
  ∀ F:Family U, Complement (⋃ F) =
  ⋂ ([ S : Ensemble U | Complement S ∈ F ]).
Proof.
intros. apply Extensionality_Ensembles; split; red; intros.
+ do 2 red in H. constructor. intros. destruct H0. apply NNPP; intro.
  contradict H. exists (Complement S); trivial.
+ intro. destruct H, H0. revert H1; change (x ∈ Complement S).
  apply H. constructor. rewrite Complement_Complement; trivial.
Qed.

Lemma Complement_IndexedIntersection {A U:Type} :
  ∀ F:IndexedFamily A U, Complement (IndexedIntersection F) =
  ⋃ [a:A] (Complement (F a)).
Proof.
intros. apply Extensionality_Ensembles; split; red; intros.
+ apply NNPP; intro. do 2 red in H. contradict H. constructor.
  intros. apply NNPP; intro. contradict H0. exists a. assumption.
+ intro. destruct H, H0. auto.
Qed.

Lemma Complement_IndexedUnion {A U:Type} :
  ∀ F:IndexedFamily A U, Complement (IndexedUnion F) =
  ⋂ [a:A] (Complement (F a)).
Proof.
intros. apply Extensionality_Ensembles; split; red; intros.
+ constructor. intros. intro. do 2 red in H. contradict H.
  exists a; trivial.
+ intro. destruct H, H0. pose proof (H a). do 2 red in H1. contradiction.
Qed.
