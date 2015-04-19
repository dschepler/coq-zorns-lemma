Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Require Export Morphisms.
Require Import FunctionalExtensionality.

Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X :=
  [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.

Instance inverse_image_increasing : forall {X Y:Type} (f:X->Y),
  Proper (Included ++> Included) (inverse_image f).
Proof.
intros. intros T1 T2 ?. red; intros. destruct H0. constructor. auto.
Qed.

Lemma inverse_image_empty: forall {X Y:Type} (f:X->Y),
  inverse_image f Empty_set = Empty_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H as [[]].
destruct H.
Qed.

Lemma inverse_image_full: forall {X Y:Type} (f:X->Y),
  inverse_image f Full_set = Full_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros;
  constructor; constructor.
Qed.

Lemma inverse_image_intersection: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), inverse_image f (Intersection T1 T2) =
  Intersection (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
inversion H.
constructor; constructor; trivial.

destruct H as [? [] []].
constructor; constructor; trivial.
Qed.

Lemma inverse_image_union: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), inverse_image f (Union T1 T2) =
  Union (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
inversion H.
left; constructor; trivial.
right; constructor; trivial.

constructor.
destruct H as [? []|? []].
left; trivial.
right; trivial.
Qed.

Lemma inverse_image_complement: forall {X Y:Type} (f:X->Y)
  (T:Ensemble Y), inverse_image f (Complement T) =
  Complement (inverse_image f T).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
red; intro.
destruct H.
destruct H0.
contradiction H.

constructor.
intro.
contradiction H.
constructor; trivial.
Qed.

Definition composition {Y Z:Type} (f:Y->Z) {X:Type} (g:X->Y) : X->Z :=
fun x => f (g x).

Infix "○" := composition (left associativity, at level 25).

Lemma inverse_image_composition: forall {Y Z:Type} (f:Y->Z) {X:Type} (g:X->Y),
  inverse_image (f ○ g) = inverse_image g ○ inverse_image f.
Proof.
intros. extensionality T; unfold composition.
apply Extensionality_Ensembles; split; red; intros.
+ constructor; constructor. destruct H. assumption.
+ constructor. destruct H. destruct H. assumption.
Qed.

Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full
  @inverse_image_intersection @inverse_image_union
  @inverse_image_complement @inverse_image_composition : sets.
