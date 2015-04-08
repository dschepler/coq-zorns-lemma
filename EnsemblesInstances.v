Require Export Ensembles.
Require Import EnsemblesUtf8.
Require Export Morphisms.
Require Export RelationClasses.

Instance Included_PreOrder : forall X:Type,
  PreOrder (@Included X).
Proof.
constructor.
+ intros S. auto with sets.
+ intros S T U ? ?. auto with sets.
Qed.

Instance Included_PartialOrder : forall X:Type,
  PartialOrder eq (@Included X).
Proof.
constructor.
+ intros. subst x0. unfold Basics.flip; split; reflexivity.
+ intros. unfold Basics.flip in H; destruct H.
  apply Extensionality_Ensembles; split; assumption.
Qed.

Instance Intersection_incr : forall X:Type,
  Proper (Included ++> Included ++> Included) (@Intersection X).
Proof.
intros X S1 S2 ? T1 T2 ?. red; intros ? []; auto with sets.
Qed.

Instance Union_incr : forall X:Type,
  Proper (Included ++> Included ++> Included) (@Union X).
Proof.
intros X S1 S2 ? T1 T2 ?. red; intros ? [|]; auto with sets.
Qed.

Instance Complement_decr : forall X:Type,
  Proper (Included --> Included) (@Ensembles.Complement X).
Proof.
intros X S T ?. red in H. intros x ?. intro. do 2 red in H0.
auto with sets.
Qed.

Instance Setminus_incr_decr : forall X:Type,
  Proper (Included ++> Included --> Included) (@Setminus X).
Proof.
intros X S1 S2 ? T1 T2 ?. red; intros. red in H0. destruct H1.
auto with sets.
Qed.
