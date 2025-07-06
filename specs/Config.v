From Stdlib Require Import
  Eqdep_dec
  PeanoNat.

Module Type LLSC_Config.
  Parameter (val_t : Type).
  Parameter (n : nat). (* Participant number *)
  Parameter (init_val : val_t).
  Parameter (n_pos : n > 0).

  Definition tag_t := { t : nat | t <=? 2 * n = true }.

  Module DecidableTypeBool <: DecidableType.
    Definition U := bool.
    Lemma eq_dec : forall (x y : U), {x = y} + {x <> y}.
    Proof.
      intros x y; destruct x; destruct y.
      1,4: left; auto.
      all: right; discriminate.
    Qed.
  End DecidableTypeBool.

  Module UIPBool := DecidableEqDep DecidableTypeBool.
  Definition bool_uip := UIPBool.UIP.

  Lemma tag_t_eq_dec : forall (t t' : tag_t), {t = t'} + {t <> t'}.
  Proof.
    intros t t'.
    destruct t; destruct t'.
    destruct (Nat.eq_dec x x0).
    - subst x0.
      left.
      f_equal.
      apply bool_uip.
    - right; intros Heq; injection Heq; intros; subst x0; contradiction.
  Qed.

  Lemma tag_nid_t_eq_dec : forall (t t' : tag_t * nat), {t = t'} + {t <> t'}.
  Proof.
    intros t t'.
    destruct t; destruct t'.
    destruct (tag_t_eq_dec t t0).
    - subst t0.
      destruct (Nat.eq_dec n0 n1).
      + subst n1; left; auto.
      + right; intros Heq; injection Heq; intros; subst n1; contradiction.
    - right; intros Heq; injection Heq; intros; subst t0; contradiction.
  Qed.

End LLSC_Config.
