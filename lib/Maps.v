From Stdlib Require Import
  List
  Peano_dec.
Import ListNotations.

Section Defs.
  Definition ListMap (T : Type) (U : Type) := list (T * U).
  Fixpoint list_map_find {T : Type} (t_eq_dec : forall (x y : T), {x = y} + {x <> y}) {U : Type} (x : T) (m : ListMap T U) :=
    match m with
    | [] => None
    | (a, b) :: c => match t_eq_dec x a with left _ => Some b | right _ => list_map_find t_eq_dec x c end
    end.
  Definition list_map_add {T : Type} {U : Type} (x : T) (y : U) (m : ListMap T U) := (x, y) :: m.
  Definition list_map_empty (T : Type) (U : Type) : ListMap T U := [].
End Defs.

Section Lemmas.
  Context {T : Type} (t_eq_dec : forall (a b : T), {a = b} + {a <> b}).
  Lemma list_map_gse : forall {U : Type} (m : ListMap T U) (x y : T) (z : U), x = y -> list_map_find t_eq_dec y (list_map_add x z m) = Some z.
  Proof. intros U m x y z Heq. cbn. destruct (t_eq_dec y x). 1: easy. symmetry in Heq; contradiction. Qed.
  Lemma list_map_gso : forall {U : Type} (m : ListMap T U) (x y : T) (z : U), x <> y -> list_map_find t_eq_dec y (list_map_add x z m) = list_map_find t_eq_dec y m.
  Proof. intros U m x y z Hneq. cbn. destruct (t_eq_dec y x). 1: symmetry in e; contradiction. easy. Qed.
End Lemmas.

Section Examples.
  Definition NatMap := ListMap nat.
  Definition NatMap_add {U : Type} (x : nat) (y : U) := list_map_add x y.
  Definition NatMap_find {U : Type} x (m : ListMap nat U) := list_map_find eq_nat_dec x m.
  Definition NatMap_empty (U : Type) := list_map_empty nat U.

  Lemma NatMap_gse : forall {T : Type} nmap r r' (e : T), r = r' -> NatMap_find r' (NatMap_add r e nmap) = Some e.
  Proof. unfold NatMap_find. unfold NatMap_add. apply list_map_gse. Qed.
  Lemma NatMap_gso : forall {T : Type} nmap r r' (e : T), r <> r' -> NatMap_find r' (NatMap_add r e nmap) = NatMap_find r' nmap.
  Proof. unfold NatMap_find. unfold NatMap_add. apply list_map_gso. Qed.
End Examples.

Ltac NatMap_rwe a b := repeat (match goal with |- context[NatMap_find a (NatMap_add b ?e ?nmap)] => replace (NatMap_find a (NatMap_add b e nmap)) with (Some e) by (rewrite (NatMap_gse nmap b a); auto) end).

(*
Lemma NatMap_rwe_test : forall x y (e : nat) nmap, x = y -> NatMap_find x (NatMap_add y e nmap) = Some e.
Proof. intros x y e nmap Heq. NatMap_rwe x y. easy. Qed.
*)

Ltac NatMap_rwo a b := repeat (match goal with |- context[NatMap_find a (NatMap_add b ?e ?nmap)] => replace (NatMap_find a (NatMap_add b e nmap)) with (NatMap_find a nmap) by (rewrite (NatMap_gso nmap b a); auto) end).

(*
Lemma NatMap_rwe_test : forall x y (e : nat) nmap, x <> y -> NatMap_find x (NatMap_add y e nmap) = NatMap_find x nmap.
Proof. intros x y e nmap Heq. NatMap_rwo x y. easy. Qed.
*)

Ltac NatMap_case a b := destruct (eq_nat_dec a b); [subst a; NatMap_rwe b b | NatMap_rwo a b].
Ltac NatMap_cmp a b := destruct (eq_nat_dec a b); [NatMap_rwe a b | NatMap_rwo a b].
