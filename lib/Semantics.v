Section Semantics.
  Record Semantics := {
    s_state : Type;
    s_init : s_state;
    s_step : s_state -> s_state -> Prop;
  }.

  Variable s : Semantics.

  Inductive reachable : s.(s_state) -> s.(s_state) -> Prop :=
  | reachable_self : forall st, reachable st st
  | reachable_step : forall st st' st'', reachable st st' -> s.(s_step) st' st'' -> reachable st st''.

  (* We could have defined valid_state st := reachable s.(s_init) st, but this definition is not very inconvenient for doing induction. *)
  Inductive valid_state : s.(s_state) -> Prop :=
  | valid_state_init : valid_state s.(s_init)
  | valid_state_step : forall st st', valid_state st -> s.(s_step) st st' -> valid_state st'.

  Lemma valid_reach_valid : forall st st', valid_state st -> reachable st st' -> valid_state st'.
  Proof. intros st st' Hval Hreach. induction Hreach. 1: auto. eapply valid_state_step. 1: apply IHHreach. all: auto. Qed.

  Lemma valid_init_reachable : forall st, valid_state st <-> reachable s.(s_init) st.
  Proof. intro st. split.
         - intro Hval. induction Hval. 1: apply reachable_self. eapply reachable_step. 1: apply IHHval. auto.
         - intro Hreach. remember (s_init s) as init. revert Heqinit. induction Hreach. 1: intro Heq; subst st; apply valid_state_init. intro Heq. specialize (IHHreach Heq). eapply valid_state_step. 1: apply IHHreach. auto.
  Qed.

  Lemma reachable_trans : forall st st' st'', reachable st st' -> reachable st' st'' -> reachable st st''.
  Proof. intros st st' st'' Hreach Hreach'. induction Hreach'.
         - auto.
         - specialize (IHHreach' Hreach). eapply reachable_step. 1: apply IHHreach'. auto.
  Qed.

End Semantics.
