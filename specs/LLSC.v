(* Ideal functionality of non-faulty LL/SC *)

From Stdlib Require Import
  PeanoNat
  Lia.
From LLSC.lib Require Import
  Semantics
  Maps.
From LLSC.specs Require Import
  Config.

Module Type LLSC (Config : LLSC_Config).

  #[local] Notation val_t := Config.val_t.

  Inductive LLSC_Cmd :=
  | Idle
  | LLWait (v : nat)
  | LLDone
  | VLWait (v : nat)
  | VLDone (ret : bool)
  | SCWait (x : val_t)
  | SCDone (ret : bool).

  Record LLSC_State := {
    llsc_curr_ver : nat;
    llsc_curr_excl_ver : NatMap nat;
    llsc_val_hist : NatMap val_t;
    llsc_cmd : NatMap LLSC_Cmd;
  }.

  Definition llsc_init_state := {|
    llsc_curr_ver := 0;
    llsc_curr_excl_ver := NatMap_empty nat;
    llsc_val_hist := NatMap_add 0 Config.init_val (NatMap_empty val_t);
    llsc_cmd := NatMap_empty LLSC_Cmd;
  |}.

  Definition llsc_get_excl_ver (nid : nat) (st : LLSC_State) :=
    match NatMap_find nid st.(llsc_curr_excl_ver) with
    | None => 0
    | Some v => v
    end.

  Definition llsc_get_cmd (nid : nat) (st : LLSC_State) :=
    match NatMap_find nid st.(llsc_cmd) with
    | None => Idle
    | Some cmd => cmd
    end.

  (* State transitions *)
  Definition llsc_start_ll (nid : nat) (st : LLSC_State) := {|
    llsc_curr_ver := st.(llsc_curr_ver);
    llsc_curr_excl_ver := st.(llsc_curr_excl_ver);
    llsc_val_hist := st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid (LLWait st.(llsc_curr_ver)) st.(llsc_cmd);
  |}.

  Definition llsc_ret_ll (nid : nat) (v : nat) (st : LLSC_State) := {|
    llsc_curr_ver := st.(llsc_curr_ver);
    llsc_curr_excl_ver := NatMap_add nid v st.(llsc_curr_excl_ver);
    llsc_val_hist := st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid LLDone st.(llsc_cmd);
  |}.

  Definition llsc_cl (nid : nat) (st : LLSC_State) := {|
    llsc_curr_ver := st.(llsc_curr_ver);
    llsc_curr_excl_ver := st.(llsc_curr_excl_ver);
    llsc_val_hist := st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid Idle st.(llsc_cmd);
  |}.

  Definition llsc_start_vl (nid : nat) (st : LLSC_State) := {|
    llsc_curr_ver := st.(llsc_curr_ver);
    llsc_curr_excl_ver := st.(llsc_curr_excl_ver);
    llsc_val_hist := st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid (VLWait st.(llsc_curr_ver)) st.(llsc_cmd);
  |}.

  Definition llsc_succ_vl (nid : nat) (st : LLSC_State) := {|
    llsc_curr_ver := st.(llsc_curr_ver);
    llsc_curr_excl_ver := st.(llsc_curr_excl_ver);
    llsc_val_hist := st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid (VLDone true) st.(llsc_cmd);
  |}.

  Definition llsc_fail_vl (nid : nat) (st : LLSC_State) := {|
    llsc_curr_ver := st.(llsc_curr_ver);
    llsc_curr_excl_ver := st.(llsc_curr_excl_ver);
    llsc_val_hist := st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid (VLDone false) st.(llsc_cmd);
  |}.

  Definition llsc_ret_vl (nid : nat) (st : LLSC_State) := {|
    llsc_curr_ver := st.(llsc_curr_ver);
    llsc_curr_excl_ver := st.(llsc_curr_excl_ver);
    llsc_val_hist := st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid LLDone st.(llsc_cmd);
  |}.

  Definition llsc_start_sc (nid : nat) (x : val_t) (st : LLSC_State) := {|
    llsc_curr_ver := st.(llsc_curr_ver);
    llsc_curr_excl_ver := st.(llsc_curr_excl_ver);
    llsc_val_hist := st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid (SCWait x) st.(llsc_cmd);
  |}.

  Definition llsc_succ_sc (nid : nat) (x : val_t) (st : LLSC_State) := {|
    llsc_curr_ver := S st.(llsc_curr_ver);
    llsc_curr_excl_ver := st.(llsc_curr_excl_ver);
    llsc_val_hist := NatMap_add (S st.(llsc_curr_ver)) x st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid (SCDone true) st.(llsc_cmd);
  |}.

  Definition llsc_fail_sc (nid : nat) (st : LLSC_State) := {|
    llsc_curr_ver := st.(llsc_curr_ver);
    llsc_curr_excl_ver := st.(llsc_curr_excl_ver);
    llsc_val_hist := st.(llsc_val_hist);
    llsc_cmd := NatMap_add nid (SCDone false) st.(llsc_cmd);
  |}.

  Inductive llsc_call_step : LLSC_State -> LLSC_State -> Prop :=
  | llsc_call_step_ll : forall nid st,
      nid < Config.n ->
      llsc_get_cmd nid st = Idle ->
      llsc_call_step st (llsc_start_ll nid st)
  | llsc_call_step_cl : forall nid st,
      nid < Config.n ->
      llsc_get_cmd nid st = LLDone ->
      llsc_call_step st (llsc_cl nid st)
  | llsc_call_step_vl : forall nid st,
      nid < Config.n ->
      llsc_get_cmd nid st = LLDone ->
      llsc_call_step st (llsc_start_vl nid st)
  | llsc_call_step_sc : forall nid x st,
      nid < Config.n ->
      llsc_get_cmd nid st = LLDone ->
      llsc_call_step st (llsc_start_sc nid x st).

  Inductive llsc_vl_step : LLSC_State -> LLSC_State -> Prop :=
  | llsc_ret_step_vl_succ : forall nid v st,
      nid < Config.n ->
      llsc_get_cmd nid st = VLWait v ->
      llsc_get_excl_ver nid st = v ->
      llsc_vl_step st (llsc_succ_vl nid st)
  | llsc_ret_step_vl_fail : forall nid v st,
      nid < Config.n ->
      llsc_get_cmd nid st = VLWait v ->
      llsc_get_excl_ver nid st < st.(llsc_curr_ver) ->
      llsc_vl_step st (llsc_fail_vl nid st).

  Inductive llsc_sc_step : LLSC_State -> LLSC_State -> Prop :=
  | llsc_ret_step_sc_succ : forall nid x st,
      nid < Config.n ->
      llsc_get_cmd nid st = SCWait x ->
      llsc_get_excl_ver nid st = st.(llsc_curr_ver) ->
      llsc_sc_step st (llsc_succ_sc nid x st)
  | llsc_ret_step_sc_fail : forall nid x st,
      nid < Config.n ->
      llsc_get_cmd nid st = SCWait x ->
      llsc_get_excl_ver nid st < st.(llsc_curr_ver) ->
      llsc_sc_step st (llsc_fail_sc nid st).

  Inductive llsc_ret_step : LLSC_State -> LLSC_State -> Prop :=
  | llsc_ret_step_ll : forall nid v v' st,
      nid < Config.n ->
      llsc_get_cmd nid st = LLWait v ->
      v <= v' <= st.(llsc_curr_ver) ->
      llsc_ret_step st (llsc_ret_ll nid v' st)
  | llsc_ret_step_vl : forall nid b st,
      nid < Config.n ->
      llsc_get_cmd nid st = VLDone b ->
      llsc_ret_step st (llsc_ret_vl nid st)
  | llsc_ret_step_sc : forall nid b st,
      nid < Config.n ->
      llsc_get_cmd nid st = SCDone b ->
      llsc_ret_step st (llsc_cl nid st).

  Definition llsc_step st st' := llsc_call_step st st' \/ llsc_vl_step st st' \/ llsc_sc_step st st' \/ llsc_ret_step st st'.

  Definition llsc_sem : Semantics := {|
    s_state := LLSC_State;
    s_init := llsc_init_state;
    s_step := llsc_step;
  |}.

  #[local] Notation llsc_valid st := (valid_state llsc_sem st).
  #[local] Notation llsc_reachable st st' := (reachable llsc_sem st st').

  Ltac llsc_unfold := unfold llsc_start_ll, llsc_ret_ll, llsc_cl, llsc_start_vl, llsc_succ_vl, llsc_fail_vl, llsc_ret_vl, llsc_start_sc, llsc_succ_sc, llsc_fail_sc, llsc_get_excl_ver, llsc_get_cmd.
  Ltac llsc_reduce := cbn [llsc_curr_ver llsc_curr_excl_ver llsc_val_hist llsc_cmd].

  Ltac step_case Hstep :=
    destruct Hstep as [Hstep | [Hstep | [Hstep | Hstep]]];
    [ destruct Hstep as [nid st Hpre1 Hpre2 | nid st Hpre1 Hpre2 | nid st Hpre1 Hpre2 | nid x st Hpre1 Hpre2] |
      destruct Hstep as [nid v st Hpre1 Hpre2 Hpre3 | nid v st Hpre1 Hpre2 Hpre3] |
      destruct Hstep as [nid x st Hpre1 Hpre2 Hpre3 | nid x st Hpre1 Hpre2 Hpre3] |
      destruct Hstep as [nid v v' st Hpre1 Hpre2 Hpre3 | nid b st Hpre1 Hpre2 | nid b st Hpre1 Hpre2]
    ].

  Lemma llsc_excl_ver_le : forall nid st,
    llsc_valid st ->
    llsc_get_excl_ver nid st <= st.(llsc_curr_ver).
  Proof.
    intros NID st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; auto.
    - step_case Hstep.
      all: llsc_unfold; llsc_reduce; destruct (Nat.eq_dec NID nid); [subst NID; try rewrite NatMap_gse by auto; try apply IH | try rewrite NatMap_gso by auto; try apply IH].
      all: try (fold (llsc_get_excl_ver nid st); lia).
      all: try (fold (llsc_get_excl_ver NID st); lia).
  Qed.

  Lemma llsc_ll_wait_phase_prop : forall nid v st,
    llsc_valid st ->
    llsc_get_cmd nid st = LLWait v ->
    v <= st.(llsc_curr_ver).
  Proof.
    intros NID V st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - step_case Hstep.
      all: llsc_unfold; llsc_reduce; destruct (Nat.eq_dec NID nid); [subst NID; rewrite NatMap_gse by auto; try discriminate | rewrite NatMap_gso by auto; try apply IH].
      + intros Heq; injection Heq; intros; subst V; auto.
      + intros Heq; specialize (IH Heq); lia.
  Qed.

  Lemma llsc_vl_wait_phase_prop1 : forall nid v st,
    llsc_valid st ->
    llsc_get_cmd nid st = VLWait v ->
    v <= st.(llsc_curr_ver).
  Proof.
    intros NID V st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - step_case Hstep.
      all: llsc_unfold; llsc_reduce; destruct (Nat.eq_dec NID nid); [subst NID; rewrite NatMap_gse by auto; try discriminate | rewrite NatMap_gso by auto; try apply IH].
      + intros Heq; injection Heq; intros; subst V; auto.
      + intros Heq; specialize (IH Heq); lia.
  Qed.

  Lemma llsc_vl_wait_phase_prop2 : forall nid v st,
    llsc_valid st ->
    llsc_get_cmd nid st = VLWait v ->
    llsc_get_excl_ver nid st <= v.
  Proof.
    intros NID V st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - step_case Hstep.
      all: llsc_unfold; llsc_reduce; destruct (Nat.eq_dec NID nid); [subst NID; rewrite NatMap_gse by auto; try discriminate | rewrite NatMap_gso by auto; try apply IH].
      + intros Hphase; injection Hphase; intros; subst V.
        apply llsc_excl_ver_le; auto.
      + rewrite NatMap_gso by auto.
        auto.
  Qed.

End LLSC.
