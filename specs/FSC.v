(* Ideal functionality of non-faulty LL/SC *)

From Stdlib Require Import
  PeanoNat
  Lia
  Structures.Equalities.
From LLSC.lib Require Import
  Semantics
  Maps.
From LLSC.specs Require Import
  Config.

Module Type FSC (Config : LLSC_Config).

  #[local] Notation val_t := Config.val_t.
  #[local] Notation tag_t := Config.tag_t.

  Inductive FSC_Cmd :=
  | Idle
  | LLWait (v : nat)
  | LLDone
  | SCWait (x : val_t) (t : tag_t)
  | SCDone (ret : bool)
  | WriteWait (x : val_t) (t : tag_t).

  Record FSC_State := {
    fsc_curr_ver : nat;
    fsc_curr_excl_ver : NatMap nat;
    fsc_val_hist : NatMap (val_t * (tag_t * nat));
    fsc_cmd : NatMap FSC_Cmd;
    fsc_succ_count : NatMap nat;
    fsc_local_ver : NatMap nat;
  }.

  Definition zero_tag : tag_t.
    unfold tag_t; exists 0; rewrite Nat.leb_le; lia.
  Defined.

  Definition fsc_init_state := {|
    fsc_curr_ver := 0;
    fsc_curr_excl_ver := NatMap_empty nat;
    fsc_val_hist := NatMap_add 0 (Config.init_val, (zero_tag, 0)) (NatMap_empty (val_t * (tag_t * nat)));
    fsc_cmd := NatMap_empty FSC_Cmd;
    fsc_succ_count := NatMap_add 0 1 (NatMap_empty nat);
    fsc_local_ver := NatMap_add 0 0 (NatMap_empty nat);
  |}.

  Definition fsc_get_excl_ver (nid : nat) (st : FSC_State) :=
    match NatMap_find nid st.(fsc_curr_excl_ver) with
    | None => 0
    | Some v => v
    end.

  Definition fsc_get_cmd (nid : nat) (st : FSC_State) :=
    match NatMap_find nid st.(fsc_cmd) with
    | None => Idle
    | Some cmd => cmd
    end.

  Definition fsc_get_succ_count (nid : nat) (st : FSC_State) :=
    match NatMap_find nid st.(fsc_succ_count) with
    | None => 0
    | Some n => n
    end.

  (* State transitions *)
  Definition fsc_start_ll (nid : nat) (st : FSC_State) := {|
    fsc_curr_ver := st.(fsc_curr_ver);
    fsc_curr_excl_ver := st.(fsc_curr_excl_ver);
    fsc_val_hist := st.(fsc_val_hist);
    fsc_cmd := NatMap_add nid (LLWait st.(fsc_curr_ver)) st.(fsc_cmd);
    fsc_succ_count := st.(fsc_succ_count);
    fsc_local_ver := st.(fsc_local_ver);
  |}.

  Definition fsc_ret_ll (nid : nat) (v : nat) (st : FSC_State) := {|
    fsc_curr_ver := st.(fsc_curr_ver);
    fsc_curr_excl_ver := NatMap_add nid v st.(fsc_curr_excl_ver);
    fsc_val_hist := st.(fsc_val_hist);
    fsc_cmd := NatMap_add nid LLDone st.(fsc_cmd);
    fsc_succ_count := st.(fsc_succ_count);
    fsc_local_ver := st.(fsc_local_ver);
  |}.

  Definition fsc_cl (nid : nat) (st : FSC_State) := {|
    fsc_curr_ver := st.(fsc_curr_ver);
    fsc_curr_excl_ver := st.(fsc_curr_excl_ver);
    fsc_val_hist := st.(fsc_val_hist);
    fsc_cmd := NatMap_add nid Idle st.(fsc_cmd);
    fsc_succ_count := st.(fsc_succ_count);
    fsc_local_ver := st.(fsc_local_ver);
  |}.

  Definition fsc_start_sc (nid : nat) (x : val_t) (t : tag_t) (st : FSC_State) := {|
    fsc_curr_ver := st.(fsc_curr_ver);
    fsc_curr_excl_ver := st.(fsc_curr_excl_ver);
    fsc_val_hist := st.(fsc_val_hist);
    fsc_cmd := NatMap_add nid (SCWait x t) st.(fsc_cmd);
    fsc_succ_count := st.(fsc_succ_count);
    fsc_local_ver := st.(fsc_local_ver);
  |}.

  Definition fsc_succ_sc (nid : nat) (x : val_t) (t : tag_t) (st : FSC_State) := {|
    fsc_curr_ver := S st.(fsc_curr_ver);
    fsc_curr_excl_ver := st.(fsc_curr_excl_ver);
    fsc_val_hist := NatMap_add (S st.(fsc_curr_ver)) (x, (t, nid)) st.(fsc_val_hist);
    fsc_cmd := NatMap_add nid (SCDone true) st.(fsc_cmd);
    fsc_succ_count := NatMap_add nid (S (fsc_get_succ_count nid st)) st.(fsc_succ_count);
    fsc_local_ver := NatMap_add (S st.(fsc_curr_ver)) (fsc_get_succ_count nid st) st.(fsc_local_ver);
  |}.

  Definition fsc_fail_sc (nid : nat) (st : FSC_State) := {|
    fsc_curr_ver := st.(fsc_curr_ver);
    fsc_curr_excl_ver := st.(fsc_curr_excl_ver);
    fsc_val_hist := st.(fsc_val_hist);
    fsc_cmd := NatMap_add nid (SCDone false) st.(fsc_cmd);
    fsc_succ_count := st.(fsc_succ_count);
    fsc_local_ver := st.(fsc_local_ver);
  |}.

  Definition fsc_start_write (nid : nat) (x : val_t) (t : tag_t) (st : FSC_State) := {|
    fsc_curr_ver := st.(fsc_curr_ver);
    fsc_curr_excl_ver := st.(fsc_curr_excl_ver);
    fsc_val_hist := st.(fsc_val_hist);
    fsc_cmd := NatMap_add nid (WriteWait x t) st.(fsc_cmd);
    fsc_succ_count := st.(fsc_succ_count);
    fsc_local_ver := st.(fsc_local_ver);
  |}.

  Definition fsc_ret_write (nid : nat) (x : val_t) (t : tag_t) (st : FSC_State) := {|
    fsc_curr_ver := S st.(fsc_curr_ver);
    fsc_curr_excl_ver := st.(fsc_curr_excl_ver);
    fsc_val_hist := NatMap_add (S st.(fsc_curr_ver)) (x, (t, nid)) st.(fsc_val_hist);
    fsc_cmd := NatMap_add nid Idle st.(fsc_cmd);
    fsc_succ_count := NatMap_add nid (S (fsc_get_succ_count nid st)) st.(fsc_succ_count);
    fsc_local_ver := NatMap_add (S st.(fsc_curr_ver)) (fsc_get_succ_count nid st) st.(fsc_local_ver);
  |}.

  Inductive fsc_call_step : FSC_State -> FSC_State -> Prop :=
  | fsc_call_step_ll : forall nid st,
      nid < Config.n ->
      fsc_get_cmd nid st = Idle ->
      fsc_call_step st (fsc_start_ll nid st)
  | fsc_call_step_cl : forall nid st,
      nid < Config.n ->
      fsc_get_cmd nid st = LLDone ->
      fsc_call_step st (fsc_cl nid st)
  | fsc_call_step_sc : forall nid x t st,
      nid < Config.n ->
      fsc_get_cmd nid st = LLDone ->
      fsc_call_step st (fsc_start_sc nid x t st)
  | fsc_call_step_write : forall nid x t st,
      nid < Config.n ->
      fsc_get_cmd nid st = Idle ->
      fsc_call_step st (fsc_start_write nid x t st).

  Inductive fsc_sc_step : FSC_State -> FSC_State -> Prop :=
  | fsc_ret_step_sc_succ : forall nid x t st,
      nid < Config.n ->
      fsc_get_cmd nid st = SCWait x t ->
      fsc_get_excl_ver nid st = st.(fsc_curr_ver) ->
      fsc_sc_step st (fsc_succ_sc nid x t st)
  | fsc_ret_step_sc_fail : forall nid x t st,
      nid < Config.n ->
      fsc_get_cmd nid st = SCWait x t ->
      fsc_sc_step st (fsc_fail_sc nid st).

  Inductive fsc_ret_step : FSC_State -> FSC_State -> Prop :=
  | fsc_ret_step_ll : forall nid v v' st,
      nid < Config.n ->
      fsc_get_cmd nid st = LLWait v ->
      v <= v' <= st.(fsc_curr_ver) ->
      fsc_ret_step st (fsc_ret_ll nid v' st)
  | fsc_ret_step_sc : forall nid b st,
      nid < Config.n ->
      fsc_get_cmd nid st = SCDone b ->
      fsc_ret_step st (fsc_cl nid st)
  | fsc_ret_step_write : forall nid x t st,
      nid < Config.n ->
      fsc_get_cmd nid st = WriteWait x t ->
      fsc_ret_step st (fsc_ret_write nid x t st).

  Definition fsc_step st st' := fsc_call_step st st' \/ fsc_sc_step st st' \/ fsc_ret_step st st'.

  Definition fsc_sem : Semantics := {|
    s_state := FSC_State;
    s_init := fsc_init_state;
    s_step := fsc_step;
  |}.

  #[local] Notation fsc_valid st := (valid_state fsc_sem st).
  #[local] Notation fsc_reachable st st' := (reachable fsc_sem st st').

  Ltac step_case Hstep :=
    match type of Hstep with fsc_step ?st ?st' =>
    unfold fsc_step in Hstep;
    destruct Hstep as [Hstep | [Hstep | Hstep]];
    [ destruct Hstep as [nid st Hpre1 Hpre2 | nid st Hpre1 Hpre2 | nid x t st Hpre1 Hpre2 | nid x t st Hpre1 Hpre2] |
      destruct Hstep as [nid x t st Hpre1 Hpre2 Hpre3 | nid x t st Hpre1 Hpre2] |
      destruct Hstep as [nid v v' st Hpre1 Hpre2 Hpre3 | nid b st Hpre1 Hpre2 | nid x t st Hpre1 Hpre2]
    ]
    end.

  Ltac fsc_unfold := unfold fsc_start_ll, fsc_cl, fsc_start_sc, fsc_start_write, fsc_succ_sc, fsc_fail_sc, fsc_ret_ll, fsc_ret_write, fsc_get_cmd, fsc_get_excl_ver, fsc_get_succ_count.
  Ltac fsc_reduce := cbn [fsc_curr_ver fsc_curr_excl_ver fsc_val_hist fsc_cmd fsc_succ_count fsc_local_ver].

  Lemma fsc_ver_mono : forall st st', fsc_reachable st st' -> st.(fsc_curr_ver) <= st'.(fsc_curr_ver).
  Proof.
    intros st st' Hreach.
    induction Hreach as [st | st st' st'' Hreach IH Hstep].
    - auto.
    - cbn in Hstep; step_case Hstep; cbn; auto.
  Qed.

  Lemma fsc_wait_ver : forall st nid v,
    fsc_valid st ->
    fsc_get_cmd nid st = LLWait v ->
    v <= st.(fsc_curr_ver).
  Proof.
    intros st nid v Hval.
    revert nid v.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - cbn in Hstep; step_case Hstep.
      all: intros nid'' v''.
      all: fsc_unfold; fsc_reduce; NatMap_case nid'' nid; try discriminate; try apply IH; auto.
      + intros Heq; injection Heq; intros; subst v''; auto.
      + intros Hcmd.
        specialize (IH nid'' v'' Hcmd).
        lia.
      + intros Hcmd.
        specialize (IH nid'' v'' Hcmd).
        lia.
  Qed.

  Lemma fsc_val_hist_not_none : forall st v,
    fsc_valid st ->
    v <= st.(fsc_curr_ver) ->
    NatMap_find v st.(fsc_val_hist) <> None.
  Proof.
    intros st v Hval.
    revert v.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; intros v Hv.
      destruct (Nat.eq_dec v 0); [discriminate | lia].
    - cbn in Hstep; step_case Hstep.
      all: fsc_unfold; fsc_reduce.
      all: try apply IH.
      + intros v' Hv'.
        assert (Hv'2 : v' <= fsc_curr_ver st \/ v' = S (fsc_curr_ver st)) by lia.
        destruct Hv'2 as [Hv'2 | Hv'2].
        * rewrite NatMap_gso by lia.
          apply IH; auto.
        * subst v'; rewrite NatMap_gse by auto; discriminate.
      + intros v' Hv'.
        assert (Hv'2 : v' <= fsc_curr_ver st \/ v' = S (fsc_curr_ver st)) by lia.
        destruct Hv'2 as [Hv'2 | Hv'2].
        * rewrite NatMap_gso by lia.
          apply IH; auto.
        * subst v'; rewrite NatMap_gse by auto; discriminate.
  Qed.

  Lemma fsc_val_hist_valid : forall st v,
    fsc_valid st ->
    NatMap_find v st.(fsc_val_hist) <> None ->
    v <= st.(fsc_curr_ver).
  Proof.
    intros st v Hval.
    revert v.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; intros v Hv.
      destruct (Nat.eq_dec v 0); [lia | contradiction].
    - cbn in Hstep; step_case Hstep.
      all: fsc_unfold; fsc_reduce.
      all: try apply IH.
      + intros v' Hv'.
        destruct (Nat.eq_dec v' (S (fsc_curr_ver st))).
        * subst v'; lia.
        * rewrite NatMap_gso in Hv' by auto.
          specialize (IH _ Hv'); lia.
      + intros v' Hv'.
        destruct (Nat.eq_dec v' (S (fsc_curr_ver st))).
        * subst v'; lia.
        * rewrite NatMap_gso in Hv' by auto.
          specialize (IH _ Hv'); lia.
  Qed.

  Lemma fsc_val_author_valid : forall st v entry,
    fsc_valid st ->
    NatMap_find v st.(fsc_val_hist) = Some entry ->
    snd (snd entry) < Config.n.
  Proof.
    intros st v entry Hval.
    revert v entry.
    induction Hval as [| st st' Hval IH Hstep].
    - intros v entry; cbn.
      destruct (Nat.eq_dec v 0); try discriminate.
      intros Hentry; injection Hentry; intros; subst entry; clear Hentry; cbn.
      apply Config.n_pos.
    - cbn in Hstep; step_case Hstep.
      all: fsc_unfold; fsc_reduce.
      all: try apply IH.
      + intros v' entry'.
        destruct (Nat.eq_dec v' (S (fsc_curr_ver st))).
        * subst v'; rewrite NatMap_gse by auto.
          intros Heq; injection Heq; intros Heq2; subst entry'.
          cbn; auto.
        * rewrite NatMap_gso by auto.
          apply IH; auto.
      + intros v' entry'.
        destruct (Nat.eq_dec v' (S (fsc_curr_ver st))).
        * subst v'; rewrite NatMap_gse by auto.
          intros Heq; injection Heq; intros Heq2; subst entry'.
          cbn; auto.
        * rewrite NatMap_gso by auto.
          apply IH; auto.
  Qed.

  Lemma fsc_val_local_ver_not_none : forall st v,
    fsc_valid st ->
    v <= st.(fsc_curr_ver) ->
    NatMap_find v st.(fsc_local_ver) <> None.
  Proof.
    intros st v Hval.
    revert v.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; intros v Hv.
      replace v with 0 by lia; cbn; discriminate.
    - cbn in Hstep; step_case Hstep.
      all: fsc_unfold; fsc_reduce.
      all: try apply IH.
      + intros v' Hv'.
        assert (Hv'2 : v' <= fsc_curr_ver st \/ v' = S (fsc_curr_ver st)) by lia.
        destruct Hv'2 as [Hv'2 | Hv'2].
        * rewrite NatMap_gso by lia; apply IH; auto.
        * subst v'; rewrite NatMap_gse; auto; discriminate.
      + intros v' Hv'.
        assert (Hv'2 : v' <= fsc_curr_ver st \/ v' = S (fsc_curr_ver st)) by lia.
        destruct Hv'2 as [Hv'2 | Hv'2].
        * rewrite NatMap_gso by lia; apply IH; auto.
        * subst v'; rewrite NatMap_gse; auto; discriminate.
  Qed.

  Lemma fsc_local_ver_valid : forall st v,
    fsc_valid st ->
    NatMap_find v st.(fsc_local_ver) <> None ->
    v <= st.(fsc_curr_ver).
  Proof.
    intros st v Hval.
    revert v.
    induction Hval as [| st st' Hval IH Hstep].
    - intros v; cbn; destruct (Nat.eq_dec v 0); [lia | contradiction].
    - cbn in Hstep; step_case Hstep.
      all: fsc_unfold; fsc_reduce.
      all: try apply IH.
      + intros v' Hv'.
        destruct (Nat.eq_dec v' (S (fsc_curr_ver st))).
        * subst v'; lia.
        * rewrite NatMap_gso in Hv' by auto.
          specialize (IH _ Hv'); lia.
      + intros v' Hv'.
        destruct (Nat.eq_dec v' (S (fsc_curr_ver st))).
        * subst v'; lia.
        * rewrite NatMap_gso in Hv' by auto.
          specialize (IH _ Hv'); lia.
  Qed.

  Lemma fsc_ver_hist_mono : forall st st' v,
    fsc_valid st ->
    fsc_reachable st st' ->
    NatMap_find v st.(fsc_val_hist) <> None ->
    NatMap_find v st'.(fsc_val_hist) = NatMap_find v st.(fsc_val_hist).
  Proof.
    intros st st' v'' Hval Hreach.
    induction Hreach as [st | st st' st'' Hreach IH Hstep].
    - auto.
    - cbn in Hstep; step_case Hstep; specialize (IH Hval).
      all: try (fsc_unfold; fsc_reduce; apply IH).
      + intros Hnone; specialize (IH Hnone).
        rewrite <- IH in Hnone.
        pose proof (valid_reach_valid _ _ _ Hval Hreach) as Hval'.
        pose proof (fsc_val_hist_valid _ _ Hval' Hnone).
        fsc_unfold; fsc_reduce; rewrite NatMap_gso by lia; auto.
      + intros Hnone; specialize (IH Hnone).
        rewrite <- IH in Hnone.
        pose proof (valid_reach_valid _ _ _ Hval Hreach) as Hval'.
        pose proof (fsc_val_hist_valid _ _ Hval' Hnone).
        fsc_unfold; fsc_reduce; rewrite NatMap_gso by lia; auto.
  Qed.

  Lemma fsc_val_hist_zero : forall st,
    fsc_valid st -> NatMap_find 0 st.(fsc_val_hist) = Some (Config.init_val, (zero_tag, 0)).
  Proof.
    intros st Hval'.
    rewrite valid_init_reachable in Hval'; cbn in Hval'.
    assert (Hval : fsc_valid fsc_init_state) by apply valid_state_init.
    pose proof (fsc_ver_hist_mono _ _ 0 Hval Hval' ltac:(cbn; discriminate)) as Heq.
    rewrite Heq; cbn; auto.
  Qed.

  Lemma fsc_local_ver_mono : forall st st' v,
    fsc_valid st ->
    fsc_reachable st st' ->
    NatMap_find v st.(fsc_local_ver) <> None ->
    NatMap_find v st'.(fsc_local_ver) = NatMap_find v st.(fsc_local_ver).
  Proof.
    intros st st' v'' Hval Hreach.
    induction Hreach as [st | st st' st'' Hreach IH Hstep].
    - auto.
    - cbn in Hstep; step_case Hstep; specialize (IH Hval).
      all: try (fsc_unfold; fsc_reduce; apply IH).
      + intros Hnone; specialize (IH Hnone).
        rewrite <- IH in Hnone.
        pose proof (valid_reach_valid _ _ _ Hval Hreach) as Hval'.
        pose proof (fsc_local_ver_valid _ _ Hval' Hnone).
        fsc_unfold; fsc_reduce; rewrite NatMap_gso by lia; auto.
      + intros Hnone; specialize (IH Hnone).
        rewrite <- IH in Hnone.
        pose proof (valid_reach_valid _ _ _ Hval Hreach) as Hval'.
        pose proof (fsc_local_ver_valid _ _ Hval' Hnone).
        fsc_unfold; fsc_reduce; rewrite NatMap_gso by lia; auto.
  Qed.

  Lemma fsc_local_ver_zero : forall st,
    fsc_valid st -> NatMap_find 0 st.(fsc_local_ver) = Some 0.
  Proof.
    intros st Hval'.
    rewrite valid_init_reachable in Hval'; cbn in Hval'.
    assert (Hval : fsc_valid fsc_init_state) by apply valid_state_init.
    pose proof (fsc_local_ver_mono _ _ 0 Hval Hval' ltac:(cbn; discriminate)) as Heq.
    rewrite Heq; cbn; auto.
  Qed.

  Lemma fsc_local_ver_lt_succ_count : forall st v entry nid lv,
    fsc_valid st ->
    NatMap_find v st.(fsc_val_hist) = Some entry ->
    nid = snd (snd entry) ->
    NatMap_find v st.(fsc_local_ver) = Some lv ->
    lv < fsc_get_succ_count nid st.
  Proof.
    intros st v entry nid lv Hval.
    revert v entry nid lv.
    induction Hval as [| st st' Hval IH Hstep].
    - intros v entry nid lv; cbn; destruct (Nat.eq_dec v 0); try discriminate.
      intros Hentry; injection Hentry; intros Heq; subst entry; clear Hentry.
      cbn; intros Hnid Hlv; injection Hlv; intros Heq; subst nid lv.
      cbn; auto.
    - cbn in Hstep; step_case Hstep.
      all: fsc_unfold; fsc_reduce.
      all: try apply IH.
      + intros v' entry' nid' lv'.
        destruct (Nat.eq_dec v' (S (fsc_curr_ver st))).
        * subst v'; repeat rewrite NatMap_gse by auto.
          intros Hentry' Hnid'.
          injection Hentry'; intros Hentry'2; subst entry'; clear Hentry'.
          cbn in Hnid'; subst nid'.
          rewrite NatMap_gse by auto.
          intros Heq; injection Heq; intros Heq2; subst lv'.
          lia.
        * repeat rewrite NatMap_gso by auto.
          intros Hentry' Hnid' Hlv'.
          specialize (IH _ _ _ _ Hentry' Hnid' Hlv').
          destruct (Nat.eq_dec nid' nid).
          -- subst nid'; rewrite NatMap_gse by auto.
             unfold fsc_get_succ_count in IH; rewrite e in IH; lia.
          -- rewrite NatMap_gso by auto.
             unfold fsc_get_succ_count in IH; auto.
      + intros v' entry' nid' lv'.
        destruct (Nat.eq_dec v' (S (fsc_curr_ver st))).
        * subst v'; repeat rewrite NatMap_gse by auto.
          intros Hentry' Hnid'.
          injection Hentry'; intros Hentry'2; subst entry'; clear Hentry'.
          cbn in Hnid'; subst nid'.
          rewrite NatMap_gse by auto.
          intros Heq; injection Heq; intros Heq2; subst lv'.
          lia.
        * repeat rewrite NatMap_gso by auto.
          intros Hentry' Hnid' Hlv'.
          specialize (IH _ _ _ _ Hentry' Hnid' Hlv').
          destruct (Nat.eq_dec nid' nid).
          -- subst nid'; rewrite NatMap_gse by auto.
             unfold fsc_get_succ_count in IH; rewrite e in IH; lia.
          -- rewrite NatMap_gso by auto.
             unfold fsc_get_succ_count in IH; auto.
  Qed.

  Lemma fsc_succ_count_exist : forall st nid,
    fsc_valid st ->
    fsc_get_succ_count nid st = 0 \/
    exists v entry,
      NatMap_find v st.(fsc_val_hist) = Some entry /\
      snd (snd entry) = nid /\
      NatMap_find v st.(fsc_local_ver) = Some (fsc_get_succ_count nid st - 1).
  Proof.
    intros st nid Hval.
    revert nid.
    induction Hval as [| st st' Hval IH Hstep].
    - intros nid; destruct (Nat.eq_dec nid 0).
      2: left; fsc_unfold; cbn; destruct (Nat.eq_dec nid 0); [contradiction | auto].
      subst nid; cbn; right; exists 0; eexists; cbn; repeat split.
    - cbn in Hstep; step_case Hstep.
      all: fsc_unfold; fsc_reduce.
      all: try apply IH.
      + intros nid'.
        destruct (Nat.eq_dec nid' nid).
        * subst nid'; repeat rewrite NatMap_gse by auto.
          right.
          repeat eexists.
          1: rewrite NatMap_gse.
          1,2: reflexivity.
          1: cbn; auto.
          rewrite NatMap_gse by auto.
          f_equal; lia.
        * repeat rewrite NatMap_gso by auto.
          specialize (IH nid').
          destruct IH as [IH | (v & entry & IH)].
          1: left; apply IH.
          right; exists v; exists entry.
          destruct IH as (IH1 & IH2 & IH3).
          pose proof (fsc_val_hist_valid _ _ Hval ltac:(rewrite IH1; discriminate)) as Hv.
          repeat split; auto.
          all: rewrite NatMap_gso by lia; auto.
      + intros nid'.
        destruct (Nat.eq_dec nid' nid).
        * subst nid'; repeat rewrite NatMap_gse by auto.
          right.
          repeat eexists.
          1: rewrite NatMap_gse.
          1,2: reflexivity.
          1: cbn; auto.
          rewrite NatMap_gse by auto.
          f_equal; lia.
        * repeat rewrite NatMap_gso by auto.
          specialize (IH nid').
          destruct IH as [IH | (v & entry & IH)].
          1: left; apply IH.
          right; exists v; exists entry.
          destruct IH as (IH1 & IH2 & IH3).
          pose proof (fsc_val_hist_valid _ _ Hval ltac:(rewrite IH1; discriminate)) as Hv.
          repeat split; auto.
          all: rewrite NatMap_gso by lia; auto.
  Qed.

  Lemma fsc_local_ver_ordered : forall st nid v v' entry entry' lv lv',
    fsc_valid st ->
    v < v' ->
    NatMap_find v st.(fsc_val_hist) = Some entry ->
    NatMap_find v' st.(fsc_val_hist) = Some entry' ->
    snd (snd entry) = nid ->
    snd (snd entry') = nid ->
    NatMap_find v st.(fsc_local_ver) = Some lv ->
    NatMap_find v' st.(fsc_local_ver) = Some lv' ->
    lv < lv'.
  Proof.
    intros st nid v v' entry entry' lv lv' Hval.
    revert nid v v' entry entry' lv lv'.
    induction Hval as [| st st' Hval IH Hstep].
    - intros nid v v' entry entry' lv lv' Hlt Hentry Hentry'.
      cbn in Hentry'.
      destruct (Nat.eq_dec v' 0); [lia | discriminate].
    - cbn in Hstep; step_case Hstep.
      all: fsc_unfold; fsc_reduce.
      all: try apply IH.
      + intros nid' v' v'' entry' entry'' lv' lv'' Hv'1 Hv'2 Hv''.
        destruct (Nat.eq_dec v'' (S (fsc_curr_ver st))).
        * subst v''; rewrite NatMap_gse in Hv'' by auto.
          injection Hv''; intros Heq; subst entry''; clear Hv''.
          rewrite NatMap_gso in Hv'2 by lia.
          intros Hnid'1 Hnid'2; cbn in Hnid'2; subst nid'.
          rewrite NatMap_gso by lia.
          rewrite NatMap_gse by auto.
          intros Hlv' Hlv''.
          injection Hlv''; intros Heq; subst lv''; clear Hlv''.
          apply (fsc_local_ver_lt_succ_count _ v' _ _ _ Hval Hv'2 Hnid'2 Hlv').
        * rewrite NatMap_gso in Hv'' by lia.
          pose proof (fsc_val_hist_valid _ _ Hval ltac:(rewrite Hv''; discriminate)) as Hle.
          rewrite NatMap_gso in Hv'2 by lia.
          do 2 rewrite NatMap_gso by lia.
          apply IH; auto.
      + intros nid' v' v'' entry' entry'' lv' lv'' Hv'1 Hv'2 Hv''.
        destruct (Nat.eq_dec v'' (S (fsc_curr_ver st))).
        * subst v''; rewrite NatMap_gse in Hv'' by auto.
          injection Hv''; intros Heq; subst entry''; clear Hv''.
          rewrite NatMap_gso in Hv'2 by lia.
          intros Hnid'1 Hnid'2; cbn in Hnid'2; subst nid'.
          rewrite NatMap_gso by lia.
          rewrite NatMap_gse by auto.
          intros Hlv' Hlv''.
          injection Hlv''; intros Heq; subst lv''; clear Hlv''.
          apply (fsc_local_ver_lt_succ_count _ v' _ _ _ Hval Hv'2 Hnid'2 Hlv').
        * rewrite NatMap_gso in Hv'' by lia.
          pose proof (fsc_val_hist_valid _ _ Hval ltac:(rewrite Hv''; discriminate)) as Hle.
          rewrite NatMap_gso in Hv'2 by lia.
          do 2 rewrite NatMap_gso by lia.
          apply IH; auto.
  Qed.

  Lemma fsc_succ_count_lt_exist : forall st nid lv,
    fsc_valid st ->
    lv < fsc_get_succ_count nid st ->
    exists v entry,
      NatMap_find v st.(fsc_val_hist) = Some entry /\
      snd (snd entry) = nid /\
      NatMap_find v st.(fsc_local_ver) = Some lv.
  Proof.
    intros st nid lv Hval.
    revert nid lv.
    induction Hval as [| st st' Hval IH Hstep].
    - intros nid lv; fsc_unfold; intros Hlv; cbn in Hlv.
      destruct (Nat.eq_dec nid 0); [subst nid | lia].
      replace lv with 0 by lia.
      exists 0; eexists; repeat split.
    - cbn in Hstep; step_case Hstep.
      all: fsc_unfold; fsc_reduce.
      all: try apply IH.
      + intros nid' lv' Hlv'.
        destruct (Nat.eq_dec nid' nid).
        * subst nid'; rewrite NatMap_gse in Hlv' by auto.
          match type of Hlv' with lv' < S ?x => assert (Hlv'2 : lv' < x \/ lv' = x) by lia end.
          destruct Hlv'2 as [Hlv'2 | Hlv'2].
          -- specialize (IH _ _ Hlv'2) as (v' & entry' & IH1 & IH2 & IH3).
             exists v'; exists entry'.
             pose proof (fsc_val_hist_valid _ _ Hval ltac:(rewrite IH1; discriminate)) as Hle.
             do 2 rewrite NatMap_gso by lia.
             repeat split; auto.
          -- subst lv'; do 2 eexists; repeat split.
             1: rewrite NatMap_gse.
             1,2: reflexivity.
             1: cbn; auto.
             rewrite NatMap_gse; auto.
        * rewrite NatMap_gso in Hlv' by auto.
          specialize (IH _ _ Hlv') as (v' & entry' & IH1 & IH2 & IH3).
          exists v'; exists entry'.
          pose proof (fsc_val_hist_valid _ _ Hval ltac:(rewrite IH1; discriminate)) as Hle.
          do 2 rewrite NatMap_gso by lia.
          repeat split; auto.
      + intros nid' lv' Hlv'.
        destruct (Nat.eq_dec nid' nid).
        * subst nid'; rewrite NatMap_gse in Hlv' by auto.
          match type of Hlv' with lv' < S ?x => assert (Hlv'2 : lv' < x \/ lv' = x) by lia end.
          destruct Hlv'2 as [Hlv'2 | Hlv'2].
          -- specialize (IH _ _ Hlv'2) as (v' & entry' & IH1 & IH2 & IH3).
             exists v'; exists entry'.
             pose proof (fsc_val_hist_valid _ _ Hval ltac:(rewrite IH1; discriminate)) as Hle.
             do 2 rewrite NatMap_gso by lia.
             repeat split; auto.
          -- subst lv'; do 2 eexists; repeat split.
             1: rewrite NatMap_gse.
             1,2: reflexivity.
             1: cbn; auto.
             rewrite NatMap_gse; auto.
        * rewrite NatMap_gso in Hlv' by auto.
          specialize (IH _ _ Hlv') as (v' & entry' & IH1 & IH2 & IH3).
          exists v'; exists entry'.
          pose proof (fsc_val_hist_valid _ _ Hval ltac:(rewrite IH1; discriminate)) as Hle.
          do 2 rewrite NatMap_gso by lia.
          repeat split; auto.
  Qed.

  Lemma fsc_local_ver_le_global_ver : forall st v lv,
    fsc_valid st ->
    NatMap_find v st.(fsc_local_ver) = Some lv ->
    lv <= v.
  Proof.
    intros st v.
    remember v as v_max.
    rewrite Heqv_max.
    assert (Hle : v <= v_max) by lia.
    clear Heqv_max.
    revert v Hle.
    induction v_max.
    - intros v Hle.
      replace v with 0 by lia.
      intros lv Hval Hlv.
      rewrite fsc_local_ver_zero in Hlv by auto.
      injection Hlv; intros; subst lv; auto.
    - intros v Hle.
      assert (Hv : v <= v_max \/ v = S v_max) by lia.
      destruct Hv as [Hv | Hv].
      1: apply IHv_max; auto.
      subst v; clear Hle.
      intros lv Hval Hlv.
      destruct lv as [|lv']; [lia|].
      (* Since local version (S lv') exists, there also exists local version lv' *)
      pose proof (fsc_local_ver_valid _ _ Hval ltac:(rewrite Hlv; discriminate)) as Hle.
      pose proof (fsc_val_hist_not_none _ (S v_max) Hval ltac:(lia)) as Hnone.
      destruct (NatMap_find (S v_max) (fsc_val_hist st)) as [entry|] eqn:Hentry; [clear Hnone | contradiction].
      remember (snd (snd entry)) as nid.
      pose proof (fsc_local_ver_lt_succ_count _ _ _ _ _ Hval Hentry Heqnid Hlv) as Hlt.
      pose proof (fsc_succ_count_lt_exist _ nid lv' Hval ltac:(lia)) as (v' & entry' & Hv'1 & Hv'2 & Hv'3).
      (* We must have v' < S v_max *)
      assert (Hv'4 : v' < S v_max).
      { assert (Hv'4 : v' < S v_max \/ v' = S v_max \/ v' > S v_max) by lia.
        destruct Hv'4 as [Hv'4 | [Hv'4 | Hv'4]]; auto.
        1: subst v'; rewrite Hv'3 in Hlv; injection Hlv; lia.
        pose proof (fsc_local_ver_ordered _ _ _ _ _ _ _ _ Hval Hv'4 Hentry Hv'1 ltac:(symmetry in Heqnid; apply Heqnid) Hv'2 Hlv Hv'3).
        lia.
      }
      (* Hence apply IH *)
      specialize (IHv_max v' ltac:(lia) _ Hval Hv'3).
      lia.
  Qed.

  Lemma fsc_succ_count_le_global_ver : forall st nid,
    fsc_valid st ->
    fsc_get_succ_count nid st <= S st.(fsc_curr_ver).
  Proof.
    intros st nid Hval.
    pose proof (fsc_succ_count_exist _ nid Hval) as [Hcount | Hcount].
    1: rewrite Hcount; lia.
    destruct Hcount as (v & entry & Hv1 & Hv2 & Hv3).
    pose proof (fsc_local_ver_le_global_ver _ _ _ Hval Hv3) as Hlt.
    pose proof (fsc_local_ver_valid _ _ Hval ltac:(rewrite Hv3; discriminate)).
    lia.
  Qed.

End FSC.
