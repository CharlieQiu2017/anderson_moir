(* An abstract model for the Anderson-Moir algorithm
   that implements non-faulty LL/SC from a faulty one
 *)

From Stdlib Require Import
  PeanoNat
  Lia
  Structures.Equalities.
From LLSC.lib Require Import
  Semantics
  Maps.
From LLSC.specs Require Import
  Config
  FSC.

Module Type Anderson (Config : LLSC_Config) (Import FSC : FSC Config).

  #[local] Notation val_t := Config.val_t.
  #[local] Notation tag_t := Config.tag_t.

  Inductive Adrs_Phase :=
  | Idle
  | LLRead1
  | LLWriteTag (old_v : nat)
  | LLRead2 (old_v : nat)
  | LLDone (old_v : nat) (chk_v : nat)
  | SCStart (old_v : nat) (chk_v : nat) (x : val_t)
  | SCLLWait (chk_v : nat) (x : val_t)
  | SCLLDone (chk_v : nat) (ll_v : nat) (x : val_t)
  | SCSCWait (chk_v : nat) (ll_v : nat) (x : val_t) (t : tag_t)
  | SCReadTag.

  Record Adrs_State := {
    (* The FSC object state *)
    adrs_fsc : FSC.FSC_State;
    (* Phase of each process *)
    adrs_phase : NatMap Adrs_Phase;
    (* The locked-tag array, called A in the paper.
       When a process writes into the locked-tag array, we also make a copy of the succ_count array of FSC.
       This is needed to state the invariant about when processes should read this array.
     *)
    adrs_lock_array : NatMap (tag_t * NatMap nat);
    (* Local view of the locked-tag array of each process, not explicitly named in the paper *)
    adrs_lock_view : NatMap (NatMap tag_t);
  }.

  Definition adrs_init_state := {|
    adrs_fsc := FSC.fsc_init_state;
    adrs_phase := NatMap_empty _;
    adrs_lock_array := NatMap_empty _;
    adrs_lock_view := NatMap_empty _;
  |}.

  Definition adrs_get_phase nid st :=
    match NatMap_find nid st.(adrs_phase) with
    | None => Idle
    | Some p => p
    end.

  Definition adrs_get_locked_tag nid st :=
    match NatMap_find nid st.(adrs_lock_array) with
    | None => zero_tag
    | Some t => fst t
    end.

  Definition adrs_get_locked_tag_local_time nid nid' st :=
    match NatMap_find nid st.(adrs_lock_array) with
    | None => 0
    | Some t => match NatMap_find nid' (snd t) with
      | None => 0
      | Some n => n
      end
    end.

  Definition adrs_get_local_view nid st :=
    match NatMap_find nid st.(adrs_lock_view) with
    | None => NatMap_empty _
    | Some view => view
    end.

  Definition adrs_get_local_view_tag nid nid' st :=
    let view := adrs_get_local_view nid st in
    match NatMap_find nid' view with
    | None => zero_tag
    | Some t => t
    end.

  (* State transitions *)
  Definition adrs_start_ll (nid : nat) (st : Adrs_State) := {|
    adrs_fsc := st.(adrs_fsc);
    adrs_phase := NatMap_add nid LLRead1 st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_read1_done (nid : nat) (st : Adrs_State) := {|
    adrs_fsc := st.(adrs_fsc);
    adrs_phase := NatMap_add nid (LLWriteTag st.(adrs_fsc).(fsc_curr_ver)) st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_write_tag_done (nid : nat) (v : nat) (t : tag_t) (st : Adrs_State) := {|
    adrs_fsc := st.(adrs_fsc);
    adrs_phase := NatMap_add nid (LLRead2 v) st.(adrs_phase);
    adrs_lock_array := NatMap_add nid (t, st.(adrs_fsc).(fsc_succ_count)) st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_read2_done (nid : nat) (v : nat) (st : Adrs_State) := {|
    adrs_fsc := st.(adrs_fsc);
    adrs_phase := NatMap_add nid (LLDone v st.(adrs_fsc).(fsc_curr_ver)) st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_cl (nid : nat) (st : Adrs_State) := {|
    adrs_fsc := st.(adrs_fsc);
    adrs_phase := NatMap_add nid Idle st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_start_sc (nid : nat) (v v' : nat) (x : val_t) (st : Adrs_State) := {|
    adrs_fsc := st.(adrs_fsc);
    adrs_phase := NatMap_add nid (SCStart v v' x) st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_start_fll (nid : nat) (v : nat) (x : val_t) (st : Adrs_State) := {|
    adrs_fsc := fsc_start_ll nid st.(adrs_fsc);
    adrs_phase := NatMap_add nid (SCLLWait v x) st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_ret_fll (nid : nat) (v v' : nat) (x : val_t) (st : Adrs_State) := {|
    adrs_fsc := fsc_ret_ll nid v' st.(adrs_fsc);
    adrs_phase := NatMap_add nid (SCLLDone v v' x) st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_fsc_cl (nid : nat) (st : Adrs_State) := {|
    adrs_fsc := fsc_cl nid st.(adrs_fsc);
    adrs_phase := NatMap_add nid Idle st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_start_fsc (nid : nat) (v v' : nat) (x : val_t) (t : tag_t) (st : Adrs_State) := {|
    adrs_fsc := fsc_start_sc nid x t st.(adrs_fsc);
    adrs_phase := NatMap_add nid (SCSCWait v v' x t) st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_fsc_step (fsc_st : FSC_State) (st : Adrs_State) := {|
    adrs_fsc := fsc_st;
    adrs_phase := st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_ret_fsc_fail (nid : nat) (v : nat) (x : val_t) (st : Adrs_State) := {|
    adrs_fsc := fsc_start_ll nid (fsc_cl nid st.(adrs_fsc));
    adrs_phase := NatMap_add nid (SCLLWait v x) st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_ret_fsc_succ (nid : nat) (st : Adrs_State) := {|
    adrs_fsc := fsc_cl nid st.(adrs_fsc);
    adrs_phase := NatMap_add nid SCReadTag st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := st.(adrs_lock_view);
  |}.

  Definition adrs_read_tag_done (nid : nat) (nid' : nat) (t : tag_t) (st : Adrs_State) := {|
    adrs_fsc := st.(adrs_fsc);
    adrs_phase := NatMap_add nid Idle st.(adrs_phase);
    adrs_lock_array := st.(adrs_lock_array);
    adrs_lock_view := NatMap_add nid (NatMap_add nid' t (adrs_get_local_view nid st)) st.(adrs_lock_view);
  |}.

  Parameter read_tag_schedule : nat -> nat.
  Parameter read_tag_schedule_next : nat -> nat -> nat.
  Parameter read_tag_schedule_next_prop : forall nid n, nid < Config.n -> n < read_tag_schedule_next nid n <= n + Config.n /\ read_tag_schedule (read_tag_schedule_next nid n) = nid.

  Inductive adrs_call_step : Adrs_State -> Adrs_State -> Prop :=
  | adrs_call_step_ll : forall nid st,
      nid < Config.n ->
      adrs_get_phase nid st = Idle ->
      adrs_call_step st (adrs_start_ll nid st)
  | adrs_call_step_sc : forall nid v v' x st,
      nid < Config.n ->
      adrs_get_phase nid st = LLDone v v' ->
      adrs_call_step st (adrs_start_sc nid v v' x st)
  | adrs_call_step_cl : forall nid v v' st,
      nid < Config.n ->
      adrs_get_phase nid st = LLDone v v' ->
      adrs_call_step st (adrs_cl nid st).

  Inductive adrs_internal_step : Adrs_State -> Adrs_State -> Prop :=
  | adrs_int_step_read1 : forall nid st,
      nid < Config.n ->
      adrs_get_phase nid st = LLRead1 ->
      adrs_internal_step st (adrs_read1_done nid st)
  | adrs_int_step_write_tag : forall nid v entry t st,
      nid < Config.n ->
      adrs_get_phase nid st = LLWriteTag v ->
      NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      fst (snd entry) = t ->
      adrs_internal_step st (adrs_write_tag_done nid v t st)
  | adrs_int_step_read2 : forall nid v st,
      nid < Config.n ->
      adrs_get_phase nid st = LLRead2 v ->
      adrs_internal_step st (adrs_read2_done nid v st)
  | adrs_int_step_start_fll : forall nid v v' x entry entry' st,
      nid < Config.n ->
      adrs_get_phase nid st = SCStart v v' x ->
      NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v' st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
      snd entry = snd entry' ->
      adrs_internal_step st (adrs_start_fll nid v' x st)
  | adrs_int_step_ret_fll : forall nid v v' v'' x st,
      nid < Config.n ->
      adrs_get_phase nid st = SCLLWait v x ->
      fsc_get_cmd nid st.(adrs_fsc) = FSC.LLWait v' ->
      v' <= v'' <= st.(adrs_fsc).(fsc_curr_ver) ->
      adrs_internal_step st (adrs_ret_fll nid v v'' x st)
  | adrs_int_step_start_fsc : forall nid v v' x entry entry' lv t st,
      nid < Config.n ->
      adrs_get_phase nid st = SCLLDone v v' x ->
      NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v' st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
      snd entry = snd entry' ->
      (* Do not reuse previous N tags that were successfully written *)
      fsc_get_succ_count nid st.(adrs_fsc) = lv ->
      (forall v'' lv'' entry'',
          NatMap_find v'' st.(adrs_fsc).(fsc_val_hist) = Some entry'' ->
          snd (snd entry'') = nid ->
          NatMap_find v'' st.(adrs_fsc).(fsc_local_ver) = Some lv'' ->
          lv - Config.n <= lv'' ->
          fst (snd entry'') <> t
      ) ->
      (* Do not use tags in the local view of locked-tag array *)
      (forall nid',
          nid' < Config.n ->
          adrs_get_local_view_tag nid nid' st <> t
      ) ->
      adrs_internal_step st (adrs_start_fsc nid v v' x t st)
  | adrs_int_step_fsc_step : forall st st_fst,
      fsc_sc_step st.(adrs_fsc) st_fst ->
      adrs_internal_step st (adrs_fsc_step st_fst st)
  | adrs_int_step_ret_fsc_fail : forall nid v v' x t st,
      nid < Config.n ->
      adrs_get_phase nid st = SCSCWait v v' x t ->
      fsc_get_cmd nid st.(adrs_fsc) = FSC.SCDone false ->
      adrs_internal_step st (adrs_ret_fsc_fail nid v x st)
  | adrs_int_step_ret_fsc_succ : forall nid v v' x t st,
      nid < Config.n ->
      adrs_get_phase nid st = SCSCWait v v' x t ->
      fsc_get_cmd nid st.(adrs_fsc) = FSC.SCDone true ->
      adrs_internal_step st (adrs_ret_fsc_succ nid st).

  Inductive adrs_ret_step : Adrs_State -> Adrs_State -> Prop :=
  | adrs_ret_step_fail : forall nid v v' x entry entry' st,
      nid < Config.n ->
      adrs_get_phase nid st = SCLLDone v v' x ->
      NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v' st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
      snd entry <> snd entry' ->
      adrs_ret_step st (adrs_fsc_cl nid st)
  | adrs_ret_step_succ : forall nid nid' t st,
      nid < Config.n ->
      adrs_get_phase nid st = SCReadTag ->
      read_tag_schedule (fsc_get_succ_count nid st.(adrs_fsc)) = nid' ->
      adrs_get_locked_tag nid' st = t ->
      adrs_ret_step st (adrs_read_tag_done nid nid' t st).

  Definition adrs_step st st' := adrs_call_step st st' \/ adrs_internal_step st st' \/ adrs_ret_step st st'.

  Definition adrs_sem : Semantics := {|
    s_state := Adrs_State;
    s_init := adrs_init_state;
    s_step := adrs_step;
  |}.

  #[local] Notation adrs_valid st := (valid_state adrs_sem st).
  #[local] Notation adrs_reachable st st' := (reachable adrs_sem st st').
  #[local] Notation fsc_valid st := (valid_state fsc_sem st).
  #[local] Notation fsc_reachable st st' := (reachable fsc_sem st st').

  Ltac step_case Hstep :=
    match type of Hstep with adrs_step ?st ?st' =>
    unfold adrs_step in Hstep;
    destruct Hstep as [Hstep | [Hstep | Hstep]];
    [ destruct Hstep as [nid st Hpre1 Hpre2 | nid v v' x st Hpre1 Hpre2 | nid v v' st Hpre1 Hpre2] |
      destruct Hstep as
      [ nid st Hpre1 Hpre2 |
        nid v entry t st Hpre1 Hpre2 Hpre3 Hpre4 |
        nid v st Hpre1 Hpre2 |
        nid v v' x entry entry' st Hpre1 Hpre2 Hpre3 Hpre4 Hpre5 |
        nid v v' v'' x st Hpre1 Hpre2 Hpre3 Hpre4 |
        nid v v' x entry entry' lv t st Hpre1 Hpre2 Hpre3 Hpre4 Hpre5 Hpre6 Hpre7 Hpre8 |
        st st_fst Hpre |
        nid v v' x t st Hpre1 Hpre2 Hpre3 |
        nid v v' x t st Hpre1 Hpre2 Hpre3
      ];
      [ | | | | | | remember st.(adrs_fsc) as fsc_st; destruct Hpre as [nid x t fsc_st Hpre1 Hpre2 Hpre3 | nid x t fsc_st Hpre1 Hpre2] | | ] |
      destruct Hstep as [nid v v' x entry entry' st Hpre1 Hpre2 Hpre3 Hpre4 Hpre5 | nid nid' t st Hpre1 Hpre2 Hpre3 Hpre4]
    ]
    end.

  Ltac adrs_unfold := unfold adrs_start_ll, adrs_read1_done, adrs_write_tag_done, adrs_read2_done, adrs_cl, adrs_start_sc, adrs_start_fll, adrs_ret_fll, adrs_fsc_cl, adrs_start_fsc, adrs_fsc_step, adrs_ret_fsc_fail, adrs_ret_fsc_succ, adrs_read_tag_done, adrs_get_phase, adrs_get_locked_tag, adrs_get_locked_tag_local_time, adrs_get_local_view_tag, adrs_get_local_view.
  Ltac adrs_reduce := cbn [adrs_fsc adrs_phase adrs_lock_array adrs_lock_view].

  Definition adrs_phase_prop_def nid st :=
    match adrs_get_phase nid st with
    | Idle => fsc_get_cmd nid st.(adrs_fsc) = FSC.Idle
    | LLRead1 => fsc_get_cmd nid st.(adrs_fsc) = FSC.Idle
    | LLWriteTag v => fsc_get_cmd nid st.(adrs_fsc) = FSC.Idle
    | LLRead2 v => fsc_get_cmd nid st.(adrs_fsc) = FSC.Idle
    | LLDone v v' => fsc_get_cmd nid st.(adrs_fsc) = FSC.Idle
    | SCStart v v' x => fsc_get_cmd nid st.(adrs_fsc) = FSC.Idle
    | SCLLWait v x => exists v', fsc_get_cmd nid st.(adrs_fsc) = FSC.LLWait v'
    | SCLLDone v v' x => fsc_get_cmd nid st.(adrs_fsc) = FSC.LLDone /\ fsc_get_excl_ver nid st.(adrs_fsc) = v'
    | SCSCWait v v' x t =>
        fsc_get_cmd nid st.(adrs_fsc) = FSC.SCDone true \/
        fsc_get_cmd nid st.(adrs_fsc) = FSC.SCDone false \/
        fsc_get_cmd nid st.(adrs_fsc) = FSC.SCWait x t /\
        fsc_get_excl_ver nid st.(adrs_fsc) = v'
    | SCReadTag => fsc_get_cmd nid st.(adrs_fsc) = FSC.Idle
    end.

  Lemma adrs_phase_prop : forall nid st,
    adrs_valid st ->
    adrs_phase_prop_def nid st.
  Proof.
    intros nid'' st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; auto.
    - unfold adrs_phase_prop_def in IH.
      unfold adrs_phase_prop_def.
      cbn in Hstep; step_case Hstep.
      all: try (destruct (Nat.eq_dec nid nid''); [subst nid'' | adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto; apply IH]).
      all: try (adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto; match goal with H : adrs_get_phase ?nid ?st = ?p |- _ => rewrite H in IH; apply IH end).

      + (* start_fll *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto.
          eexists; reflexivity.
        * adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gso by auto.
          apply IH.

      + (* ret_fll *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto.
          fsc_unfold; fsc_reduce; do 2 rewrite NatMap_gse by auto.
          split; auto.
        * adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto.
          fsc_unfold; fsc_reduce; do 2 rewrite NatMap_gso by auto.
          apply IH.

      + (* start_fsc *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto.
          rewrite Hpre2 in IH.
          right; right; split; auto; apply IH.
        * adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gso by auto.
          apply IH.

      + (* fsc_succ_sc *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto.
          fold (adrs_get_phase nid st).
          match goal with H : fsc_get_cmd ?nid ?st = ?p |- _ => rewrite H in IH end.
          destruct (adrs_get_phase nid st); try (repeat destruct IH as (? & IH); discriminate).
          left; auto.
        * adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; rewrite NatMap_gso by auto.
          fold (adrs_get_phase nid'' st).
          destruct (adrs_get_phase nid'' st); repeat destruct IH as (? & IH); repeat split; auto.
          exists x1; auto.

      + (* fsc_fail_sc *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto.
          fold (adrs_get_phase nid st).
          match goal with H : fsc_get_cmd ?nid ?st = ?p |- _ => rewrite H in IH end.
          destruct (adrs_get_phase nid st); try (repeat destruct IH as (? & IH); discriminate).
          right; left; auto.
        * adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; rewrite NatMap_gso by auto.
          fold (adrs_get_phase nid'' st).
          destruct (adrs_get_phase nid'' st); repeat destruct IH as (? & IH); repeat split; auto.
          exists x1; auto.

      + (* ret_fsc_fail *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto.
          rewrite Hpre2 in IH.
          eexists; split.
        * adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto.
          fsc_unfold; fsc_reduce; do 2 rewrite NatMap_gso by auto.
          apply IH.

      + (* ret_fsc_succ *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto; auto.
        * adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gso by auto.
          apply IH.

      + (* fsc_cl *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto; auto.
        * adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gso by auto.
          apply IH.
  Qed.

  Lemma adrs_step_fsc_step st st' :
    adrs_valid st ->
    adrs_step st st' ->
    fsc_reachable st.(adrs_fsc) st'.(adrs_fsc).
  Proof.
    intros Hval Hstep.
    step_case Hstep.
    all: adrs_unfold; adrs_reduce; try apply reachable_self.
    all: eapply reachable_step.
    1,3,5,7,9,13,15: apply reachable_self.
    - cbn; left; constructor; auto.
      pose proof (adrs_phase_prop nid _ Hval) as Hphase.
      unfold adrs_phase_prop_def in Hphase; rewrite Hpre2 in Hphase; apply Hphase.
    - cbn; right; right; econstructor; auto.
      1: apply Hpre3.
      auto.
    - cbn; left; constructor; auto.
      pose proof (adrs_phase_prop nid _ Hval) as Hphase.
      unfold adrs_phase_prop_def in Hphase; rewrite Hpre2 in Hphase; apply Hphase.
    - cbn; right; left; constructor; auto.
    - cbn; right; left; econstructor; auto.
      1: apply Hpre2.
    - eapply reachable_step; [apply reachable_self|].
      cbn; right; right; eapply fsc_ret_step_sc.
      1: apply Hpre1.
      apply Hpre3.
    - cbn; left; constructor; auto.
      fsc_unfold; fsc_reduce; rewrite NatMap_gse; auto.
    - cbn; right; right; eapply fsc_ret_step_sc; auto.
      apply Hpre3.
    - cbn; left; constructor; auto.
      pose proof (adrs_phase_prop nid _ Hval) as Hphase.
      unfold adrs_phase_prop_def in Hphase; rewrite Hpre2 in Hphase; apply Hphase.
  Qed.

  Lemma adrs_fsc_valid : forall st,
    adrs_valid st -> fsc_valid st.(adrs_fsc).
  Proof.
    intros st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; apply valid_state_init.
    - pose proof (adrs_step_fsc_step _ _ Hval Hstep).
      eapply valid_reach_valid; try apply IH; auto.
  Qed.

  Lemma adrs_tag_selection1 : forall nid v v' x t lv st,
    adrs_valid st ->
    adrs_get_phase nid st = SCSCWait v v' x t ->
    fsc_get_cmd nid st.(adrs_fsc) = FSC.SCWait x t ->
    fsc_get_succ_count nid st.(adrs_fsc) = lv ->
    forall v'' lv'' entry'',
      NatMap_find v'' st.(adrs_fsc).(fsc_val_hist) = Some entry'' ->
      snd (snd entry'') = nid ->
      NatMap_find v'' st.(adrs_fsc).(fsc_local_ver) = Some lv'' ->
      lv - Config.n <= lv'' ->
      fst (snd entry'') <> t.
  Proof.
    intros nid'' v v' x t lv st Hval.
    revert v v' x t lv.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - cbn in Hstep; step_case Hstep.
      all: intros V V' x' t' lv'.
      all: try (destruct (Nat.eq_dec nid nid''); [subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto; discriminate | adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto; try apply IH; fsc_unfold; fsc_reduce; rewrite NatMap_gso by auto; apply IH]).

      + (* start_fsc *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto.
          intros Hphase.
          injection Hphase; intros Heq1 Heq2 Heq3 Heq4; subst V V' x' t'; clear Hphase.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto.
          intros _ Hlv'.
          subst lv lv'; apply Hpre7.
        * adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto.
          fsc_unfold; fsc_reduce; rewrite NatMap_gso by auto.
          apply IH.

      + (* fsc_succ_sc *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto.
          discriminate.
        * adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; do 2 rewrite NatMap_gso by auto.
          intros Hphase1 Hphase2 Hlv'.
          specialize (IH V V' x' t' lv' Hphase1 Hphase2 Hlv').
          intros v'' lv'' entry'' Hv''1 Hv''2 Hv''3.
          destruct (Nat.eq_dec v'' (S (fsc_curr_ver fsc_st))).
          1: subst v''; rewrite NatMap_gse in Hv''1 by auto; injection Hv''1; intros Heq; subst entry''; cbn in Hv''2; contradiction.
          rewrite NatMap_gso in Hv''1 by auto.
          rewrite NatMap_gso in Hv''3 by auto.
          specialize (IH _ _ _ Hv''1 Hv''2 Hv''3).
          apply IH.

      + (* fsc_fail_sc *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto.
          discriminate.
        * adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; rewrite NatMap_gso by auto.
          apply IH.

      + (* ret_fsc_fail *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto.
          discriminate.
        * adrs_unfold; adrs_reduce.
          fsc_unfold; fsc_reduce; do 3 rewrite NatMap_gso by auto.
          apply IH.
  Qed.

  Lemma adrs_tag_selection2 : forall nid v v' x t st,
    adrs_valid st ->
    adrs_get_phase nid st = SCSCWait v v' x t ->
    forall nid',
      nid' < Config.n ->
      adrs_get_local_view_tag nid nid' st <> t.
  Proof.
    intros nid'' v v' x t st Hval.
    revert v v' x t.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - cbn in Hstep; step_case Hstep.
      all: intros V V' x' t'.
      all: try (destruct (Nat.eq_dec nid nid''); [subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto; discriminate | adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto; apply IH]).

      + (* start_fsc *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto.
          intros Hphase.
          injection Hphase; intros Heq1 Heq2 Heq3 Heq4; subst V V' x' t'; clear Hphase.
          apply Hpre8.
        * adrs_unfold; adrs_reduce; rewrite NatMap_gso by auto; apply IH.

      + (* fsc_succ_sc *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; apply IH.
        * adrs_unfold; adrs_reduce; apply IH.

      + (* fsc_fail_sc *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; apply IH.
        * adrs_unfold; adrs_reduce; apply IH.

      + (* read_tag_done *)
        destruct (Nat.eq_dec nid nid'').
        * subst nid''; adrs_unfold; adrs_reduce; rewrite NatMap_gse by auto; discriminate.
        * adrs_unfold; adrs_reduce; do 2 rewrite NatMap_gso by auto; apply IH.
  Qed.

  Lemma adrs_read_tag_progress : forall nid nid' r r' st,
    adrs_valid st ->
    nid' < Config.n ->
    adrs_get_locked_tag_local_time nid' nid st = r ->
    read_tag_schedule_next nid' r = r' ->
    fsc_get_succ_count nid st.(adrs_fsc) < r' \/
    fsc_get_succ_count nid st.(adrs_fsc) = r' /\
    fsc_get_cmd nid st.(adrs_fsc) = FSC.SCDone true \/
    fsc_get_succ_count nid st.(adrs_fsc) = r' /\
    adrs_get_phase nid st = SCReadTag \/
    adrs_get_local_view_tag nid nid' st = adrs_get_locked_tag nid' st.
  Proof.
    intros NID NID' r r' st Hval.
    revert r r'.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; intros; right; right; right; auto.
    - cbn in Hstep; step_case Hstep.
      all: adrs_unfold; adrs_reduce; destruct (Nat.eq_dec NID nid); [subst NID; repeat rewrite NatMap_gse by auto | try rewrite NatMap_gso by auto].

      all: try (intros r r' HNID' Hr Hr'; specialize (IH _ _ HNID' Hr Hr');
                destruct IH as [IH | [(IH1 & IH2) | [(IH1 & IH2) | IH]]];
                [ left; auto |
                  right; left; split; auto |
                  right; right; left; split; auto |
                  right; right; right; auto
                ];
                try (rewrite Hpre2 in IH2; discriminate);
                try (rewrite Hpre3 in IH2; discriminate);
                try (fsc_unfold; fsc_reduce; repeat rewrite NatMap_gso by auto; auto; fail);
                try (pose proof (adrs_phase_prop nid st Hval) as Hphase;
                     unfold adrs_phase_prop_def in Hphase;
                     rewrite Hpre2 in Hphase;
                     rewrite IH2 in Hphase;
                     try (destruct Hphase as (? & Hphase)); discriminate);
                fail
            ).

      + (* write_tag_done, NID == nid *)
        intros r r' HNID'.
        destruct (Nat.eq_dec NID' nid).
        * subst NID'; rewrite NatMap_gse by auto; cbn [snd].
          fold (fsc_get_succ_count nid st.(adrs_fsc)).
          intros Hr Hr'; left.
          pose proof (read_tag_schedule_next_prop nid r Hpre1); lia.
        * rewrite NatMap_gso by auto.
          intros Hr Hr'; specialize (IH _ _ HNID' Hr Hr').
          destruct IH as [IH | [(IH1 & IH2) | [(IH1 & IH2) | IH]]];
            [ left; auto |
              right; left; split; auto |
              right; right; left; split; auto |
              right; right; right; auto
            ].
          rewrite Hpre2 in IH2; discriminate.

      + (* write_tag_done, NID <> nid *)
        intros r r' HNID'.
        destruct (Nat.eq_dec NID' nid).
        * subst NID'; rewrite NatMap_gse by auto; cbn [snd].
          fold (fsc_get_succ_count NID st.(adrs_fsc)).
          intros Hr Hr'; left.
          pose proof (read_tag_schedule_next_prop nid r Hpre1); lia.
        * rewrite NatMap_gso by auto.
          intros Hr Hr'; specialize (IH _ _ HNID' Hr Hr').
          destruct IH as [IH | [(IH1 & IH2) | [(IH1 & IH2) | IH]]];
            [ left; auto |
              right; left; split; auto |
              right; right; left; split; auto |
              right; right; right; auto
            ].
          rewrite NatMap_gso by auto; auto.

      + (* fsc_succ_sc *)
        intros r r' HNID' Hr Hr'.
        specialize (IH _ _ HNID' Hr Hr').
        destruct IH as [IH | [(IH1 & IH2) | [(IH1 & IH2) | IH]]];
        [ idtac | exfalso | exfalso | auto].
        * fsc_unfold; fsc_reduce; repeat rewrite NatMap_gse by auto.
          fold (fsc_get_succ_count nid fsc_st).
          assert (Hr'2 : S (fsc_get_succ_count nid fsc_st) < r' \/ S (fsc_get_succ_count nid fsc_st) = r') by lia.
          destruct Hr'2 as [Hr'2 | Hr'2]; [left; auto | right; left; split; auto].
        * rewrite Hpre2 in IH2; discriminate.
        * pose proof (adrs_phase_prop nid st Hval) as Hphase;
          unfold adrs_phase_prop_def in Hphase;
          rewrite IH2 in Hphase;
          rewrite <- Heqfsc_st in Hphase;
          rewrite Hpre2 in Hphase; discriminate.

      + (* ret_fsc_succ *)
        intros r r' HNID' Hr Hr'.
        specialize (IH _ _ HNID' Hr Hr').
        fsc_unfold; fsc_reduce; rewrite NatMap_gse by auto; fold (fsc_get_succ_count nid (adrs_fsc st)).
        destruct IH as [IH | [(IH1 & IH2) | [(IH1 & IH2) | IH]]];
        [ left; auto | right; right; left; split; auto | right; right; left; split; auto | auto].

      + (* read_tag_done *)
        intros r r' HNID' Hr Hr'.
        specialize (IH _ _ HNID' Hr Hr').
        destruct IH as [IH | [(IH1 & IH2) | [(IH1 & IH2) | IH]]].
        * left; auto.
        * pose proof (adrs_phase_prop nid st Hval) as Hphase;
          unfold adrs_phase_prop_def in Hphase;
          rewrite IH2 in Hphase;
          rewrite Hpre2 in Hphase; discriminate.
        * rewrite IH1 in Hpre3.
          pose proof (read_tag_schedule_next_prop NID' r HNID') as Hr'2.
          destruct Hr'2 as (_ & Hr'2).
          rewrite Hr' in Hr'2.
          rewrite Hr'2 in Hpre3; subst NID'.
          rewrite NatMap_gse by auto.
          right; right; right; auto.
        * right; right; right.
          destruct (Nat.eq_dec NID' nid').
          -- subst NID'; rewrite NatMap_gse by auto; auto.
          -- rewrite NatMap_gso by auto; auto.
  Qed.

  Lemma adrs_tag_no_reuse1 : forall nid v v' entry entry' lv lv' st,
    adrs_valid st ->
    NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
    NatMap_find v' st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
    snd (snd entry) = nid ->
    snd (snd entry') = nid ->
    NatMap_find v st.(adrs_fsc).(fsc_local_ver) = Some lv ->
    NatMap_find v' st.(adrs_fsc).(fsc_local_ver) = Some lv' ->
    lv <> lv' -> lv - lv' <= Config.n -> lv' - lv <= Config.n ->
    fst (snd entry) <> fst (snd entry').
  Proof.
    intros NID V V' Entry Entry' LV LV' st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; destruct (Nat.eq_dec V 0); [|discriminate].
      destruct (Nat.eq_dec V' 0); [|discriminate].
      intros _ _ _ _ HLV HLV'.
      injection HLV; injection HLV'.
      intros Heq1 Heq2; subst; contradiction.
    - cbn in Hstep; step_case Hstep.
      all: adrs_unfold; adrs_reduce; try apply IH.
      + fsc_unfold; fsc_reduce.
        destruct (Nat.eq_dec V (S (fsc_curr_ver fsc_st))).
        * subst V; repeat rewrite (NatMap_gse _ _ (S (fsc_curr_ver fsc_st))) by auto.
          destruct (Nat.eq_dec V' (S (fsc_curr_ver fsc_st))).
          -- subst V'; repeat rewrite NatMap_gse by auto.
             intros _ _ _ _ HLV HLV'.
             injection HLV; injection HLV'; intros Heq1 Heq2; subst LV LV'.
             contradiction.
          -- clear IH.
             repeat rewrite NatMap_gso by auto.
             intros Hentry Hentry'.
             injection Hentry; intros Heq; subst Entry; clear Hentry; cbn [snd].
             intros Hnid1 Hnid2; subst NID.
             fold (fsc_get_succ_count nid fsc_st).
             intros HLV HLV' _; injection HLV; intros Heq; subst LV; clear HLV.
             (* nid must be in phase LLSCWait *)
             pose proof (adrs_phase_prop nid st Hval) as Hphase.
             unfold adrs_phase_prop_def in Hphase.
             rewrite <- Heqfsc_st in Hphase.
             rewrite Hpre2 in Hphase.
             destruct (adrs_get_phase nid st) eqn:Ephase; try discriminate.
             1,2: destruct Hphase; discriminate.
             destruct Hphase as [? | [? | (Hphase & _)]]; try discriminate.
             injection Hphase; intros Heq1 Heq2; subst x0 t0; clear Hphase.
             (* Now invoke adrs_tag_selection1 *)
             pose proof (adrs_tag_selection1 nid _ _ _ _ _ _ Hval Ephase ltac:(rewrite <- Heqfsc_st; apply Hpre2) ltac:(reflexivity)) as Htag.
             rewrite <- Heqfsc_st in Htag.
             specialize (Htag _ _ _ Hentry' Hnid2 HLV').
             intros HLV'1 HLV'2.
             specialize (Htag ltac:(lia)).
             cbn; auto.
             
        * repeat rewrite (NatMap_gso _ (S (fsc_curr_ver fsc_st)) V) by auto.
          destruct (Nat.eq_dec V' (S (fsc_curr_ver fsc_st))).
          -- subst V'; repeat rewrite NatMap_gse by auto.
             clear IH.
             intros Hentry Hentry'.
             injection Hentry'; intros Heq; subst Entry'; clear Hentry'; cbn [snd].
             intros Hnid1 Hnid2; revert Hnid1; subst NID; intros Hnid1.
             fold (fsc_get_succ_count nid fsc_st).
             intros HLV HLV' _; injection HLV'; intros Heq; subst LV'; clear HLV'.
             (* nid must be in phase LLSCWait *)
             pose proof (adrs_phase_prop nid st Hval) as Hphase.
             unfold adrs_phase_prop_def in Hphase.
             rewrite <- Heqfsc_st in Hphase.
             rewrite Hpre2 in Hphase.
             destruct (adrs_get_phase nid st) eqn:Ephase; try discriminate.
             1,2: destruct Hphase; discriminate.
             destruct Hphase as [? | [? | (Hphase & _)]]; try discriminate.
             injection Hphase; intros Heq1 Heq2; subst x0 t0; clear Hphase.
             (* Now invoke adrs_tag_selection1 *)
             pose proof (adrs_tag_selection1 nid _ _ _ _ _ _ Hval Ephase ltac:(rewrite <- Heqfsc_st; apply Hpre2) ltac:(reflexivity)) as Htag.
             rewrite <- Heqfsc_st in Htag.
             specialize (Htag _ _ _ Hentry Hnid1 HLV).
             intros HLV1 HLV2.
             specialize (Htag ltac:(lia)).
             cbn; auto.
          -- repeat rewrite NatMap_gso by auto.
             apply IH.
  Qed.

  Lemma adrs_tag_no_reuse2 : forall nid nid' r r' v entry lv st,
    adrs_valid st ->
    nid' < Config.n ->
    adrs_get_locked_tag_local_time nid' nid st = r ->
    read_tag_schedule_next nid' r = r' ->
    NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
    snd (snd entry) = nid ->
    NatMap_find v st.(adrs_fsc).(fsc_local_ver) = Some lv ->
    lv >= r' ->
    fst (snd entry) <> adrs_get_locked_tag nid' st.
  Proof.
    intros NID NID' r r' V Entry LV st Hval HNID.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; intros Hr Hr'; subst r r'.
      destruct (Nat.eq_dec V 0); [|discriminate].
      intros _ _ Heq Hgt.
      pose proof (read_tag_schedule_next_prop NID' 0 HNID).
      injection Heq; intros; subst LV; lia.
    - cbn in Hstep; step_case Hstep.
      all: adrs_unfold; adrs_reduce; try apply IH.

      + (* write_tag_done *)
        destruct (Nat.eq_dec NID' nid).
        2: rewrite NatMap_gso by auto; apply IH.
        subst NID'; rewrite NatMap_gse by auto; cbn [snd].
        fold (fsc_get_succ_count NID (adrs_fsc st)).
        intros Hr Hr' Hentry HNID2 HLV Hgt.
        pose proof (read_tag_schedule_next_prop nid r HNID).
        pose proof (adrs_fsc_valid _ Hval) as Hval'.
        pose proof (fsc_local_ver_lt_succ_count _ _ _ _ _ Hval' Hentry ltac:(symmetry; apply HNID2) HLV) as Hlt.
        lia.

      + (* fsc_succ_sc *)
        fsc_unfold; fsc_reduce.
        destruct (Nat.eq_dec V (S (fsc_curr_ver fsc_st))).
        2: repeat rewrite NatMap_gso by auto; apply IH.
        subst V; repeat rewrite NatMap_gse by auto.
        (* nid must be in phase LLSCWait *)
        pose proof (adrs_phase_prop nid st Hval) as Hphase.
        unfold adrs_phase_prop_def in Hphase.
        rewrite <- Heqfsc_st in Hphase.
        rewrite Hpre2 in Hphase.
        destruct (adrs_get_phase nid st) eqn:Ephase; try discriminate.
        1,2: destruct Hphase; discriminate.
        destruct Hphase as [? | [? | (Hphase & _)]]; try discriminate.
        injection Hphase; intros Heq1 Heq2; subst x0 t0; clear Hphase.
        (* By adrs_read_tag_progress, the tag locked by NID' should be in nid's view *)
        fold (adrs_get_locked_tag_local_time NID' NID st).
        fold (adrs_get_locked_tag NID' st).
        fold (fsc_get_succ_count nid fsc_st).
        intros Hr Hr' Hentry1 Hentry2.
        injection Hentry1; intros Heq; subst Entry; clear Hentry1.
        cbn in Hentry2; subst NID.
        intros HLV1 HLV2.
        injection HLV1; intros Heq; subst LV; clear HLV1.
        pose proof (adrs_read_tag_progress nid NID' _ _ _ Hval HNID Hr Hr') as Htag.
        rewrite <- Heqfsc_st in Htag.
        rewrite Hpre2, Ephase in Htag.
        destruct Htag as [? | [(_ & ?) | [(_ & ?) | Htag]]]; try discriminate; [lia|].
        rewrite <- Htag; cbn [fst snd].
        (* Now invoke adrs_tag_selection2 *)
        pose proof (adrs_tag_selection2 _ _ _ _ _ _ Hval Ephase _ HNID).
        auto.
  Qed.

  Lemma adrs_write_tag_phase_prop : forall nid v st,
    adrs_valid st ->
    adrs_get_phase nid st = LLWriteTag v ->
    v <= st.(adrs_fsc).(fsc_curr_ver).
  Proof.
    intros NID V st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - cbn in Hstep; step_case Hstep.
      all: adrs_unfold; adrs_reduce; destruct (Nat.eq_dec NID nid); [subst NID; repeat rewrite NatMap_gse by auto | repeat rewrite NatMap_gso by auto]; try discriminate; try apply IH.
      + intros Heq; injection Heq; intros; subst V; clear Heq; auto.
      + fsc_unfold; fsc_reduce; intros H; specialize (IH H); lia.
      + fsc_unfold; fsc_reduce; intros H; specialize (IH H); lia.
  Qed.

  Lemma adrs_read2_phase_prop : forall nid v st,
    adrs_valid st ->
    adrs_get_phase nid st = LLRead2 v ->
    v <= st.(adrs_fsc).(fsc_curr_ver) /\
    forall entry lv,
      NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v st.(adrs_fsc).(fsc_local_ver) = Some lv ->
      adrs_get_locked_tag nid st = fst (snd entry) /\
      lv < adrs_get_locked_tag_local_time nid (snd (snd entry)) st /\
      forall nid', adrs_get_locked_tag_local_time nid nid' st <= fsc_get_succ_count nid' st.(adrs_fsc).
  Proof.
    intros NID V st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - cbn in Hstep; step_case Hstep.
      all: adrs_unfold; adrs_reduce; destruct (Nat.eq_dec NID nid); [subst NID; repeat rewrite NatMap_gse by auto | repeat rewrite NatMap_gso by auto]; try discriminate; try apply IH.
      + intros Heq; injection Heq; intros; subst V; clear Heq IH.
        split.
        1: apply (adrs_write_tag_phase_prop _ _ _ Hval Hpre2).
        intros Entry LV Hentry HLV.
        rewrite Hpre3 in Hentry.
        injection Hentry; intros Heq; subst Entry; clear Hentry.
        split; auto.
        cbn [snd].
        split; auto.
        apply (fsc_local_ver_lt_succ_count _ _ _ _ _ (adrs_fsc_valid _ Hval) Hpre3 ltac:(reflexivity) HLV).
      + intros Hphase; specialize (IH Hphase).
        pose proof (adrs_phase_prop nid _ Hval) as Hphase2.
        unfold adrs_phase_prop_def in Hphase2.
        unfold adrs_get_phase in Hphase2; rewrite Hphase in Hphase2.
        rewrite <- Heqfsc_st, Hpre2 in Hphase2; discriminate.
      + intros Hphase; specialize (IH Hphase).
        fsc_unfold; fsc_reduce; split; [lia|].
        repeat rewrite (NatMap_gso _ (S (fsc_curr_ver fsc_st)) V) by lia.
        destruct IH as (IH1 & IH2).
        intros Entry LV Hentry HLV.
        specialize (IH2 _ _ Hentry HLV).
        destruct IH2 as (IH2 & IH3).
        split; auto.
        split; [apply IH3|].
        intros NID'; fold (adrs_get_locked_tag_local_time NID NID' st).
        destruct IH3 as (_ & IH3); specialize (IH3 NID').
        destruct (Nat.eq_dec NID' nid).
        * subst nid; rewrite NatMap_gse by auto.
          fold (fsc_get_succ_count NID' fsc_st). lia.
        * rewrite NatMap_gso by auto.
          fold (fsc_get_succ_count NID' fsc_st); apply IH3.
  Qed.

  Lemma adrs_ll_done_phase_prop : forall nid v v' st,
    adrs_valid st ->
    adrs_get_phase nid st = LLDone v v' ->
    v <= v' <= st.(adrs_fsc).(fsc_curr_ver) /\
    forall entry entry' lv lv',
      NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v' st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
      NatMap_find v st.(adrs_fsc).(fsc_local_ver) = Some lv ->
      NatMap_find v' st.(adrs_fsc).(fsc_local_ver) = Some lv' ->
      adrs_get_locked_tag nid st = fst (snd entry) /\
      lv < adrs_get_locked_tag_local_time nid (snd (snd entry)) st /\
      adrs_get_locked_tag_local_time nid (snd (snd entry')) st <= S lv'.
  Proof.
    intros NID V V' st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - cbn in Hstep; step_case Hstep.
      all: adrs_unfold; adrs_reduce; destruct (Nat.eq_dec NID nid); [subst NID; repeat rewrite NatMap_gse by auto | repeat rewrite NatMap_gso by auto]; try discriminate; try apply IH.
      + intros Heq; injection Heq; intros; subst V V'; clear Heq IH.
        pose proof (adrs_read2_phase_prop _ _ _ Hval Hpre2) as Hphase.
        split; [lia|].
        destruct Hphase as (Hphase1 & Hphase2).
        intros entry entry' lv lv' Hentry Hentry' Hlv Hlv'.
        specialize (Hphase2 _ _ Hentry Hlv).
        repeat split; [apply Hphase2 | apply Hphase2 | idtac].
        destruct Hphase2 as (_ & _ & Hphase2).
        specialize (Hphase2 (snd (snd entry'))).
        fold (adrs_get_locked_tag_local_time nid (snd (snd entry')) st).
        (* We have lv' < succ_count *)
        pose proof (fsc_local_ver_lt_succ_count _ _ _ _ _ (adrs_fsc_valid _ Hval) Hentry' ltac:(reflexivity) Hlv').
        (* There exists an entry with lv = succ_count - 1 *)
        pose proof (fsc_succ_count_exist _ (snd (snd entry')) (adrs_fsc_valid _ Hval)) as [Hex | Hex]; [lia|].
        destruct Hex as (V & Entry & HV1 & HV2 & HV3).
        (* We have V <= fsc_curr_ver *)
        pose proof (fsc_val_hist_valid _ _ (adrs_fsc_valid _ Hval) ltac:(rewrite HV1; discriminate)) as Hle.
        assert (Hle2 : V < fsc_curr_ver (adrs_fsc st) \/ V = fsc_curr_ver (adrs_fsc st)) by lia.
        destruct Hle2 as [Hle2 | Hle2].
        1: pose proof (fsc_local_ver_ordered _ _ _ _ _ _ _ _ (adrs_fsc_valid _ Hval) Hle2 HV1 Hentry' HV2 ltac:(reflexivity) HV3 Hlv'); lia.
        subst V.
        rewrite Hlv' in HV3.
        injection HV3; intros; subst lv'.
        cbn in H, Hphase2.
        cbn; lia.
      + intros Hphase; specialize (IH Hphase).
        pose proof (adrs_phase_prop nid _ Hval) as Hphase2.
        unfold adrs_phase_prop_def in Hphase2.
        unfold adrs_get_phase in Hphase2; rewrite Hphase in Hphase2.
        rewrite <- Heqfsc_st, Hpre2 in Hphase2; discriminate.
      + intros Hphase; specialize (IH Hphase).
        fsc_unfold; fsc_reduce; split; [lia|].
        repeat rewrite (NatMap_gso _ (S (fsc_curr_ver fsc_st)) V) by lia.
        destruct IH as (IH1 & IH2).
        intros Entry Entry' LV LV' Hentry Hentry' HLV HLV'.
        rewrite NatMap_gso in Hentry' by lia.
        rewrite NatMap_gso in HLV' by lia.
        specialize (IH2 _ _ _ _ Hentry Hentry' HLV HLV').
        apply IH2.
  Qed.

  Lemma adrs_sc_start_phase_prop : forall nid v v' x st,
    adrs_valid st ->
    adrs_get_phase nid st = SCStart v v' x ->
    v <= v' <= st.(adrs_fsc).(fsc_curr_ver) /\
    forall entry entry' lv lv',
      NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v' st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
      NatMap_find v st.(adrs_fsc).(fsc_local_ver) = Some lv ->
      NatMap_find v' st.(adrs_fsc).(fsc_local_ver) = Some lv' ->
      adrs_get_locked_tag nid st = fst (snd entry) /\
      lv < adrs_get_locked_tag_local_time nid (snd (snd entry)) st /\
      adrs_get_locked_tag_local_time nid (snd (snd entry')) st <= S lv'.
  Proof.
    intros NID V V' X st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; discriminate.
    - cbn in Hstep; step_case Hstep.
      all: adrs_unfold; adrs_reduce; destruct (Nat.eq_dec NID nid); [subst NID; repeat rewrite NatMap_gse by auto | repeat rewrite NatMap_gso by auto]; try discriminate; try apply IH.
      + intros Heq; injection Heq; intros; subst V V' X; clear Heq IH.
        apply adrs_ll_done_phase_prop; auto.
      + intros Hphase; specialize (IH Hphase).
        pose proof (adrs_phase_prop nid _ Hval) as Hphase2.
        unfold adrs_phase_prop_def in Hphase2.
        unfold adrs_get_phase in Hphase2; rewrite Hphase in Hphase2.
        rewrite <- Heqfsc_st, Hpre2 in Hphase2; discriminate.
      + intros Hphase; specialize (IH Hphase).
        fsc_unfold; fsc_reduce; split; [lia|].
        repeat rewrite (NatMap_gso _ (S (fsc_curr_ver fsc_st)) V) by lia.
        destruct IH as (IH1 & IH2).
        intros Entry Entry' LV LV' Hentry Hentry' HLV HLV'.
        rewrite NatMap_gso in Hentry' by lia.
        rewrite NatMap_gso in HLV' by lia.
        specialize (IH2 _ _ _ _ Hentry Hentry' HLV HLV').
        apply IH2.
  Qed.

  (* The properties of SCLLWait, SCLLDone, and SCSCWait must be proved together, since SCSCWait may transition to SCLLWait *)

  Lemma adrs_sc_ll_wait_phase_prop : forall nid st,
    adrs_valid st ->
    (forall v x,
       adrs_get_phase nid st = SCLLWait v x ->
       (exists v',
          fsc_get_cmd nid st.(adrs_fsc) = LLWait v' /\
          v <= v' <= st.(adrs_fsc).(fsc_curr_ver)
       ) /\
       forall entry lv,
         NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
         NatMap_find v st.(adrs_fsc).(fsc_local_ver) = Some lv ->
         adrs_get_locked_tag nid st = fst (snd entry) /\
         adrs_get_locked_tag_local_time nid (snd (snd entry)) st <= S lv
    ) /\
    (forall v v' x,
       adrs_get_phase nid st = SCLLDone v v' x ->
       v <= v' <= st.(adrs_fsc).(fsc_curr_ver) /\
       forall entry lv,
         NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
         NatMap_find v st.(adrs_fsc).(fsc_local_ver) = Some lv ->
         adrs_get_locked_tag nid st = fst (snd entry) /\
         adrs_get_locked_tag_local_time nid (snd (snd entry)) st <= S lv
    ) /\
    (forall v v' x t,
       adrs_get_phase nid st = SCSCWait v v' x t ->
       v = v' /\ v <= st.(adrs_fsc).(fsc_curr_ver) /\
       forall entry lv,
         NatMap_find v st.(adrs_fsc).(fsc_val_hist) = Some entry ->
         NatMap_find v st.(adrs_fsc).(fsc_local_ver) = Some lv ->
         adrs_get_locked_tag nid st = fst (snd entry) /\
         adrs_get_locked_tag_local_time nid (snd (snd entry)) st <= S lv
    ).
  Proof.
    intros NID st Hval.
    induction Hval as [| st st' Hval IH Hstep].
    - cbn; split; [|split]; discriminate.
    - cbn in Hstep; step_case Hstep.
      all: adrs_unfold; adrs_reduce; destruct (Nat.eq_dec NID nid); [subst NID; repeat rewrite NatMap_gse by auto | repeat rewrite NatMap_gso by auto].
      all: split; [|split].
      all: try discriminate; try apply IH.
      all: fsc_unfold; fsc_reduce; repeat rewrite NatMap_gse by auto; repeat rewrite NatMap_gso by auto; try apply IH.
      all: try (fold (adrs_get_phase nid st);
                intros;
                pose proof (adrs_phase_prop nid st Hval) as Hphase;
                unfold adrs_phase_prop_def in Hphase;
                rewrite <- Heqfsc_st in Hphase;
                match goal with H : adrs_get_phase ?nid ?st = _ |- _ => rewrite H in Hphase end;
                rewrite Hpre2 in Hphase;
                try destruct Hphase; discriminate
             ).

      + (* SCStart -> SCLLWait *)
        intros v0 x0 Hphase.
        injection Hphase; intros; subst v0 x0; clear Hphase.
        pose proof (adrs_sc_start_phase_prop _ _ _ _ _ Hval Hpre2) as (Hphase1 & Hphase2).
        split.
        1: eexists; split; [reflexivity | lia].
        pose proof (fsc_val_local_ver_not_none _ v (adrs_fsc_valid _ Hval) ltac:(lia)) as Hlv.
        destruct (NatMap_find v (fsc_local_ver (adrs_fsc st))) eqn:Elv; try contradiction; clear Hlv.
        intros Entry LV Hentry HLV.
        rewrite Hpre4 in Hentry; injection Hentry; intros; subst Entry; clear Hentry.
        specialize (Hphase2 _ _ _ _ Hpre3 Hpre4 ltac:(reflexivity) HLV).
        rewrite <- Hpre5.
        rewrite <- Hpre5 in Hphase2.
        split; [apply Hphase2|].
        fold (adrs_get_locked_tag_local_time nid (snd (snd entry)) st).
        apply Hphase2.

      + (* SCLLWait -> SCLLDone *)
        intros V V' X Hphase.
        injection Hphase; intros; subst V V' X; clear Hphase.
        destruct IH as (IH & _ & _).
        specialize (IH _ _ Hpre2).
        destruct IH as (IH1 & IH2).
        destruct IH1 as (V & IH1_1 & IH1_2).
        rewrite Hpre3 in IH1_1; injection IH1_1; intros; subst V; clear IH1_1.
        split; [lia|].
        apply IH2.

      + (* SCLLDone -> SCSCWait *)
        intros V V' X T Hphase.
        injection Hphase; intros; subst V V' X T; clear Hphase.
        destruct IH as (_ & IH & _).
        specialize (IH _ _ _ Hpre2).
        destruct IH as (IH1 & IH2).
        pose proof (fsc_val_local_ver_not_none _ v (adrs_fsc_valid _ Hval) ltac:(lia)) as Hlv.
        destruct (NatMap_find v (fsc_local_ver (adrs_fsc st))) eqn:Elv; try contradiction; clear Hlv.
        specialize (IH2 _ _ Hpre3 ltac:(reflexivity)).
        destruct IH2 as (IH2 & IH3).
        split; [|split].
        2: lia.
        2: { intros Entry LV Heq1 Heq2.
             rewrite Hpre3 in Heq1; injection Heq1; injection Heq2.
             intros; subst Entry LV; clear Heq1 Heq2.
             split; auto.
        }

        (* v <= v', we should have n <= n0 *)
        pose proof (fsc_val_local_ver_not_none _ v' (adrs_fsc_valid _ Hval) ltac:(apply IH1)) as Hlv.
        destruct (NatMap_find v' (fsc_local_ver (adrs_fsc st))) eqn:Elv'; try contradiction; clear Hlv.
        assert (Hlv1 : n <= n0).
        { assert (Hv : v = v' \/ v < v') by lia.
          destruct Hv as [Hv | Hv].
          1: subst v'; rewrite Elv in Elv'; injection Elv'; intros; subst n0; auto.
          pose proof (fsc_local_ver_ordered _ _ _ _ _ _ _ _ (adrs_fsc_valid _ Hval) Hv Hpre3 Hpre4 ltac:(reflexivity) ltac:(rewrite <- Hpre5; auto) Elv Elv').
          lia.
        }

        (* Analyze the read tag schedule *)
        pose proof (adrs_tag_no_reuse2 (snd (snd entry)) nid _ _ _ _ _ _ Hval Hpre1 ltac:(reflexivity) ltac:(reflexivity) Hpre4 ltac:(congruence) Elv') as Hlv2.
        rewrite IH2 in Hlv2.
        pose proof (read_tag_schedule_next_prop nid (adrs_get_locked_tag_local_time nid (snd (snd entry)) st) Hpre1) as (Hlv3 & _).
        assert (Hlv4 : n = n0 \/ n < n0 <= adrs_get_locked_tag_local_time nid (snd (snd entry)) st + Config.n - 1 \/ n0 >= adrs_get_locked_tag_local_time nid (snd (snd entry)) st + Config.n) by lia.
        destruct Hlv4 as [Hlv4 | [Hlv4 | Hlv4]].
        1: { subst n0.
             assert (Hv : v = v' \/ v < v') by lia.
             destruct Hv as [? | Hv]; [auto|].
             pose proof (fsc_local_ver_ordered _ _ _ _ _ _ _ _ (adrs_fsc_valid _ Hval) Hv Hpre3 Hpre4 ltac:(reflexivity) ltac:(rewrite <- Hpre5; auto) Elv Elv').
             lia.
        }
        2: specialize (Hlv2 ltac:(lia)); rewrite Hpre5 in Hlv2; contradiction.
        pose proof (adrs_tag_no_reuse1 _ _ _ _ _ _ _ _ Hval Hpre3 Hpre4 ltac:(reflexivity) ltac:(rewrite <- Hpre5; auto) Elv Elv' ltac:(lia) ltac:(lia) ltac:(lia)) as Hlv5.
        rewrite Hpre5 in Hlv5; contradiction.

      + (* SCWait -> SCDone, NID == nid, SCSCWait *)
        fold (adrs_get_phase nid st).
        intros V V' X T Hphase.
        destruct IH as (_ & _ & IH).
        specialize (IH _ _ _ _ Hphase).
        repeat rewrite NatMap_gso by lia.
        split; [|split]; try apply IH.
        lia.

      + (* SCWait -> SCDone, NID <> nid, SCLLWait *)
        fold (adrs_get_phase NID st).
        intros V X Hphase.
        destruct IH as (IH & _ & _).
        specialize (IH _ _ Hphase).
        destruct IH as ((v' & IH1 & IH2) & IH3).
        repeat rewrite NatMap_gso by lia.
        split; [|apply IH3].
        exists v'; split; [apply IH1 | lia].

      + (* SCWait -> SCDone, NID <> nid, SCLLDone *)
        fold (adrs_get_phase NID st).
        intros V V' X Hphase.
        destruct IH as (_ & IH & _).
        specialize (IH _ _ _ Hphase).
        destruct IH as (IH1 & IH2).
        repeat rewrite NatMap_gso by lia.
        split; [lia | apply IH2].

      + (* SCWait -> SCDone, NID <> nid, SCSCWait *)
        fold (adrs_get_phase NID st).
        intros V V' X T Hphase.
        destruct IH as (_ & _ & IH).
        specialize (IH _ _ _ _ Hphase).
        repeat rewrite NatMap_gso by lia.
        split; [|split]; [apply IH | lia | apply IH].

      + (* SCDone false, NID == nid *)
        destruct IH as (_ & _ & IH).
        specialize (IH _ _ _ _ Hpre2).
        destruct IH as (_ & IH1 & IH2).
        intros V X Hphase.
        injection Hphase; intros; subst V X; clear Hphase.
        split.
        1: eexists; split; [reflexivity | lia].
        apply IH2.
  Qed.

End Anderson.
