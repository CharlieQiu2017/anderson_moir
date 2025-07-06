From Stdlib Require Import
  PeanoNat
  Lia.
From LLSC.lib Require Import
  Maps
  Semantics.
From LLSC.specs Require Import
  Config
  LLSC
  FSC
  Anderson.

Module Type Adrs_Refine (Config : LLSC_Config) (Import LLSC : LLSC Config) (Import FSC : FSC Config) (Import Adrs : Anderson Config FSC).

  #[local] Notation adrs_valid st := (valid_state adrs_sem st).
  #[local] Notation adrs_reachable st st' := (reachable adrs_sem st st').
  #[local] Notation fsc_valid st := (valid_state fsc_sem st).
  #[local] Notation fsc_reachable st st' := (reachable fsc_sem st st').
  #[local] Notation llsc_valid st := (valid_state llsc_sem st).
  #[local] Notation llsc_reachable st st' := (reachable llsc_sem st st').

  Record R_adrs (adrs_st : Adrs_State) (llsc_st : LLSC_State) : Prop := {
    R_adrs_idle : forall nid, adrs_get_phase nid adrs_st = Idle -> llsc_get_cmd nid llsc_st = LLSC.Idle;
    R_adrs_read1 : forall nid, adrs_get_phase nid adrs_st = LLRead1 -> exists v, llsc_get_cmd nid llsc_st = LLSC.LLWait v;
    R_adrs_write_tag : forall nid v, adrs_get_phase nid adrs_st = LLWriteTag v -> exists v', v' <= v /\ llsc_get_cmd nid llsc_st = LLSC.LLWait v';
    R_adrs_read2 : forall nid v, adrs_get_phase nid adrs_st = LLRead2 v -> exists v', v' <= v /\ llsc_get_cmd nid llsc_st = LLSC.LLWait v';
    R_adrs_ll_done1 : forall nid v v' entry entry',
      adrs_get_phase nid adrs_st = LLDone v v' ->
      NatMap_find v adrs_st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v' adrs_st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
      snd entry = snd entry' ->
      llsc_get_cmd nid llsc_st = LLSC.LLDone /\
      llsc_get_excl_ver nid llsc_st = v';
    R_adrs_ll_done2 : forall nid v v' entry entry',
      adrs_get_phase nid adrs_st = LLDone v v' ->
      NatMap_find v adrs_st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v' adrs_st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
      snd entry <> snd entry' ->
      llsc_get_cmd nid llsc_st = LLSC.LLDone /\
      llsc_get_excl_ver nid llsc_st = v;
    R_adrs_sc_start1 : forall nid v v' x entry entry',
      adrs_get_phase nid adrs_st = SCStart v v' x ->
      NatMap_find v adrs_st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v' adrs_st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
      snd entry = snd entry' ->
      llsc_get_cmd nid llsc_st = LLSC.SCWait x /\
      llsc_get_excl_ver nid llsc_st = v';
    R_adrs_sc_start2 : forall nid v v' x entry entry',
      adrs_get_phase nid adrs_st = SCStart v v' x ->
      NatMap_find v adrs_st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v' adrs_st.(adrs_fsc).(fsc_val_hist) = Some entry' ->
      snd entry <> snd entry' ->
      llsc_get_cmd nid llsc_st = LLSC.SCWait x /\
      llsc_get_excl_ver nid llsc_st = v;
    R_adrs_sc_llwait : forall nid v x,
      adrs_get_phase nid adrs_st = SCLLWait v x ->
      llsc_get_cmd nid llsc_st = LLSC.SCWait x /\
      llsc_get_excl_ver nid llsc_st = v;
    R_adrs_sc_lldone : forall nid v v' x,
      adrs_get_phase nid adrs_st = SCLLDone v v' x ->
      llsc_get_cmd nid llsc_st = LLSC.SCWait x /\
      llsc_get_excl_ver nid llsc_st = v;
    R_adrs_sc_scwait1 : forall nid v v' x t,
      adrs_get_phase nid adrs_st = SCSCWait v v' x t ->
      fsc_get_cmd nid adrs_st.(adrs_fsc) = FSC.SCWait x t ->
      llsc_get_cmd nid llsc_st = LLSC.SCWait x /\
      llsc_get_excl_ver nid llsc_st = v;
    R_adrs_sc_scwait2 : forall nid v v' x t,
      adrs_get_phase nid adrs_st = SCSCWait v v' x t ->
      fsc_get_cmd nid adrs_st.(adrs_fsc) = FSC.SCDone true ->
      llsc_get_cmd nid llsc_st = LLSC.SCDone true;
    R_adrs_sc_scwait3 : forall nid v v' x t,
      adrs_get_phase nid adrs_st = SCSCWait v v' x t ->
      fsc_get_cmd nid adrs_st.(adrs_fsc) = FSC.SCDone false ->
      llsc_get_cmd nid llsc_st = LLSC.SCWait x /\
      llsc_get_excl_ver nid llsc_st = v;
    R_adrs_read_tag : forall nid,
      adrs_get_phase nid adrs_st = SCReadTag ->
      llsc_get_cmd nid llsc_st = LLSC.SCDone true;
    R_adrs_ver : adrs_st.(adrs_fsc).(fsc_curr_ver) = llsc_st.(llsc_curr_ver);
    R_adrs_val_hist : forall v entry,
      NatMap_find v adrs_st.(adrs_fsc).(fsc_val_hist) = Some entry ->
      NatMap_find v llsc_st.(llsc_val_hist) = Some (fst entry);
  }.

  #[local] Ltac hammer nid HR :=
    constructor;
    [ intros NID; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V V' Entry Entry'; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V V' Entry Entry'; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V V' X Entry Entry'; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V V' X Entry Entry'; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V X; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V V' X; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V V' X T; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; fsc_unfold; fsc_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; fsc_unfold; fsc_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V V' X T; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; fsc_unfold; fsc_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; fsc_unfold; fsc_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID V V' X T; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; fsc_unfold; fsc_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; fsc_unfold; fsc_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      intros NID; destruct (Nat.eq_dec NID nid); [ subst NID; adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gse by auto; try discriminate | adrs_unfold; adrs_reduce; llsc_unfold; llsc_reduce; repeat rewrite NatMap_gso by auto; try apply HR ] |
      adrs_unfold; adrs_reduce; fsc_unfold; fsc_reduce; llsc_unfold; llsc_reduce; try apply HR |
      intros V Entry; adrs_unfold; adrs_reduce; fsc_unfold; fsc_reduce; llsc_unfold; llsc_reduce; try apply HR
    ].
  

  Lemma R_adrs_init : R_adrs adrs_init_state llsc_init_state.
  Proof.
    constructor; cbn; try discriminate; auto.
    - intros v entry.
      destruct (Nat.eq_dec v 0); try discriminate; subst v.
      intros Heq; injection Heq; intros; subst entry; clear Heq.
      cbn; auto.
  Qed.

  Lemma R_adrs_step : forall adrs_st adrs_st' llsc_st,
    adrs_valid adrs_st ->
    llsc_valid llsc_st ->
    R_adrs adrs_st llsc_st ->
    adrs_step adrs_st adrs_st' ->
    exists llsc_st', llsc_reachable llsc_st llsc_st' /\ R_adrs adrs_st' llsc_st'.
  Proof.
    intros adrs_st adrs_st' llsc_st Hval_adrs Hval_llsc HR Hstep.
    Adrs.step_case Hstep.
    - (* start_ll *)
      exists (llsc_start_ll nid llsc_st); split.
      + eapply reachable_step; [apply reachable_self|].
        left; constructor; auto.
        apply (R_adrs_idle _ _ HR); auto.
      + hammer nid HR.
        intros _; eexists; reflexivity.

    - (* start_sc *)
      pose proof (adrs_ll_done_phase_prop nid _ _ _ Hval_adrs Hpre2) as (Hphase & _).
      pose proof (fsc_val_hist_not_none _ v (adrs_fsc_valid _ Hval_adrs) ltac:(lia)) as Hv.
      destruct (NatMap_find v (fsc_val_hist (adrs_fsc adrs_st))) eqn:Ev; [|contradiction]; clear Hv.
      pose proof (fsc_val_hist_not_none _ v' (adrs_fsc_valid _ Hval_adrs) ltac:(lia)) as Hv.
      destruct (NatMap_find v' (fsc_val_hist (adrs_fsc adrs_st))) eqn:Ev'; [|contradiction]; clear Hv.
      destruct (Config.tag_nid_t_eq_dec (snd p) (snd p0)).

      + pose proof (R_adrs_ll_done1 _ _ HR _ _ _ _ _ Hpre2 Ev Ev' e) as (HR'1 & HR'2).
        exists (llsc_start_sc nid x llsc_st); split.
        * eapply reachable_step; [apply reachable_self|].
          left; constructor; auto.
        * hammer nid HR.
          -- intros Heq; injection Heq; intros ? ? ?; subst V V' X; clear Heq.
             intros Heq1 Heq2; rewrite Ev in Heq1; rewrite Ev' in Heq2.
             injection Heq1; injection Heq2; intros ? ?; subst Entry Entry'.
             intros _; split; auto.
          -- intros Heq; injection Heq; intros ? ? ?; subst V V' X; clear Heq.
             intros Heq1 Heq2; rewrite Ev in Heq1; rewrite Ev' in Heq2.
             injection Heq1; injection Heq2; intros ? ?; subst Entry Entry'.
             intros; contradiction.

      + pose proof (R_adrs_ll_done2 _ _ HR _ _ _ _ _ Hpre2 Ev Ev' n) as (HR'1 & HR'2).
        exists (llsc_start_sc nid x llsc_st); split.
        * eapply reachable_step; [apply reachable_self|].
          left; constructor; auto.
        * hammer nid HR.
          -- intros Heq; injection Heq; intros ? ? ?; subst V V' X; clear Heq.
             intros Heq1 Heq2; rewrite Ev in Heq1; rewrite Ev' in Heq2.
             injection Heq1; injection Heq2; intros ? ?; subst Entry Entry'.
             intros; contradiction.
          -- intros Heq; injection Heq; intros ? ? ?; subst V V' X; clear Heq.
             intros Heq1 Heq2; rewrite Ev in Heq1; rewrite Ev' in Heq2.
             injection Heq1; injection Heq2; intros ? ?; subst Entry Entry'.
             intros _; split; auto.

    - (* adrs_cl *)
      pose proof (adrs_ll_done_phase_prop nid _ _ _ Hval_adrs Hpre2) as (Hphase & _).
      pose proof (fsc_val_hist_not_none _ v (adrs_fsc_valid _ Hval_adrs) ltac:(lia)) as Hv.
      destruct (NatMap_find v (fsc_val_hist (adrs_fsc adrs_st))) eqn:Ev; [|contradiction]; clear Hv.
      pose proof (fsc_val_hist_not_none _ v' (adrs_fsc_valid _ Hval_adrs) ltac:(lia)) as Hv.
      destruct (NatMap_find v' (fsc_val_hist (adrs_fsc adrs_st))) eqn:Ev'; [|contradiction]; clear Hv.
      destruct (Config.tag_nid_t_eq_dec (snd p) (snd p0)).

      + pose proof (R_adrs_ll_done1 _ _ HR _ _ _ _ _ Hpre2 Ev Ev' e) as (HR'1 & HR'2).
        exists (llsc_cl nid llsc_st); split.
        * eapply reachable_step; [apply reachable_self|].
          left; constructor; auto.
        * hammer nid HR.
          auto.
          
      + pose proof (R_adrs_ll_done2 _ _ HR _ _ _ _ _ Hpre2 Ev Ev' n) as (HR'1 & HR'2).
        exists (llsc_cl nid llsc_st); split.
        * eapply reachable_step; [apply reachable_self|].
          left; constructor; auto.
        * hammer nid HR.
          auto.

    - (* read1_done *)
      exists llsc_st; split.
      + apply reachable_self.
      + hammer nid HR.
        intros Heq; injection Heq; intros ?; subst V; clear Heq.
        pose proof (R_adrs_read1 _ _ HR _ Hpre2) as Hphase.
        destruct Hphase as (v & Hphase).
        pose proof (llsc_ll_wait_phase_prop _ _ _ Hval_llsc Hphase) as Hle.
        exists v; split; auto.
        rewrite (R_adrs_ver _ _ HR); auto.

    - (* write_tag_done *)
      exists llsc_st; split.
      + apply reachable_self.
      + hammer nid HR.
        intros Heq; injection Heq; intros ?; subst V; clear Heq.
        apply (R_adrs_write_tag _ _ HR _ _ Hpre2).

    - (* read2_done *)
      pose proof (R_adrs_read2 _ _ HR _ _ Hpre2) as (v' & Hphase1 & Hphase2).
      pose proof (adrs_read2_phase_prop nid _ _ Hval_adrs Hpre2) as (Hphase3 & _).
      pose proof (fsc_val_hist_not_none _ _ (adrs_fsc_valid _ Hval_adrs) Hphase3) as Hv.
      destruct (NatMap_find v (fsc_val_hist (adrs_fsc adrs_st))) eqn:Ev; [|contradiction]; clear Hv.
      pose proof (fsc_val_hist_not_none _ (fsc_curr_ver (adrs_fsc adrs_st)) (adrs_fsc_valid _ Hval_adrs) ltac:(auto)) as Hv.
      destruct (NatMap_find (fsc_curr_ver (adrs_fsc adrs_st)) (fsc_val_hist (adrs_fsc adrs_st))) eqn:Ev'; [|contradiction]; clear Hv.
      destruct (Config.tag_nid_t_eq_dec (snd p) (snd p0)).

      + (* equal tags *)
        exists (llsc_ret_ll nid llsc_st.(llsc_curr_ver) llsc_st); split.
        * eapply reachable_step; [apply reachable_self|].
          right; right; econstructor.
          1: auto.
          1: apply Hphase2.
          rewrite (R_adrs_ver _ _ HR) in Hphase3; lia.
        * hammer nid HR.
          -- intros Heq; injection Heq; intros ? ?; subst V V'; clear Heq.
             intros _ _ _; split; auto; symmetry; apply HR.
          -- intros Heq; injection Heq; intros ? ?; subst V V'; clear Heq.
             intros Hv Hv'; rewrite Ev in Hv; rewrite Ev' in Hv'.
             injection Hv; injection Hv'; intros ? ?; subst Entry Entry'.
             intros; contradiction.

      + (* unequal tags *)
        exists (llsc_ret_ll nid v llsc_st); split.
        * eapply reachable_step; [apply reachable_self|].
          right; right; econstructor.
          1: auto.
          1: apply Hphase2.
          rewrite (R_adrs_ver _ _ HR) in Hphase3; lia.
        * hammer nid HR.
          -- intros Heq; injection Heq; intros ? ?; subst V V'; clear Heq.
             intros Hv Hv'; rewrite Ev in Hv; rewrite Ev' in Hv'.
             injection Hv; injection Hv'; intros ? ?; subst Entry Entry'.
             intros; contradiction.
          -- intros Heq; injection Heq; intros ? ?; subst V V'; clear Heq.
             intros _ _ _; split; auto; symmetry; apply HR.

    - (* start_fll *)
      exists llsc_st; split.
      + apply reachable_self.
      + hammer nid HR.
        intros Heq; injection Heq; intros ? ?; subst V X; clear Heq.
        apply (R_adrs_sc_start1 _ _ HR _ _ _ _ _ _ Hpre2 Hpre3 Hpre4 Hpre5).

    - (* ret_fll *)
      exists llsc_st; split.
      + apply reachable_self.
      + hammer nid HR.
        intros Heq; injection Heq; intros ? ? ?; subst V V' X; clear Heq.
        apply (R_adrs_sc_llwait _ _ HR); auto.

    - (* start_fsc *)
      exists llsc_st; split.
      + apply reachable_self.
      + hammer nid HR.
        intros Heq; injection Heq; intros ? ? ? ?; subst V V' X T; clear Heq.
        intros _.
        apply (R_adrs_sc_lldone _ _ HR _ _ _ _ Hpre2).

    - (* fsc_succ_sc *)
      pose proof (adrs_phase_prop nid _ Hval_adrs) as Hphase.
      unfold adrs_phase_prop_def in Hphase.
      rewrite <- Heqfsc_st in Hphase.
      rewrite Hpre2 in Hphase.
      destruct (adrs_get_phase nid adrs_st) eqn:Ephase; try (destruct Hphase as (? & ?)); try discriminate.
      destruct Hphase as [? | [? | (Hphase1 & Hphase2)]]; try discriminate.
      injection Hphase1; intros; subst x0 t0; clear Hphase1.
      pose proof (R_adrs_sc_scwait1 _ _ HR _ _ _ _ _ Ephase ltac:(rewrite <- Heqfsc_st; auto)) as (HR'1 & HR'2).
      pose proof (adrs_sc_ll_wait_phase_prop nid _ Hval_adrs) as (_ & _ & Hphase).
      specialize (Hphase _ _ _ _ Ephase) as (Hphase & _); subst ll_v chk_v.

      exists (llsc_succ_sc nid x llsc_st); split.
      + eapply reachable_step; [apply reachable_self|].
        right; left; constructor; auto.
        rewrite Hphase, Hpre3.
        rewrite Heqfsc_st, (R_adrs_ver _ _ HR); auto.
      + subst fsc_st; hammer nid HR; auto.
        all: try (fold (adrs_get_phase nid adrs_st); rewrite Ephase; discriminate).
        5: rewrite (R_adrs_ver _ _ HR); auto.
        5: rewrite (R_adrs_ver _ _ HR); NatMap_cmp V (S (llsc_curr_ver llsc_st)); cbn; [intros Heq; inversion Heq; cbn; auto | apply HR].
        1,2: fsc_unfold; fsc_reduce;
             intros HNID1 HNID2 HNID3 HNID4;
             pose proof (adrs_ll_done_phase_prop _ _ _ _ Hval_adrs HNID1) as (HNID5 & _);
             rewrite NatMap_gso in HNID2 by lia;
             rewrite NatMap_gso in HNID3 by lia.
        1: apply (R_adrs_ll_done1 _ _ HR NID V V' Entry Entry' HNID1 HNID2 HNID3 HNID4).
        1: apply (R_adrs_ll_done2 _ _ HR NID V V' Entry Entry' HNID1 HNID2 HNID3 HNID4).
        1,2: fsc_unfold; fsc_reduce;
             intros HNID1 HNID2 HNID3 HNID4;
             pose proof (adrs_sc_start_phase_prop _ _ _ _ _ Hval_adrs HNID1) as (HNID5 & _);
             rewrite NatMap_gso in HNID2 by lia;
             rewrite NatMap_gso in HNID3 by lia.
        1: apply (R_adrs_sc_start1 _ _ HR NID V V' X Entry Entry' HNID1 HNID2 HNID3 HNID4).
        1: apply (R_adrs_sc_start2 _ _ HR NID V V' X Entry Entry' HNID1 HNID2 HNID3 HNID4).

    - (* fsc_fail_sc *)
      pose proof (adrs_phase_prop nid _ Hval_adrs) as Hphase.
      unfold adrs_phase_prop_def in Hphase.
      rewrite <- Heqfsc_st in Hphase.
      rewrite Hpre2 in Hphase.
      destruct (adrs_get_phase nid adrs_st) eqn:Ephase; try (destruct Hphase as (? & ?)); try discriminate.
      destruct Hphase as [? | [? | (Hphase1 & Hphase2)]]; try discriminate.
      injection Hphase1; intros; subst x0 t0; clear Hphase1.
      pose proof (R_adrs_sc_scwait1 _ _ HR _ _ _ _ _ Ephase ltac:(rewrite <- Heqfsc_st; auto)) as (HR'1 & HR'2).
      pose proof (adrs_sc_ll_wait_phase_prop nid _ Hval_adrs) as (_ & _ & Hphase).
      specialize (Hphase _ _ _ _ Ephase) as (Hphase & _); subst ll_v chk_v.

      exists llsc_st; split.
      + apply reachable_self.
      + subst fsc_st; hammer nid HR.
        all: try (fold (adrs_get_phase nid adrs_st); rewrite Ephase; discriminate).
        fold (adrs_get_phase nid adrs_st).
        intros Heq; rewrite Ephase in Heq.
        injection Heq; intros ? ? ? ?; subst V V' X T; clear Heq.
        intros _.
        split; auto.

    - (* ret_fsc_fail *)
      exists llsc_st; split.
      + apply reachable_self.
      + hammer nid HR.
        intros Heq; injection Heq; intros ? ?; subst V X; clear Heq.
        apply (R_adrs_sc_scwait3 _ _ HR _ _ _ _ _ Hpre2 Hpre3).

    - (* ret_fsc_succ *)
      exists llsc_st; split.
      + apply reachable_self.
      + hammer nid HR.
        intros _.
        apply (R_adrs_sc_scwait2 _ _ HR _ _ _ _ _ Hpre2 Hpre3).

    - (* sc_fail *)
      pose proof (adrs_sc_ll_wait_phase_prop nid _ Hval_adrs) as (_ & Hphase & _).
      specialize (Hphase _ _ _ Hpre2) as (Hphase & _).
      assert (Hv : v = v' \/ v < v') by lia.
      destruct Hv as [Hv | Hv].
      1: subst v'; rewrite Hpre3 in Hpre4; injection Hpre4; intros; subst entry'; contradiction.
      rewrite (R_adrs_ver _ _ HR) in Hphase.
      pose proof (R_adrs_sc_lldone _ _ HR _ _ _ _ Hpre2) as (HR'1 & HR'2).

      exists (llsc_cl nid (llsc_fail_sc nid llsc_st)); split.
      + eapply reachable_step; [eapply reachable_step|].
        1: apply reachable_self.
        2: right; right; econstructor.
        1: right; left; econstructor.
        all: auto.
        1: apply HR'1.
        1: lia.
        unfold llsc_get_cmd, llsc_fail_sc; cbn [llsc_cmd]; rewrite NatMap_gse by auto; reflexivity.
      + hammer nid HR; auto.

    - (* read_tag_done *)
      exists (llsc_cl nid llsc_st); split.
      + eapply reachable_step; [apply reachable_self|].
        right; right; econstructor; auto.
        apply (R_adrs_read_tag _ _ HR _ Hpre2).
      + hammer nid HR; auto.
  Qed.

End Adrs_Refine.
