Require Import lib.LibTacticsMin.
Require Import riscv.Utility.Monads. Require Import riscv.Utility.MonadNotations.
Require Import coqutil.Macros.unique.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Spec.Execute.
Require Import riscv.Platform.Run.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.PowerFunc.
Require Import riscv.Utility.ListLib.
Require Import coqutil.Decidable.
Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Primitives.
Require Import Coq.micromega.Lia.
Require Import riscv.Utility.div_mod_to_quot_rem.
Require Import compiler.util.Misc.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.ZBitOps.
Require Import compiler.util.Common.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.EmitsValid.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Scalars.
Require Import compiler.Simp.
Require Import compiler.SimplWordExpr.
Require Import bedrock2.ptsto_bytes.
Require Import compiler.RiscvWordProperties.
Require Import compiler.eqexact.
Require Import compiler.on_hyp_containing.
Require Import compiler.FlatToRiscvBW.
Require coqutil.Map.Empty_set_keyed_map.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Section TODO.
  Context {K V: Type}.
  Context {M: map.map K V}.
  Axiom put_put_same: forall k v1 v2 m, map.put (map.put m k v1) k v2 = map.put m k v2.
End TODO.


Axiom TODO: False.

Module Import FlatToRiscv.
  Export FlatToRiscvDef.FlatToRiscvDef.

  Class parameters := {
    def_params :> FlatToRiscvDef.parameters;

    locals :> map.map Register word;
    mem :> map.map word byte;

    M: Type -> Type;
    MM :> Monad M;
    RVM :> RiscvProgram M word;
    PRParams :> PrimitivesParams M (RiscvMachine Register actname);

    ext_spec : list (mem * actname * list word * (mem * list word)) ->
               mem -> actname -> list word -> (mem -> list word -> Prop) -> Prop;

    (* An abstract predicate on the low-level state, which can be chosen by authors of
       extensions. The compiler will ensure that this guarantee holds before each external
       call. *)
    ext_guarantee: RiscvMachine Register actname -> Prop;
  }.

  Instance syntax_params{p: parameters}: Syntax.parameters := {|
    Syntax.varname := Register;
    Syntax.funname := Empty_set;
    Syntax.actname := actname;
  |}.

  Instance Semantics_params{p: parameters}: Semantics.parameters := {|
    Semantics.syntax := syntax_params;
    Semantics.ext_spec := ext_spec;
    Semantics.funname_eqb := Empty_set_rect _;
    Semantics.funname_env := Empty_set_keyed_map.map;
  |}.

  Class assumptions{p: parameters} := {
    word_riscv_ok :> word.riscv_ok (@word W);
    locals_ok :> map.ok locals;
    mem_ok :> map.ok mem;
    actname_eq_dec :> DecidableEq actname;
    PR :> Primitives PRParams;

    (* For authors of extensions, a freely choosable ext_guarantee sounds too good to be true!
       And indeed, there are two restrictions:
       The first restriction is that ext_guarantee needs to be preservable for the compiler: *)
    ext_guarantee_preservable: forall (m1 m2: RiscvMachine Register actname),
        ext_guarantee m1 ->
        map.same_domain m1.(getMem) m2.(getMem) ->
        m1.(getLog) = m2.(getLog) ->
        ext_guarantee m2;

    (* And the second restriction is part of the correctness requirement for compilation of
       external calls: Every compiled external call has to preserve ext_guarantee *)
    compile_ext_call_correct: forall (initialL: RiscvMachine Register actname) action postH newPc insts
        (argvars resvars: list Register) initialMH R,
      insts = compile_ext_call resvars action argvars ->
      newPc = word.add initialL.(getPc) (word.mul (word.of_Z 4) (word.of_Z (Zlength insts))) ->
      Forall valid_register argvars ->
      Forall valid_register resvars ->
      (program initialL.(getPc) insts * eq initialMH * R)%sep initialL.(getMem) ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      ext_guarantee initialL ->
      exec map.empty (SInteract resvars action argvars)
           initialL.(getLog) initialMH initialL.(getRegs) postH ->
      runsTo (mcomp_sat (run1 iset)) initialL
             (fun finalL =>
                  (* external calls can't modify the memory for now *)
                  postH finalL.(getLog) initialMH finalL.(getRegs) /\
                  finalL.(getPc) = newPc /\
                  finalL.(getNextPc) = add newPc (ZToReg 4) /\
                  (program initialL.(getPc) insts * eq initialMH * R)%sep finalL.(getMem) /\
                  ext_guarantee finalL);
  }.

  Instance BW_params(p: parameters)(h: assumptions): FlatToRiscvBW.parameters width width_cases :=
  {
    FlatToRiscvBW.actname := actname;
    FlatToRiscvBW.compile_ext_call := compile_ext_call;
    FlatToRiscvBW.max_ext_call_code_size := max_ext_call_code_size;
    FlatToRiscvBW.compile_ext_call_length := compile_ext_call_length;
    FlatToRiscvBW.compile_ext_call_emits_valid := compile_ext_call_emits_valid;
    FlatToRiscvBW.PRParams := PRParams;
    FlatToRiscvBW.PR := PR;
  }.

  Instance BW_specific_proofs(p: parameters)(h: assumptions):
    FlatToRiscvBW.proofs (@BW_params p h) := ProofsBW width width_cases (BW_params h).
End FlatToRiscv.

Local Unset Universe Polymorphism. (* for Add Ring *)

Section FlatToRiscv1.
  Context {p: unique! FlatToRiscv.parameters}.
  Context {h: unique! FlatToRiscv.assumptions}.

  Notation var := Z (only parsing).

  Definition trace := list (LogItem actname).

  Local Notation RiscvMachineL := (RiscvMachine Register actname).

  Ltac word_cst w :=
    match w with
    | word.of_Z ?x => let b := isZcst x in
                      match b with
                      | true => x
                      | _ => constr:(NotConstant)
                      end
    | _ => constr:(NotConstant)
    end.

  Definition word_ring_morph := word.ring_morph (word := word).
  Definition word_ring_theory := word.ring_theory (word := word).

  Hint Rewrite
    word_ring_morph.(morph_add)
    word_ring_morph.(morph_sub)
    word_ring_morph.(morph_mul)
    word_ring_morph.(morph_opp)
  : rew_word_morphism.

  Add Ring wring : word_ring_theory
      (preprocess [autorewrite with rew_word_morphism],
       morphism word_ring_morph,
       constants [word_cst]).

  Hint Rewrite @Zlength_nil @Zlength_cons @Zlength_app: rew_Zlength.

  Lemma reduce_eq_to_sub_and_lt: forall (y z: word) {T: Type} (thenVal elseVal: T),
      (if word.eqb y z then thenVal else elseVal) =
      (if word.ltu (word.sub y z) (word.of_Z 1) then thenVal else elseVal).
  Proof.
  Admitted.

  (* TODO is there a principled way of writing such proofs? *)
  Lemma reduce_eq_to_sub_and_lt_old: forall (y z: word) {T: Type} (thenVal elseVal: T),
    (if ltu (sub y  z) (fromImm 1) then thenVal else elseVal) =
    (if reg_eqb y z        then thenVal else elseVal).
  Proof. (*
    intros. destruct (weq y z).
    - subst z. unfold wminus. rewrite wminus_inv.
      destruct (wlt_dec (wzero wXLEN) $1); [reflexivity|].
      change (wzero wXLEN) with (natToWord wXLEN 0) in n. unfold wlt in n.
      exfalso. apply n.
      do 2 rewrite wordToN_nat. rewrite roundTrip_0.
      clear.
      destruct wXLEN as [|w1] eqn: E.
      + unfold wXLEN in *. destruct bitwidth; discriminate.
      + rewrite roundTrip_1. simpl. constructor.
    - destruct (@wlt_dec wXLEN (y ^- z) $ (1)) as [E|NE]; [|reflexivity].
      exfalso. apply n. apply sub_0_eq.
      unfold wlt in E.
      do 2 rewrite wordToN_nat in E.
      clear -E.
      destruct wXLEN as [|w1] eqn: F.
      + unfold wXLEN in *. destruct bitwidth; discriminate.
      + rewrite roundTrip_1 in E.
        simpl in E. apply N.lt_1_r in E. change 0%N with (N.of_nat 0) in E.
        apply Nnat.Nat2N.inj in E. rewrite <- (roundTrip_0 (S w1)) in E.
        apply wordToNat_inj in E.
        exact E.
  Qed.
*)
  Admitted.

  (*
  Lemma wlshift_bitSlice_plus: forall (sz1 sz2: Z) v,
      (0 <= sz1)%Z ->
      (0 <= sz2)%Z ->
      wlshift (ZToWord wXLEN (bitSlice v sz1 (sz1 + sz2))) (Z.to_nat sz1)
      ^+ ZToWord wXLEN (bitSlice v 0 sz1)
      = ZToWord wXLEN (bitSlice v 0 (sz1 + sz2)).
  Proof.
    intros. rewrite wlshift_alt.
    rewrite wlshift_mul_Zpow2 by assumption.
    rewrite <- ZToWord_mult.
    rewrite <- ZToWord_plus.
    f_equal.
    apply bitSlice_split; assumption.
  Qed.
  *)

  (*
  Context {Name: NameWithEq}.

  (* If we made it a definition instead, destructing an if on "@dec (@eq (@var Name) x x0)"
     (from this file), where a "@dec (@eq (@Reg Name) x x0)" (from another file, Riscv.v)
     is in the context, will not recognize that these two are the same (they both reduce to
     "@dec (@eq var x x0)", which is annoying. *)
  Notation var := var.
  Existing Instance eq_name_dec.
   *)

  (* Set Printing Projections.
     Uncaught anomaly when stepping through proofs :(
     https://github.com/coq/coq/issues/6257 *)

  Arguments Z.mul: simpl never.
  Arguments Z.add: simpl never.
  Arguments run1: simpl never.

  Ltac ensure_is_nat_rel R :=
    match R with
    | ?P /\ ?Q => ensure_is_nat_rel P; ensure_is_nat_rel Q
    | ?P \/ ?Q => ensure_is_nat_rel P; ensure_is_nat_rel Q
    | @eq nat _ _  => idtac (* can't use %nat here because = is polymorphic *)
    | (_ <  _)%nat => idtac
    | (_ <= _)%nat => idtac
    | (_ >  _)%nat => idtac
    | (_ >= _)%nat => idtac
    end.

  Lemma pow2_wXLEN_4: 4 < 2 ^ XLEN.
  Proof.
    unfold XLEN, MachineWidth_XLEN.
    pose proof (@word.width_pos _ _ word_ok).
    pose proof (Z.pow_gt_1 2 width).
    (* TODO doesn't hold, if we want this we'll have to add a stronger bound to Words,
       or somewhere else *)
  Admitted.

  Ltac nat_rel_with_words_pre :=
    match goal with
    | |- ?P => ensure_is_nat_rel P
    end(*;
    repeat match goal with
           | IsMem: Memory.Memory ?M _, m: ?M |- _ =>
             unique pose proof (@Memory.memSize_bound M _ IsMem m)
           end;
    pose proof pow2_wXLEN_4;
    rewrite? wordToNat_wplus in *;
    rewrite? wordToNat_natToWord_eqn in * *).

  Ltac nat_rel_with_words :=
    nat_rel_with_words_pre(*;
    nat_div_mod_to_quot_rem;
    nia *).

  Definition divisibleBy4(x: word): Prop := (word.unsigned x) mod 4 = 0.

  Definition divisibleBy4'(x: word): Prop := word.modu x (word.of_Z 4) = word.of_Z 0.

  Lemma four_fits: 4 < 2 ^ width.
  Proof.
    destruct width_cases as [C | C]; rewrite C; reflexivity.
  Qed.

  Ltac div4_sidecondition :=
    pose proof four_fits;
    rewrite ?word.unsigned_of_Z, ?Z.mod_small;
    lia.

  Lemma divisibleBy4_alt(x: word): divisibleBy4 x -> divisibleBy4' x.
  Proof.
    intro H. unfold divisibleBy4, divisibleBy4' in *.
    apply word.unsigned_inj.
    rewrite word.unsigned_modu_nowrap by div4_sidecondition.
    replace (word.unsigned (word.of_Z 4)) with 4 by div4_sidecondition.
    rewrite H.
    div4_sidecondition.
  Qed.

  Lemma unsigned_of_Z_4: word.unsigned (word.of_Z (word := word) 4) = 4.
  Proof. div4_sidecondition. Qed.

  Lemma unsigned_of_Z_0: word.unsigned (word.of_Z (word := word) 0) = 0.
  Proof. div4_sidecondition. Qed.

  Lemma divisibleBy4_add_4_r(x: word)
    (D: divisibleBy4 x):
    divisibleBy4 (word.add x (word.of_Z 4)).
  Proof.
    unfold divisibleBy4 in *.
    rewrite word.unsigned_add.
    rewrite <- Znumtheory.Zmod_div_mod.
    - rewrite Zplus_mod. rewrite D. rewrite unsigned_of_Z_4. reflexivity.
    - lia.
    - destruct width_cases as [C | C]; rewrite C; reflexivity.
    - unfold Z.divide. exists (2 ^ width / 4).
      destruct width_cases as [C | C]; rewrite C; reflexivity.
  Qed.

  Lemma divisibleBy4_admit(x y: word):
    divisibleBy4 x ->
    divisibleBy4 y.
  Admitted.

  Ltac solve_divisibleBy4 :=
    lazymatch goal with
    | |- divisibleBy4 _ => idtac
    | |- _ => fail "not a divisibleBy4 goal"
    end;
    solve [eapply divisibleBy4_admit; eassumption (* TODO *) ].

  Ltac simpl_modu4_0 :=
    simpl;
    match goal with
    | |- context [word.eqb ?a ?b] =>
      rewrite (word.eqb_eq a b) by (apply divisibleBy4_alt; solve_divisibleBy4)
    end;
    simpl.

  Definition runsTo: RiscvMachineL -> (RiscvMachineL -> Prop) -> Prop :=
    runsTo (mcomp_sat (run1 iset)).

  Lemma one_step: forall initialL P,
      mcomp_sat (run1 iset) initialL P ->
      runsTo initialL P.
  Proof.
    intros.
    eapply runsToStep; [eassumption|].
    intros.
    apply runsToDone. assumption.
  Qed.

  Lemma det_step: forall initialL midL P,
      mcomp_sat (run1 iset) initialL (eq midL) ->
      runsTo midL P ->
      runsTo initialL P.
  Proof.
    intros.
    eapply runsToStep; [eassumption|].
    intros. subst.
    assumption.
  Qed.

  Ltac simpl_run1 :=
    cbv [run1 (*execState*) OStateNDOperations.put OStateNDOperations.get
         Return Bind State_Monad OStateND_Monad
         execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute
         getRegs getPc getNextPc getMem getLog
         getPC setPC getRegister setRegister].

  Tactic Notation "log_solved" tactic(t) :=
    match goal with
    | |- ?G => let H := fresh in assert G as H by t; idtac "solved" G; exact H
    | |- ?G => idtac "did not solve" G
    end.

  Local Ltac solve_stmt_not_too_big :=
    lazymatch goal with
    | H: stmt_not_too_big _ |- stmt_not_too_big _ =>
        clear -H;
        unfold stmt_not_too_big in *;
        change (2 ^ 9)%Z with 512%Z in *;
        simpl stmt_size in H;
        repeat match goal with
               | s: stmt |- _ => unique pose proof (stmt_size_nonneg s)
               end;
        match goal with
        | |- ?SZ _ _ < _ => (* COQBUG https://github.com/coq/coq/issues/9268 *)
          change @stmt_size with SZ in *
        end;
        lia
    end.

  (* Needed because simpl will unfold (4 * ...) which is unreadable *)
  Local Ltac simpl_pow2 := idtac. (*
    repeat match goal with
    | |- context [1 + ?a] => change (1 + a) with (S a)
    | |- context [pow2 (S ?a)] => change (pow2 (S a)) with (2 * pow2 a)
    | |- context [pow2 0] => change (pow2 0) with 1
    end.
*)

  Ltac simpl_RiscvMachine_get_set := simpl in *. (* TODO is this enough? *)

  Ltac destruct_RiscvMachine_0 m :=
    let t := type of m in
    unify t RiscvMachine;
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let e := fresh m "_eh" in
    let me := fresh m "_mem" in
    destruct m as [ [r p n e] me ];
    simpl_RiscvMachine_get_set.

  Ltac destruct_RiscvMachine m :=
    let t := type of m in
    unify t RiscvMachineL;
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let me := fresh m "_mem" in
    let l := fresh m "_log" in
    destruct m as [r p n me l];
    simpl_RiscvMachine_get_set.

  Arguments Z.modulo : simpl never.

  Ltac solve_valid_registers :=
    match goal with
    | |- valid_registers _ => solve [simpl; auto]
    end.

  Instance word_eq_dec: DecidableEq word. (* TODO *) Admitted.

  Lemma disjoint_putmany_preserves_store_bytes: forall n a vs (m1 m1' mq: mem),
      store_bytes n m1 a vs = Some m1' ->
      map.disjoint m1 mq ->
      store_bytes n (map.putmany m1 mq) a vs = Some (map.putmany m1' mq).
  Proof.
    intros.
    unfold store_bytes, load_bytes, unchecked_store_bytes in *. simp.
    erewrite map.getmany_of_tuple_in_disjoint_putmany by eassumption.
    f_equal.
    set (ks := (footprint a n)) in *.
    rename mq into m2.
    rewrite map.putmany_of_tuple_to_putmany.
    rewrite (map.putmany_of_tuple_to_putmany n m1 ks vs).
    apply map.disjoint_putmany_commutes.
    pose proof map.getmany_of_tuple_to_sub_domain as P.
    specialize P with (1 := E).
    apply map.sub_domain_value_indep with (vs2 := vs) in P.
    set (mp := (map.putmany_of_tuple ks vs map.empty)) in *.
    apply map.disjoint_comm.
    eapply map.sub_domain_disjoint; eassumption.
  Qed.

  Lemma store_bytes_preserves_footprint: forall n a v (m m': mem),
      Memory.store_bytes n m a v = Some m' ->
      map.same_domain m m'.
  Proof.
    intros. unfold store_bytes, load_bytes, unchecked_store_bytes in *. simp.
    eauto using map.putmany_of_tuple_preserves_domain.
  Qed.

  Ltac simpl_bools :=
    repeat match goal with
           | H : ?x = false |- _ =>
             progress rewrite H in *
           | H : ?x = true |- _ =>
             progress rewrite H in *
           | |- context [negb true] => progress unfold negb
           | |- context [negb false] => progress unfold negb
           | H : negb ?x = true |- _ =>
             let H' := fresh in
             assert (x = false) as H' by (eapply negb_true_iff; eauto);
             clear H
           | H : negb ?x = false |- _ =>
             let H' := fresh in
             assert (x = true) as H' by (eapply negb_false_iff; eauto);
             clear H
           end.

  Ltac prove_ext_guarantee :=
    eapply ext_guarantee_preservable; [eassumption | simpl | reflexivity ];
    (* eauto using the lemmas below doesn't work, why? *)
    first [ eapply map.same_domain_refl |
            eapply store_bytes_preserves_footprint; eassumption ].

  Ltac simulate'_step :=
    first (* lemmas introduced only in this file: *)
    [ refine (@FlatToRiscvBW.go_load _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [sidecondition..|]
    | refine (@FlatToRiscvBW.go_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [sidecondition..|]
    | simulate_step
    | simpl_modu4_0 ].

  Ltac simulate' := repeat simulate'_step.

  Ltac run1det :=
    eapply det_step;
    [ simulate';
      match goal with
      | |- ?mid = ?RHS =>
        (* simpl RHS because mid will be instantiated to it and turn up again in the next step *)
        is_evar mid; simpl; reflexivity
      | |- _ => fail 10000 "simulate' did not go through completely"
      end
    | ].

  (* seplog which knows that "program" is an array and how to deal with cons and append in
     that array, and how to make addresses match *)
  Ltac pseplog :=
    unfold program in *;
    repeat match goal with
           | H: _ ?m |- _ ?m => progress (simpl in * (* does array_cons *))
           | H: context [array _ _ ?addr1 ?content] |- context [array _ _ ?addr2 ?content] =>
             progress replace addr1 with addr2 in H by ring;
               ring_simplify addr2;
               ring_simplify addr2 in H
           (* just unprotected seprewrite will instantiate evars in undesired ways *)
           | |- context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
             seprewrite0 (array_append_DEPRECATED PT SZ xs ys start)
           | H: context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] |- _ =>
             seprewrite0_in (array_append_DEPRECATED PT SZ xs ys start) H
           end;
    seplog.

  Ltac apply_post :=
    match goal with
    | H: ?post _ _ _ |- ?post _ _ _ =>
      eqexact H; f_equal; symmetry;
      (apply word.sru_ignores_hibits ||
       apply word.slu_ignores_hibits ||
       apply word.srs_ignores_hibits ||
       apply word.mulhuu_simpl ||
       apply word.divu0_simpl ||
       apply word.modu0_simpl)
    end.

  Ltac run1done :=
    apply runsToDone;
    simpl in *;
    eexists;
    repeat split;
    simpl_word_exprs (@word_ok (@W (@def_params p)));
    first
      [ solve [eauto]
      | solve_word_eq (@word_ok (@W (@def_params p)))
      | solve [pseplog]
      | prove_ext_guarantee
      | apply_post
      | idtac ].

(*
  Ltac IH_done IH :=
    eapply runsToSatisfying_imp; [ exact IH | ];
    subst;
    clear;
    simpl;
    intros;
    destruct_products;
    repeat match goal with
           | |- _ /\ _ => split
           end;
    try assumption;
    try match goal with
        | H: ?m.(core).(pc) = _ |- ?m.(core).(pc) = _ => rewrite H
        end;
    solve_word_eq.
*)

  Arguments LittleEndian.combine: simpl never.

  Lemma iset_is_supported: supported_iset iset.
  Proof.
    unfold iset. destruct_one_match; constructor.
  Qed.

  Definition load_lit_semantics(v: Z): word :=
    add (sll (add (sll (add (sll (add (sll (add (sll (add (sll (add (sll (add
      (ZToReg 0)
      (ZToReg (bitSlice v (7 * 8) (8 * 8)))) 8)
      (ZToReg (bitSlice v (6 * 8) (7 * 8)))) 8)
      (ZToReg (bitSlice v (5 * 8) (6 * 8)))) 8)
      (ZToReg (bitSlice v (4 * 8) (5 * 8)))) 8)
      (ZToReg (bitSlice v (3 * 8) (4 * 8)))) 8)
      (ZToReg (bitSlice v (2 * 8) (3 * 8)))) 8)
      (ZToReg (bitSlice v (1 * 8) (2 * 8)))) 8)
      (ZToReg (bitSlice v (0 * 8) (1 * 8))).

  Lemma compile_lit_correct: forall v: Z,
      load_lit_semantics v = ZToReg v.
  Proof using .
  Admitted.

  Ltac substs :=
    repeat match goal with
           | x := _ |- _ => subst x
           | _: ?x = _ |- _ => subst x
           | _: _ = ?x |- _ => subst x
           end.

  Lemma compile_lit_correct_full: forall initialL post x v R,
      initialL.(getNextPc) = add initialL.(getPc) (ZToReg 4) ->
      let insts := compile_stmt (SLit x v) in
      let d := mul (ZToReg 4) (ZToReg (Zlength insts)) in
      (program initialL.(getPc) insts * R)%sep initialL.(getMem) ->
      valid_registers (SLit x v) ->
      runsTo (withRegs   (map.put initialL.(getRegs) x (ZToReg v))
             (withPc     (add initialL.(getPc) d)
             (withNextPc (add initialL.(getNextPc) d)
                         initialL)))
             post ->
      runsTo initialL post.
  Proof.
    intros *. intros E1 insts d P V N. substs.
    lazymatch goal with
    | H1: valid_registers ?s |- _ =>
      pose proof (compile_stmt_emits_valid iset_is_supported H1 eq_refl) as EV
    end.
    simpl in *.
    destruct_RiscvMachine initialL.
    subst.
    unfold compile_lit_new in *.
    destruct (dec (- 2 ^ 11 <= v < 2 ^ 11)). {
      unfold compile_lit_small in *.
      run1det.
      simpl_word_exprs word_ok.
      exact N.
    }
    destruct (width =? 32) eqn: E. {
      unfold compile_lit_medium in *.
      run1det.
      run1det.
      match goal with
      | R: runsTo ?m post |- runsTo ?m' post =>
        replace m' with m; [exact R|]
      end.
      cbv [withRegs withPc withNextPc withMem withLog]. clear N. f_equal.
      - rewrite put_put_same. f_equal.
        apply word.signed_inj.
        rewrite word.signed_of_Z.
        rewrite word.signed_add.
        rewrite! word.signed_of_Z.
        remember (signExtend 12 (bitSlice (swrap 32 v) 0 12)) as lo.
        remember (v - lo) as hi.
        unfold word.swrap, swrap.
        assert (width = 32) as A by case TODO.
        rewrite <- A.
        remember (2 ^ (width - 1)) as B.
        remember (2 ^ width) as M.
        f_equal.
        (*
        match goal with
        | |- (?a + ?b) mod ?n = (?a' + ?b) mod ?n =>
          rewrite (Zplus_mod a b n); rewrite (Zplus_mod a' b n)
        end.
        f_equal.
        f_equal.
        (* push *)
        rewrite Zplus_mod.
        rewrite (Zminus_mod ((hi + B) mod M) B M).
        rewrite (Zminus_mod ((lo + B) mod M) B M).
        rewrite (Zplus_mod hi B M).
        rewrite (Zplus_mod lo B M).

        rewrite! Zmod_mod.

        (* pull *)
        rewrite <- (Zplus_mod hi B M).
        rewrite <- (Zplus_mod lo B M).
        rewrite <- (Zminus_mod (hi + B) B M).
        rewrite <- (Zminus_mod (lo + B) B M).
        rewrite <- (Zplus_mod (hi + B - B) (lo + B - B) M).
        ring_simplify (hi + B - B + (lo + B - B)).

(*
do we have ready-to-use push/pull mod tactics to solve goals like

(v + B) mod M = ((v - E + B) mod M - B + ((E + B) mod M - B) + B) mod M

?
 *)
        subst hi.
        f_equal.
        lia.

      - solve_word_eq word_ok.
      - solve_word_eq word_ok.
    }
*)
  Admitted.

  Definition eval_stmt := exec map.empty.

  Lemma seplog_subst_eq{A B R: mem -> Prop} {mL mH: mem}
      (H: A mL)
      (H0: iff1 A (R * eq mH)%sep)
      (H1: B mH):
      (B * R)%sep mL.
  Proof.
    unfold iff1 in *.
    destruct (H0 mL) as [P1 P2]. specialize (P1 H).
    apply sep_comm.
    unfold sep in *.
    destruct P1 as (mR & mH' & P11 & P12 & P13). subst mH'. eauto.
  Qed.

  Lemma subst_load_bytes_for_eq {sz} {mH mL: mem} {addr: word} {bs P R}:
      let n := @Memory.bytes_per width sz in
      bedrock2.Memory.load_bytes n mH addr = Some bs ->
      (P * eq mH * R)%sep mL ->
      exists Q, (P * ptsto_bytes n addr bs * Q * R)%sep mL.
  Proof.
    intros n H H0.
    apply sep_of_load_bytes in H; cycle 1. {
      subst n. clear. destruct sz; destruct width_cases as [C | C]; rewrite C; cbv; discriminate.
    }
    destruct H as [Q A]. exists Q.
    assert (((ptsto_bytes n addr bs * Q) * (P * R))%sep mL); [|ecancel_assumption].
    eapply seplog_subst_eq; [exact H0|..|exact A]. ecancel.
  Qed.

  Ltac subst_load_bytes_for_eq :=
    match goal with
    | Load: bedrock2.Memory.load_bytes _ ?m _ = _, Sep: (_ * eq ?m * _)%sep _ |- _ =>
      let Q := fresh "Q" in
      destruct (subst_load_bytes_for_eq Load Sep) as [Q ?]
    end.

  Lemma store_bytes_frame: forall {n: nat} {m1 m1' m: mem} {a: word} {v: HList.tuple byte n} {F},
      Memory.store_bytes n m1 a v = Some m1' ->
      (eq m1 * F)%sep m ->
      exists m', (eq m1' * F)%sep m' /\ Memory.store_bytes n m a v = Some m'.
  Proof.
    intros.
    unfold sep in H0.
    destruct H0 as (mp & mq & A & B & C).
    subst mp.
    unfold map.split in A. destruct A as [A1 A2].
    eexists (map.putmany m1' mq).
    split.
    - unfold sep.
      exists m1' mq. repeat split; trivial.
      apply store_bytes_preserves_footprint in H.
      clear -H A2.
      unfold map.disjoint, map.same_domain, map.sub_domain in *. destruct H as [P Q].
      intros.
      edestruct Q; eauto.
    - subst m.
      eauto using disjoint_putmany_preserves_store_bytes.
  Qed.

  Ltac IH_sidecondition :=
    simpl_word_exprs (@word_ok (@W (@def_params p)));
    first
      [ reflexivity
      | solve [auto]
      | solve_stmt_not_too_big
      | solve_word_eq (@word_ok (@W (@def_params p)))
      | solve_divisibleBy4
      | prove_ext_guarantee
      | pseplog
      | idtac ].

  Arguments map.empty: simpl never.
  Arguments map.get: simpl never.

  Lemma compile_stmt_correct:
    forall (s: stmt) t initialMH initialRegsH postH,
    eval_stmt s t initialMH initialRegsH postH ->
    forall R initialL insts,
    @compile_stmt def_params s = insts ->
    stmt_not_too_big s ->
    valid_registers s ->
    divisibleBy4 initialL.(getPc) ->
    initialL.(getRegs) = initialRegsH ->
    (program initialL.(getPc) insts * eq initialMH * R)%sep initialL.(getMem) ->
    initialL.(getLog) = t ->
    initialL.(getNextPc) = add initialL.(getPc) (ZToReg 4) ->
    ext_guarantee initialL ->
    runsTo initialL (fun finalL => exists finalMH,
          postH finalL.(getLog) finalMH finalL.(getRegs) /\
          (program initialL.(getPc) insts * eq finalMH * R)%sep finalL.(getMem) /\
          finalL.(getPc) = add initialL.(getPc) (mul (ZToReg 4) (ZToReg (Zlength insts))) /\
          finalL.(getNextPc) = add finalL.(getPc) (ZToReg 4) /\
          ext_guarantee finalL).
  Proof.
    pose proof compile_stmt_emits_valid.
    induction 1; intros;
      lazymatch goal with
      | H1: valid_registers ?s, H2: stmt_not_too_big ?s |- _ =>
        pose proof (compile_stmt_emits_valid iset_is_supported H1 H2)
      end;
      repeat match goal with
             | m: _ |- _ => destruct_RiscvMachine m
             end;
      simpl in *;
      subst;
      simp.

    - (* SInteract *)
      eapply runsTo_weaken.
      + eapply compile_ext_call_correct with (postH := post) (action0 := action)
                                             (argvars0 := argvars) (resvars0 := resvars);
          simpl; reflexivity || eassumption || ecancel_assumption || idtac.
        eapply @exec.interact; try eassumption.
      + simpl. intros finalL A. destruct_RiscvMachine finalL. simpl in *.
        destruct_products. subst. eauto 7.

    - (* SCall *)
      match goal with
      | A: map.get map.empty _ = Some _ |- _ =>
        clear -A; exfalso; simpl in *;
        rewrite map.get_empty in A
      end.
      discriminate.

    - (* SLoad *)
      unfold Memory.load, Memory.load_Z in *. simp. subst_load_bytes_for_eq.
      run1det. run1done.

    - (* SStore *)
      assert ((eq m * (program initialL_pc [[compile_store sz a v 0]] * R))%sep initialL_mem)
             as A by ecancel_assumption.
      pose proof (store_bytes_frame H2 A) as P.
      destruct P as (finalML & P1 & P2).
      run1det. run1done.

    - (* SLit *)
      remember (compile_lit x v) as insts.
      eapply compile_lit_correct_full.
      + sidecondition.
      + unfold compile_stmt. unfold getPc, getMem. subst insts. ecancel_assumption.
      + sidecondition.
      + simpl. run1done.

      (* SOp *)
    - match goal with
      | o: Syntax.bopname.bopname |- _ => destruct o
      end;
      simpl in *; run1det; try solve [run1done].
      run1det. run1done.
      match goal with
      | H: ?post _ _ _ |- ?post _ _ _ => eqexact H
      end.
      rewrite reduce_eq_to_sub_and_lt.
      symmetry. apply put_put_same.

    - (* SSet *)
      run1det. run1done.

    - (* SIf/Then *)
      (* execute branch instruction, which will not jump *)
      eapply det_step; simpl in *; subst.
      + simulate'.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + eapply runsTo_trans.
        * (* use IH for then-branch *)
          eapply IHexec; IH_sidecondition.
        * (* jump over else-branch *)
          simpl. intros. simp. destruct_RiscvMachine middle. subst.
          run1det. run1done.

    - (* SIf/Else *)
      (* execute branch instruction, which will jump over then-branch *)
      eapply det_step; simpl in *; subst.
      + simulate'.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + eapply runsTo_trans.
        * (* use IH for else-branch *)
          eapply IHexec; IH_sidecondition.
        * (* at end of else-branch, i.e. also at end of if-then-else, just prove that
             computed post satisfies required post *)
          simpl. intros. simp. destruct_RiscvMachine middle. subst. run1done.

    - (* SLoop/again *)
      on hyp[(stmt_not_too_big body1); runsTo] do (fun H => rename H into IH1).
      on hyp[(stmt_not_too_big body2); runsTo] do (fun H => rename H into IH2).
      on hyp[(stmt_not_too_big (SLoop body1 cond body2)); runsTo] do (fun H => rename H into IH12).
      eapply runsTo_trans.
      + (* 1st application of IH: part 1 of loop body *)
        eapply IH1; IH_sidecondition.
      + simpl in *. simpl. intros. simp. destruct_RiscvMachine middle. subst.
        destruct (@eval_bcond (@Semantics_params p) middle_regs cond) as [condB|] eqn: E.
        2: exfalso;
           match goal with
           | H: context [_ <> None] |- _ => solve [eapply H; eauto]
           end.
        destruct condB.
        * (* true: iterate again *)
          eapply det_step; simpl in *; subst.
          { simulate'.
            destruct cond; [destruct op | ];
              simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity. }
          { eapply runsTo_trans.
            - (* 2nd application of IH: part 2 of loop body *)
              eapply IH2; IH_sidecondition.
            - simpl in *. simpl. intros. simp. destruct_RiscvMachine middle. subst.
              (* jump back to beginning of loop: *)
              run1det.
              eapply runsTo_trans.
              + (* 3rd application of IH: run the whole loop again *)
                eapply IH12; IH_sidecondition.
              + (* at end of loop, just prove that computed post satisfies required post *)
                simpl. intros. simp. destruct_RiscvMachine middle. subst.
                run1done. }
        * (* false: done, jump over body2 *)
          eapply det_step; simpl in *; subst.
          { simulate'.
            destruct cond; [destruct op | ];
              simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity. }
          { simpl in *. run1done. }

    - (* SSeq *)
      rename IHexec into IH1, H2 into IH2.
      eapply runsTo_trans.
      + eapply IH1; IH_sidecondition.
      + simpl. intros. simp. destruct_RiscvMachine middle. subst.
        eapply runsTo_trans.
        * eapply IH2; IH_sidecondition.
        * simpl. intros. simp. destruct_RiscvMachine middle. subst. run1done.

    - (* SSkip *)
      run1done.
  Qed.

End FlatToRiscv1.
