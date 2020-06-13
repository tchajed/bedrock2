From coqutil Require Import Decidable.
From coqutil Require Import Map.Interface Map.Properties.
Require Import bedrock2.Map.Separation.
Require Export bedrock2.Lift1Prop bedrock2.Map.SeparationLogic.
(* for this to work you'll need to opam install coq-iris from the Coq opam
repository *)
From iris Require Export proofmode.tactics.

(* need to provide an interpretation for this notation in default scope *)
Notation "'emp'" := Separation.emp : core_scope.

(* the proof mode emits this all the time *)
Global Set Warnings "-convert_concl_no_check".

Section mem.
  Context {key value} {mem : map.map key value} {mem_ok: map.ok mem}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
  (* this will the the carrier for the BI, meaning the proof mode will be able
  to prove properties about entailments (impl1) over this type (which is generic
  over the keys and values) *)
  Notation pred := (mem → Prop).

  Definition pred_iff_def (p1 p2: pred) := iff1 p1 p2.
  Definition pred_aux : seal (@pred_iff_def). by eexists. Qed.
  Definition pred_iff := unseal (@pred_aux).
  Definition pred_iff_eq : @pred_iff = @pred_iff_def := seal_eq pred_aux.

  Instance pred_equiv : Equiv pred := iff1.
  Instance pred_equivalence : Equivalence (≡@{pred}).
  Proof. firstorder. Qed.
  Canonical Structure predO := discreteO pred.

  (* pred_entails = impl1 *)
  (* pred_emp = emp *)

  Definition pred_pure (φ: Prop) : pred :=
    λ _, φ.
  Definition pred_or (p1 p2: pred) : pred :=
    λ m, p1 m ∨ p2 m.
  Definition pred_and (p1 p2: pred) : pred :=
    λ m, p1 m ∧ p2 m.
  Definition pred_impl (p1 p2: pred) : pred :=
    λ m, p1 m → p2 m.
  Definition pred_forall A (p: A → (pred)) : pred :=
    λ m, ∀ (x:A), p x m.
  Definition pred_persistently (p: pred) : pred :=
    λ m, p map.empty.
  Definition pred_wand (p1 p2: pred) : pred :=
    λ m, ∀ m1 m2, map.split m2 m m1 → p1 m1 → p2 m2.
  Definition pred_ex A (p: A → (pred)) : pred :=
    ex1 p.

  Theorem pred_wand_intro P Q R :
    impl1 (sep P Q) R →
    impl1 P (pred_wand Q R).
  Proof.
    rewrite /impl1 /sep /pred_wand; intros.
    apply H.
    eexists _, _; intuition eauto.
  Qed.

  Instance pred_wand_proper : Proper (iff1 ==> iff1 ==> iff1) pred_wand.
  Proof.
    intros p1 p2 HP q1 q2 HQ.
    rewrite /pred_wand.
    split; intros.
    - apply HP in H1.
      apply HQ.
      firstorder.
    - apply HP in H1.
      apply HQ.
      firstorder.
  Qed.

  Lemma pred_persistently_and_sep_elim (P Q: pred) :
    impl1 (pred_and (pred_persistently P) Q) (sep P Q).
  Proof.
    rewrite /impl1 /pred_and /pred_persistently /sep; intuition.
    exists map.empty, x; intuition.
    apply map.split_empty_l; auto.
  Qed.

  Hint Resolve pred_persistently_and_sep_elim : core.

  (* this proves all the core properties that our needed for the BI algebraic
  structure *)
  Lemma pred_bi_mixin :
    BiMixin (H0:=iff1) impl1 (Separation.emp True) pred_pure pred_and pred_or pred_impl pred_forall
            pred_ex sep pred_wand pred_persistently.
  Proof.
    split; intros; auto; try firstorder. (* almost everything is proven with firstorder *)
    - apply _.
    - rewrite sep_emp_True_l //.
    - rewrite sep_emp_True_l //.
    - rewrite sep_comm //.
    - rewrite sep_assoc //.
  Qed.

  Canonical Structure pred_bi : bi.
    refine {|
        bi_emp := Separation.emp True;
        bi_and := pred_and;
        bi_wand := pred_wand;
        bi_bi_mixin := pred_bi_mixin;
        bi_later := id;
      |}.
    eapply bi_later_mixin_id; eauto using pred_bi_mixin.
  Defined.

  Global Instance impl1_as_emp_valid (p q: pred) :
    AsEmpValid0 (impl1 p q) (bi_wand p q).
  Proof.
    apply _.
  Qed.

  Global Instance iff1_as_emp_valid (p q: pred) :
    AsEmpValid0 (iff1 p q) (bi_wand_iff p q).
  Proof.
    hnf.
    split; intros.
    - apply bi.equiv_wand_iff; auto.
    - apply bi.wand_iff_equiv in H; auto.
  Qed.

  Global Instance pred_iff_as_emp_valid (p q: pred) :
    AsEmpValid0 (pred_iff p q) (bi_wand_iff p q).
  Proof.
    rewrite pred_iff_eq /pred_iff_def.
    apply _.
  Qed.

  Theorem test1 (p q: pred) :
    iff1 p p.
  Proof.
    iSplit; auto.
  Qed.

  Theorem test2 (p q: pred) :
    p ∗ q -∗ q ∗ p.
  Proof.
    iIntros "[HP HQ]".
    iFrame.
  Qed.

End mem.

Import iris.proofmode.coq_tactics.
(* XXX: hack to check for iff1 before using impl *)
Ltac IntoEmpValid_go := first
  [ notypeclasses refine (into_emp_valid_here (iff1 _ _) _ _)
  | (* Case [φ → ψ] *)
  notypeclasses refine (into_emp_valid_impl _ _ _ _ _);
  [(*goal for [φ] *)|iIntoEmpValid_go]
  |(* Case [∀ x : A, φ] *)
  notypeclasses refine (into_emp_valid_forall _ _ _ _); iIntoEmpValid_go
  |(* Case [∀.. x : TT, φ] *)
  notypeclasses refine (into_emp_valid_tforall _ _ _ _); iIntoEmpValid_go
  | (* Case [P ⊢ Q], [P ⊣⊢ Q], [⊢ P] *)
  notypeclasses refine (into_emp_valid_here _ _ _)
  ].
Ltac proofmode.ltac_tactics.iIntoEmpValid_go ::= IntoEmpValid_go.
