Require Import coqutil.Map.Interface coqutil.Map.Properties bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Semantics bedrock2.Array.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Map.Interface.
Require Import coqutil.Z.div_mod_to_equations.
Import HList List PrimitivePair.
Require Import Lia.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

(* TODO move *)
Local Unset Universe Polymorphism. (* for Add Ring *)
Module word.
  Section WordLemmas.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Add Ring wring: (@word.ring_theory width word word_ok).
    Lemma add_assoc: forall (x y z: word), word.add x (word.add y z) = word.add (word.add x y) z.
    Proof. intros. ring. Qed.
  End WordLemmas.
End word.
Set Universe Polymorphism.

Section Scalars.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {byte : Word.Interface.word 8} {byte_ok : word.ok byte}.

  Context {mem : map.map word byte} {mem_ok : map.ok mem}.

  Definition ptsto_bytes (n : nat) (addr : word) (value : tuple byte n) : mem -> Prop :=
    array ptsto (word.of_Z 1) addr (tuple.to_list value).

  Lemma load_bytes_of_sep a n bs R m
    (Hsep : sep (ptsto_bytes n a bs) R m)
    : Memory.load_bytes n m a = Some bs.
  Proof.
    cbv [load_bytes footprint].
    revert bs m R a Hsep.
    induction n; [solve[cbn; intros []; trivial]|].
    intros [b0 bs] m R a Hsep.
    cbn in Hsep; eapply SeparationLogic.sep_assoc in Hsep.
    cbn [map.getmany_of_tuple tuple.option_all tuple.map tuple.unfoldn].
    erewrite SeparationLogic.get_sep by exact Hsep.
    match goal with IH: _ |- _ => setoid_rewrite IH; [exact eq_refl|] end.
    unfold ptsto_bytes.
    SeparationLogic.ecancel_assumption.
  Qed.

  Arguments Z.of_nat: simpl never.

  Lemma invert_getmany_of_tuple_Some_footprint
    (n : nat) (a: word) (vs : tuple byte (S n)) (m : mem)
    (D: Z.of_nat n < 2 ^ width)
    (H: map.getmany_of_tuple m (footprint a (S n)) = Some vs):
    exists m', map.split m (map.put map.empty a (pair._1 vs)) m' /\
      map.getmany_of_tuple m' (footprint (word.add a (word.of_Z 1)) n) = Some (pair._2 vs).
  Proof.
    apply map.invert_getmany_of_tuple_Some in H. destruct H as [B1 B2].
    exists (map.remove m a).
    repeat split.
    - apply map.map_ext. intros k.
      pose proof (map.putmany_spec (map.put map.empty a (pair._1 vs)) (map.remove m a) k) as P.
      destruct P as [[v [A B]] | [A B]].
      + rewrite B.
        destruct (word.eqb a k) eqn: E.
        * apply word.eqb_true in E. subst k.
          rewrite map.get_remove_same in A. discriminate.
        * apply word.eqb_false in E.
          rewrite map.get_remove_diff in A by congruence. exact A.
      + rewrite B.
        destruct (word.eqb a k) eqn: E.
        * apply word.eqb_true in E. subst k.
          rewrite map.get_put_same. exact B1.
        * apply word.eqb_false in E.
          rewrite map.get_remove_diff in A by congruence.
          rewrite map.get_put_diff by congruence.
          rewrite map.get_empty. exact A.
    - unfold map.disjoint. intros k ? ? G1 G2.
      destruct (word.eqb a k) eqn: E.
        * apply word.eqb_true in E. subst k.
          rewrite map.get_remove_same in G2. discriminate.
        * apply word.eqb_false in E.
          rewrite map.get_put_diff in G1 by congruence.
          rewrite map.get_empty in G1. discriminate.
    - simpl in B2.
      clear -B2 mem_ok word_ok D. destruct vs as [v vs]. simpl in *.
      assert (0 < 1) as Y by lia.
      assert (1 + Z.of_nat n <= 2 ^ width)%Z as X by lia. clear D.
      revert Y X B2.
      generalize 1%Z as d.
      clear v.
      revert a vs.
      induction n; intros a vs d Y X B2; simpl in *.
      + destruct vs. reflexivity.
      + apply map.invert_getmany_of_tuple_Some in B2. simpl in B2. destruct B2 as [A B].
        destruct vs as [v vs]. simpl in *.
        apply map.build_getmany_of_tuple_Some; simpl.
        * rewrite map.get_remove_diff; [assumption|].
          clear -X Y word_ok.
          intro C.
          apply (f_equal word.unsigned) in C.
          rewrite word.unsigned_add in C.
          rewrite <- word.wrap_unsigned in C at 2.
          apply Z.sub_move_0_r in C.
          apply (f_equal (fun x => x mod (2 ^ width))) in C.
          change (0 mod 2 ^ width) with 0 in C.
          rewrite <- Zminus_mod in C.
          rewrite Z.add_simpl_l in C.
          rewrite word.unsigned_of_Z in C.
          rewrite Z.mod_mod in C by lia.
          apply Z.mod_divide in C; [|lia].
          unfold Z.divide in C.
          destruct C as [k C].
          subst d.
          assert (0 < 2 ^ width). {
            pose proof word.width_pos.
            apply Z.pow_pos_nonneg; lia.
          }
          assert (0 < k) by nia.
          nia.
        * match goal with IH: _ |- _ => specialize (IH a vs (d + 1)%Z); rename IH into IHn end.
          replace (word.add a (word.of_Z (d + 1)))
            with (word.add (word.add a (word.of_Z d)) (word.of_Z 1)) in IHn.
          { apply IHn; lia || assumption. }
          { rewrite (morph_add word.ring_morph). rewrite word.add_assoc. reflexivity. }
  Qed.

  Lemma sep_of_load_bytes_aux: forall (n: nat) (a: word) (bs: tuple byte n) (m: mem) (Q: mem -> Prop),
      Z.of_nat n <= 2 ^ width ->
      sep (fun m0 => Memory.load_bytes n m0 a = Some bs) Q m ->
      exists R, sep (ptsto_bytes n a bs) (sep R Q) m.
  Proof.
    cbv [load_bytes footprint]. unfold ptsto_bytes.
    intro n; induction n; intros.
    - cbv [ptsto_bytes array tuple.to_list].
      simpl in *. unfold map.getmany_of_tuple, tuple.option_all in *.
      match goal with
      | H: sep _ _ _ |- _ => destruct H as (mp & mq & A & B & C)
      end.
      exists (eq mp).
      apply sep_emp_l. split; auto.
      unfold sep. eauto.
    - match goal with
      | H: sep _ _ _ |- _ => destruct H as (mp & mq & A & B & C)
      end.
      apply invert_getmany_of_tuple_Some_footprint in B; [|lia].
      destruct B as (mo & B1 & B2).
      match goal with
      | x: tuple _ (S _) |- _ => destruct x as [b bs]; simpl in *
      end.

      Fail (* TODO ecancel_assumption why does it fail? *)
      match goal with
      | IHn: _ |- _ => edestruct IHn as [R IH]; [..|exists R; ecancel_assumption]
      end.

      Ltac ecancel_assumption_fix_just_for_here :=
        seplog;
        simple refine (cancel_seps_at_indices 0 1 _ _ _ _);
        cbn [List.firstn List.skipn List.app List.hd List.tl];
        [exact (RelationClasses.reflexivity _)|];
        ecancel.

      match goal with
      | IHn: _ |- _ => edestruct IHn as [R IH]; [..|exists R; ecancel_assumption_fix_just_for_here]
      end.
      + lia.
      + match goal with
        | |- sep ?BS (sep ?P ?Q) ?m => assert (sep (sep P BS) Q m); [|ecancel_assumption]
        end.
        unfold sep, ptsto, footprint in *. eauto 10.
  Qed.

  (* The side condition is actually needed: If n was bigger than 2^width,
     ptsto_bytes would star together the same address more than once. *)
  Lemma sep_of_load_bytes: forall (n: nat) (a: word) (bs: tuple byte n) (m: mem),
      Z.of_nat n <= 2 ^ width ->
      Memory.load_bytes n m a = Some bs ->
      exists R, sep (ptsto_bytes n a bs) R m.
  Proof.
    intros.
    edestruct sep_of_load_bytes_aux as [R P].
    - eassumption.
    - apply sep_comm. apply sep_emp_l. split; [apply I|eassumption].
    - exists R. ecancel_assumption.
  Qed.

  Lemma unchecked_store_bytes_of_sep(a: word)(n: nat)(oldbs bs: tuple byte n)(R: mem -> Prop)(m: mem)
    (Hsep : sep (ptsto_bytes n a oldbs) R m)
    : sep (ptsto_bytes n a bs) R (Memory.unchecked_store_bytes n m a bs).
  Proof.
    revert oldbs bs m R a Hsep.
    induction n; [solve[cbn; intros []; trivial]|].
    intros [oldb0 oldbs] [b0 bs] m R a Hsep.
    cbn in *.
    apply sep_assoc.
    eapply sep_put. 1: exact Properties.word.eq_or_neq.
    apply sep_assoc in Hsep.
    match goal with
    | IH: _ |- _ => unshelve epose proof (IH oldbs bs m _ (word.add a (word.of_Z 1)) _)
    end.
    - shelve.
    - unfold ptsto_bytes. ecancel_assumption.
    - seplog.
  Qed.

  Lemma unchecked_store_bytes_of_sep'
      (a: word)(n: nat)(bs1 bs2: tuple byte n)(R1 R2 F: mem -> Prop)(m: mem):
      R1 m ->
      iff1 R1 (sep (ptsto_bytes n a bs1) F) ->
      iff1 R2 (sep (ptsto_bytes n a bs2) F) ->
      R2 (Memory.unchecked_store_bytes n m a bs2).
  Proof.
    intros A B C.
    apply C.
    eapply unchecked_store_bytes_of_sep.
    apply B.
    assumption.
  Qed.

  Lemma store_bytes_of_sep(a: word)(n: nat)(oldbs bs: tuple byte n)(R post: mem -> Prop)(m: mem)
    (Hsep : sep (ptsto_bytes n a oldbs) R m)
    (Hpost : forall m, sep (ptsto_bytes n a bs) R m -> post m)
    : exists m1, Memory.store_bytes n m a bs = Some m1 /\ post m1.
  Proof.
    cbv [store_bytes]. erewrite load_bytes_of_sep; eauto using unchecked_store_bytes_of_sep.
  Qed.

End Scalars.
