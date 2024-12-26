Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import SetsClass.SetsClass.
Import SetsNotation.
Import ListNotations.
Local Open Scope sets_scope.

(*********************************************************)
(**                                                      *)
(** Output Regular Expression                            *)
(**                                                      *)
(*********************************************************)

Module O.

Inductive reg_exp (T: Type) : Type :=
  (* '' *)
  | EmptyStr_r
  (* 't' *)
  | Char_r (t : T -> Prop)
  (* '<r1><r2>' *)
  | Concat_r (r1 r2 : reg_exp T)
  (* '<r1>|<r2>' *)
  | Union_r (r1 r2 : reg_exp T)
  (* '<r>*' *)
  | Star_r (r : reg_exp T).

Arguments EmptyStr_r {T}.
Arguments Char_r {T} _.
Arguments Concat_r {T} _ _.
Arguments Union_r {T} _ _.
Arguments Star_r {T} _.


(* Concat two semantic.*)
Definition set_prod {T} (A B : list T -> Prop) : list T -> Prop :=
  fun s => exists s1 s2, s1 ∈ A /\ s2 ∈ B /\ s = s1 ++ s2.

Fixpoint star_r_indexed {T} (n : nat) (s : list T -> Prop) : list T -> Prop :=
  match n with
  | 0 => [ nil ]
  | S n' => set_prod s (star_r_indexed n' s)
  end.

(* Denote the semantics as 
    list T -> Prop : The strings that regexp accepts.
    Definition of the semantics of O.reg_exp *)
Fixpoint exp_match {T} (r : reg_exp T) : list T -> Prop :=
  match r with
  | EmptyStr_r => [ nil ]
  | Char_r t => fun s => exists c, c ∈ t /\ s = (cons c nil)
  | Concat_r r1 r2 => set_prod (exp_match r1) (exp_match r2)
  | Union_r r1 r2 => (exp_match r1) ∪ (exp_match r2)
  | Star_r r => ⋃ star_r_indexed (exp_match r)
  end.

End O.

(*********************************************************)
(**                                                      *)
(** Input Regular Expression                             *)
(**                                                      *)
(*********************************************************)

Module I.

Inductive reg_exp (T: Type) : Type :=
  | EmptySet_r
  (* '' *)
  | EmptyStr_r
  (* ?<r> *)
  | Optional_r (r : reg_exp T)
  | Char_r (t : T -> Prop)
  (* '<r1><r2>' *)
  | Concat_r (r1 r2 : reg_exp T)
  (* '<r1>|<r2>' *)
  | Union_r (r1 r2 : reg_exp T)
  | String_r (s: list T)
  (* '<r>+' *)
  | Plus_r (r : reg_exp T)
  (* '<r>*' *)
  | Star_r (r : reg_exp T).

Arguments EmptySet_r {T}.
Arguments EmptyStr_r {T}.
Arguments Optional_r {T} _.
Arguments Char_r {T} _.
Arguments Concat_r {T} _ _.
Arguments Union_r {T} _ _.
Arguments String_r {T} _.
Arguments Plus_r {T} _.
Arguments Star_r {T} _.

Fixpoint plus_r_indexed {T} (n : nat) (s : list T -> Prop) : list T -> Prop :=
  match n with
  | 0 => s
  | S n' => O.set_prod s (plus_r_indexed n' s)
  end.

(* Definition of the semantics of I.reg_exp. *)
Fixpoint exp_match {T} (r: reg_exp T) : list T -> Prop :=
    match r with
    | EmptySet_r => ∅
    | EmptyStr_r => [nil]
    | Optional_r r => [nil] ∪ (exp_match r)
    | Char_r t => fun s => exists c, c ∈ t /\ s = (cons c nil)
    | Concat_r r1 r2 => O.set_prod (exp_match r1) (exp_match r2)
    | Union_r r1 r2 => (exp_match r1) ∪ (exp_match r2)
    | String_r s => [s]
    | Plus_r r => ⋃ plus_r_indexed (exp_match r)
    | Star_r r => ⋃ O.star_r_indexed (exp_match r)
    end.

End I.

(* Translate a string into O.reg_exp *)
Fixpoint string2reg {T:Type} (s: list T): O.reg_exp T :=
    match s with
    | nil => O.EmptyStr_r
    | cons c s' => O.Concat_r (O.Char_r (fun x => x = c)) (string2reg s')
    end.

Inductive trans_result (T: Type) : Type :=
    | Empty
    | Data (r : O.reg_exp T).

Arguments Empty {T}.
Arguments Data {T} _.

Lemma trans_result_inj {T:Type} :
    forall (r1 r2: O.reg_exp T),
        Data r1 = Data r2 -> r1 = r2.
Proof.
intros.
injection H.
tauto.
Qed.

(* Translate I.reg_exp to O.reg_exp *)
Fixpoint trans {T:Type} (r: I.reg_exp T): trans_result T :=
    match r with
    | I.EmptySet_r => Empty
    (* '' *)
    | I.EmptyStr_r => Data O.EmptyStr_r
    (* ?<r> *)
    | I.Optional_r r => 
        match (trans r) with
        | Empty => Data (O.EmptyStr_r)
        | Data r' => Data (O.Union_r (O.EmptyStr_r) r')
        end
    | I.Char_r t => Data (O.Char_r t)
    (* '<r1><r2>' *)
    | I.Concat_r r1 r2 => 
        match (trans r1), (trans r2) with
        | Empty, Empty => Empty
        | Empty, Data r2' => Empty
        | Data r1', Empty => Empty
        | Data r1', Data r2' => Data (O.Concat_r r1' r2')
        end
    (* '<r1>|<r2>' *)
    | I.Union_r r1 r2 => 
        match (trans r1), (trans r2) with
        | Empty, Empty => Empty
        | Empty, Data r2' => Data r2'
        | Data r1', Empty => Data r1'
        | Data r1', Data r2' => Data (O.Union_r r1' r2')
        end
    | I.String_r s => Data (string2reg s)
    (* '<r>+' *)
    | I.Plus_r r => 
        match (trans r) with
        | Empty => Empty
        | Data r' => Data (O.Concat_r r' (O.Star_r r'))
        end
    (* '<r>*' *)
    | I.Star_r r => 
        match (trans r) with 
        | Empty => Data O.EmptyStr_r
        | Data r' => Data (O.Star_r r')
        end
    end.

Lemma trans_empty:
    forall {T} (r1 : I.reg_exp T),
        trans r1 = Empty -> I.exp_match r1 == ∅.
Proof.
Admitted.

(* The proposition that the above trans maintains the equivalent semantics *)
Definition trans_correct_p {T} (r1 : I.reg_exp T): Prop :=
    forall (r2 : O.reg_exp T), Data r2 = trans r1 -> I.exp_match r1 == O.exp_match r2.

Lemma trans_EmptySet_correct: 
    forall {T} (r1 : I.reg_exp T),
        r1 = I.EmptySet_r -> trans_correct_p r1.
Proof.
    intros.
    unfold I.exp_match, O.exp_match, trans_correct_p.
    intros.
    unfold trans in H0.
    rewrite H in H0.
    discriminate.
Qed.


Lemma trans_EmptyStr_correct: 
    forall {T : Type} (r1 : I.reg_exp T),
        r1 = I.EmptyStr_r -> trans_correct_p r1.
Proof.
    intros.
    unfold I.exp_match, O.exp_match, trans_correct_p.
    intros.
    unfold trans in H0.
    rewrite H in H0.
    apply trans_result_inj in H0.
    rewrite H0.
    unfold O.exp_match, I.exp_match.
    rewrite H.
    reflexivity.
Qed.

Lemma trans_Optional_correct:
    forall {T : Type} (r1 : I.reg_exp T) (r0 : I.reg_exp T),
        r1 = I.Optional_r r0 -> trans_correct_p r0 -> trans_correct_p r1.
Proof.
    intros.
    unfold I.exp_match, O.exp_match, trans_correct_p.
    unfold trans_correct_p in H0.
    intros r2' ?.
    remember (trans r0) as res.
    destruct res.
    + symmetry in Heqres.
      pose proof trans_empty r0 Heqres.
      rewrite H.
      simpl.
      rewrite H2.
      rewrite H in H1.
      simpl in H1.
      rewrite Heqres in H1.
      injection H1.
      intros.
      rewrite H3.
      simpl.
      rewrite Sets_union_empty_r.
      reflexivity.
    + 
    specialize (H0 r eq_refl).
    rewrite H in H1.
    simpl in H1.
    rewrite <- Heqres in H1.
    apply trans_result_inj in H1.
    rewrite H, H1.
    apply Sets_equiv_Sets_included in H0; destruct H0.
    apply Sets_equiv_Sets_included; simpl; split.
    * apply Sets_union_included.
      - apply Sets_included_union1.
      - rewrite H0.
        apply Sets_included_union2.
    * apply Sets_union_included.
      - apply Sets_included_union1.
      - rewrite H2.
        apply Sets_included_union2.
Qed.

Lemma trans_Char_correct:
    forall {T : Type} (r1 : I.reg_exp T) (t : T -> Prop),
        r1 = I.Char_r t -> trans_correct_p r1.
Proof.
Admitted.

Lemma trans_Concat_correct:
    forall {T : Type} (r r1 r2: I.reg_exp T),
        r = I.Concat_r r1 r2 -> trans_correct_p r1 -> trans_correct_p r2 -> trans_correct_p r.
Proof.
Admitted.

Lemma trans_Union_correct:
    forall {T : Type} (r r1 r2 : I.reg_exp T),
        r = I.Union_r r1 r2 -> trans_correct_p r1 -> trans_correct_p r2 -> trans_correct_p r.
Proof.
Admitted.

Lemma trans_String_correct:
    forall {T : Type} (r : I.reg_exp T) (s : list T),
        r = I.String_r s -> trans_correct_p r.
Proof.
Admitted.

Lemma trans_Plus_correct:
    forall {T : Type} (r r1 : I.reg_exp T),
        r = I.Plus_r r1 -> trans_correct_p r1 -> trans_correct_p r.
Proof.
Admitted.

Lemma trans_Star_correct:
    forall {T : Type} (r r1 : I.reg_exp T),
        r = I.Star_r r1 -> trans_correct_p r1 -> trans_correct_p r.
Proof.
Admitted.

(* The equivalence of the semantics between transfer. *)
Theorem trans_correct:
    forall {T} (r1 : I.reg_exp T), trans_correct_p r1.
Proof.
    intros.
    induction r1.
    + apply trans_EmptySet_correct; reflexivity.
    + apply trans_EmptyStr_correct; reflexivity.
    + pose proof trans_Optional_correct (I.Optional_r r1) r1 eq_refl IHr1; exact H.
    + pose proof trans_Char_correct (I.Char_r t) t eq_refl; exact H.
    + pose proof trans_Concat_correct (I.Concat_r r1_1 r1_2) r1_1 r1_2 eq_refl IHr1_1 IHr1_2; exact H.
    + pose proof trans_Union_correct (I.Union_r r1_1 r1_2) r1_1 r1_2 eq_refl IHr1_1 IHr1_2; exact H.
    + pose proof trans_String_correct (I.String_r s) s eq_refl; exact H.
    + pose proof trans_Plus_correct (I.Plus_r r1) r1 eq_refl IHr1; exact H.
    + pose proof trans_Star_correct (I.Star_r r1) r1 eq_refl IHr1; exact H.
Qed.

(* Remove all 'EmptyStr r1' and 'r2 EmptyStr' *)
Fixpoint reduce {T} (r : O.reg_exp T): (O.reg_exp T) :=
    match r with
    | O.EmptyStr_r => O.EmptyStr_r
    | O.Char_r t => O.Char_r t
    | O.Concat_r r1 r2 => 
        match (reduce r1), (reduce r2) with
        | O.EmptyStr_r, O.EmptyStr_r => O.EmptyStr_r
        | O.EmptyStr_r, _ => reduce r2
        | _, O.EmptyStr_r => reduce r1
        | _, _ => O.Concat_r (reduce r1) (reduce r2)
        end
    | O.Union_r r1 r2 => O.Union_r (reduce r1) (reduce r2)
    | O.Star_r r1 => O.Star_r (reduce r1)
    end.

(* The propostion that reduce maintains the equivalence of semantics. *)
Definition reduce_correct_p {T} (r : O.reg_exp T): Prop :=
    forall r1 : O.reg_exp T, r1 = (reduce r) -> O.exp_match r == O.exp_match r1.

Lemma transivity:
    forall {T} (A B C : list T -> Prop),
        A == B -> B == C -> A == C.
Proof.
intros.
rewrite H.
exact H0.
Qed.

(* 'EmptyStr r1' *)
Lemma reduce_left_empty_correct:
    forall {T:Type} (r r1 : O.reg_exp T),
        r = O.Concat_r O.EmptyStr_r r1 -> reduce_correct_p r1 -> reduce_correct_p r.
Proof.
unfold reduce_correct_p.
intros.
remember (reduce r1) as r1'.
pose proof H0 r1' eq_refl.
rewrite H.
rewrite H in H1.
rewrite H1.
simpl.
assert (forall {T} (t : list T -> Prop), O.set_prod [nil] t == t). {
    unfold O.set_prod.
    intros.
    Sets_unfold.
    intros.
    split.
    + intros.
      repeat destruct H3.
      destruct H4.
      rewrite app_nil_l in H4.
      rewrite H4; exact H3.
    + intros.
      exists nil, a.
      simpl.
      split; try tauto; try reflexivity.
}
specialize H3 with T (O.exp_match r1).
rewrite H3.
rewrite H2.
rewrite <- Heqr1'.
destruct r1'; try reflexivity.
Qed.

(* 'r2 EmptyStr' *)
Lemma reduce_right_empty_correct:
    forall {T:Type} (r r1 : O.reg_exp T),
        r = O.Concat_r r1 O.EmptyStr_r -> reduce_correct_p r1 -> reduce_correct_p r.
Proof.
unfold reduce_correct_p.
intros.
remember (reduce r1) as r1'.
pose proof H0 r1' eq_refl.
rewrite H.
rewrite H in H1.
rewrite H1.
simpl.
assert (forall {T} (t : list T -> Prop), O.set_prod t [nil] == t). {
    unfold O.set_prod.
    intros.
    Sets_unfold.
    intros.
    split.
    + intros.
      repeat destruct H3.
      destruct H4.
      destruct H4.
      rewrite app_nil_r in H5.
      rewrite H5; exact H3.
    + intros.
      exists a, nil.
      repeat split; try tauto; try reflexivity.
      rewrite app_nil_r; reflexivity.
}
specialize H3 with T (O.exp_match r1).
rewrite H3.
rewrite H2.
rewrite <- Heqr1'.
destruct r1'; try reflexivity.
Qed.

Lemma reduce_EmptyStr_correct:
    forall {T:Type} (r : O.reg_exp T),
        r = O.EmptyStr_r -> reduce_correct_p r.
Proof.
Admitted.

Lemma reduce_Char_correct:
    forall {T:Type} (r : O.reg_exp T) (t : T -> Prop),
        r = O.Char_r t -> reduce_correct_p r.
Proof.
Admitted.

Lemma reduce_Concat_correct:
    forall {T:Type} (r r1 r2 : O.reg_exp T),
        r = O.Concat_r r1 r2 -> reduce_correct_p r1 -> reduce_correct_p r2 -> reduce_correct_p r.
Proof.
Admitted.

Lemma reduce_Union_correct:
    forall {T:Type} (r r1 r2 : O.reg_exp T),
        r = O.Union_r r1 r2 -> reduce_correct_p r1 -> reduce_correct_p r2 -> reduce_correct_p r.
Proof.
Admitted.

Lemma reduce_Star_correct:
    forall {T:Type} (r r1 : O.reg_exp T),
        r = O.Star_r r1 -> reduce_correct_p r1 -> reduce_correct_p r.
Proof.
Admitted.

(* The equivalence of semantics before and after reduce *)
Theorem reduce_correct:
    forall {T} (r : O.reg_exp T),
        reduce_correct_p r.
Proof.
induction r.
+ apply reduce_EmptyStr_correct; reflexivity.
+ pose proof reduce_Char_correct (O.Char_r t) t eq_refl; exact H.
+ pose proof reduce_Concat_correct (O.Concat_r r1 r2) r1 r2 eq_refl IHr1 IHr2; exact H.
+ pose proof reduce_Union_correct (O.Union_r r1 r2) r1 r2 eq_refl IHr1 IHr2; exact H.
+ pose proof reduce_Star_correct (O.Star_r r) r eq_refl IHr; exact H.
Qed.

(* The proposition that reduce really reduced. *)
Fixpoint simpl_p {T} (r : O.reg_exp T) : Prop :=
    match r with
    | O.EmptyStr_r => True
    | O.Char_r t => True
    | O.Concat_r r1 r2 => r1 <> O.EmptyStr_r /\ simpl_p r1 /\ r2 <> O.EmptyStr_r /\ simpl_p r2
    | O.Union_r r1 r2 => simpl_p r1 /\ simpl_p r2
    | O.Star_r r => simpl_p r
    end.

Lemma reduce_Concat_simpl:
    forall {T} (r r1 r2 : O.reg_exp T),
        r = O.Concat_r r1 r2 -> simpl_p (reduce r1) -> simpl_p (reduce r2) -> simpl_p (reduce r).
Proof.
    intros.
    rewrite H; simpl.
    remember (reduce r1) as r1'.
    remember (reduce r2) as r2'.
    destruct r1', r2'; repeat tauto; simpl in *; simpl; repeat split; repeat tauto; repeat discriminate.
Qed.

(* Simplicity of reduce. *)
Theorem reduce_simpl:
    forall {T} (r r0 : O.reg_exp T),
        r0 = (reduce r) -> simpl_p r0.
Proof.
induction r.
+ intros; rewrite H; simpl; tauto.
+ intros; rewrite H; simpl; tauto.
+ (* Concat *)
  intros.
  pose proof reduce_Concat_simpl (O.Concat_r r1 r2) r1 r2 eq_refl (IHr1 (reduce r1) eq_refl) (IHr2 (reduce r2) eq_refl).
  rewrite H; exact H0.
+ intros.
  rewrite H; simpl.
  split.
  * apply IHr1; reflexivity.
  * apply IHr2; reflexivity.
+ intros.
  rewrite H; simpl.
  apply IHr; reflexivity.
Qed.

Theorem trans_reduce_correct: 
    forall {T} (r0: I.reg_exp T) (r1 : O.reg_exp T),
        Data r1 = trans r0 -> O.exp_match (reduce r1) == I.exp_match r0.
Proof.
    intros.
    pose proof reduce_correct r1.
    unfold reduce_correct_p in H.
    remember (trans r0) as res; destruct res; [discriminate|].
    injection H.
    intros.
    pose proof trans_correct r0.
    unfold trans_correct_p in H2.
    specialize H2 with r.
    apply H2 in Heqres as H3.
    rewrite H3.
    unfold reduce_correct_p in H0.
    specialize H0 with (reduce r1).
    rewrite H1.
    pose proof H0 eq_refl.
    rewrite H1 in H4. symmetry in H4.
    exact H4.
Qed.
