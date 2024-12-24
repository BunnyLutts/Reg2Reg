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
    | EmptySet_r => [nil]
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

(* Translate I.reg_exp to O.reg_exp *)
Fixpoint trans {T:Type} (r: I.reg_exp T): O.reg_exp T :=
    match r with
    | I.EmptySet_r => O.EmptyStr_r
    (* '' *)
    | I.EmptyStr_r => O.EmptyStr_r
    (* ?<r> *)
    | I.Optional_r r => O.Union_r (O.EmptyStr_r) (trans r)
    | I.Char_r t => O.Char_r t
    (* '<r1><r2>' *)
    | I.Concat_r r1 r2 => O.Concat_r (trans r1) (trans r2)
    (* '<r1>|<r2>' *)
    | I.Union_r r1 r2 => O.Union_r (trans r1) (trans r2)
    | I.String_r s => string2reg s
    (* '<r>+' *)
    | I.Plus_r r => O.Concat_r (trans r) (O.Star_r (trans r))
    (* '<r>*' *)
    | I.Star_r r => O.Star_r (trans r)
    end.

(* The proposition that the above trans maintains the equivalent semantics *)
Definition trans_correct_p {T} (r1 : I.reg_exp T): Prop :=
    forall (r2 : O.reg_exp T), r2 = trans r1 -> I.exp_match r1 = O.exp_match r2.

Lemma trans_EmptySet_correct: 
    forall {T} (r1 : I.reg_exp T),
        r1 = I.EmptySet_r -> trans_correct_p r1.
Proof.
    intros.
    unfold I.exp_match, O.exp_match, trans_correct_p.
    intros.
    unfold trans in H0.
    rewrite H in H0.
    rewrite H0.
    unfold O.exp_match, I.exp_match.
    rewrite H.
    reflexivity.
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
    rewrite H0.
    unfold O.exp_match, I.exp_match.
    rewrite H.
    reflexivity.
Qed.

Lemma trans_Optional_correct:
    forall {T : Type} (r1 : I.reg_exp T) (r0 : I.reg_exp T),
        r1 = I.Optional_r r0 -> trans_correct_p r0 -> trans_correct_p r1.
Proof.
Admitted.

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
    | O.Concat_r r' O.EmptyStr_r => reduce r'
    | O.Concat_r O.EmptyStr_r r' => reduce r'
    | O.EmptyStr_r => O.EmptyStr_r
    | O.Char_r t => O.Char_r t
    | O.Concat_r r1 r2 => O.Concat_r (reduce r1) (reduce r2)
    | O.Union_r r1 r2 => O.Union_r (reduce r1) (reduce r2)
    | O.Star_r r1 => O.Star_r (reduce r1)
    end.

(* The propostion that reduce maintains the equivalence of semantics. *)
Definition reduce_correct_p {T} (r : O.reg_exp T): Prop :=
    forall r1 : O.reg_exp T, r1 = (reduce r) -> O.exp_match r = O.exp_match r1.

(* 'EmptyStr r1' *)
Lemma reduce_left_empty_correct:
    forall {T:Type} (r r1 : O.reg_exp T),
        r = O.Concat_r O.EmptyStr_r r1 -> reduce_correct_p r1 -> reduce_correct_p r.
Proof.
Admitted.

(* 'r2 EmptyStr' *)
Lemma reduce_right_empty_correct:
    forall {T:Type} (r r1 : O.reg_exp T),
        r = O.Concat_r r1 O.EmptyStr_r -> reduce_correct_p r1 -> reduce_correct_p r.
Proof.
Admitted.

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

(* Simplicity of reduce. *)
Theorem reduce_simpl:
    forall {T} (r r0 : O.reg_exp T),
        r0 = (reduce r) -> simpl_p r0.
Proof.
induction r.
+ intros; rewrite H; simpl; tauto.
+ intros; rewrite H; simpl; tauto.
+ admit.
+ intros.
  rewrite H; simpl.
  split.
  * apply IHr1; reflexivity.
  * apply IHr2; reflexivity.
+ intros.
  rewrite H; simpl.
  apply IHr; reflexivity.
Admitted.

Theorem trans_reduce_correct: 
    forall {T} (r0 : I.reg_exp T),
        O.exp_match (reduce (trans r0)) = I.exp_match r0.
Proof.
    intros.
    pose proof reduce_correct (trans r0).
    unfold reduce_correct_p in H.
    specialize H with (reduce (trans r0)).
    pose proof H eq_refl.
    rewrite <- H0.
    pose proof trans_correct r0.
    unfold trans_correct_p in H1.
    pose proof H1 (trans r0) eq_refl.
    rewrite <- H2.
    reflexivity.
Qed.
