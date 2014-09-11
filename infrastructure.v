Add LoadPath "../../provers/metalib/trunk".
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metatheory.
Require Export LibLNgen.

Require Export terms.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme B_ind' := Induction for B Sort Prop.

Definition B_mutind :=
  fun H1 H2 H3 =>
  B_ind' H1 H2 H3.

Scheme B_rec' := Induction for B Sort Set.

Definition B_mutrec :=
  fun H1 H2 H3 =>
  B_rec' H1 H2 H3.

Scheme k_ind' := Induction for k Sort Prop.

Definition k_mutind :=
  fun H1 H2 H3 H4 =>
  k_ind' H1 H2 H3 H4.

Scheme k_rec' := Induction for k Sort Set.

Definition k_mutrec :=
  fun H1 H2 H3 H4 =>
  k_rec' H1 H2 H3 H4.

Scheme b_ind' := Induction for b Sort Prop.

Definition b_mutind :=
  fun H1 H2 =>
  b_ind' H1 H2.

Scheme b_rec' := Induction for b Sort Set.

Definition b_mutrec :=
  fun H1 H2 =>
  b_rec' H1 H2.

Scheme s_ind' := Induction for s Sort Prop
  with SS_ind' := Induction for SS Sort Prop.

Definition s_SS_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  (conj (s_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)
  (SS_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)).

Scheme s_rec' := Induction for s Sort Set
  with SS_rec' := Induction for SS Sort Set.

Definition s_SS_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  (pair (s_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)
  (SS_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)).

Scheme F_ind' := Induction for F Sort Prop.

Definition F_mutind :=
  fun H1 H2 H3 H4 =>
  F_ind' H1 H2 H3 H4.

Scheme F_rec' := Induction for F Sort Set.

Definition F_mutrec :=
  fun H1 H2 H3 H4 =>
  F_rec' H1 H2 H3 H4.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_s_wrt_s_rec (n1 : nat) (x1 : x) (s1 : s) {struct s1} : s :=
  match s1 with
    | s_var_f x2 => if (x1 == x2) then (s_var_b n1) else (s_var_f x2)
    | s_var_b n2 => if (lt_ge_dec n2 n1) then (s_var_b n2) else (s_var_b (S n2))
    | s_const k1 => s_const k1
    | s_lam SS1 s2 => s_lam (close_SS_wrt_s_rec n1 x1 SS1) (close_s_wrt_s_rec (S n1) x1 s2)
    | s_app s2 s3 => s_app (close_s_wrt_s_rec n1 x1 s2) (close_s_wrt_s_rec n1 x1 s3)
    | s_blame b1 => s_blame b1
    | s_cast SS1 SS2 l1 => s_cast (close_SS_wrt_s_rec n1 x1 SS1) (close_SS_wrt_s_rec n1 x1 SS2) l1
    | s_check SS1 s2 k1 l1 => s_check (close_SS_wrt_s_rec n1 x1 SS1) (close_s_wrt_s_rec n1 x1 s2) k1 l1
  end

with close_SS_wrt_s_rec (n1 : nat) (x1 : x) (SS1 : SS) {struct SS1} : SS :=
  match SS1 with
    | SS_refinement B1 s1 => SS_refinement B1 (close_s_wrt_s_rec (S n1) x1 s1)
    | SS_darrow SS2 SS3 => SS_darrow (close_SS_wrt_s_rec n1 x1 SS2) (close_SS_wrt_s_rec (S n1) x1 SS3)
  end.

Definition close_s_wrt_s x1 s1 := close_s_wrt_s_rec 0 x1 s1.

Definition close_SS_wrt_s x1 SS1 := close_SS_wrt_s_rec 0 x1 SS1.

Fixpoint close_F_wrt_s_rec (n1 : nat) (x1 : x) (F1 : F) {struct F1} : F :=
  match F1 with
    | F_appl s1 => F_appl (close_s_wrt_s_rec n1 x1 s1)
    | F_appr s1 => F_appr (close_s_wrt_s_rec n1 x1 s1)
    | F_check SS1 k1 l1 => F_check (close_SS_wrt_s_rec n1 x1 SS1) k1 l1
  end.

Definition close_F_wrt_s x1 F1 := close_F_wrt_s_rec 0 x1 F1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_B (B1 : B) {struct B1} : nat :=
  match B1 with
    | B_bool => 1
    | B_others => 1
  end.

Fixpoint size_k (k1 : k) {struct k1} : nat :=
  match k1 with
    | k_true => 1
    | k_false => 1
    | k_others => 1
  end.

Fixpoint size_b (b1 : b) {struct b1} : nat :=
  match b1 with
    | b_blame l1 => 1
  end.

Fixpoint size_s (s1 : s) {struct s1} : nat :=
  match s1 with
    | s_var_f x1 => 1
    | s_var_b n1 => 1
    | s_const k1 => 1 + (size_k k1)
    | s_lam SS1 s2 => 1 + (size_SS SS1) + (size_s s2)
    | s_app s2 s3 => 1 + (size_s s2) + (size_s s3)
    | s_blame b1 => 1 + (size_b b1)
    | s_cast SS1 SS2 l1 => 1 + (size_SS SS1) + (size_SS SS2)
    | s_check SS1 s2 k1 l1 => 1 + (size_SS SS1) + (size_s s2) + (size_k k1)
  end

with size_SS (SS1 : SS) {struct SS1} : nat :=
  match SS1 with
    | SS_refinement B1 s1 => 1 + (size_B B1) + (size_s s1)
    | SS_darrow SS2 SS3 => 1 + (size_SS SS2) + (size_SS SS3)
  end.

Fixpoint size_F (F1 : F) {struct F1} : nat :=
  match F1 with
    | F_appl s1 => 1 + (size_s s1)
    | F_appr s1 => 1 + (size_s s1)
    | F_check SS1 k1 l1 => 1 + (size_SS SS1) + (size_k k1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_s_wrt_s : nat -> s -> Prop :=
  | degree_wrt_s_s_var_f : forall n1 x1,
    degree_s_wrt_s n1 (s_var_f x1)
  | degree_wrt_s_s_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_s_wrt_s n1 (s_var_b n2)
  | degree_wrt_s_s_const : forall n1 k1,
    degree_s_wrt_s n1 (s_const k1)
  | degree_wrt_s_s_lam : forall n1 SS1 s1,
    degree_SS_wrt_s n1 SS1 ->
    degree_s_wrt_s (S n1) s1 ->
    degree_s_wrt_s n1 (s_lam SS1 s1)
  | degree_wrt_s_s_app : forall n1 s1 s2,
    degree_s_wrt_s n1 s1 ->
    degree_s_wrt_s n1 s2 ->
    degree_s_wrt_s n1 (s_app s1 s2)
  | degree_wrt_s_s_blame : forall n1 b1,
    degree_s_wrt_s n1 (s_blame b1)
  | degree_wrt_s_s_cast : forall n1 SS1 SS2 l1,
    degree_SS_wrt_s n1 SS1 ->
    degree_SS_wrt_s n1 SS2 ->
    degree_s_wrt_s n1 (s_cast SS1 SS2 l1)
  | degree_wrt_s_s_check : forall n1 SS1 s1 k1 l1,
    degree_SS_wrt_s n1 SS1 ->
    degree_s_wrt_s n1 s1 ->
    degree_s_wrt_s n1 (s_check SS1 s1 k1 l1)

with degree_SS_wrt_s : nat -> SS -> Prop :=
  | degree_wrt_s_SS_refinement : forall n1 B1 s1,
    degree_s_wrt_s (S n1) s1 ->
    degree_SS_wrt_s n1 (SS_refinement B1 s1)
  | degree_wrt_s_SS_darrow : forall n1 SS1 SS2,
    degree_SS_wrt_s n1 SS1 ->
    degree_SS_wrt_s (S n1) SS2 ->
    degree_SS_wrt_s n1 (SS_darrow SS1 SS2).

Scheme degree_s_wrt_s_ind' := Induction for degree_s_wrt_s Sort Prop
  with degree_SS_wrt_s_ind' := Induction for degree_SS_wrt_s Sort Prop.

Definition degree_s_wrt_s_degree_SS_wrt_s_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  (conj (degree_s_wrt_s_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)
  (degree_SS_wrt_s_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)).

Hint Constructors degree_s_wrt_s : core lngen.

Hint Constructors degree_SS_wrt_s : core lngen.

Inductive degree_F_wrt_s : nat -> F -> Prop :=
  | degree_wrt_s_F_appl : forall n1 s1,
    degree_s_wrt_s n1 s1 ->
    degree_F_wrt_s n1 (F_appl s1)
  | degree_wrt_s_F_appr : forall n1 s1,
    degree_s_wrt_s n1 s1 ->
    degree_F_wrt_s n1 (F_appr s1)
  | degree_wrt_s_F_check : forall n1 SS1 k1 l1,
    degree_SS_wrt_s n1 SS1 ->
    degree_F_wrt_s n1 (F_check SS1 k1 l1).

Scheme degree_F_wrt_s_ind' := Induction for degree_F_wrt_s Sort Prop.

Definition degree_F_wrt_s_mutind :=
  fun H1 H2 H3 H4 =>
  degree_F_wrt_s_ind' H1 H2 H3 H4.

Hint Constructors degree_F_wrt_s : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_s : s -> Set :=
  | lc_set_s_var_f : forall x1,
    lc_set_s (s_var_f x1)
  | lc_set_s_const : forall k1,
    lc_set_s (s_const k1)
  | lc_set_s_lam : forall SS1 s1,
    lc_set_SS SS1 ->
    (forall x1 : x, lc_set_s (open_s_wrt_s s1 (s_var_f x1))) ->
    lc_set_s (s_lam SS1 s1)
  | lc_set_s_app : forall s1 s2,
    lc_set_s s1 ->
    lc_set_s s2 ->
    lc_set_s (s_app s1 s2)
  | lc_set_s_blame : forall b1,
    lc_set_s (s_blame b1)
  | lc_set_s_cast : forall SS1 SS2 l1,
    lc_set_SS SS1 ->
    lc_set_SS SS2 ->
    lc_set_s (s_cast SS1 SS2 l1)
  | lc_set_s_check : forall SS1 s1 k1 l1,
    lc_set_SS SS1 ->
    lc_set_s s1 ->
    lc_set_s (s_check SS1 s1 k1 l1)

with lc_set_SS : SS -> Set :=
  | lc_set_SS_refinement : forall B1 s1,
    (forall x1 : x, lc_set_s (open_s_wrt_s s1 (s_var_f x1))) ->
    lc_set_SS (SS_refinement B1 s1)
  | lc_set_SS_darrow : forall SS1 SS2,
    lc_set_SS SS1 ->
    (forall x1 : x, lc_set_SS (open_SS_wrt_s SS2 (s_var_f x1))) ->
    lc_set_SS (SS_darrow SS1 SS2).

Scheme lc_s_ind' := Induction for lc_s Sort Prop
  with lc_SS_ind' := Induction for lc_SS Sort Prop.

Definition lc_s_lc_SS_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (conj (lc_s_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (lc_SS_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Scheme lc_set_s_ind' := Induction for lc_set_s Sort Prop
  with lc_set_SS_ind' := Induction for lc_set_SS Sort Prop.

Definition lc_set_s_lc_set_SS_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (conj (lc_set_s_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (lc_set_SS_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Scheme lc_set_s_rec' := Induction for lc_set_s Sort Set
  with lc_set_SS_rec' := Induction for lc_set_SS Sort Set.

Definition lc_set_s_lc_set_SS_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (pair (lc_set_s_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (lc_set_SS_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Hint Constructors lc_s : core lngen.

Hint Constructors lc_SS : core lngen.

Hint Constructors lc_set_s : core lngen.

Hint Constructors lc_set_SS : core lngen.

Inductive lc_set_F : F -> Set :=
  | lc_set_F_appl : forall s1,
    lc_set_s s1 ->
    lc_set_F (F_appl s1)
  | lc_set_F_appr : forall s1,
    lc_set_s s1 ->
    lc_set_F (F_appr s1)
  | lc_set_F_check : forall SS1 k1 l1,
    lc_set_SS SS1 ->
    lc_set_F (F_check SS1 k1 l1).

Scheme lc_F_ind' := Induction for lc_F Sort Prop.

Definition lc_F_mutind :=
  fun H1 H2 H3 H4 =>
  lc_F_ind' H1 H2 H3 H4.

Scheme lc_set_F_ind' := Induction for lc_set_F Sort Prop.

Definition lc_set_F_mutind :=
  fun H1 H2 H3 H4 =>
  lc_set_F_ind' H1 H2 H3 H4.

Scheme lc_set_F_rec' := Induction for lc_set_F Sort Set.

Definition lc_set_F_mutrec :=
  fun H1 H2 H3 H4 =>
  lc_set_F_rec' H1 H2 H3 H4.

Hint Constructors lc_F : core lngen.

Hint Constructors lc_set_F : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_s_wrt_s s1 := forall x1, lc_s (open_s_wrt_s s1 (s_var_f x1)).

Definition body_SS_wrt_s SS1 := forall x1, lc_SS (open_SS_wrt_s SS1 (s_var_f x1)).

Hint Unfold body_s_wrt_s.

Hint Unfold body_SS_wrt_s.

Definition body_F_wrt_s F1 := forall x1, lc_F (open_F_wrt_s F1 (s_var_f x1)).

Hint Unfold body_F_wrt_s.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_B_min_mutual :
(forall B1, 1 <= size_B B1).
Proof.
apply_mutual_ind B_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_B_min :
forall B1, 1 <= size_B B1.
Proof.
pose proof size_B_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_B_min : lngen.

(* begin hide *)

Lemma size_k_min_mutual :
(forall k1, 1 <= size_k k1).
Proof.
apply_mutual_ind k_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_k_min :
forall k1, 1 <= size_k k1.
Proof.
pose proof size_k_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_k_min : lngen.

(* begin hide *)

Lemma size_b_min_mutual :
(forall b1, 1 <= size_b b1).
Proof.
apply_mutual_ind b_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_b_min :
forall b1, 1 <= size_b b1.
Proof.
pose proof size_b_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_b_min : lngen.

(* begin hide *)

Lemma size_s_min_size_SS_min_mutual :
(forall s1, 1 <= size_s s1) /\
(forall SS1, 1 <= size_SS SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_s_min :
forall s1, 1 <= size_s s1.
Proof.
pose proof size_s_min_size_SS_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_s_min : lngen.

Lemma size_SS_min :
forall SS1, 1 <= size_SS SS1.
Proof.
pose proof size_s_min_size_SS_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_SS_min : lngen.

(* begin hide *)

Lemma size_F_min_mutual :
(forall F1, 1 <= size_F F1).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_F_min :
forall F1, 1 <= size_F F1.
Proof.
pose proof size_F_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_F_min : lngen.

(* begin hide *)

Lemma size_s_close_s_wrt_s_rec_size_SS_close_SS_wrt_s_rec_mutual :
(forall s1 x1 n1,
  size_s (close_s_wrt_s_rec n1 x1 s1) = size_s s1) /\
(forall SS1 x1 n1,
  size_SS (close_SS_wrt_s_rec n1 x1 SS1) = size_SS SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_s_close_s_wrt_s_rec :
forall s1 x1 n1,
  size_s (close_s_wrt_s_rec n1 x1 s1) = size_s s1.
Proof.
pose proof size_s_close_s_wrt_s_rec_size_SS_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_s_close_s_wrt_s_rec : lngen.
Hint Rewrite size_s_close_s_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_SS_close_SS_wrt_s_rec :
forall SS1 x1 n1,
  size_SS (close_SS_wrt_s_rec n1 x1 SS1) = size_SS SS1.
Proof.
pose proof size_s_close_s_wrt_s_rec_size_SS_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_SS_close_SS_wrt_s_rec : lngen.
Hint Rewrite size_SS_close_SS_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_F_close_F_wrt_s_rec_mutual :
(forall F1 x1 n1,
  size_F (close_F_wrt_s_rec n1 x1 F1) = size_F F1).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_F_close_F_wrt_s_rec :
forall F1 x1 n1,
  size_F (close_F_wrt_s_rec n1 x1 F1) = size_F F1.
Proof.
pose proof size_F_close_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_F_close_F_wrt_s_rec : lngen.
Hint Rewrite size_F_close_F_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_s_close_s_wrt_s :
forall s1 x1,
  size_s (close_s_wrt_s x1 s1) = size_s s1.
Proof.
unfold close_s_wrt_s; default_simp.
Qed.

Hint Resolve size_s_close_s_wrt_s : lngen.
Hint Rewrite size_s_close_s_wrt_s using solve [auto] : lngen.

Lemma size_SS_close_SS_wrt_s :
forall SS1 x1,
  size_SS (close_SS_wrt_s x1 SS1) = size_SS SS1.
Proof.
unfold close_SS_wrt_s; default_simp.
Qed.

Hint Resolve size_SS_close_SS_wrt_s : lngen.
Hint Rewrite size_SS_close_SS_wrt_s using solve [auto] : lngen.

Lemma size_F_close_F_wrt_s :
forall F1 x1,
  size_F (close_F_wrt_s x1 F1) = size_F F1.
Proof.
unfold close_F_wrt_s; default_simp.
Qed.

Hint Resolve size_F_close_F_wrt_s : lngen.
Hint Rewrite size_F_close_F_wrt_s using solve [auto] : lngen.

(* begin hide *)

Lemma size_s_open_s_wrt_s_rec_size_SS_open_SS_wrt_s_rec_mutual :
(forall s1 s2 n1,
  size_s s1 <= size_s (open_s_wrt_s_rec n1 s2 s1)) /\
(forall SS1 s1 n1,
  size_SS SS1 <= size_SS (open_SS_wrt_s_rec n1 s1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_s_open_s_wrt_s_rec :
forall s1 s2 n1,
  size_s s1 <= size_s (open_s_wrt_s_rec n1 s2 s1).
Proof.
pose proof size_s_open_s_wrt_s_rec_size_SS_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_s_open_s_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_SS_open_SS_wrt_s_rec :
forall SS1 s1 n1,
  size_SS SS1 <= size_SS (open_SS_wrt_s_rec n1 s1 SS1).
Proof.
pose proof size_s_open_s_wrt_s_rec_size_SS_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_SS_open_SS_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_F_open_F_wrt_s_rec_mutual :
(forall F1 s1 n1,
  size_F F1 <= size_F (open_F_wrt_s_rec n1 s1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_F_open_F_wrt_s_rec :
forall F1 s1 n1,
  size_F F1 <= size_F (open_F_wrt_s_rec n1 s1 F1).
Proof.
pose proof size_F_open_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_F_open_F_wrt_s_rec : lngen.

(* end hide *)

Lemma size_s_open_s_wrt_s :
forall s1 s2,
  size_s s1 <= size_s (open_s_wrt_s s1 s2).
Proof.
unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve size_s_open_s_wrt_s : lngen.

Lemma size_SS_open_SS_wrt_s :
forall SS1 s1,
  size_SS SS1 <= size_SS (open_SS_wrt_s SS1 s1).
Proof.
unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve size_SS_open_SS_wrt_s : lngen.

Lemma size_F_open_F_wrt_s :
forall F1 s1,
  size_F F1 <= size_F (open_F_wrt_s F1 s1).
Proof.
unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve size_F_open_F_wrt_s : lngen.

(* begin hide *)

Lemma size_s_open_s_wrt_s_rec_var_size_SS_open_SS_wrt_s_rec_var_mutual :
(forall s1 x1 n1,
  size_s (open_s_wrt_s_rec n1 (s_var_f x1) s1) = size_s s1) /\
(forall SS1 x1 n1,
  size_SS (open_SS_wrt_s_rec n1 (s_var_f x1) SS1) = size_SS SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_s_open_s_wrt_s_rec_var :
forall s1 x1 n1,
  size_s (open_s_wrt_s_rec n1 (s_var_f x1) s1) = size_s s1.
Proof.
pose proof size_s_open_s_wrt_s_rec_var_size_SS_open_SS_wrt_s_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_s_open_s_wrt_s_rec_var : lngen.
Hint Rewrite size_s_open_s_wrt_s_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_SS_open_SS_wrt_s_rec_var :
forall SS1 x1 n1,
  size_SS (open_SS_wrt_s_rec n1 (s_var_f x1) SS1) = size_SS SS1.
Proof.
pose proof size_s_open_s_wrt_s_rec_var_size_SS_open_SS_wrt_s_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_SS_open_SS_wrt_s_rec_var : lngen.
Hint Rewrite size_SS_open_SS_wrt_s_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_F_open_F_wrt_s_rec_var_mutual :
(forall F1 x1 n1,
  size_F (open_F_wrt_s_rec n1 (s_var_f x1) F1) = size_F F1).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_F_open_F_wrt_s_rec_var :
forall F1 x1 n1,
  size_F (open_F_wrt_s_rec n1 (s_var_f x1) F1) = size_F F1.
Proof.
pose proof size_F_open_F_wrt_s_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_F_open_F_wrt_s_rec_var : lngen.
Hint Rewrite size_F_open_F_wrt_s_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_s_open_s_wrt_s_var :
forall s1 x1,
  size_s (open_s_wrt_s s1 (s_var_f x1)) = size_s s1.
Proof.
unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve size_s_open_s_wrt_s_var : lngen.
Hint Rewrite size_s_open_s_wrt_s_var using solve [auto] : lngen.

Lemma size_SS_open_SS_wrt_s_var :
forall SS1 x1,
  size_SS (open_SS_wrt_s SS1 (s_var_f x1)) = size_SS SS1.
Proof.
unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve size_SS_open_SS_wrt_s_var : lngen.
Hint Rewrite size_SS_open_SS_wrt_s_var using solve [auto] : lngen.

Lemma size_F_open_F_wrt_s_var :
forall F1 x1,
  size_F (open_F_wrt_s F1 (s_var_f x1)) = size_F F1.
Proof.
unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve size_F_open_F_wrt_s_var : lngen.
Hint Rewrite size_F_open_F_wrt_s_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_s_wrt_s_S_degree_SS_wrt_s_S_mutual :
(forall n1 s1,
  degree_s_wrt_s n1 s1 ->
  degree_s_wrt_s (S n1) s1) /\
(forall n1 SS1,
  degree_SS_wrt_s n1 SS1 ->
  degree_SS_wrt_s (S n1) SS1).
Proof.
apply_mutual_ind degree_s_wrt_s_degree_SS_wrt_s_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_s_wrt_s_S :
forall n1 s1,
  degree_s_wrt_s n1 s1 ->
  degree_s_wrt_s (S n1) s1.
Proof.
pose proof degree_s_wrt_s_S_degree_SS_wrt_s_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_s_wrt_s_S : lngen.

Lemma degree_SS_wrt_s_S :
forall n1 SS1,
  degree_SS_wrt_s n1 SS1 ->
  degree_SS_wrt_s (S n1) SS1.
Proof.
pose proof degree_s_wrt_s_S_degree_SS_wrt_s_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_SS_wrt_s_S : lngen.

(* begin hide *)

Lemma degree_F_wrt_s_S_mutual :
(forall n1 F1,
  degree_F_wrt_s n1 F1 ->
  degree_F_wrt_s (S n1) F1).
Proof.
apply_mutual_ind degree_F_wrt_s_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_F_wrt_s_S :
forall n1 F1,
  degree_F_wrt_s n1 F1 ->
  degree_F_wrt_s (S n1) F1.
Proof.
pose proof degree_F_wrt_s_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_F_wrt_s_S : lngen.

Lemma degree_s_wrt_s_O :
forall n1 s1,
  degree_s_wrt_s O s1 ->
  degree_s_wrt_s n1 s1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_s_wrt_s_O : lngen.

Lemma degree_SS_wrt_s_O :
forall n1 SS1,
  degree_SS_wrt_s O SS1 ->
  degree_SS_wrt_s n1 SS1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_SS_wrt_s_O : lngen.

Lemma degree_F_wrt_s_O :
forall n1 F1,
  degree_F_wrt_s O F1 ->
  degree_F_wrt_s n1 F1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_F_wrt_s_O : lngen.

(* begin hide *)

Lemma degree_s_wrt_s_close_s_wrt_s_rec_degree_SS_wrt_s_close_SS_wrt_s_rec_mutual :
(forall s1 x1 n1,
  degree_s_wrt_s n1 s1 ->
  degree_s_wrt_s (S n1) (close_s_wrt_s_rec n1 x1 s1)) /\
(forall SS1 x1 n1,
  degree_SS_wrt_s n1 SS1 ->
  degree_SS_wrt_s (S n1) (close_SS_wrt_s_rec n1 x1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_s_wrt_s_close_s_wrt_s_rec :
forall s1 x1 n1,
  degree_s_wrt_s n1 s1 ->
  degree_s_wrt_s (S n1) (close_s_wrt_s_rec n1 x1 s1).
Proof.
pose proof degree_s_wrt_s_close_s_wrt_s_rec_degree_SS_wrt_s_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_s_wrt_s_close_s_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_SS_wrt_s_close_SS_wrt_s_rec :
forall SS1 x1 n1,
  degree_SS_wrt_s n1 SS1 ->
  degree_SS_wrt_s (S n1) (close_SS_wrt_s_rec n1 x1 SS1).
Proof.
pose proof degree_s_wrt_s_close_s_wrt_s_rec_degree_SS_wrt_s_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_SS_wrt_s_close_SS_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_F_wrt_s_close_F_wrt_s_rec_mutual :
(forall F1 x1 n1,
  degree_F_wrt_s n1 F1 ->
  degree_F_wrt_s (S n1) (close_F_wrt_s_rec n1 x1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_F_wrt_s_close_F_wrt_s_rec :
forall F1 x1 n1,
  degree_F_wrt_s n1 F1 ->
  degree_F_wrt_s (S n1) (close_F_wrt_s_rec n1 x1 F1).
Proof.
pose proof degree_F_wrt_s_close_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_F_wrt_s_close_F_wrt_s_rec : lngen.

(* end hide *)

Lemma degree_s_wrt_s_close_s_wrt_s :
forall s1 x1,
  degree_s_wrt_s 0 s1 ->
  degree_s_wrt_s 1 (close_s_wrt_s x1 s1).
Proof.
unfold close_s_wrt_s; default_simp.
Qed.

Hint Resolve degree_s_wrt_s_close_s_wrt_s : lngen.

Lemma degree_SS_wrt_s_close_SS_wrt_s :
forall SS1 x1,
  degree_SS_wrt_s 0 SS1 ->
  degree_SS_wrt_s 1 (close_SS_wrt_s x1 SS1).
Proof.
unfold close_SS_wrt_s; default_simp.
Qed.

Hint Resolve degree_SS_wrt_s_close_SS_wrt_s : lngen.

Lemma degree_F_wrt_s_close_F_wrt_s :
forall F1 x1,
  degree_F_wrt_s 0 F1 ->
  degree_F_wrt_s 1 (close_F_wrt_s x1 F1).
Proof.
unfold close_F_wrt_s; default_simp.
Qed.

Hint Resolve degree_F_wrt_s_close_F_wrt_s : lngen.

(* begin hide *)

Lemma degree_s_wrt_s_close_s_wrt_s_rec_inv_degree_SS_wrt_s_close_SS_wrt_s_rec_inv_mutual :
(forall s1 x1 n1,
  degree_s_wrt_s (S n1) (close_s_wrt_s_rec n1 x1 s1) ->
  degree_s_wrt_s n1 s1) /\
(forall SS1 x1 n1,
  degree_SS_wrt_s (S n1) (close_SS_wrt_s_rec n1 x1 SS1) ->
  degree_SS_wrt_s n1 SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_s_wrt_s_close_s_wrt_s_rec_inv :
forall s1 x1 n1,
  degree_s_wrt_s (S n1) (close_s_wrt_s_rec n1 x1 s1) ->
  degree_s_wrt_s n1 s1.
Proof.
pose proof degree_s_wrt_s_close_s_wrt_s_rec_inv_degree_SS_wrt_s_close_SS_wrt_s_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_s_wrt_s_close_s_wrt_s_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_SS_wrt_s_close_SS_wrt_s_rec_inv :
forall SS1 x1 n1,
  degree_SS_wrt_s (S n1) (close_SS_wrt_s_rec n1 x1 SS1) ->
  degree_SS_wrt_s n1 SS1.
Proof.
pose proof degree_s_wrt_s_close_s_wrt_s_rec_inv_degree_SS_wrt_s_close_SS_wrt_s_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_SS_wrt_s_close_SS_wrt_s_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_F_wrt_s_close_F_wrt_s_rec_inv_mutual :
(forall F1 x1 n1,
  degree_F_wrt_s (S n1) (close_F_wrt_s_rec n1 x1 F1) ->
  degree_F_wrt_s n1 F1).
Proof.
apply_mutual_ind F_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_F_wrt_s_close_F_wrt_s_rec_inv :
forall F1 x1 n1,
  degree_F_wrt_s (S n1) (close_F_wrt_s_rec n1 x1 F1) ->
  degree_F_wrt_s n1 F1.
Proof.
pose proof degree_F_wrt_s_close_F_wrt_s_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_F_wrt_s_close_F_wrt_s_rec_inv : lngen.

(* end hide *)

Lemma degree_s_wrt_s_close_s_wrt_s_inv :
forall s1 x1,
  degree_s_wrt_s 1 (close_s_wrt_s x1 s1) ->
  degree_s_wrt_s 0 s1.
Proof.
unfold close_s_wrt_s; eauto with lngen.
Qed.

Hint Immediate degree_s_wrt_s_close_s_wrt_s_inv : lngen.

Lemma degree_SS_wrt_s_close_SS_wrt_s_inv :
forall SS1 x1,
  degree_SS_wrt_s 1 (close_SS_wrt_s x1 SS1) ->
  degree_SS_wrt_s 0 SS1.
Proof.
unfold close_SS_wrt_s; eauto with lngen.
Qed.

Hint Immediate degree_SS_wrt_s_close_SS_wrt_s_inv : lngen.

Lemma degree_F_wrt_s_close_F_wrt_s_inv :
forall F1 x1,
  degree_F_wrt_s 1 (close_F_wrt_s x1 F1) ->
  degree_F_wrt_s 0 F1.
Proof.
unfold close_F_wrt_s; eauto with lngen.
Qed.

Hint Immediate degree_F_wrt_s_close_F_wrt_s_inv : lngen.

(* begin hide *)

Lemma degree_s_wrt_s_open_s_wrt_s_rec_degree_SS_wrt_s_open_SS_wrt_s_rec_mutual :
(forall s1 s2 n1,
  degree_s_wrt_s (S n1) s1 ->
  degree_s_wrt_s n1 s2 ->
  degree_s_wrt_s n1 (open_s_wrt_s_rec n1 s2 s1)) /\
(forall SS1 s1 n1,
  degree_SS_wrt_s (S n1) SS1 ->
  degree_s_wrt_s n1 s1 ->
  degree_SS_wrt_s n1 (open_SS_wrt_s_rec n1 s1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_s_wrt_s_open_s_wrt_s_rec :
forall s1 s2 n1,
  degree_s_wrt_s (S n1) s1 ->
  degree_s_wrt_s n1 s2 ->
  degree_s_wrt_s n1 (open_s_wrt_s_rec n1 s2 s1).
Proof.
pose proof degree_s_wrt_s_open_s_wrt_s_rec_degree_SS_wrt_s_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_s_wrt_s_open_s_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_SS_wrt_s_open_SS_wrt_s_rec :
forall SS1 s1 n1,
  degree_SS_wrt_s (S n1) SS1 ->
  degree_s_wrt_s n1 s1 ->
  degree_SS_wrt_s n1 (open_SS_wrt_s_rec n1 s1 SS1).
Proof.
pose proof degree_s_wrt_s_open_s_wrt_s_rec_degree_SS_wrt_s_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_SS_wrt_s_open_SS_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_F_wrt_s_open_F_wrt_s_rec_mutual :
(forall F1 s1 n1,
  degree_F_wrt_s (S n1) F1 ->
  degree_s_wrt_s n1 s1 ->
  degree_F_wrt_s n1 (open_F_wrt_s_rec n1 s1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_F_wrt_s_open_F_wrt_s_rec :
forall F1 s1 n1,
  degree_F_wrt_s (S n1) F1 ->
  degree_s_wrt_s n1 s1 ->
  degree_F_wrt_s n1 (open_F_wrt_s_rec n1 s1 F1).
Proof.
pose proof degree_F_wrt_s_open_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_F_wrt_s_open_F_wrt_s_rec : lngen.

(* end hide *)

Lemma degree_s_wrt_s_open_s_wrt_s :
forall s1 s2,
  degree_s_wrt_s 1 s1 ->
  degree_s_wrt_s 0 s2 ->
  degree_s_wrt_s 0 (open_s_wrt_s s1 s2).
Proof.
unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve degree_s_wrt_s_open_s_wrt_s : lngen.

Lemma degree_SS_wrt_s_open_SS_wrt_s :
forall SS1 s1,
  degree_SS_wrt_s 1 SS1 ->
  degree_s_wrt_s 0 s1 ->
  degree_SS_wrt_s 0 (open_SS_wrt_s SS1 s1).
Proof.
unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve degree_SS_wrt_s_open_SS_wrt_s : lngen.

Lemma degree_F_wrt_s_open_F_wrt_s :
forall F1 s1,
  degree_F_wrt_s 1 F1 ->
  degree_s_wrt_s 0 s1 ->
  degree_F_wrt_s 0 (open_F_wrt_s F1 s1).
Proof.
unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve degree_F_wrt_s_open_F_wrt_s : lngen.

(* begin hide *)

Lemma degree_s_wrt_s_open_s_wrt_s_rec_inv_degree_SS_wrt_s_open_SS_wrt_s_rec_inv_mutual :
(forall s1 s2 n1,
  degree_s_wrt_s n1 (open_s_wrt_s_rec n1 s2 s1) ->
  degree_s_wrt_s (S n1) s1) /\
(forall SS1 s1 n1,
  degree_SS_wrt_s n1 (open_SS_wrt_s_rec n1 s1 SS1) ->
  degree_SS_wrt_s (S n1) SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_s_wrt_s_open_s_wrt_s_rec_inv :
forall s1 s2 n1,
  degree_s_wrt_s n1 (open_s_wrt_s_rec n1 s2 s1) ->
  degree_s_wrt_s (S n1) s1.
Proof.
pose proof degree_s_wrt_s_open_s_wrt_s_rec_inv_degree_SS_wrt_s_open_SS_wrt_s_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_s_wrt_s_open_s_wrt_s_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_SS_wrt_s_open_SS_wrt_s_rec_inv :
forall SS1 s1 n1,
  degree_SS_wrt_s n1 (open_SS_wrt_s_rec n1 s1 SS1) ->
  degree_SS_wrt_s (S n1) SS1.
Proof.
pose proof degree_s_wrt_s_open_s_wrt_s_rec_inv_degree_SS_wrt_s_open_SS_wrt_s_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_SS_wrt_s_open_SS_wrt_s_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_F_wrt_s_open_F_wrt_s_rec_inv_mutual :
(forall F1 s1 n1,
  degree_F_wrt_s n1 (open_F_wrt_s_rec n1 s1 F1) ->
  degree_F_wrt_s (S n1) F1).
Proof.
apply_mutual_ind F_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_F_wrt_s_open_F_wrt_s_rec_inv :
forall F1 s1 n1,
  degree_F_wrt_s n1 (open_F_wrt_s_rec n1 s1 F1) ->
  degree_F_wrt_s (S n1) F1.
Proof.
pose proof degree_F_wrt_s_open_F_wrt_s_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_F_wrt_s_open_F_wrt_s_rec_inv : lngen.

(* end hide *)

Lemma degree_s_wrt_s_open_s_wrt_s_inv :
forall s1 s2,
  degree_s_wrt_s 0 (open_s_wrt_s s1 s2) ->
  degree_s_wrt_s 1 s1.
Proof.
unfold open_s_wrt_s; eauto with lngen.
Qed.

Hint Immediate degree_s_wrt_s_open_s_wrt_s_inv : lngen.

Lemma degree_SS_wrt_s_open_SS_wrt_s_inv :
forall SS1 s1,
  degree_SS_wrt_s 0 (open_SS_wrt_s SS1 s1) ->
  degree_SS_wrt_s 1 SS1.
Proof.
unfold open_SS_wrt_s; eauto with lngen.
Qed.

Hint Immediate degree_SS_wrt_s_open_SS_wrt_s_inv : lngen.

Lemma degree_F_wrt_s_open_F_wrt_s_inv :
forall F1 s1,
  degree_F_wrt_s 0 (open_F_wrt_s F1 s1) ->
  degree_F_wrt_s 1 F1.
Proof.
unfold open_F_wrt_s; eauto with lngen.
Qed.

Hint Immediate degree_F_wrt_s_open_F_wrt_s_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_s_wrt_s_rec_inj_close_SS_wrt_s_rec_inj_mutual :
(forall s1 s2 x1 n1,
  close_s_wrt_s_rec n1 x1 s1 = close_s_wrt_s_rec n1 x1 s2 ->
  s1 = s2) /\
(forall SS1 SS2 x1 n1,
  close_SS_wrt_s_rec n1 x1 SS1 = close_SS_wrt_s_rec n1 x1 SS2 ->
  SS1 = SS2).
Proof.
apply_mutual_ind s_SS_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_s_wrt_s_rec_inj :
forall s1 s2 x1 n1,
  close_s_wrt_s_rec n1 x1 s1 = close_s_wrt_s_rec n1 x1 s2 ->
  s1 = s2.
Proof.
pose proof close_s_wrt_s_rec_inj_close_SS_wrt_s_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_s_wrt_s_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_SS_wrt_s_rec_inj :
forall SS1 SS2 x1 n1,
  close_SS_wrt_s_rec n1 x1 SS1 = close_SS_wrt_s_rec n1 x1 SS2 ->
  SS1 = SS2.
Proof.
pose proof close_s_wrt_s_rec_inj_close_SS_wrt_s_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_SS_wrt_s_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_F_wrt_s_rec_inj_mutual :
(forall F1 F2 x1 n1,
  close_F_wrt_s_rec n1 x1 F1 = close_F_wrt_s_rec n1 x1 F2 ->
  F1 = F2).
Proof.
apply_mutual_ind F_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_F_wrt_s_rec_inj :
forall F1 F2 x1 n1,
  close_F_wrt_s_rec n1 x1 F1 = close_F_wrt_s_rec n1 x1 F2 ->
  F1 = F2.
Proof.
pose proof close_F_wrt_s_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_F_wrt_s_rec_inj : lngen.

(* end hide *)

Lemma close_s_wrt_s_inj :
forall s1 s2 x1,
  close_s_wrt_s x1 s1 = close_s_wrt_s x1 s2 ->
  s1 = s2.
Proof.
unfold close_s_wrt_s; eauto with lngen.
Qed.

Hint Immediate close_s_wrt_s_inj : lngen.

Lemma close_SS_wrt_s_inj :
forall SS1 SS2 x1,
  close_SS_wrt_s x1 SS1 = close_SS_wrt_s x1 SS2 ->
  SS1 = SS2.
Proof.
unfold close_SS_wrt_s; eauto with lngen.
Qed.

Hint Immediate close_SS_wrt_s_inj : lngen.

Lemma close_F_wrt_s_inj :
forall F1 F2 x1,
  close_F_wrt_s x1 F1 = close_F_wrt_s x1 F2 ->
  F1 = F2.
Proof.
unfold close_F_wrt_s; eauto with lngen.
Qed.

Hint Immediate close_F_wrt_s_inj : lngen.

(* begin hide *)

Lemma close_s_wrt_s_rec_open_s_wrt_s_rec_close_SS_wrt_s_rec_open_SS_wrt_s_rec_mutual :
(forall s1 x1 n1,
  x1 `notin` sfv_s s1 ->
  close_s_wrt_s_rec n1 x1 (open_s_wrt_s_rec n1 (s_var_f x1) s1) = s1) /\
(forall SS1 x1 n1,
  x1 `notin` sfv_SS SS1 ->
  close_SS_wrt_s_rec n1 x1 (open_SS_wrt_s_rec n1 (s_var_f x1) SS1) = SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_s_wrt_s_rec_open_s_wrt_s_rec :
forall s1 x1 n1,
  x1 `notin` sfv_s s1 ->
  close_s_wrt_s_rec n1 x1 (open_s_wrt_s_rec n1 (s_var_f x1) s1) = s1.
Proof.
pose proof close_s_wrt_s_rec_open_s_wrt_s_rec_close_SS_wrt_s_rec_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_s_wrt_s_rec_open_s_wrt_s_rec : lngen.
Hint Rewrite close_s_wrt_s_rec_open_s_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_SS_wrt_s_rec_open_SS_wrt_s_rec :
forall SS1 x1 n1,
  x1 `notin` sfv_SS SS1 ->
  close_SS_wrt_s_rec n1 x1 (open_SS_wrt_s_rec n1 (s_var_f x1) SS1) = SS1.
Proof.
pose proof close_s_wrt_s_rec_open_s_wrt_s_rec_close_SS_wrt_s_rec_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_SS_wrt_s_rec_open_SS_wrt_s_rec : lngen.
Hint Rewrite close_SS_wrt_s_rec_open_SS_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_F_wrt_s_rec_open_F_wrt_s_rec_mutual :
(forall F1 x1 n1,
  x1 `notin` sfv_F F1 ->
  close_F_wrt_s_rec n1 x1 (open_F_wrt_s_rec n1 (s_var_f x1) F1) = F1).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_F_wrt_s_rec_open_F_wrt_s_rec :
forall F1 x1 n1,
  x1 `notin` sfv_F F1 ->
  close_F_wrt_s_rec n1 x1 (open_F_wrt_s_rec n1 (s_var_f x1) F1) = F1.
Proof.
pose proof close_F_wrt_s_rec_open_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_F_wrt_s_rec_open_F_wrt_s_rec : lngen.
Hint Rewrite close_F_wrt_s_rec_open_F_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_s_wrt_s_open_s_wrt_s :
forall s1 x1,
  x1 `notin` sfv_s s1 ->
  close_s_wrt_s x1 (open_s_wrt_s s1 (s_var_f x1)) = s1.
Proof.
unfold close_s_wrt_s; unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve close_s_wrt_s_open_s_wrt_s : lngen.
Hint Rewrite close_s_wrt_s_open_s_wrt_s using solve [auto] : lngen.

Lemma close_SS_wrt_s_open_SS_wrt_s :
forall SS1 x1,
  x1 `notin` sfv_SS SS1 ->
  close_SS_wrt_s x1 (open_SS_wrt_s SS1 (s_var_f x1)) = SS1.
Proof.
unfold close_SS_wrt_s; unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve close_SS_wrt_s_open_SS_wrt_s : lngen.
Hint Rewrite close_SS_wrt_s_open_SS_wrt_s using solve [auto] : lngen.

Lemma close_F_wrt_s_open_F_wrt_s :
forall F1 x1,
  x1 `notin` sfv_F F1 ->
  close_F_wrt_s x1 (open_F_wrt_s F1 (s_var_f x1)) = F1.
Proof.
unfold close_F_wrt_s; unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve close_F_wrt_s_open_F_wrt_s : lngen.
Hint Rewrite close_F_wrt_s_open_F_wrt_s using solve [auto] : lngen.

(* begin hide *)

Lemma open_s_wrt_s_rec_close_s_wrt_s_rec_open_SS_wrt_s_rec_close_SS_wrt_s_rec_mutual :
(forall s1 x1 n1,
  open_s_wrt_s_rec n1 (s_var_f x1) (close_s_wrt_s_rec n1 x1 s1) = s1) /\
(forall SS1 x1 n1,
  open_SS_wrt_s_rec n1 (s_var_f x1) (close_SS_wrt_s_rec n1 x1 SS1) = SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_s_wrt_s_rec_close_s_wrt_s_rec :
forall s1 x1 n1,
  open_s_wrt_s_rec n1 (s_var_f x1) (close_s_wrt_s_rec n1 x1 s1) = s1.
Proof.
pose proof open_s_wrt_s_rec_close_s_wrt_s_rec_open_SS_wrt_s_rec_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_s_wrt_s_rec_close_s_wrt_s_rec : lngen.
Hint Rewrite open_s_wrt_s_rec_close_s_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_SS_wrt_s_rec_close_SS_wrt_s_rec :
forall SS1 x1 n1,
  open_SS_wrt_s_rec n1 (s_var_f x1) (close_SS_wrt_s_rec n1 x1 SS1) = SS1.
Proof.
pose proof open_s_wrt_s_rec_close_s_wrt_s_rec_open_SS_wrt_s_rec_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_SS_wrt_s_rec_close_SS_wrt_s_rec : lngen.
Hint Rewrite open_SS_wrt_s_rec_close_SS_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_F_wrt_s_rec_close_F_wrt_s_rec_mutual :
(forall F1 x1 n1,
  open_F_wrt_s_rec n1 (s_var_f x1) (close_F_wrt_s_rec n1 x1 F1) = F1).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_F_wrt_s_rec_close_F_wrt_s_rec :
forall F1 x1 n1,
  open_F_wrt_s_rec n1 (s_var_f x1) (close_F_wrt_s_rec n1 x1 F1) = F1.
Proof.
pose proof open_F_wrt_s_rec_close_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_F_wrt_s_rec_close_F_wrt_s_rec : lngen.
Hint Rewrite open_F_wrt_s_rec_close_F_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_s_wrt_s_close_s_wrt_s :
forall s1 x1,
  open_s_wrt_s (close_s_wrt_s x1 s1) (s_var_f x1) = s1.
Proof.
unfold close_s_wrt_s; unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve open_s_wrt_s_close_s_wrt_s : lngen.
Hint Rewrite open_s_wrt_s_close_s_wrt_s using solve [auto] : lngen.

Lemma open_SS_wrt_s_close_SS_wrt_s :
forall SS1 x1,
  open_SS_wrt_s (close_SS_wrt_s x1 SS1) (s_var_f x1) = SS1.
Proof.
unfold close_SS_wrt_s; unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve open_SS_wrt_s_close_SS_wrt_s : lngen.
Hint Rewrite open_SS_wrt_s_close_SS_wrt_s using solve [auto] : lngen.

Lemma open_F_wrt_s_close_F_wrt_s :
forall F1 x1,
  open_F_wrt_s (close_F_wrt_s x1 F1) (s_var_f x1) = F1.
Proof.
unfold close_F_wrt_s; unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve open_F_wrt_s_close_F_wrt_s : lngen.
Hint Rewrite open_F_wrt_s_close_F_wrt_s using solve [auto] : lngen.

(* begin hide *)

Lemma open_s_wrt_s_rec_inj_open_SS_wrt_s_rec_inj_mutual :
(forall s2 s1 x1 n1,
  x1 `notin` sfv_s s2 ->
  x1 `notin` sfv_s s1 ->
  open_s_wrt_s_rec n1 (s_var_f x1) s2 = open_s_wrt_s_rec n1 (s_var_f x1) s1 ->
  s2 = s1) /\
(forall SS2 SS1 x1 n1,
  x1 `notin` sfv_SS SS2 ->
  x1 `notin` sfv_SS SS1 ->
  open_SS_wrt_s_rec n1 (s_var_f x1) SS2 = open_SS_wrt_s_rec n1 (s_var_f x1) SS1 ->
  SS2 = SS1).
Proof.
apply_mutual_ind s_SS_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_s_wrt_s_rec_inj :
forall s2 s1 x1 n1,
  x1 `notin` sfv_s s2 ->
  x1 `notin` sfv_s s1 ->
  open_s_wrt_s_rec n1 (s_var_f x1) s2 = open_s_wrt_s_rec n1 (s_var_f x1) s1 ->
  s2 = s1.
Proof.
pose proof open_s_wrt_s_rec_inj_open_SS_wrt_s_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_s_wrt_s_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_SS_wrt_s_rec_inj :
forall SS2 SS1 x1 n1,
  x1 `notin` sfv_SS SS2 ->
  x1 `notin` sfv_SS SS1 ->
  open_SS_wrt_s_rec n1 (s_var_f x1) SS2 = open_SS_wrt_s_rec n1 (s_var_f x1) SS1 ->
  SS2 = SS1.
Proof.
pose proof open_s_wrt_s_rec_inj_open_SS_wrt_s_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_SS_wrt_s_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_F_wrt_s_rec_inj_mutual :
(forall F2 F1 x1 n1,
  x1 `notin` sfv_F F2 ->
  x1 `notin` sfv_F F1 ->
  open_F_wrt_s_rec n1 (s_var_f x1) F2 = open_F_wrt_s_rec n1 (s_var_f x1) F1 ->
  F2 = F1).
Proof.
apply_mutual_ind F_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_F_wrt_s_rec_inj :
forall F2 F1 x1 n1,
  x1 `notin` sfv_F F2 ->
  x1 `notin` sfv_F F1 ->
  open_F_wrt_s_rec n1 (s_var_f x1) F2 = open_F_wrt_s_rec n1 (s_var_f x1) F1 ->
  F2 = F1.
Proof.
pose proof open_F_wrt_s_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_F_wrt_s_rec_inj : lngen.

(* end hide *)

Lemma open_s_wrt_s_inj :
forall s2 s1 x1,
  x1 `notin` sfv_s s2 ->
  x1 `notin` sfv_s s1 ->
  open_s_wrt_s s2 (s_var_f x1) = open_s_wrt_s s1 (s_var_f x1) ->
  s2 = s1.
Proof.
unfold open_s_wrt_s; eauto with lngen.
Qed.

Hint Immediate open_s_wrt_s_inj : lngen.

Lemma open_SS_wrt_s_inj :
forall SS2 SS1 x1,
  x1 `notin` sfv_SS SS2 ->
  x1 `notin` sfv_SS SS1 ->
  open_SS_wrt_s SS2 (s_var_f x1) = open_SS_wrt_s SS1 (s_var_f x1) ->
  SS2 = SS1.
Proof.
unfold open_SS_wrt_s; eauto with lngen.
Qed.

Hint Immediate open_SS_wrt_s_inj : lngen.

Lemma open_F_wrt_s_inj :
forall F2 F1 x1,
  x1 `notin` sfv_F F2 ->
  x1 `notin` sfv_F F1 ->
  open_F_wrt_s F2 (s_var_f x1) = open_F_wrt_s F1 (s_var_f x1) ->
  F2 = F1.
Proof.
unfold open_F_wrt_s; eauto with lngen.
Qed.

Hint Immediate open_F_wrt_s_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_s_wrt_s_of_lc_s_degree_SS_wrt_s_of_lc_SS_mutual :
(forall s1,
  lc_s s1 ->
  degree_s_wrt_s 0 s1) /\
(forall SS1,
  lc_SS SS1 ->
  degree_SS_wrt_s 0 SS1).
Proof.
apply_mutual_ind lc_s_lc_SS_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_s_wrt_s_of_lc_s :
forall s1,
  lc_s s1 ->
  degree_s_wrt_s 0 s1.
Proof.
pose proof degree_s_wrt_s_of_lc_s_degree_SS_wrt_s_of_lc_SS_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_s_wrt_s_of_lc_s : lngen.

Lemma degree_SS_wrt_s_of_lc_SS :
forall SS1,
  lc_SS SS1 ->
  degree_SS_wrt_s 0 SS1.
Proof.
pose proof degree_s_wrt_s_of_lc_s_degree_SS_wrt_s_of_lc_SS_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_SS_wrt_s_of_lc_SS : lngen.

(* begin hide *)

Lemma degree_F_wrt_s_of_lc_F_mutual :
(forall F1,
  lc_F F1 ->
  degree_F_wrt_s 0 F1).
Proof.
apply_mutual_ind lc_F_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_F_wrt_s_of_lc_F :
forall F1,
  lc_F F1 ->
  degree_F_wrt_s 0 F1.
Proof.
pose proof degree_F_wrt_s_of_lc_F_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_F_wrt_s_of_lc_F : lngen.

(* begin hide *)

Lemma lc_s_of_degree_lc_SS_of_degree_size_mutual :
forall i1,
(forall s1,
  size_s s1 = i1 ->
  degree_s_wrt_s 0 s1 ->
  lc_s s1) /\
(forall SS1,
  size_SS SS1 = i1 ->
  degree_SS_wrt_s 0 SS1 ->
  lc_SS SS1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind s_SS_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_s_of_degree :
forall s1,
  degree_s_wrt_s 0 s1 ->
  lc_s s1.
Proof.
intros s1; intros;
pose proof (lc_s_of_degree_lc_SS_of_degree_size_mutual (size_s s1));
intuition eauto.
Qed.

Hint Resolve lc_s_of_degree : lngen.

Lemma lc_SS_of_degree :
forall SS1,
  degree_SS_wrt_s 0 SS1 ->
  lc_SS SS1.
Proof.
intros SS1; intros;
pose proof (lc_s_of_degree_lc_SS_of_degree_size_mutual (size_SS SS1));
intuition eauto.
Qed.

Hint Resolve lc_SS_of_degree : lngen.

(* begin hide *)

Lemma lc_F_of_degree_size_mutual :
forall i1,
(forall F1,
  size_F F1 = i1 ->
  degree_F_wrt_s 0 F1 ->
  lc_F F1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind F_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_F_of_degree :
forall F1,
  degree_F_wrt_s 0 F1 ->
  lc_F F1.
Proof.
intros F1; intros;
pose proof (lc_F_of_degree_size_mutual (size_F F1));
intuition eauto.
Qed.

Hint Resolve lc_F_of_degree : lngen.

Ltac B_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac k_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac b_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac s_SS_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_s_wrt_s_of_lc_s in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_SS_wrt_s_of_lc_SS in J1; clear H
          end).

Ltac F_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_F_wrt_s_of_lc_F in J1; clear H
          end).

Lemma lc_s_lam_exists :
forall x1 SS1 s1,
  lc_SS SS1 ->
  lc_s (open_s_wrt_s s1 (s_var_f x1)) ->
  lc_s (s_lam SS1 s1).
Proof.
intros; s_SS_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_SS_refinement_exists :
forall x1 B1 s1,
  lc_s (open_s_wrt_s s1 (s_var_f x1)) ->
  lc_SS (SS_refinement B1 s1).
Proof.
intros; s_SS_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_SS_darrow_exists :
forall x1 SS1 SS2,
  lc_SS SS1 ->
  lc_SS (open_SS_wrt_s SS2 (s_var_f x1)) ->
  lc_SS (SS_darrow SS1 SS2).
Proof.
intros; s_SS_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_s (s_lam _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_s_lam_exists x1).

Hint Extern 1 (lc_SS (SS_refinement _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_SS_refinement_exists x1).

Hint Extern 1 (lc_SS (SS_darrow _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_SS_darrow_exists x1).

Lemma lc_body_s_wrt_s :
forall s1 s2,
  body_s_wrt_s s1 ->
  lc_s s2 ->
  lc_s (open_s_wrt_s s1 s2).
Proof.
unfold body_s_wrt_s;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
s_SS_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_s_wrt_s : lngen.

Lemma lc_body_SS_wrt_s :
forall SS1 s1,
  body_SS_wrt_s SS1 ->
  lc_s s1 ->
  lc_SS (open_SS_wrt_s SS1 s1).
Proof.
unfold body_SS_wrt_s;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
s_SS_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_SS_wrt_s : lngen.

Lemma lc_body_F_wrt_s :
forall F1 s1,
  body_F_wrt_s F1 ->
  lc_s s1 ->
  lc_F (open_F_wrt_s F1 s1).
Proof.
unfold body_F_wrt_s;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
F_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_F_wrt_s : lngen.

Lemma lc_body_s_lam_2 :
forall SS1 s1,
  lc_s (s_lam SS1 s1) ->
  body_s_wrt_s s1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_s_lam_2 : lngen.

Lemma lc_body_SS_refinement_2 :
forall B1 s1,
  lc_SS (SS_refinement B1 s1) ->
  body_s_wrt_s s1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_SS_refinement_2 : lngen.

Lemma lc_body_SS_darrow_2 :
forall SS1 SS2,
  lc_SS (SS_darrow SS1 SS2) ->
  body_SS_wrt_s SS2.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_SS_darrow_2 : lngen.

(* begin hide *)

Lemma lc_s_unique_lc_SS_unique_mutual :
(forall s1 (proof2 proof3 : lc_s s1), proof2 = proof3) /\
(forall SS1 (proof2 proof3 : lc_SS SS1), proof2 = proof3).
Proof.
apply_mutual_ind lc_s_lc_SS_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_s_unique :
forall s1 (proof2 proof3 : lc_s s1), proof2 = proof3.
Proof.
pose proof lc_s_unique_lc_SS_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_s_unique : lngen.

Lemma lc_SS_unique :
forall SS1 (proof2 proof3 : lc_SS SS1), proof2 = proof3.
Proof.
pose proof lc_s_unique_lc_SS_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_SS_unique : lngen.

(* begin hide *)

Lemma lc_F_unique_mutual :
(forall F1 (proof2 proof3 : lc_F F1), proof2 = proof3).
Proof.
apply_mutual_ind lc_F_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_F_unique :
forall F1 (proof2 proof3 : lc_F F1), proof2 = proof3.
Proof.
pose proof lc_F_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_F_unique : lngen.

(* begin hide *)

Lemma lc_s_of_lc_set_s_lc_SS_of_lc_set_SS_mutual :
(forall s1, lc_set_s s1 -> lc_s s1) /\
(forall SS1, lc_set_SS SS1 -> lc_SS SS1).
Proof.
apply_mutual_ind lc_set_s_lc_set_SS_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_s_of_lc_set_s :
forall s1, lc_set_s s1 -> lc_s s1.
Proof.
pose proof lc_s_of_lc_set_s_lc_SS_of_lc_set_SS_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_s_of_lc_set_s : lngen.

Lemma lc_SS_of_lc_set_SS :
forall SS1, lc_set_SS SS1 -> lc_SS SS1.
Proof.
pose proof lc_s_of_lc_set_s_lc_SS_of_lc_set_SS_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_SS_of_lc_set_SS : lngen.

(* begin hide *)

Lemma lc_F_of_lc_set_F_mutual :
(forall F1, lc_set_F F1 -> lc_F F1).
Proof.
apply_mutual_ind lc_set_F_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_F_of_lc_set_F :
forall F1, lc_set_F F1 -> lc_F F1.
Proof.
pose proof lc_F_of_lc_set_F_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_F_of_lc_set_F : lngen.

(* begin hide *)

Lemma lc_set_s_of_lc_s_lc_set_SS_of_lc_SS_size_mutual :
forall i1,
(forall s1,
  size_s s1 = i1 ->
  lc_s s1 ->
  lc_set_s s1) *
(forall SS1,
  size_SS SS1 = i1 ->
  lc_SS SS1 ->
  lc_set_SS SS1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind s_SS_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_B_of_lc_B
 | apply lc_set_SS_of_lc_SS
 | apply lc_set_b_of_lc_b
 | apply lc_set_k_of_lc_k
 | apply lc_set_s_of_lc_s
 | apply lc_set_B_of_lc_B
 | apply lc_set_SS_of_lc_SS
 | apply lc_set_b_of_lc_b
 | apply lc_set_k_of_lc_k
 | apply lc_set_s_of_lc_s];
default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_s_of_lc_s :
forall s1,
  lc_s s1 ->
  lc_set_s s1.
Proof.
intros s1; intros;
pose proof (lc_set_s_of_lc_s_lc_set_SS_of_lc_SS_size_mutual (size_s s1));
intuition eauto.
Qed.

Hint Resolve lc_set_s_of_lc_s : lngen.

Lemma lc_set_SS_of_lc_SS :
forall SS1,
  lc_SS SS1 ->
  lc_set_SS SS1.
Proof.
intros SS1; intros;
pose proof (lc_set_s_of_lc_s_lc_set_SS_of_lc_SS_size_mutual (size_SS SS1));
intuition eauto.
Qed.

Hint Resolve lc_set_SS_of_lc_SS : lngen.

(* begin hide *)

Lemma lc_set_F_of_lc_F_size_mutual :
forall i1,
(forall F1,
  size_F F1 = i1 ->
  lc_F F1 ->
  lc_set_F F1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind F_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_B_of_lc_B
 | apply lc_set_F_of_lc_F
 | apply lc_set_SS_of_lc_SS
 | apply lc_set_b_of_lc_b
 | apply lc_set_k_of_lc_k
 | apply lc_set_s_of_lc_s];
default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_F_of_lc_F :
forall F1,
  lc_F F1 ->
  lc_set_F F1.
Proof.
intros F1; intros;
pose proof (lc_set_F_of_lc_F_size_mutual (size_F F1));
intuition eauto.
Qed.

Hint Resolve lc_set_F_of_lc_F : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_s_wrt_s_rec_degree_s_wrt_s_close_SS_wrt_s_rec_degree_SS_wrt_s_mutual :
(forall s1 x1 n1,
  degree_s_wrt_s n1 s1 ->
  x1 `notin` sfv_s s1 ->
  close_s_wrt_s_rec n1 x1 s1 = s1) /\
(forall SS1 x1 n1,
  degree_SS_wrt_s n1 SS1 ->
  x1 `notin` sfv_SS SS1 ->
  close_SS_wrt_s_rec n1 x1 SS1 = SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_s_wrt_s_rec_degree_s_wrt_s :
forall s1 x1 n1,
  degree_s_wrt_s n1 s1 ->
  x1 `notin` sfv_s s1 ->
  close_s_wrt_s_rec n1 x1 s1 = s1.
Proof.
pose proof close_s_wrt_s_rec_degree_s_wrt_s_close_SS_wrt_s_rec_degree_SS_wrt_s_mutual as H; intuition eauto.
Qed.

Hint Resolve close_s_wrt_s_rec_degree_s_wrt_s : lngen.
Hint Rewrite close_s_wrt_s_rec_degree_s_wrt_s using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_SS_wrt_s_rec_degree_SS_wrt_s :
forall SS1 x1 n1,
  degree_SS_wrt_s n1 SS1 ->
  x1 `notin` sfv_SS SS1 ->
  close_SS_wrt_s_rec n1 x1 SS1 = SS1.
Proof.
pose proof close_s_wrt_s_rec_degree_s_wrt_s_close_SS_wrt_s_rec_degree_SS_wrt_s_mutual as H; intuition eauto.
Qed.

Hint Resolve close_SS_wrt_s_rec_degree_SS_wrt_s : lngen.
Hint Rewrite close_SS_wrt_s_rec_degree_SS_wrt_s using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_F_wrt_s_rec_degree_F_wrt_s_mutual :
(forall F1 x1 n1,
  degree_F_wrt_s n1 F1 ->
  x1 `notin` sfv_F F1 ->
  close_F_wrt_s_rec n1 x1 F1 = F1).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_F_wrt_s_rec_degree_F_wrt_s :
forall F1 x1 n1,
  degree_F_wrt_s n1 F1 ->
  x1 `notin` sfv_F F1 ->
  close_F_wrt_s_rec n1 x1 F1 = F1.
Proof.
pose proof close_F_wrt_s_rec_degree_F_wrt_s_mutual as H; intuition eauto.
Qed.

Hint Resolve close_F_wrt_s_rec_degree_F_wrt_s : lngen.
Hint Rewrite close_F_wrt_s_rec_degree_F_wrt_s using solve [auto] : lngen.

(* end hide *)

Lemma close_s_wrt_s_lc_s :
forall s1 x1,
  lc_s s1 ->
  x1 `notin` sfv_s s1 ->
  close_s_wrt_s x1 s1 = s1.
Proof.
unfold close_s_wrt_s; default_simp.
Qed.

Hint Resolve close_s_wrt_s_lc_s : lngen.
Hint Rewrite close_s_wrt_s_lc_s using solve [auto] : lngen.

Lemma close_SS_wrt_s_lc_SS :
forall SS1 x1,
  lc_SS SS1 ->
  x1 `notin` sfv_SS SS1 ->
  close_SS_wrt_s x1 SS1 = SS1.
Proof.
unfold close_SS_wrt_s; default_simp.
Qed.

Hint Resolve close_SS_wrt_s_lc_SS : lngen.
Hint Rewrite close_SS_wrt_s_lc_SS using solve [auto] : lngen.

Lemma close_F_wrt_s_lc_F :
forall F1 x1,
  lc_F F1 ->
  x1 `notin` sfv_F F1 ->
  close_F_wrt_s x1 F1 = F1.
Proof.
unfold close_F_wrt_s; default_simp.
Qed.

Hint Resolve close_F_wrt_s_lc_F : lngen.
Hint Rewrite close_F_wrt_s_lc_F using solve [auto] : lngen.

(* begin hide *)

Lemma open_s_wrt_s_rec_degree_s_wrt_s_open_SS_wrt_s_rec_degree_SS_wrt_s_mutual :
(forall s2 s1 n1,
  degree_s_wrt_s n1 s2 ->
  open_s_wrt_s_rec n1 s1 s2 = s2) /\
(forall SS1 s1 n1,
  degree_SS_wrt_s n1 SS1 ->
  open_SS_wrt_s_rec n1 s1 SS1 = SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_s_wrt_s_rec_degree_s_wrt_s :
forall s2 s1 n1,
  degree_s_wrt_s n1 s2 ->
  open_s_wrt_s_rec n1 s1 s2 = s2.
Proof.
pose proof open_s_wrt_s_rec_degree_s_wrt_s_open_SS_wrt_s_rec_degree_SS_wrt_s_mutual as H; intuition eauto.
Qed.

Hint Resolve open_s_wrt_s_rec_degree_s_wrt_s : lngen.
Hint Rewrite open_s_wrt_s_rec_degree_s_wrt_s using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_SS_wrt_s_rec_degree_SS_wrt_s :
forall SS1 s1 n1,
  degree_SS_wrt_s n1 SS1 ->
  open_SS_wrt_s_rec n1 s1 SS1 = SS1.
Proof.
pose proof open_s_wrt_s_rec_degree_s_wrt_s_open_SS_wrt_s_rec_degree_SS_wrt_s_mutual as H; intuition eauto.
Qed.

Hint Resolve open_SS_wrt_s_rec_degree_SS_wrt_s : lngen.
Hint Rewrite open_SS_wrt_s_rec_degree_SS_wrt_s using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_F_wrt_s_rec_degree_F_wrt_s_mutual :
(forall F1 s1 n1,
  degree_F_wrt_s n1 F1 ->
  open_F_wrt_s_rec n1 s1 F1 = F1).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_F_wrt_s_rec_degree_F_wrt_s :
forall F1 s1 n1,
  degree_F_wrt_s n1 F1 ->
  open_F_wrt_s_rec n1 s1 F1 = F1.
Proof.
pose proof open_F_wrt_s_rec_degree_F_wrt_s_mutual as H; intuition eauto.
Qed.

Hint Resolve open_F_wrt_s_rec_degree_F_wrt_s : lngen.
Hint Rewrite open_F_wrt_s_rec_degree_F_wrt_s using solve [auto] : lngen.

(* end hide *)

Lemma open_s_wrt_s_lc_s :
forall s2 s1,
  lc_s s2 ->
  open_s_wrt_s s2 s1 = s2.
Proof.
unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve open_s_wrt_s_lc_s : lngen.
Hint Rewrite open_s_wrt_s_lc_s using solve [auto] : lngen.

Lemma open_SS_wrt_s_lc_SS :
forall SS1 s1,
  lc_SS SS1 ->
  open_SS_wrt_s SS1 s1 = SS1.
Proof.
unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve open_SS_wrt_s_lc_SS : lngen.
Hint Rewrite open_SS_wrt_s_lc_SS using solve [auto] : lngen.

Lemma open_F_wrt_s_lc_F :
forall F1 s1,
  lc_F F1 ->
  open_F_wrt_s F1 s1 = F1.
Proof.
unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve open_F_wrt_s_lc_F : lngen.
Hint Rewrite open_F_wrt_s_lc_F using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma sfv_s_close_s_wrt_s_rec_sfv_SS_close_SS_wrt_s_rec_mutual :
(forall s1 x1 n1,
  sfv_s (close_s_wrt_s_rec n1 x1 s1) [=] remove x1 (sfv_s s1)) /\
(forall SS1 x1 n1,
  sfv_SS (close_SS_wrt_s_rec n1 x1 SS1) [=] remove x1 (sfv_SS SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma sfv_s_close_s_wrt_s_rec :
forall s1 x1 n1,
  sfv_s (close_s_wrt_s_rec n1 x1 s1) [=] remove x1 (sfv_s s1).
Proof.
pose proof sfv_s_close_s_wrt_s_rec_sfv_SS_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_s_close_s_wrt_s_rec : lngen.
Hint Rewrite sfv_s_close_s_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma sfv_SS_close_SS_wrt_s_rec :
forall SS1 x1 n1,
  sfv_SS (close_SS_wrt_s_rec n1 x1 SS1) [=] remove x1 (sfv_SS SS1).
Proof.
pose proof sfv_s_close_s_wrt_s_rec_sfv_SS_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_SS_close_SS_wrt_s_rec : lngen.
Hint Rewrite sfv_SS_close_SS_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma sfv_F_close_F_wrt_s_rec_mutual :
(forall F1 x1 n1,
  sfv_F (close_F_wrt_s_rec n1 x1 F1) [=] remove x1 (sfv_F F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma sfv_F_close_F_wrt_s_rec :
forall F1 x1 n1,
  sfv_F (close_F_wrt_s_rec n1 x1 F1) [=] remove x1 (sfv_F F1).
Proof.
pose proof sfv_F_close_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_F_close_F_wrt_s_rec : lngen.
Hint Rewrite sfv_F_close_F_wrt_s_rec using solve [auto] : lngen.

(* end hide *)

Lemma sfv_s_close_s_wrt_s :
forall s1 x1,
  sfv_s (close_s_wrt_s x1 s1) [=] remove x1 (sfv_s s1).
Proof.
unfold close_s_wrt_s; default_simp.
Qed.

Hint Resolve sfv_s_close_s_wrt_s : lngen.
Hint Rewrite sfv_s_close_s_wrt_s using solve [auto] : lngen.

Lemma sfv_SS_close_SS_wrt_s :
forall SS1 x1,
  sfv_SS (close_SS_wrt_s x1 SS1) [=] remove x1 (sfv_SS SS1).
Proof.
unfold close_SS_wrt_s; default_simp.
Qed.

Hint Resolve sfv_SS_close_SS_wrt_s : lngen.
Hint Rewrite sfv_SS_close_SS_wrt_s using solve [auto] : lngen.

Lemma sfv_F_close_F_wrt_s :
forall F1 x1,
  sfv_F (close_F_wrt_s x1 F1) [=] remove x1 (sfv_F F1).
Proof.
unfold close_F_wrt_s; default_simp.
Qed.

Hint Resolve sfv_F_close_F_wrt_s : lngen.
Hint Rewrite sfv_F_close_F_wrt_s using solve [auto] : lngen.

(* begin hide *)

Lemma sfv_s_open_s_wrt_s_rec_lower_sfv_SS_open_SS_wrt_s_rec_lower_mutual :
(forall s1 s2 n1,
  sfv_s s1 [<=] sfv_s (open_s_wrt_s_rec n1 s2 s1)) /\
(forall SS1 s1 n1,
  sfv_SS SS1 [<=] sfv_SS (open_SS_wrt_s_rec n1 s1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma sfv_s_open_s_wrt_s_rec_lower :
forall s1 s2 n1,
  sfv_s s1 [<=] sfv_s (open_s_wrt_s_rec n1 s2 s1).
Proof.
pose proof sfv_s_open_s_wrt_s_rec_lower_sfv_SS_open_SS_wrt_s_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_s_open_s_wrt_s_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma sfv_SS_open_SS_wrt_s_rec_lower :
forall SS1 s1 n1,
  sfv_SS SS1 [<=] sfv_SS (open_SS_wrt_s_rec n1 s1 SS1).
Proof.
pose proof sfv_s_open_s_wrt_s_rec_lower_sfv_SS_open_SS_wrt_s_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_SS_open_SS_wrt_s_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma sfv_F_open_F_wrt_s_rec_lower_mutual :
(forall F1 s1 n1,
  sfv_F F1 [<=] sfv_F (open_F_wrt_s_rec n1 s1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma sfv_F_open_F_wrt_s_rec_lower :
forall F1 s1 n1,
  sfv_F F1 [<=] sfv_F (open_F_wrt_s_rec n1 s1 F1).
Proof.
pose proof sfv_F_open_F_wrt_s_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_F_open_F_wrt_s_rec_lower : lngen.

(* end hide *)

Lemma sfv_s_open_s_wrt_s_lower :
forall s1 s2,
  sfv_s s1 [<=] sfv_s (open_s_wrt_s s1 s2).
Proof.
unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve sfv_s_open_s_wrt_s_lower : lngen.

Lemma sfv_SS_open_SS_wrt_s_lower :
forall SS1 s1,
  sfv_SS SS1 [<=] sfv_SS (open_SS_wrt_s SS1 s1).
Proof.
unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve sfv_SS_open_SS_wrt_s_lower : lngen.

Lemma sfv_F_open_F_wrt_s_lower :
forall F1 s1,
  sfv_F F1 [<=] sfv_F (open_F_wrt_s F1 s1).
Proof.
unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve sfv_F_open_F_wrt_s_lower : lngen.

(* begin hide *)

Lemma sfv_s_open_s_wrt_s_rec_upper_sfv_SS_open_SS_wrt_s_rec_upper_mutual :
(forall s1 s2 n1,
  sfv_s (open_s_wrt_s_rec n1 s2 s1) [<=] sfv_s s2 `union` sfv_s s1) /\
(forall SS1 s1 n1,
  sfv_SS (open_SS_wrt_s_rec n1 s1 SS1) [<=] sfv_s s1 `union` sfv_SS SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma sfv_s_open_s_wrt_s_rec_upper :
forall s1 s2 n1,
  sfv_s (open_s_wrt_s_rec n1 s2 s1) [<=] sfv_s s2 `union` sfv_s s1.
Proof.
pose proof sfv_s_open_s_wrt_s_rec_upper_sfv_SS_open_SS_wrt_s_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_s_open_s_wrt_s_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma sfv_SS_open_SS_wrt_s_rec_upper :
forall SS1 s1 n1,
  sfv_SS (open_SS_wrt_s_rec n1 s1 SS1) [<=] sfv_s s1 `union` sfv_SS SS1.
Proof.
pose proof sfv_s_open_s_wrt_s_rec_upper_sfv_SS_open_SS_wrt_s_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_SS_open_SS_wrt_s_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma sfv_F_open_F_wrt_s_rec_upper_mutual :
(forall F1 s1 n1,
  sfv_F (open_F_wrt_s_rec n1 s1 F1) [<=] sfv_s s1 `union` sfv_F F1).
Proof.
apply_mutual_ind F_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma sfv_F_open_F_wrt_s_rec_upper :
forall F1 s1 n1,
  sfv_F (open_F_wrt_s_rec n1 s1 F1) [<=] sfv_s s1 `union` sfv_F F1.
Proof.
pose proof sfv_F_open_F_wrt_s_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_F_open_F_wrt_s_rec_upper : lngen.

(* end hide *)

Lemma sfv_s_open_s_wrt_s_upper :
forall s1 s2,
  sfv_s (open_s_wrt_s s1 s2) [<=] sfv_s s2 `union` sfv_s s1.
Proof.
unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve sfv_s_open_s_wrt_s_upper : lngen.

Lemma sfv_SS_open_SS_wrt_s_upper :
forall SS1 s1,
  sfv_SS (open_SS_wrt_s SS1 s1) [<=] sfv_s s1 `union` sfv_SS SS1.
Proof.
unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve sfv_SS_open_SS_wrt_s_upper : lngen.

Lemma sfv_F_open_F_wrt_s_upper :
forall F1 s1,
  sfv_F (open_F_wrt_s F1 s1) [<=] sfv_s s1 `union` sfv_F F1.
Proof.
unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve sfv_F_open_F_wrt_s_upper : lngen.

(* begin hide *)

Lemma sfv_s_ssubst_s_fresh_sfv_SS_ssubst_SS_fresh_mutual :
(forall s1 s2 x1,
  x1 `notin` sfv_s s1 ->
  sfv_s (ssubst_s s2 x1 s1) [=] sfv_s s1) /\
(forall SS1 s1 x1,
  x1 `notin` sfv_SS SS1 ->
  sfv_SS (ssubst_SS s1 x1 SS1) [=] sfv_SS SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma sfv_s_ssubst_s_fresh :
forall s1 s2 x1,
  x1 `notin` sfv_s s1 ->
  sfv_s (ssubst_s s2 x1 s1) [=] sfv_s s1.
Proof.
pose proof sfv_s_ssubst_s_fresh_sfv_SS_ssubst_SS_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_s_ssubst_s_fresh : lngen.
Hint Rewrite sfv_s_ssubst_s_fresh using solve [auto] : lngen.

Lemma sfv_SS_ssubst_SS_fresh :
forall SS1 s1 x1,
  x1 `notin` sfv_SS SS1 ->
  sfv_SS (ssubst_SS s1 x1 SS1) [=] sfv_SS SS1.
Proof.
pose proof sfv_s_ssubst_s_fresh_sfv_SS_ssubst_SS_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_SS_ssubst_SS_fresh : lngen.
Hint Rewrite sfv_SS_ssubst_SS_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma sfv_F_ssubst_F_fresh_mutual :
(forall F1 s1 x1,
  x1 `notin` sfv_F F1 ->
  sfv_F (ssubst_F s1 x1 F1) [=] sfv_F F1).
Proof.
apply_mutual_ind F_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma sfv_F_ssubst_F_fresh :
forall F1 s1 x1,
  x1 `notin` sfv_F F1 ->
  sfv_F (ssubst_F s1 x1 F1) [=] sfv_F F1.
Proof.
pose proof sfv_F_ssubst_F_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_F_ssubst_F_fresh : lngen.
Hint Rewrite sfv_F_ssubst_F_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma sfv_s_ssubst_s_lower_sfv_SS_ssubst_SS_lower_mutual :
(forall s1 s2 x1,
  remove x1 (sfv_s s1) [<=] sfv_s (ssubst_s s2 x1 s1)) /\
(forall SS1 s1 x1,
  remove x1 (sfv_SS SS1) [<=] sfv_SS (ssubst_SS s1 x1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma sfv_s_ssubst_s_lower :
forall s1 s2 x1,
  remove x1 (sfv_s s1) [<=] sfv_s (ssubst_s s2 x1 s1).
Proof.
pose proof sfv_s_ssubst_s_lower_sfv_SS_ssubst_SS_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_s_ssubst_s_lower : lngen.

Lemma sfv_SS_ssubst_SS_lower :
forall SS1 s1 x1,
  remove x1 (sfv_SS SS1) [<=] sfv_SS (ssubst_SS s1 x1 SS1).
Proof.
pose proof sfv_s_ssubst_s_lower_sfv_SS_ssubst_SS_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_SS_ssubst_SS_lower : lngen.

(* begin hide *)

Lemma sfv_F_ssubst_F_lower_mutual :
(forall F1 s1 x1,
  remove x1 (sfv_F F1) [<=] sfv_F (ssubst_F s1 x1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma sfv_F_ssubst_F_lower :
forall F1 s1 x1,
  remove x1 (sfv_F F1) [<=] sfv_F (ssubst_F s1 x1 F1).
Proof.
pose proof sfv_F_ssubst_F_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_F_ssubst_F_lower : lngen.

(* begin hide *)

Lemma sfv_s_ssubst_s_notin_sfv_SS_ssubst_SS_notin_mutual :
(forall s1 s2 x1 x2,
  x2 `notin` sfv_s s1 ->
  x2 `notin` sfv_s s2 ->
  x2 `notin` sfv_s (ssubst_s s2 x1 s1)) /\
(forall SS1 s1 x1 x2,
  x2 `notin` sfv_SS SS1 ->
  x2 `notin` sfv_s s1 ->
  x2 `notin` sfv_SS (ssubst_SS s1 x1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma sfv_s_ssubst_s_notin :
forall s1 s2 x1 x2,
  x2 `notin` sfv_s s1 ->
  x2 `notin` sfv_s s2 ->
  x2 `notin` sfv_s (ssubst_s s2 x1 s1).
Proof.
pose proof sfv_s_ssubst_s_notin_sfv_SS_ssubst_SS_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_s_ssubst_s_notin : lngen.

Lemma sfv_SS_ssubst_SS_notin :
forall SS1 s1 x1 x2,
  x2 `notin` sfv_SS SS1 ->
  x2 `notin` sfv_s s1 ->
  x2 `notin` sfv_SS (ssubst_SS s1 x1 SS1).
Proof.
pose proof sfv_s_ssubst_s_notin_sfv_SS_ssubst_SS_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_SS_ssubst_SS_notin : lngen.

(* begin hide *)

Lemma sfv_F_ssubst_F_notin_mutual :
(forall F1 s1 x1 x2,
  x2 `notin` sfv_F F1 ->
  x2 `notin` sfv_s s1 ->
  x2 `notin` sfv_F (ssubst_F s1 x1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma sfv_F_ssubst_F_notin :
forall F1 s1 x1 x2,
  x2 `notin` sfv_F F1 ->
  x2 `notin` sfv_s s1 ->
  x2 `notin` sfv_F (ssubst_F s1 x1 F1).
Proof.
pose proof sfv_F_ssubst_F_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_F_ssubst_F_notin : lngen.

(* begin hide *)

Lemma sfv_s_ssubst_s_upper_sfv_SS_ssubst_SS_upper_mutual :
(forall s1 s2 x1,
  sfv_s (ssubst_s s2 x1 s1) [<=] sfv_s s2 `union` remove x1 (sfv_s s1)) /\
(forall SS1 s1 x1,
  sfv_SS (ssubst_SS s1 x1 SS1) [<=] sfv_s s1 `union` remove x1 (sfv_SS SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma sfv_s_ssubst_s_upper :
forall s1 s2 x1,
  sfv_s (ssubst_s s2 x1 s1) [<=] sfv_s s2 `union` remove x1 (sfv_s s1).
Proof.
pose proof sfv_s_ssubst_s_upper_sfv_SS_ssubst_SS_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_s_ssubst_s_upper : lngen.

Lemma sfv_SS_ssubst_SS_upper :
forall SS1 s1 x1,
  sfv_SS (ssubst_SS s1 x1 SS1) [<=] sfv_s s1 `union` remove x1 (sfv_SS SS1).
Proof.
pose proof sfv_s_ssubst_s_upper_sfv_SS_ssubst_SS_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_SS_ssubst_SS_upper : lngen.

(* begin hide *)

Lemma sfv_F_ssubst_F_upper_mutual :
(forall F1 s1 x1,
  sfv_F (ssubst_F s1 x1 F1) [<=] sfv_s s1 `union` remove x1 (sfv_F F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma sfv_F_ssubst_F_upper :
forall F1 s1 x1,
  sfv_F (ssubst_F s1 x1 F1) [<=] sfv_s s1 `union` remove x1 (sfv_F F1).
Proof.
pose proof sfv_F_ssubst_F_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve sfv_F_ssubst_F_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ssubst_s_close_s_wrt_s_rec_ssubst_SS_close_SS_wrt_s_rec_mutual :
(forall s2 s1 x1 x2 n1,
  degree_s_wrt_s n1 s1 ->
  x1 <> x2 ->
  x2 `notin` sfv_s s1 ->
  ssubst_s s1 x1 (close_s_wrt_s_rec n1 x2 s2) = close_s_wrt_s_rec n1 x2 (ssubst_s s1 x1 s2)) /\
(forall SS1 s1 x1 x2 n1,
  degree_s_wrt_s n1 s1 ->
  x1 <> x2 ->
  x2 `notin` sfv_s s1 ->
  ssubst_SS s1 x1 (close_SS_wrt_s_rec n1 x2 SS1) = close_SS_wrt_s_rec n1 x2 (ssubst_SS s1 x1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_s_close_s_wrt_s_rec :
forall s2 s1 x1 x2 n1,
  degree_s_wrt_s n1 s1 ->
  x1 <> x2 ->
  x2 `notin` sfv_s s1 ->
  ssubst_s s1 x1 (close_s_wrt_s_rec n1 x2 s2) = close_s_wrt_s_rec n1 x2 (ssubst_s s1 x1 s2).
Proof.
pose proof ssubst_s_close_s_wrt_s_rec_ssubst_SS_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_close_s_wrt_s_rec : lngen.

Lemma ssubst_SS_close_SS_wrt_s_rec :
forall SS1 s1 x1 x2 n1,
  degree_s_wrt_s n1 s1 ->
  x1 <> x2 ->
  x2 `notin` sfv_s s1 ->
  ssubst_SS s1 x1 (close_SS_wrt_s_rec n1 x2 SS1) = close_SS_wrt_s_rec n1 x2 (ssubst_SS s1 x1 SS1).
Proof.
pose proof ssubst_s_close_s_wrt_s_rec_ssubst_SS_close_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_close_SS_wrt_s_rec : lngen.

(* begin hide *)

Lemma ssubst_F_close_F_wrt_s_rec_mutual :
(forall F1 s1 x1 x2 n1,
  degree_s_wrt_s n1 s1 ->
  x1 <> x2 ->
  x2 `notin` sfv_s s1 ->
  ssubst_F s1 x1 (close_F_wrt_s_rec n1 x2 F1) = close_F_wrt_s_rec n1 x2 (ssubst_F s1 x1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_F_close_F_wrt_s_rec :
forall F1 s1 x1 x2 n1,
  degree_s_wrt_s n1 s1 ->
  x1 <> x2 ->
  x2 `notin` sfv_s s1 ->
  ssubst_F s1 x1 (close_F_wrt_s_rec n1 x2 F1) = close_F_wrt_s_rec n1 x2 (ssubst_F s1 x1 F1).
Proof.
pose proof ssubst_F_close_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_close_F_wrt_s_rec : lngen.

Lemma ssubst_s_close_s_wrt_s :
forall s2 s1 x1 x2,
  lc_s s1 ->  x1 <> x2 ->
  x2 `notin` sfv_s s1 ->
  ssubst_s s1 x1 (close_s_wrt_s x2 s2) = close_s_wrt_s x2 (ssubst_s s1 x1 s2).
Proof.
unfold close_s_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_s_close_s_wrt_s : lngen.

Lemma ssubst_SS_close_SS_wrt_s :
forall SS1 s1 x1 x2,
  lc_s s1 ->  x1 <> x2 ->
  x2 `notin` sfv_s s1 ->
  ssubst_SS s1 x1 (close_SS_wrt_s x2 SS1) = close_SS_wrt_s x2 (ssubst_SS s1 x1 SS1).
Proof.
unfold close_SS_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_SS_close_SS_wrt_s : lngen.

Lemma ssubst_F_close_F_wrt_s :
forall F1 s1 x1 x2,
  lc_s s1 ->  x1 <> x2 ->
  x2 `notin` sfv_s s1 ->
  ssubst_F s1 x1 (close_F_wrt_s x2 F1) = close_F_wrt_s x2 (ssubst_F s1 x1 F1).
Proof.
unfold close_F_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_F_close_F_wrt_s : lngen.

(* begin hide *)

Lemma ssubst_s_degree_s_wrt_s_ssubst_SS_degree_SS_wrt_s_mutual :
(forall s1 s2 x1 n1,
  degree_s_wrt_s n1 s1 ->
  degree_s_wrt_s n1 s2 ->
  degree_s_wrt_s n1 (ssubst_s s2 x1 s1)) /\
(forall SS1 s1 x1 n1,
  degree_SS_wrt_s n1 SS1 ->
  degree_s_wrt_s n1 s1 ->
  degree_SS_wrt_s n1 (ssubst_SS s1 x1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_s_degree_s_wrt_s :
forall s1 s2 x1 n1,
  degree_s_wrt_s n1 s1 ->
  degree_s_wrt_s n1 s2 ->
  degree_s_wrt_s n1 (ssubst_s s2 x1 s1).
Proof.
pose proof ssubst_s_degree_s_wrt_s_ssubst_SS_degree_SS_wrt_s_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_degree_s_wrt_s : lngen.

Lemma ssubst_SS_degree_SS_wrt_s :
forall SS1 s1 x1 n1,
  degree_SS_wrt_s n1 SS1 ->
  degree_s_wrt_s n1 s1 ->
  degree_SS_wrt_s n1 (ssubst_SS s1 x1 SS1).
Proof.
pose proof ssubst_s_degree_s_wrt_s_ssubst_SS_degree_SS_wrt_s_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_degree_SS_wrt_s : lngen.

(* begin hide *)

Lemma ssubst_F_degree_F_wrt_s_mutual :
(forall F1 s1 x1 n1,
  degree_F_wrt_s n1 F1 ->
  degree_s_wrt_s n1 s1 ->
  degree_F_wrt_s n1 (ssubst_F s1 x1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_F_degree_F_wrt_s :
forall F1 s1 x1 n1,
  degree_F_wrt_s n1 F1 ->
  degree_s_wrt_s n1 s1 ->
  degree_F_wrt_s n1 (ssubst_F s1 x1 F1).
Proof.
pose proof ssubst_F_degree_F_wrt_s_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_degree_F_wrt_s : lngen.

(* begin hide *)

Lemma ssubst_s_fresh_eq_ssubst_SS_fresh_eq_mutual :
(forall s2 s1 x1,
  x1 `notin` sfv_s s2 ->
  ssubst_s s1 x1 s2 = s2) /\
(forall SS1 s1 x1,
  x1 `notin` sfv_SS SS1 ->
  ssubst_SS s1 x1 SS1 = SS1).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_s_fresh_eq :
forall s2 s1 x1,
  x1 `notin` sfv_s s2 ->
  ssubst_s s1 x1 s2 = s2.
Proof.
pose proof ssubst_s_fresh_eq_ssubst_SS_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_fresh_eq : lngen.
Hint Rewrite ssubst_s_fresh_eq using solve [auto] : lngen.

Lemma ssubst_SS_fresh_eq :
forall SS1 s1 x1,
  x1 `notin` sfv_SS SS1 ->
  ssubst_SS s1 x1 SS1 = SS1.
Proof.
pose proof ssubst_s_fresh_eq_ssubst_SS_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_fresh_eq : lngen.
Hint Rewrite ssubst_SS_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma ssubst_F_fresh_eq_mutual :
(forall F1 s1 x1,
  x1 `notin` sfv_F F1 ->
  ssubst_F s1 x1 F1 = F1).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_F_fresh_eq :
forall F1 s1 x1,
  x1 `notin` sfv_F F1 ->
  ssubst_F s1 x1 F1 = F1.
Proof.
pose proof ssubst_F_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_fresh_eq : lngen.
Hint Rewrite ssubst_F_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma ssubst_s_fresh_same_ssubst_SS_fresh_same_mutual :
(forall s2 s1 x1,
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_s (ssubst_s s1 x1 s2)) /\
(forall SS1 s1 x1,
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_SS (ssubst_SS s1 x1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_s_fresh_same :
forall s2 s1 x1,
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_s (ssubst_s s1 x1 s2).
Proof.
pose proof ssubst_s_fresh_same_ssubst_SS_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_fresh_same : lngen.
Hint Rewrite ssubst_s_fresh_same using solve [auto] : lngen.

Lemma ssubst_SS_fresh_same :
forall SS1 s1 x1,
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_SS (ssubst_SS s1 x1 SS1).
Proof.
pose proof ssubst_s_fresh_same_ssubst_SS_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_fresh_same : lngen.
Hint Rewrite ssubst_SS_fresh_same using solve [auto] : lngen.

(* begin hide *)

Lemma ssubst_F_fresh_same_mutual :
(forall F1 s1 x1,
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_F (ssubst_F s1 x1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_F_fresh_same :
forall F1 s1 x1,
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_F (ssubst_F s1 x1 F1).
Proof.
pose proof ssubst_F_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_fresh_same : lngen.
Hint Rewrite ssubst_F_fresh_same using solve [auto] : lngen.

(* begin hide *)

Lemma ssubst_s_fresh_ssubst_SS_fresh_mutual :
(forall s2 s1 x1 x2,
  x1 `notin` sfv_s s2 ->
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_s (ssubst_s s1 x2 s2)) /\
(forall SS1 s1 x1 x2,
  x1 `notin` sfv_SS SS1 ->
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_SS (ssubst_SS s1 x2 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_s_fresh :
forall s2 s1 x1 x2,
  x1 `notin` sfv_s s2 ->
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_s (ssubst_s s1 x2 s2).
Proof.
pose proof ssubst_s_fresh_ssubst_SS_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_fresh : lngen.
Hint Rewrite ssubst_s_fresh using solve [auto] : lngen.

Lemma ssubst_SS_fresh :
forall SS1 s1 x1 x2,
  x1 `notin` sfv_SS SS1 ->
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_SS (ssubst_SS s1 x2 SS1).
Proof.
pose proof ssubst_s_fresh_ssubst_SS_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_fresh : lngen.
Hint Rewrite ssubst_SS_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ssubst_F_fresh_mutual :
(forall F1 s1 x1 x2,
  x1 `notin` sfv_F F1 ->
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_F (ssubst_F s1 x2 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_F_fresh :
forall F1 s1 x1 x2,
  x1 `notin` sfv_F F1 ->
  x1 `notin` sfv_s s1 ->
  x1 `notin` sfv_F (ssubst_F s1 x2 F1).
Proof.
pose proof ssubst_F_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_fresh : lngen.
Hint Rewrite ssubst_F_fresh using solve [auto] : lngen.

Lemma ssubst_s_lc_s :
forall s1 s2 x1,
  lc_s s1 ->
  lc_s s2 ->
  lc_s (ssubst_s s2 x1 s1).
Proof.
default_simp.
Qed.

Hint Resolve ssubst_s_lc_s : lngen.

Lemma ssubst_SS_lc_SS :
forall SS1 s1 x1,
  lc_SS SS1 ->
  lc_s s1 ->
  lc_SS (ssubst_SS s1 x1 SS1).
Proof.
default_simp.
Qed.

Hint Resolve ssubst_SS_lc_SS : lngen.

Lemma ssubst_F_lc_F :
forall F1 s1 x1,
  lc_F F1 ->
  lc_s s1 ->
  lc_F (ssubst_F s1 x1 F1).
Proof.
default_simp.
Qed.

Hint Resolve ssubst_F_lc_F : lngen.

(* begin hide *)

Lemma ssubst_s_open_s_wrt_s_rec_ssubst_SS_open_SS_wrt_s_rec_mutual :
(forall s3 s1 s2 x1 n1,
  lc_s s1 ->
  ssubst_s s1 x1 (open_s_wrt_s_rec n1 s2 s3) = open_s_wrt_s_rec n1 (ssubst_s s1 x1 s2) (ssubst_s s1 x1 s3)) /\
(forall SS1 s1 s2 x1 n1,
  lc_s s1 ->
  ssubst_SS s1 x1 (open_SS_wrt_s_rec n1 s2 SS1) = open_SS_wrt_s_rec n1 (ssubst_s s1 x1 s2) (ssubst_SS s1 x1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma ssubst_s_open_s_wrt_s_rec :
forall s3 s1 s2 x1 n1,
  lc_s s1 ->
  ssubst_s s1 x1 (open_s_wrt_s_rec n1 s2 s3) = open_s_wrt_s_rec n1 (ssubst_s s1 x1 s2) (ssubst_s s1 x1 s3).
Proof.
pose proof ssubst_s_open_s_wrt_s_rec_ssubst_SS_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_open_s_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma ssubst_SS_open_SS_wrt_s_rec :
forall SS1 s1 s2 x1 n1,
  lc_s s1 ->
  ssubst_SS s1 x1 (open_SS_wrt_s_rec n1 s2 SS1) = open_SS_wrt_s_rec n1 (ssubst_s s1 x1 s2) (ssubst_SS s1 x1 SS1).
Proof.
pose proof ssubst_s_open_s_wrt_s_rec_ssubst_SS_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_open_SS_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma ssubst_F_open_F_wrt_s_rec_mutual :
(forall F1 s1 s2 x1 n1,
  lc_s s1 ->
  ssubst_F s1 x1 (open_F_wrt_s_rec n1 s2 F1) = open_F_wrt_s_rec n1 (ssubst_s s1 x1 s2) (ssubst_F s1 x1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma ssubst_F_open_F_wrt_s_rec :
forall F1 s1 s2 x1 n1,
  lc_s s1 ->
  ssubst_F s1 x1 (open_F_wrt_s_rec n1 s2 F1) = open_F_wrt_s_rec n1 (ssubst_s s1 x1 s2) (ssubst_F s1 x1 F1).
Proof.
pose proof ssubst_F_open_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_open_F_wrt_s_rec : lngen.

(* end hide *)

Lemma ssubst_s_open_s_wrt_s :
forall s3 s1 s2 x1,
  lc_s s1 ->
  ssubst_s s1 x1 (open_s_wrt_s s3 s2) = open_s_wrt_s (ssubst_s s1 x1 s3) (ssubst_s s1 x1 s2).
Proof.
unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_s_open_s_wrt_s : lngen.

Lemma ssubst_SS_open_SS_wrt_s :
forall SS1 s1 s2 x1,
  lc_s s1 ->
  ssubst_SS s1 x1 (open_SS_wrt_s SS1 s2) = open_SS_wrt_s (ssubst_SS s1 x1 SS1) (ssubst_s s1 x1 s2).
Proof.
unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_SS_open_SS_wrt_s : lngen.

Lemma ssubst_F_open_F_wrt_s :
forall F1 s1 s2 x1,
  lc_s s1 ->
  ssubst_F s1 x1 (open_F_wrt_s F1 s2) = open_F_wrt_s (ssubst_F s1 x1 F1) (ssubst_s s1 x1 s2).
Proof.
unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_F_open_F_wrt_s : lngen.

Lemma ssubst_s_open_s_wrt_s_var :
forall s2 s1 x1 x2,
  x1 <> x2 ->
  lc_s s1 ->
  open_s_wrt_s (ssubst_s s1 x1 s2) (s_var_f x2) = ssubst_s s1 x1 (open_s_wrt_s s2 (s_var_f x2)).
Proof.
intros; rewrite ssubst_s_open_s_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_s_open_s_wrt_s_var : lngen.

Lemma ssubst_SS_open_SS_wrt_s_var :
forall SS1 s1 x1 x2,
  x1 <> x2 ->
  lc_s s1 ->
  open_SS_wrt_s (ssubst_SS s1 x1 SS1) (s_var_f x2) = ssubst_SS s1 x1 (open_SS_wrt_s SS1 (s_var_f x2)).
Proof.
intros; rewrite ssubst_SS_open_SS_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_SS_open_SS_wrt_s_var : lngen.

Lemma ssubst_F_open_F_wrt_s_var :
forall F1 s1 x1 x2,
  x1 <> x2 ->
  lc_s s1 ->
  open_F_wrt_s (ssubst_F s1 x1 F1) (s_var_f x2) = ssubst_F s1 x1 (open_F_wrt_s F1 (s_var_f x2)).
Proof.
intros; rewrite ssubst_F_open_F_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_F_open_F_wrt_s_var : lngen.

(* begin hide *)

Lemma ssubst_s_spec_rec_ssubst_SS_spec_rec_mutual :
(forall s1 s2 x1 n1,
  ssubst_s s2 x1 s1 = open_s_wrt_s_rec n1 s2 (close_s_wrt_s_rec n1 x1 s1)) /\
(forall SS1 s1 x1 n1,
  ssubst_SS s1 x1 SS1 = open_SS_wrt_s_rec n1 s1 (close_SS_wrt_s_rec n1 x1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma ssubst_s_spec_rec :
forall s1 s2 x1 n1,
  ssubst_s s2 x1 s1 = open_s_wrt_s_rec n1 s2 (close_s_wrt_s_rec n1 x1 s1).
Proof.
pose proof ssubst_s_spec_rec_ssubst_SS_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma ssubst_SS_spec_rec :
forall SS1 s1 x1 n1,
  ssubst_SS s1 x1 SS1 = open_SS_wrt_s_rec n1 s1 (close_SS_wrt_s_rec n1 x1 SS1).
Proof.
pose proof ssubst_s_spec_rec_ssubst_SS_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma ssubst_F_spec_rec_mutual :
(forall F1 s1 x1 n1,
  ssubst_F s1 x1 F1 = open_F_wrt_s_rec n1 s1 (close_F_wrt_s_rec n1 x1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma ssubst_F_spec_rec :
forall F1 s1 x1 n1,
  ssubst_F s1 x1 F1 = open_F_wrt_s_rec n1 s1 (close_F_wrt_s_rec n1 x1 F1).
Proof.
pose proof ssubst_F_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_spec_rec : lngen.

(* end hide *)

Lemma ssubst_s_spec :
forall s1 s2 x1,
  ssubst_s s2 x1 s1 = open_s_wrt_s (close_s_wrt_s x1 s1) s2.
Proof.
unfold close_s_wrt_s; unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_s_spec : lngen.

Lemma ssubst_SS_spec :
forall SS1 s1 x1,
  ssubst_SS s1 x1 SS1 = open_SS_wrt_s (close_SS_wrt_s x1 SS1) s1.
Proof.
unfold close_SS_wrt_s; unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_SS_spec : lngen.

Lemma ssubst_F_spec :
forall F1 s1 x1,
  ssubst_F s1 x1 F1 = open_F_wrt_s (close_F_wrt_s x1 F1) s1.
Proof.
unfold close_F_wrt_s; unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_F_spec : lngen.

(* begin hide *)

Lemma ssubst_s_ssubst_s_ssubst_SS_ssubst_SS_mutual :
(forall s1 s2 s3 x2 x1,
  x2 `notin` sfv_s s2 ->
  x2 <> x1 ->
  ssubst_s s2 x1 (ssubst_s s3 x2 s1) = ssubst_s (ssubst_s s2 x1 s3) x2 (ssubst_s s2 x1 s1)) /\
(forall SS1 s1 s2 x2 x1,
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  ssubst_SS s1 x1 (ssubst_SS s2 x2 SS1) = ssubst_SS (ssubst_s s1 x1 s2) x2 (ssubst_SS s1 x1 SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_s_ssubst_s :
forall s1 s2 s3 x2 x1,
  x2 `notin` sfv_s s2 ->
  x2 <> x1 ->
  ssubst_s s2 x1 (ssubst_s s3 x2 s1) = ssubst_s (ssubst_s s2 x1 s3) x2 (ssubst_s s2 x1 s1).
Proof.
pose proof ssubst_s_ssubst_s_ssubst_SS_ssubst_SS_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_ssubst_s : lngen.

Lemma ssubst_SS_ssubst_SS :
forall SS1 s1 s2 x2 x1,
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  ssubst_SS s1 x1 (ssubst_SS s2 x2 SS1) = ssubst_SS (ssubst_s s1 x1 s2) x2 (ssubst_SS s1 x1 SS1).
Proof.
pose proof ssubst_s_ssubst_s_ssubst_SS_ssubst_SS_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_ssubst_SS : lngen.

(* begin hide *)

Lemma ssubst_F_ssubst_F_mutual :
(forall F1 s1 s2 x2 x1,
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  ssubst_F s1 x1 (ssubst_F s2 x2 F1) = ssubst_F (ssubst_s s1 x1 s2) x2 (ssubst_F s1 x1 F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_F_ssubst_F :
forall F1 s1 s2 x2 x1,
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  ssubst_F s1 x1 (ssubst_F s2 x2 F1) = ssubst_F (ssubst_s s1 x1 s2) x2 (ssubst_F s1 x1 F1).
Proof.
pose proof ssubst_F_ssubst_F_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_ssubst_F : lngen.

(* begin hide *)

Lemma ssubst_s_close_s_wrt_s_rec_open_s_wrt_s_rec_ssubst_SS_close_SS_wrt_s_rec_open_SS_wrt_s_rec_mutual :
(forall s2 s1 x1 x2 n1,
  x2 `notin` sfv_s s2 ->
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  degree_s_wrt_s n1 s1 ->
  ssubst_s s1 x1 s2 = close_s_wrt_s_rec n1 x2 (ssubst_s s1 x1 (open_s_wrt_s_rec n1 (s_var_f x2) s2))) *
(forall SS1 s1 x1 x2 n1,
  x2 `notin` sfv_SS SS1 ->
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  degree_s_wrt_s n1 s1 ->
  ssubst_SS s1 x1 SS1 = close_SS_wrt_s_rec n1 x2 (ssubst_SS s1 x1 (open_SS_wrt_s_rec n1 (s_var_f x2) SS1))).
Proof.
apply_mutual_ind s_SS_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma ssubst_s_close_s_wrt_s_rec_open_s_wrt_s_rec :
forall s2 s1 x1 x2 n1,
  x2 `notin` sfv_s s2 ->
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  degree_s_wrt_s n1 s1 ->
  ssubst_s s1 x1 s2 = close_s_wrt_s_rec n1 x2 (ssubst_s s1 x1 (open_s_wrt_s_rec n1 (s_var_f x2) s2)).
Proof.
pose proof ssubst_s_close_s_wrt_s_rec_open_s_wrt_s_rec_ssubst_SS_close_SS_wrt_s_rec_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_close_s_wrt_s_rec_open_s_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma ssubst_SS_close_SS_wrt_s_rec_open_SS_wrt_s_rec :
forall SS1 s1 x1 x2 n1,
  x2 `notin` sfv_SS SS1 ->
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  degree_s_wrt_s n1 s1 ->
  ssubst_SS s1 x1 SS1 = close_SS_wrt_s_rec n1 x2 (ssubst_SS s1 x1 (open_SS_wrt_s_rec n1 (s_var_f x2) SS1)).
Proof.
pose proof ssubst_s_close_s_wrt_s_rec_open_s_wrt_s_rec_ssubst_SS_close_SS_wrt_s_rec_open_SS_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_close_SS_wrt_s_rec_open_SS_wrt_s_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma ssubst_F_close_F_wrt_s_rec_open_F_wrt_s_rec_mutual :
(forall F1 s1 x1 x2 n1,
  x2 `notin` sfv_F F1 ->
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  degree_s_wrt_s n1 s1 ->
  ssubst_F s1 x1 F1 = close_F_wrt_s_rec n1 x2 (ssubst_F s1 x1 (open_F_wrt_s_rec n1 (s_var_f x2) F1))).
Proof.
apply_mutual_ind F_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma ssubst_F_close_F_wrt_s_rec_open_F_wrt_s_rec :
forall F1 s1 x1 x2 n1,
  x2 `notin` sfv_F F1 ->
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  degree_s_wrt_s n1 s1 ->
  ssubst_F s1 x1 F1 = close_F_wrt_s_rec n1 x2 (ssubst_F s1 x1 (open_F_wrt_s_rec n1 (s_var_f x2) F1)).
Proof.
pose proof ssubst_F_close_F_wrt_s_rec_open_F_wrt_s_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_close_F_wrt_s_rec_open_F_wrt_s_rec : lngen.

(* end hide *)

Lemma ssubst_s_close_s_wrt_s_open_s_wrt_s :
forall s2 s1 x1 x2,
  x2 `notin` sfv_s s2 ->
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  lc_s s1 ->
  ssubst_s s1 x1 s2 = close_s_wrt_s x2 (ssubst_s s1 x1 (open_s_wrt_s s2 (s_var_f x2))).
Proof.
unfold close_s_wrt_s; unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_s_close_s_wrt_s_open_s_wrt_s : lngen.

Lemma ssubst_SS_close_SS_wrt_s_open_SS_wrt_s :
forall SS1 s1 x1 x2,
  x2 `notin` sfv_SS SS1 ->
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  lc_s s1 ->
  ssubst_SS s1 x1 SS1 = close_SS_wrt_s x2 (ssubst_SS s1 x1 (open_SS_wrt_s SS1 (s_var_f x2))).
Proof.
unfold close_SS_wrt_s; unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_SS_close_SS_wrt_s_open_SS_wrt_s : lngen.

Lemma ssubst_F_close_F_wrt_s_open_F_wrt_s :
forall F1 s1 x1 x2,
  x2 `notin` sfv_F F1 ->
  x2 `notin` sfv_s s1 ->
  x2 <> x1 ->
  lc_s s1 ->
  ssubst_F s1 x1 F1 = close_F_wrt_s x2 (ssubst_F s1 x1 (open_F_wrt_s F1 (s_var_f x2))).
Proof.
unfold close_F_wrt_s; unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_F_close_F_wrt_s_open_F_wrt_s : lngen.

Lemma ssubst_s_s_lam :
forall x2 SS1 s2 s1 x1,
  lc_s s1 ->
  x2 `notin` sfv_s s1 `union` sfv_s s2 `union` singleton x1 ->
  ssubst_s s1 x1 (s_lam SS1 s2) = s_lam (ssubst_SS s1 x1 SS1) (close_s_wrt_s x2 (ssubst_s s1 x1 (open_s_wrt_s s2 (s_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve ssubst_s_s_lam : lngen.

Lemma ssubst_SS_SS_refinement :
forall x2 B1 s2 s1 x1,
  lc_s s1 ->
  x2 `notin` sfv_s s1 `union` sfv_s s2 `union` singleton x1 ->
  ssubst_SS s1 x1 (SS_refinement B1 s2) = SS_refinement (B1) (close_s_wrt_s x2 (ssubst_s s1 x1 (open_s_wrt_s s2 (s_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve ssubst_SS_SS_refinement : lngen.

Lemma ssubst_SS_SS_darrow :
forall x2 SS1 SS2 s1 x1,
  lc_s s1 ->
  x2 `notin` sfv_s s1 `union` sfv_SS SS2 `union` singleton x1 ->
  ssubst_SS s1 x1 (SS_darrow SS1 SS2) = SS_darrow (ssubst_SS s1 x1 SS1) (close_SS_wrt_s x2 (ssubst_SS s1 x1 (open_SS_wrt_s SS2 (s_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve ssubst_SS_SS_darrow : lngen.

(* begin hide *)

Lemma ssubst_s_intro_rec_ssubst_SS_intro_rec_mutual :
(forall s1 x1 s2 n1,
  x1 `notin` sfv_s s1 ->
  open_s_wrt_s_rec n1 s2 s1 = ssubst_s s2 x1 (open_s_wrt_s_rec n1 (s_var_f x1) s1)) /\
(forall SS1 x1 s1 n1,
  x1 `notin` sfv_SS SS1 ->
  open_SS_wrt_s_rec n1 s1 SS1 = ssubst_SS s1 x1 (open_SS_wrt_s_rec n1 (s_var_f x1) SS1)).
Proof.
apply_mutual_ind s_SS_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_s_intro_rec :
forall s1 x1 s2 n1,
  x1 `notin` sfv_s s1 ->
  open_s_wrt_s_rec n1 s2 s1 = ssubst_s s2 x1 (open_s_wrt_s_rec n1 (s_var_f x1) s1).
Proof.
pose proof ssubst_s_intro_rec_ssubst_SS_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_s_intro_rec : lngen.
Hint Rewrite ssubst_s_intro_rec using solve [auto] : lngen.

Lemma ssubst_SS_intro_rec :
forall SS1 x1 s1 n1,
  x1 `notin` sfv_SS SS1 ->
  open_SS_wrt_s_rec n1 s1 SS1 = ssubst_SS s1 x1 (open_SS_wrt_s_rec n1 (s_var_f x1) SS1).
Proof.
pose proof ssubst_s_intro_rec_ssubst_SS_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_SS_intro_rec : lngen.
Hint Rewrite ssubst_SS_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma ssubst_F_intro_rec_mutual :
(forall F1 x1 s1 n1,
  x1 `notin` sfv_F F1 ->
  open_F_wrt_s_rec n1 s1 F1 = ssubst_F s1 x1 (open_F_wrt_s_rec n1 (s_var_f x1) F1)).
Proof.
apply_mutual_ind F_mutind;
default_simp.
Qed.

(* end hide *)

Lemma ssubst_F_intro_rec :
forall F1 x1 s1 n1,
  x1 `notin` sfv_F F1 ->
  open_F_wrt_s_rec n1 s1 F1 = ssubst_F s1 x1 (open_F_wrt_s_rec n1 (s_var_f x1) F1).
Proof.
pose proof ssubst_F_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ssubst_F_intro_rec : lngen.
Hint Rewrite ssubst_F_intro_rec using solve [auto] : lngen.

Lemma ssubst_s_intro :
forall x1 s1 s2,
  x1 `notin` sfv_s s1 ->
  open_s_wrt_s s1 s2 = ssubst_s s2 x1 (open_s_wrt_s s1 (s_var_f x1)).
Proof.
unfold open_s_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_s_intro : lngen.

Lemma ssubst_SS_intro :
forall x1 SS1 s1,
  x1 `notin` sfv_SS SS1 ->
  open_SS_wrt_s SS1 s1 = ssubst_SS s1 x1 (open_SS_wrt_s SS1 (s_var_f x1)).
Proof.
unfold open_SS_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_SS_intro : lngen.

Lemma ssubst_F_intro :
forall x1 F1 s1,
  x1 `notin` sfv_F F1 ->
  open_F_wrt_s F1 s1 = ssubst_F s1 x1 (open_F_wrt_s F1 (s_var_f x1)).
Proof.
unfold open_F_wrt_s; default_simp.
Qed.

Hint Resolve ssubst_F_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto := auto; tauto.
Ltac default_autorewrite := fail.
