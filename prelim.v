Add LoadPath "../../provers/metalib/trunk".

Set Implicit Arguments.

Require Export Metatheory.
Require Export terms.
Require Export infrastructure.

Axiom denot_q : forall k k',
  (exists k'', denot k k' = s_const k'') \/ (exists l, denot k k' = s_blame (b_blame l)).

Lemma lc_denot : forall k k', lc_s (denot k k').
Proof.
  intros.  
  destruct (denot_q k k') as [[ k'' EQ] | [l EQ] ].
  rewrite EQ. auto.
  rewrite EQ. auto.
Qed.

Lemma denot_closed : forall k k', 
   forall x, x `notin` sfv_s (denot k k').
Proof.
  intros.  
  destruct (denot_q k k') as [[k'' EQ] | [ l EQ]]; rewrite EQ; auto.
Qed.

Hint Extern 1 (lc_s (denot _ _)) => 
  apply lc_denot; auto. 

Notation "s1 ~~>h s2" := (reduceh s1 s2) (at level 68).
Notation "s1 -->h s2" := (steph s1 s2) (at level 68).
Notation "s1 -->h* s2" := (evalh s1 s2) (at level 68).
Notation "s1 ==>s s2" := (parreds s1 s2) (at level 68).
Notation "s1 ==>s* s2" := (parredsrs s1 s2) (at level 68).
Notation "SS1 ==>S SS2" := (parredSS SS1 SS2) (at level 68).
Notation "SS1 ==>S* SS2" := (parredSrs SS1 SS2) (at level 68).

Notation "< SS1 => SS2 > l " := (s_cast SS1 SS2 l) (at level 69).
Notation "< SS1 , s1 , k > l " := (s_check SS1 s1 k l) (at level 68).
Notation "SS [:= s ]" := (open_SS_wrt_s SS s) (at level 68).
Notation "s1 [: s2 ]" := (open_s_wrt_s s1 s2) (at level 30).
Notation "SS1 :-> SS2" := (SS_darrow SS1 SS2) (at level 68).

(***********************************************)

Ltac gather_atoms :=
  let A := ltac_map (fun x : vars => x) in
  let B := ltac_map (fun x : var => {{x}}) in
  let D := ltac_map (fun x => sfv_s x) in
  let E := ltac_map (fun x => sfv_SS x) in
  let F := ltac_map (fun x => sfv_F x) in
  simplify_list_of_atom_sets (A ++ B ++ D ++ E ++ F).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(***********************************************)								    
Scheme parreds_ind := Induction for parreds Sort Prop
  with parredSS_ind := Induction for parredSS Sort Prop.

Combined Scheme parred_ind from parreds_ind, parredSS_ind.

(***********************************************)						

Lemma FS_inversion : forall SS,
  is_FS_of_SS SS ->
  exists S1, exists S2, SS = S1 :-> S2.
Proof.
intros. destruct SS; try solve by inversion; eauto.
Qed.

Lemma h_inversion : forall h,
  is_h_of_s h ->
  exists SS11, exists SS12, 
  exists SS21, exists SS22,
  exists l,
    h = s_cast (SS11 :-> SS12) (SS21 :-> SS22) l.
Proof.
intros. destruct h; try solve by inversion.
simpl in H. destruct H as [H1 H2].
apply FS_inversion in H1. apply FS_inversion in H2.
destruct H1 as [SS11 [SS12 Heqs]]. destruct H2 as [SS21 [SS22 Heqs0]].
subst s s0. exists SS11. exists SS12. exists SS21. exists SS22. exists l.
reflexivity.
Qed.

Lemma w_inversion : forall w,
  is_w_of_s w ->
  (exists k, w = s_const k) \/
  (exists SS1, exists s12, w = s_lam SS1 s12) \/
  (exists SS1, exists SS2, exists l, w = s_cast SS1 SS2 l) \/
  (exists SS11, exists SS12, exists SS21, exists SS22, exists l, exists w2,
    w = s_app (s_cast (SS11 :-> SS12) (SS21 :-> SS22) l) w2 /\
    is_w_of_s w2).
Proof.
intros. destruct w; try solve by inversion; simpl in H; eauto.
Case "applied cast".
  destruct H as [Hh1 Hw2]. right. right. right.
  apply h_inversion in Hh1.
  destruct Hh1 as [SS11 [SS12 [SS21 [SS22 [l Heqw1]]]]]. subst w1.
  exists SS11. exists SS12. exists SS21. exists SS22. exists l. exists w2.
  auto.
Case "cast".
  right. right. left. exists s. exists s0. exists l. auto.
Qed.

Lemma q_inversion : forall q,
  is_q_of_s q ->
  is_w_of_s q \/ 
  (exists l, q = s_blame (b_blame l)).
Proof.
intros. destruct q; try solve by inversion; eauto. destruct b; eauto.
Qed.

Lemma sfv_SS_open_SS_wrt_s : forall w SS x,
  x `notin` sfv_s w ->
  x `notin` sfv_SS (SS [:=w]) ->
  x `notin` sfv_SS SS.
Proof.
intros. induction SS.
Case "SS_refinement".
  simpl in H0. simpl.
  assert (sfv_s s [<=] sfv_s (open_s_wrt_s_rec 1 w s)).
    apply sfv_s_open_s_wrt_s_rec_lower.
  auto.
Case "SS_arrow".
  simpl in H0. simpl.
  assert (sfv_SS SS1 [<=] sfv_SS (open_SS_wrt_s_rec 0 w SS1)).
    apply sfv_SS_open_SS_wrt_s_rec_lower.
  assert (sfv_SS SS2 [<=] sfv_SS (open_SS_wrt_s_rec 1 w SS2)).
    apply sfv_SS_open_SS_wrt_s_rec_lower.
  assert (x `notin` sfv_SS SS1) by auto.
  assert (x `notin` sfv_SS SS2) by auto.
  auto.
Qed.

Lemma sfv_s_open_s_wrt_s : forall w s x,
  x `notin` sfv_s w ->
  x `notin` sfv_s (s [:w]) ->
  x `notin` sfv_s s.
Proof.
intros. induction s; auto; simpl in H0; simpl.
Case "s_lam".
  rename s into SS1. rename s0 into s12.
  assert (sfv_SS SS1 [<=] sfv_SS (open_SS_wrt_s_rec 0 w SS1)).
    apply sfv_SS_open_SS_wrt_s_rec_lower.
  assert (sfv_s s12 [<=] sfv_s (open_s_wrt_s_rec 1 w s12)).
    apply sfv_s_open_s_wrt_s_rec_lower.
  assert (x `notin` sfv_SS SS1) by auto.
  assert (x `notin` sfv_s s12) by auto.
  auto.
Case "s_app".
  assert (x `notin` sfv_s s1) by auto.
  assert (x `notin` sfv_s s2) by auto.
  auto.
Case "s_cast".
  rename s into SS1. rename s0 into SS2.
  assert (sfv_SS SS1 [<=] sfv_SS (open_SS_wrt_s_rec 0 w SS1)).
    apply sfv_SS_open_SS_wrt_s_rec_lower.
  assert (sfv_SS SS2 [<=] sfv_SS (open_SS_wrt_s_rec 0 w SS2)).
    apply sfv_SS_open_SS_wrt_s_rec_lower.
  assert (x `notin` sfv_SS SS1) by auto.
  assert (x `notin` sfv_SS SS2) by auto.
  auto.
Case "s_check".
  rename s into SS1. rename s0 into s2.
  assert (sfv_SS SS1 [<=] sfv_SS (open_SS_wrt_s_rec 0 w SS1)).
    apply sfv_SS_open_SS_wrt_s_rec_lower.
  assert (sfv_s s2 [<=] sfv_s (open_s_wrt_s_rec 0 w s2)).
    apply sfv_s_open_s_wrt_s_rec_lower.
  assert (x `notin` (sfv_SS SS1)) by auto.
  assert (x `notin` (sfv_s s2)) by auto.
  auto.
Qed.

Lemma lc_reduceh : forall s1 s2, 
  s1 ~~>h s2 -> lc_s s1 /\ lc_s s2.
Proof.
intros. induction H; intros; split; subst; auto.
Case "F_RBeta2". 
  inversion H0.
  pick_fresh x1.
  rewrite (ssubst_s_intro x1).
  apply ssubst_s_lc_s. auto. auto. auto.
Case "F_RCCheck".
  inversion H1. subst.
  pick_fresh x1.
  apply lc_s_check. auto.
  rewrite (ssubst_s_intro x1); auto.
  apply ssubst_s_lc_s; auto.
Case "F_RCCDecomp2".
  pick_fresh x1.
  inversion H3. subst.
  inversion H4. subst.
  apply lc_s_app. apply lc_s_cast.
  rewrite (ssubst_SS_intro x1); auto.
  apply ssubst_SS_lc_SS; auto.
  rewrite (ssubst_SS_intro x1); auto.
  apply ssubst_SS_lc_SS; auto.
  apply lc_s_app; auto. 
Qed.

Lemma lc_steph : forall s1 s2, s1 -->h s2 -> lc_s s1 /\ lc_s s2.
Proof.
intros. induction H.
Case "F_Reduce".
  apply lc_reduceh; auto.
Case "F_Compat".
inversion H; inversion IHsteph; subst; simpl; split; auto.
Case "F_Blame".
inversion H; subst; simpl; auto.
Qed.

Lemma lc_evalh : forall s1 s2, s1 -->h* s2 -> lc_s s1 /\ lc_s s2.
Proof.
intros. induction H. 
Case "F_Refl".
  auto.
Case "F_Step".
  destruct IHevalh. split; eauto. destruct (lc_steph H). auto.
Qed.

Definition lc_parreds_def s1 s2 (d: s1 ==>s s2) := lc_s s1 /\ lc_s s2.
Definition lc_parredSS_def SS1 SS2 (d : SS1 ==>S SS2) := 
  lc_SS SS1 /\ lc_SS SS2.
Lemma lc_parred : 
  (forall s1 s2 d, @lc_parreds_def s1 s2 d) /\
  (forall SS1 SS2 d, @lc_parredSS_def SS1 SS2 d).
Proof.
apply (parred_ind lc_parreds_def lc_parredSS_def); 
   unfold lc_parreds_def, lc_parredSS_def; 
   intros; split; subst; auto; intuition.
Case "P_RBeta1".
  apply lc_s_app. 
  pick_fresh x1; eapply (lc_s_lam_exists x1); auto.
  destruct (H x1); auto. auto.
Case "P_RBeta22".
    pick_fresh x1. 
    rewrite (ssubst_s_intro x1).
    apply ssubst_s_lc_s. destruct (H x1); auto. auto. auto.
Case "P_RCCheck1". 
  apply lc_s_app.
  apply lc_s_cast. auto. 
  pick_fresh x1.
  apply (lc_SS_refinement_exists x1). destruct (H x1); auto.
  auto.
Case "P_RCCheck2".
  apply lc_s_check.
  pick_fresh x1.
  apply (lc_SS_refinement_exists x1). destruct (H x1); auto.
  pick_fresh x1.
  rewrite (ssubst_s_intro x1).
  apply ssubst_s_lc_s. destruct (H x1); auto. auto. auto.
Case "P_RCDecomp1".
  apply lc_s_app. 
  apply lc_s_app.
  apply lc_s_cast.
  pick_fresh x1.
  apply (lc_SS_darrow_exists x1). auto. 
  apply (H0 x1). auto.
  pick_fresh x1.
  apply (lc_SS_darrow_exists x1). auto.
  apply (H2 x1). auto.
  auto. auto.
Case "P_RCDecomp2".
  apply lc_s_app.
  apply lc_s_cast.
  pick_fresh x1.
  rewrite (ssubst_SS_intro x1).
  apply ssubst_SS_lc_SS. destruct (H0 x1). auto. auto.
  auto. auto.
  pick_fresh x1.
  rewrite (ssubst_SS_intro x1).
  apply ssubst_SS_lc_SS. destruct (H2 x1). auto. auto.
  auto. auto.
  apply lc_s_app; auto.
Case "P_Lam1".
  pick_fresh x1.
  destruct (H0 x1); auto.
  apply (lc_s_lam_exists x1); auto.
Case "P_Lam2".
  pick_fresh x1.
  destruct (H0 x1); auto.
  apply (lc_s_lam_exists x1); auto.
Case "P_Blame".
  inversion v; subst; simpl; auto.
Case "P_SSRefine".
  pick_fresh x1.
  destruct (H x1); auto.
  apply (lc_SS_refinement_exists x1); auto.
Case "P_SSRefine2".
  pick_fresh x1.
  destruct (H x1); auto.
  apply (lc_SS_refinement_exists x1); auto.
Case "P_SSFun1".
  pick_fresh x1.
  destruct (H0 x1); auto.
  apply (lc_SS_darrow_exists x1); auto.
Case "P_SSFun2".
  pick_fresh x1.
  destruct (H0 x1); auto.
  apply (lc_SS_darrow_exists x1); auto.
Qed.

Lemma lc_parreds : forall s1 s2, s1 ==>s s2 -> lc_s s1 /\ lc_s s2.
Proof.
destruct lc_parred. auto. 
Qed.

Lemma lc_parredSS : forall SS1 SS2, SS1 ==>S SS2 -> lc_SS SS1 /\ lc_SS SS2.
Proof.
destruct lc_parred. auto.
Qed.

Hint Extern 1 (lc_s ?s1) =>
  match goal with  
 | H: parreds s1 _ |- _ => apply (proj1 (lc_parreds H))
 | H: parreds _ s1 |- _ => apply (proj2 (lc_parreds H))
 | H: steph   s1 _ |- _ => apply (proj1 (lc_steph H))
 | H: steph   _ s1 |- _ => apply (proj2 (lc_steph H))
 | H: reduceh s1 _ |- _ => apply (proj1 (lc_reduceh H))
 | H: reduceh _ s1 |- _ => apply (proj2 (lc_reduceh H))
 | H: evalh s1 _ |- _ => apply (proj1 (lc_evalh H))
 | H: evalh _ s1 |- _ => apply (proj2 (lc_evalh H))
 end.

Hint Extern 1 (lc_SS ?s1) =>
  match goal with  
 | H: parredSS s1 _ |- _ => apply (proj1 (lc_parredSS H))
 | H: parredSS _ s1 |- _ => apply (proj2 (lc_parredSS H))
 end.


Hint Extern 1 (lc_B ?s1) => unfold lc_B; auto.

Hint Extern 1 (lc_k ?s1) => unfold lc_k; auto.

(***************************************************)

Lemma parreds_trans : forall s1 s2, s1 ==>s* s2 -> forall s3, s2 ==>s* s3 -> s1 ==>s* s3.
Proof.
induction 1; eauto. 
Qed.

Lemma parredSS_trans : forall s1 s2, s1 ==>S* s2 -> forall s3, s2 ==>S* s3 -> s1 ==>S* s3.
Proof.
induction 1; eauto. 
Qed.


Lemma evalh_trans : forall s1 s2, s1 -->h* s2 -> forall s3, s2 -->h* s3 -> s1 -->h* s3.
Proof.
induction 1; eauto. 
Qed.

Lemma ssubst_FS : forall s1 x SS, is_FS_of_SS SS -> is_FS_of_SS (ssubst_SS s1 x SS).
Proof.
intros. destruct SS; try solve by inversion. auto.
Qed.

Lemma ssubst_h : forall s1 x h, is_h_of_s h -> is_h_of_s (ssubst_s s1 x h).
Proof.
intros. destruct h; simpl in *; auto. contradiction.
destruct H. auto using ssubst_FS. 
Qed.

Lemma ssubst_w : forall s1 x w, is_w_of_s w -> is_w_of_s (ssubst_s s1 x w).
Proof.
intros. induction w; simpl in *; auto. contradiction.
destruct w1; simpl in *; try intuition.
destruct s; simpl in *. auto. auto. destruct s0; simpl in *. auto. auto.
Qed.

Lemma ssubst_q : forall s1 x q, is_q_of_s q -> is_q_of_s (ssubst_s s1 x q).
Proof.
intros. induction q; simpl in *; auto. contradiction.
destruct q1; simpl in *; try intuition.
destruct s; simpl in *. auto. auto. destruct s0; simpl in *. auto. auto.
apply ssubst_w; auto.
Qed.

Lemma ssubst_valid : forall F w x, valid_ctx F -> lc_s w -> valid_ctx (ssubst_F w x F).
Proof.
intros. inversion H; subst.
Case "F_appl".
  simpl. apply valid_appl. apply ssubst_s_lc_s; auto.
Case "F_appr".
  simpl. apply valid_appr.
  apply ssubst_w; auto. apply ssubst_w; auto.
  apply ssubst_s_lc_s; auto.
Case "F_check".
  simpl. apply valid_check; try assumption.
  apply ssubst_SS_lc_SS; auto.
Qed.

Lemma ssubst_Fplug : forall F w x s, lc_s w -> valid_ctx F -> 
  ssubst_s w x (Fplug F s) = Fplug (ssubst_F w x F) (ssubst_s w x s).
Proof.
intros.
inversion H0; subst; auto.
Qed.

Lemma ssubst_FS_inversion : forall w x SS,
  is_FS_of_SS (ssubst_SS w x SS) -> is_FS_of_SS SS.
Proof.
intros. destruct SS; try solve by inversion; auto.
Qed.

Lemma ssubst_h_inversion : forall w x s,
  is_h_of_s (ssubst_s w x s) ->
  is_h_of_s s \/ (s = s_var_f x /\ is_h_of_s w).
Proof.
intros. destruct s; subst; try solve by inversion.
Case "s_var_f".
  right.
  simpl in H. destruct (x0 == x); try solve by inversion.
  subst. auto.
Case "s_cast".
  left. rename s into SS1. rename s0 into SS2.
  simpl in H. destruct H.
  apply ssubst_FS_inversion in H. apply ssubst_FS_inversion in H0.
  simpl. auto.
Qed.

Lemma ssubst_w_inversion : forall w x s,
  is_w_of_s (ssubst_s w x s) ->
  is_w_of_s w ->
  is_w_of_s s \/ 
  s = s_var_f x \/ 
  (exists s2, s = s_app (s_var_f x) s2 /\ is_h_of_s w /\ is_w_of_s (ssubst_s w x s2)) \/
  (exists s1, exists s2, s = s_app s1 s2 /\ is_h_of_s s1 /\ is_w_of_s (ssubst_s w x s2)).
Proof.
intros. induction s; try solve by inversion; try auto.
Case "s_var_f".
  right. left.
  simpl in H. destruct (x0 == x); try solve by inversion. subst. auto.
Case "s_app".
  right. right.
  simpl in H. destruct H as [Hh Hw].
  apply ssubst_h_inversion in Hh. clear IHs1. apply IHs2 in Hw; clear IHs2.
  destruct Hh.
  SCase "s1 is funcast".
    right.
    destruct Hw as [Hw | 
                   [Hw | 
                   [[s22 [Heqs2 [Hh Hw]]] | 
                   [s21 [s22 [Heqs2 [Hhs21 Hws22]]]]]]]; subst; exists s1.
    SSCase "s2 is w".
      exists s2. auto using ssubst_w.
    SSCase "s2 is x".
      exists (s_var_f x).
      replace (ssubst_s w x (s_var_f x)) with w by default_simp.
      auto.
    SSCase "s2 is (s_app x s22)".
      exists (s_app (s_var_f x) s22).
      default_simp.
    SSCase "s2 is (s_app s21 s22)".
      exists (s_app s21 s22).
      default_simp. auto using ssubst_h.
  SCase "s1 is a var".
    left.
    destruct H as [Heqs1 Hww]. subst.
    exists s2. split; auto. split; auto.
    destruct Hw as [Hw | 
                   [Hw | 
                   [[s22 [Heqs2 [Hh Hw]]] | 
                   [s21 [s22 [Heqs2 [Hhs21 Hws22]]]]]]]; subst; default_simp;
    auto using ssubst_w, ssubst_h.
Qed.    

Lemma reduceh_deterministic : forall s1 s2 s3, s1 ~~>h s2 -> s1 ~~>h s3 -> s2 = s3.
Proof with reflexivity.
intros.
inversion H; inversion H0; subst; auto; try solve by inversion.
Case "F_RConst".
  inversion H7; subst...
Case "F_RBeta".
  inversion H9; subst...
Case "F_RCCheck".
  inversion H9; subst...
Case "F_ROK".
  inversion H7; subst...
Case "F_RFail".
  inversion H7; subst...
Case "F_RCDecomp".
  inversion H17; subst...
Qed.

Lemma h_is_w : forall s, is_h_of_s s -> is_w_of_s s.
Proof.
  intros. destruct s; try solve by inversion.
  simpl. auto.
Qed.  

Lemma w_is_q : forall s, is_w_of_s s -> is_q_of_s s.
Proof.
  intros. destruct s; simpl; auto.
Qed.

Lemma h_is_q : forall h, is_h_of_s h -> is_q_of_s h.
Proof.
intros. auto using w_is_q, h_is_w.
Qed.


Lemma results_dont_reduce : forall s1 s2, is_q_of_s s1 -> ~(s1 ~~>h s2).
Proof.
intros. intros C.
destruct s1; try solve by inversion.
Case "s_app".
  simpl in H. destruct H as [H1 H2].
  inversion C; subst; try solve by inversion.
  simpl in H1. destruct H1; auto.
Qed.  

Lemma results_dont_step : forall s1 s2, is_q_of_s s1 -> ~(s1 -->h s2).
Proof.
intro s1. induction s1; intros; intros C; try solve by inversion.
Case "const".
  inversion C; subst; try solve by inversion;
    destruct F5; solve by inversion.
Case "lambda".
  inversion C; subst; try solve by inversion;
    destruct F5; solve by inversion.
Case "app".
  inversion C; subst.
  SCase "F_Reduce".
    eapply results_dont_reduce; eauto.
  SCase "F_Compat".
    destruct F5; try solve by inversion.
    SSCase "F_appl".
      simpl in H. destruct H as [Hs11 Hs12].
      simpl in H0. inversion H0; subst.
      destruct s1_1; try solve by inversion.
      apply h_is_w in Hs11.
      eapply IHs1_1; eauto.
    SSCase "F_appr".
      simpl in H. destruct H as [Hs11 Hs12].
      simpl in H0. inversion H0; subst.
      apply w_is_q in Hs12.
      eapply IHs1_2; eauto.
  SCase "F_Blame".
    destruct F5; try solve by inversion.
    SSCase "F_appl".
      simpl in H. destruct H as [Hs11 Hs12].
      simpl in H0. inversion H0; subst.
      inversion Hs11.
    SSCase "F_appr".
      simpl in H. destruct H as [Hs11 Hs12].
      simpl in H0. inversion H0; subst.
      inversion Hs12.
Case "blame".
  inversion C; subst.
  SCase "F_Reduce".
    eapply results_dont_reduce; eauto.
  SCase "F_Compat".
    destruct F5; try solve by inversion.
  SCase "F_Blame".
    destruct F5; try solve by inversion.
Case "cast".
  inversion C; subst.
  SCase "F_Reduce".
    eapply results_dont_reduce; eauto.
  SCase "F_Compat".
    destruct F5; try solve by inversion.
  SCase "F_Blame".
    destruct F5; try solve by inversion.
Qed.

Lemma compat_noreduce : forall F s1 s2 s3, Fplug F s1 ~~>h s2 -> ~(s1 ~~>h s3).
Proof.
intros. intro C. destruct F.
Case "F_appl".
  inversion H; subst; try solve by inversion.
Case "F_appr".
  inversion H; subst; try solve by inversion.
  SCase "F_RBeta".
    apply w_is_q in H2.
    apply (results_dont_reduce H2 C).
  SCase "F_CCheck".
    apply w_is_q in H3.
    apply (results_dont_reduce H3 C).
Case "F_check".
  inversion H; subst; try solve by inversion.
Qed.

Lemma compat_nostep : forall F s1 s2 s3, Fplug F s1 ~~>h s2 -> ~(s1 -->h s3).
Proof.
intros. intro C. destruct F.
Case "F_appl".
  inversion H; subst.
  SCase "F_RConst".
    assert (is_q_of_s (s_const k5)) by auto.
    eapply (results_dont_step H0 C).
  SCase "F_RBeta".
    assert (is_q_of_s (s_lam SS5 s12)) by (simpl; auto).
    apply (results_dont_step H0 C).
  SCase "F_RCCheck".
    assert (is_q_of_s (s_cast (SS_refinement B5 s0) (SS_refinement B5 s4) l5)) by (simpl; auto).
    apply (results_dont_step H0 C).
  SCase "F_RCDecomp".
    assert (is_q_of_s (s_app (s_cast (SS11 :-> SS12) (SS21 :-> SS22) l5) w5)) by (simpl; auto).
    apply (results_dont_step H0 C).
Case "F_appr".
  inversion H; subst.
  SCase "F_RConst".
    assert (is_q_of_s (s_const k')) by auto.
    eapply (results_dont_step H0 C).
  SCase "F_RBeta".
    apply w_is_q in H2.
    apply (results_dont_step H2 C).
  SCase "F_RCCheck".
    assert (is_q_of_s (s_const k5)) by auto.
    apply (results_dont_step H0 C).
  SCase "F_RCDecomp".
    apply w_is_q in H3.
    apply (results_dont_step H3 C).
Case "F_check".
  inversion H; subst.
  SCase "F_ROK".
    assert (is_q_of_s (s_const k_true)) by auto.
    apply (results_dont_step H0 C).
  SCase "F_RFail".
    assert (is_q_of_s (s_const k_false)) by auto.
    apply (results_dont_step H0 C).
Qed.

Lemma plug_blame_doesnt_reduce : forall F l s, valid_ctx F -> ~(Fplug F (s_blame (b_blame l)) ~~>h s).
Proof.
intros. intro C.
inversion C; inversion H; subst; simpl in H0; try solve by inversion.
Case "F_RBeta".
  inversion H0; subst. inversion H1.
Case "F_RCDecomp".
  inversion H0; subst. inversion H2.
Qed.  

Lemma steph_deterministic : forall s1 s2 s3, s1 -->h s2 -> s1 -->h s3 -> s2 = s3.
Proof.
intros. generalize dependent s3.
induction H; intros.
Case "F_Reduce".
  inversion H0; subst.
  SCase "F_Reduce".
    apply reduceh_deterministic with s1; auto.
  SCase "F_Compat".
    assert False as C by (apply (compat_nostep F5 H H2)).
    inversion C.
  SCase "F_Blame".
    inversion H; subst; destruct F5; simpl in H2; inversion H2; subst.
    SSCase "F_RBeta".
      inversion H3.
    SSCase "F_RCDecomp".
      inversion H4.
Case "F_Compat".
  remember (Fplug F5 s1) as s.
  inversion H1; subst.
  SCase "F_Reduce".
    assert False as C by (apply (compat_nostep F5 H2 H0)).
    inversion C.
  SCase "F_Compat".
    inversion H; subst;
    inversion H2; subst; 
    try solve by inversion; simpl in H4; inversion H4; subst.
    SSCase "F_appl".
      SSSCase "F_appl".
        assert (s2 = s4) by (apply (IHsteph s4 H3)).
        subst. reflexivity.
      SSSCase "F_appr".
        apply w_is_q in H7.
        assert False as C by (apply (results_dont_step H7 H0)).
        inversion C.
    SSCase "F_appr".
      SSSCase "F_appl".
        apply w_is_q in H6.
        assert False as C by (apply (results_dont_step H6 H3)).
        inversion C.
      SSSCase "F_appr".
        assert (s2 = s4) by (apply (IHsteph s4 H3)).
        subst. reflexivity.
    SSCase "F_check".
      SSSCase "F_check".
        assert (s2 = s4) by (apply (IHsteph s4 H3)).
        subst. reflexivity.
  SCase "F_Blame".
    assert (is_q_of_s (s_blame (b_blame l5))) by (simpl; auto).
    inversion H; subst;
    inversion H2; subst; 
    try solve by inversion; simpl in H3; inversion H3; subst.
    SSCase "F_appl".
      SSSCase "F_appl".
        assert False as C by (apply (results_dont_step H4 H0)).
        inversion C.
      SSSCase "F_appr".
        apply w_is_q in H6.
        assert False as C by (apply (results_dont_step H6 H0)).
        inversion C.
    SSCase "F_appr".
      SSSCase "F_appl".
        inversion H5.
      SSSCase "F_appr".
        assert False as C by (apply (results_dont_step H4 H0)).
        inversion C.
    SSCase "F_check".
      SSSCase "F_check".
        assert False as C by (apply (results_dont_step H4 H0)).
        inversion C.
Case "F_Blame".
  remember (Fplug F5 (s_blame (b_blame l5))) as s1.
  assert (is_q_of_s (s_blame (b_blame l5))) by (simpl; auto).
  inversion H0; subst.
  SCase "F_Reduce".
    assert False as C by (apply (plug_blame_doesnt_reduce l5 H H2)).
    inversion C.
  SCase "F_Compat".
    inversion H; subst;
    inversion H2; subst;
    try solve by inversion; simpl in H4; inversion H4; subst.
    SSCase "F_appl".
      SSSCase "F_appl".
        assert False as C by (apply (results_dont_step H1 H3)).
        inversion C.
      SSSCase "F_appr".
        inversion H6.
    SSCase "F_appr".
      SSSCase "F_appl".
        apply w_is_q in H6.
        assert False as C by (apply (results_dont_step H6 H3)).
        inversion C.
      SSSCase "F_appr".
        assert False as C by (apply (results_dont_step H1 H3)).
        inversion C.
    SSCase "F_check".
      SSSCase "F_check".
        assert False as C by (apply (results_dont_step H1 H3)).
        inversion C.
  SCase "F_Blame".
    inversion H; subst;
    inversion H2; subst;
    try solve by inversion; 
    simpl in H3; inversion H3; subst; 
    try reflexivity; solve by inversion.
Qed.

