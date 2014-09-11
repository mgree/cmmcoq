Add LoadPath "../../provers/metalib/trunk".

Set Implicit Arguments.

Require Import prelim.

(***************************************************)

Definition A1_s sa (lc : lc_s sa) := forall s1 s2 x,  
  ( s1 ==>s s2 ) -> ssubst_s s1 x sa ==>s ssubst_s s2 x sa.
Definition A1_SS SSa (lc : lc_SS SSa) := forall s1 s2 x, 
  ( s1 ==>s s2 ) -> ssubst_SS s1 x SSa ==>S ssubst_SS s2 x SSa.
	  
Lemma A1 : 
  (forall sa lc, @A1_s sa lc) /\ (forall SSa lc, @A1_SS SSa lc).
Proof.
apply (lc_s_lc_SS_mutind A1_s A1_SS); unfold A1_s, A1_SS; simpl; intros; auto.
Case "lc_var". 
  destruct (x5 == x); auto. 
Case "lc_lam".
  pick fresh x1 and apply P_Lam. eauto. 
  rewrite ssubst_s_open_s_wrt_s_var; auto.
  rewrite ssubst_s_open_s_wrt_s_var; auto. 
Case "lc_refine".
  pick fresh x1 and apply P_SSRefine; auto.
  rewrite ssubst_s_open_s_wrt_s_var; auto. 
  rewrite ssubst_s_open_s_wrt_s_var; auto. 
Case "lc_arrow".
  pick fresh x1 and apply P_SSFun; auto. 
  rewrite ssubst_SS_open_SS_wrt_s_var; auto.
  rewrite ssubst_SS_open_SS_wrt_s_var; auto.
Qed.


(* This is not the same as in the appendix. It is a weaker property. I don't think 
   that the real A2 property holds. *)
(* WHAT LEMMAs are true about denotations of constants? *)
(*
Lemma A2 : forall w k' k,  is_w_of_s w -> 
  (s_app (s_const k) w) ==>s (denot k k') -> exists k'', w = s_const k'' /\ denot k k' = denot k k''.
intros.
inversion H0.
Case "Refl". 
  assert (J:= denot_w k k'). rewrite <- H1 in J. simpl in J. intuition.
Case "PRConst". subst. exists k'0. split; auto.
   inversion H6; subst; auto; simpl in H4; intuition.
Case "?".
  assert (J:= denot_w k k'). rewrite <- H3 in J. simpl in J. inversion H4. subst.
  simpl in J. intuition. subst. simpl in J. intuition.
Case "4".
  assert (J:= denot_w k k'). rewrite <- H2 in J. inversion J.
Qed.
*)

Lemma A2' : forall w k', is_w_of_s w ->  w ==>s (s_const k') -> w = s_const k'.
  intros.
  inversion H0; subst; simpl in H; auto; intuition. 
Qed.
	      
Definition A3_s s1 s2 (H: s1 ==>s s2) := forall w w' x,  
(*  is_w_of_s w -> is_w_of_s w' -> *)
  ( w ==>s w' ) -> ssubst_s w x s1 ==>s ssubst_s w' x s2.
Definition A3_SS SS1 SS2 (H : SS1 ==>S SS2) := forall w w' x, 
(*  is_w_of_s w -> is_w_of_s w' -> *)
  ( w ==>s w' ) -> ssubst_SS w x SS1 ==>S ssubst_SS w' x SS2.
	  
Lemma A3 : 
  (forall s1 s2 H, @A3_s s1 s2 H) /\ (forall SS1 SS2 H, @A3_SS SS1 SS2 H).
apply (parred_ind A3_s A3_SS); unfold A3_s, A3_SS; intros; auto.
Case "Refl".
  destruct A1. unfold A1_s in *. auto. 
Case "RConst".
  simpl in H.
  destruct (denot_q k5 k') as [ [ k1 EQ ] | [ l1 EQ ] ]; 
    rewrite EQ; simpl; rewrite <- EQ; eauto using ssubst_w.
Case "RBeta".
  rewrite ssubst_s_open_s_wrt_s; auto. simpl.
  eapply P_RBeta with (L:=L `union` singleton x); auto. 
  apply ssubst_w; auto.
  apply ssubst_w; auto.
  apply ssubst_SS_lc_SS; auto.
  intros. 
  rewrite ssubst_s_open_s_wrt_s_var; auto.
  rewrite ssubst_s_open_s_wrt_s_var; auto.
Case "RCCheck".
  simpl.
  rewrite ssubst_s_open_s_wrt_s; auto.
  eapply P_RCCheck with (L := L `union` singleton x); auto.
  replace (SS_refinement B5 (ssubst_s w x s1)) with (ssubst_SS w x (SS_refinement B5 s1)); auto.
  eapply ssubst_SS_lc_SS; auto. 
  intros. 
  rewrite ssubst_s_open_s_wrt_s_var; auto.
  rewrite ssubst_s_open_s_wrt_s_var; auto.
Case "ROK". 
  simpl.
  subst. eapply P_ROK; auto.
  apply ssubst_SS_lc_SS; auto. simpl. auto.
Case "RFail".
  simpl.
  subst.
  apply P_RFail; auto. 
  apply ssubst_SS_lc_SS. auto. auto.
Case "RCDecomp".
  simpl.
  rewrite ssubst_SS_open_SS_wrt_s.
  rewrite ssubst_SS_open_SS_wrt_s. simpl.
  apply P_RCDecomp with (L := L `union` singleton x)
          (SS12' := ssubst_SS w' x SS12') (SS22' := ssubst_SS w' x SS22'); auto; try (apply ssubst_w; auto).
  intros.
  rewrite ssubst_SS_open_SS_wrt_s_var; auto.
  rewrite ssubst_SS_open_SS_wrt_s_var; auto.
  intros.
  rewrite ssubst_SS_open_SS_wrt_s_var; auto.
  rewrite ssubst_SS_open_SS_wrt_s_var; auto.
  auto. auto.
Case "Lam".
  simpl.
  pick fresh x5 and apply P_Lam. auto.
  rewrite ssubst_s_open_s_wrt_s_var; auto.
  rewrite ssubst_s_open_s_wrt_s_var; auto.
Case "App".
  simpl. eauto.
Case "Cast".
  simpl. auto.
Case "Check". 
  simpl. auto.
Case "Blame".
  simpl.
  destruct (lc_parreds H) as [Hlcw Hlcw'].
  rewrite ssubst_Fplug; auto.
  eapply P_Blame.
  apply ssubst_valid; auto.
Case "P_SsRefl".
  destruct A1. unfold A1_SS in *. auto. 
Case "P_Refine".
  pick fresh x1 and apply P_SSRefine; auto.
  rewrite ssubst_s_open_s_wrt_s_var; auto.
  rewrite ssubst_s_open_s_wrt_s_var; auto.
Case "P_SSFun".
  pick fresh x1 and apply P_SSFun; auto.
  rewrite ssubst_SS_open_SS_wrt_s_var; auto.
  rewrite ssubst_SS_open_SS_wrt_s_var; auto.
Qed.

Lemma A3_sw : forall s1 s2 w1 w2 x,
  s1 ==>s s2 ->
  w1 ==>s w2 ->
  ssubst_s w1 x s1 ==>s ssubst_s w2 x s2.
Proof.
  destruct A3 as [A3_term _]. unfold A3_s in A3_term.
  intros. apply A3_term; auto.
Qed.

Lemma A3_SSw : forall SS1 SS2 w1 w2 x,
  SS1 ==>S SS2 ->
  w1 ==>s w2 ->
  ssubst_SS w1 x SS1 ==>S ssubst_SS w2 x SS2.
Proof.
  destruct A3 as [_ A3_type]. unfold A3_SS in A3_type.
  intros. apply A3_type; auto.
Qed.

Lemma A4_red : forall s1 s2, s1 ~~>h s2 -> s1 ==>s s2.
Proof.
destruct 1.
  SCase "F_RConst".  auto.
  SCase "F_RBeta". inversion H0. apply P_RBeta with (L := empty); auto.
  SCase "F_RCCheck". inversion H1. apply P_RCCheck with (L := empty) (s1 := s1); auto.
  SCase "F_ROK". apply P_ROK; auto.
  SCase "F_RFail". apply P_RFail; auto.
  SCase "F_RCDecomp".
    inversion H3. inversion H4. subst. 
    apply P_RCDecomp with (L := empty) (SS12' :=  SS12) (SS22' := SS22); auto. 
Qed.

Lemma A4 : forall s1 s2, s1 -->h s2 -> s1 ==>s s2.
Proof.
induction 1.
Case "F_Reduce". apply A4_red; auto. 
Case "F_Compat".
  inversion H; simpl; auto.
Case "F_Blame".
  auto.
Qed.

Lemma A5_1 : forall x sa s1 s2, lc_s sa -> s1 -->h s2 -> (ssubst_s s1 x sa ==>s ssubst_s s2 x sa). 
Proof.
intros. 
apply (proj1 A1); auto.
apply A4. auto.
Qed.

Lemma A5_2 : forall x SSA s1 s2, lc_SS SSA -> s1 -->h s2 -> (ssubst_SS s1 x SSA ==>S ssubst_SS s2 x SSA). 
Proof.
intros. 
apply (proj2 A1); auto.
apply A4. auto.
Qed.


Lemma A6_1 : forall x sa s1 s2, lc_s sa -> s1 -->h* s2 -> ssubst_s s1 x sa ==>s* ssubst_s s2 x sa.
Proof.
intros. induction H0. auto with lngen. 
eapply P_ssStep. apply A5_1; auto. eauto. eauto.
Qed.

Lemma A6_2 : forall x sa s1 s2, lc_SS sa -> s1 -->h* s2 -> ssubst_SS s1 x sa ==>S* ssubst_SS s2 x sa.
Proof.
intros. induction H0. auto with lngen. 
eapply P_SsStep. apply A5_2; auto. eauto. eauto.
Qed.

Lemma parallel_const_inversion : forall k s, (s_const k) ==>s s -> s = (s_const k).
Proof.
intros. inversion H. auto.
destruct H1; simpl in *; inversion H0.
Qed.


Lemma app_inversion : forall k1 k2 s1 s2, s_app (s_const k1) (s_const k2) ==>s s_app s1 s2 -> s1 = (s_const k1) /\ s2 = (s_const k2).
Proof.
intros.
inversion H; destruct (denot_q k1 k2) as [ [k3 EQ] | [l EQ]]; subst; auto;
try (inversion H5; subst; rewrite H2 in EQ; inversion EQ).
pose proof (parallel_const_inversion H3).
pose proof (parallel_const_inversion H5).
subst. auto.
pose proof (parallel_const_inversion H3).
pose proof (parallel_const_inversion H5).
subst. auto.
Qed.


Lemma parallel_lam_inversion :
  forall SS1 s1 s2, s_lam SS1 s1 ==>s s2 -> exists SS1', exists s1', s2 = s_lam SS1' s1' /\ SS1 ==>S SS1' /\
    (exists L, forall x, x `notin` L -> open_s_wrt_s s1 (s_var_f x) ==>s open_s_wrt_s s1' (s_var_f x)).
Proof.
intros.
inversion H.
subst. exists SS1. exists s1. split. auto. split.
inversion H0. auto. exists empty. intro. inversion H0. eauto.
subst. exists SS1'. exists s12'. split. auto. split. auto. 
  exists L. intros. eauto.
destruct H1; simpl in *. inversion  H0.  inversion H0. inversion H0.
Qed.


Lemma parallel_cast_inversion:
  forall SS1 SS2 s2 l1, s_cast SS1 SS2 l1 ==>s s2 -> exists SS1', exists SS2', 
    s2 = s_cast SS1' SS2' l1 /\ SS1 ==>S SS1' /\ SS2 ==>S SS2'.
Proof.
intros.
inversion H.
subst. exists SS1. exists SS2. inversion H0. eauto.
subst. exists SS1'. exists SS2'. eauto.
destruct H1; simpl in *; inversion H0.
Qed.

(* Running out of names for these inversion lemmas *)
Lemma inversion42 :
  forall SS11 SS12 SS11' SS12', 
    (SS_darrow SS11 SS12) ==>S (SS_darrow SS11' SS12') -> 
    exists L, (forall x, x `notin` L ->
      open_SS_wrt_s SS12 (s_var_f x) ==>S open_SS_wrt_s SS12' (s_var_f x)) /\
    SS11 ==>S SS11'.
Proof.
intros. 
 inversion H. 
 inversion H2.
 exists empty. subst. intros. auto.
 subst. exists L. auto.
Qed.

(* Parallel reduction of values produces values *)

Lemma parallel_FS : forall FS FS', is_FS_of_SS FS -> FS ==>S FS' -> is_FS_of_SS FS'.
Proof.
intros. destruct FS. simpl in H. contradiction.
inversion H0. subst. simpl. auto.
subst. simpl. auto.
Qed.

Lemma parallel_x : forall x s, s_var_f x ==>s s -> s = s_var_f x.
Proof.
intros. inversion H; subst. reflexivity.
destruct F5; inversion H0.
Qed.

Lemma parallel_w : forall w, is_w_of_s w -> forall w', w ==>s w' -> is_w_of_s w'.
Proof.
intro w. induction w; intros; simpl in H; try contradiction.
inversion H0. subst. auto.
inversion H2; subst; simpl in H1; inversion H1.
Case "w is lam".
destruct (parallel_lam_inversion H0) as [SS1 [s1 [K [R1 [L R2]]]]]. subst. auto.
Case "w is app (hocast)".
  destruct w1; simpl in H; try intuition.
  inversion H0. 
    SCase "Refl". subst. simpl. auto.
    SCase "App". subst. simpl in *. contradiction.
    SCase "". subst.
      assert (is_w_of_s s2'). auto. 
      inversion H6. subst. simpl. auto.
        subst. simpl. eauto using parallel_FS.
        inversion H7; subst; simpl in * ; inversion H5. 
        inversion H5; subst; simpl in * ; inversion H4. subst. inversion H2.
Case "w is scast".
destruct (parallel_cast_inversion H0) as [SS1 [s1 [K [R1 R2]]]]. subst. auto.
Qed.

Lemma parallel_h : forall h, is_h_of_s h -> forall h', h ==>s h' -> is_h_of_s h'.
Proof.
intros. destruct h; simpl in H; inversion H; try solve by inversion.
rename s into SS1. rename s0 into SS2.
inversion H0; auto; subst.
Case "P_Cast".
  destruct SS1; simpl in H1; try solve by inversion; clear H1.
  destruct SS2; simpl in H2; try solve by inversion; clear H2.
  destruct H.
  assert (is_FS_of_SS SS1').
    destruct SS1'; try solve by inversion; auto.
  assert (is_FS_of_SS SS2').
    destruct SS2'; try solve by inversion; auto.
  simpl. auto.
Case "P_Blame".
  destruct F5; inversion H3.
Qed.

Lemma parallel_q : forall q, is_q_of_s q -> forall q', q ==>s q' -> is_q_of_s q'.
intros. destruct q; try solve by inversion.
Case "s_const".
  inversion H0; subst; auto.
Case "s_lam".
  inversion H0; subst; auto.
Case "s_app".
  simpl in H. destruct H.
  inversion H0; subst; try solve by inversion; auto.
  SCase "P_Refl".
    simpl. auto.
  SCase "P_RCCheck".
    inversion H. inversion H2.
  SCase "P_App".
    simpl.
    apply parallel_h in H4; auto.
    apply parallel_w in H6; auto.
  SCase "P_Blame".
    destruct F5; simpl in H2; inversion H2; subst; solve by inversion.
Case "s_blame".
  inversion H0; subst. auto.
  destruct F5; solve by inversion.
Case "s_cast".
  apply w_is_q.
  apply parallel_w with (s_cast s s0 l); auto.
Qed.

Lemma parallel_blame : forall l s, s_blame (b_blame l) ==>s s -> s = s_blame (b_blame l).
Proof.
  intros. inversion H; subst.
  reflexivity.
  inversion H1; subst; simpl in H0; try solve by inversion.
Qed.

Lemma parallel_refinement_inversion: forall B5 s1 SS1, 
   SS_refinement B5 s1 ==>S SS1 -> exists s1', SS1 = SS_refinement B5 s1' /\ 
     exists L, forall x, x `notin` L -> (open_s_wrt_s s1 (s_var_f x)) ==>s (open_s_wrt_s s1' (s_var_f x)).
Proof.
intros.
inversion H. subst.
  exists s1. inversion H0.
  split; auto. exists empty. intros. auto.
subst. exists s'. eauto.
Qed.

Lemma parallel_hocast_inversion:
  forall SS11 SS12 SS21 SS22 w s1 l, 
  s_app (s_cast (SS_darrow SS11 SS12) (SS_darrow SS21 SS22) l) w ==>s s1 -> 
  is_w_of_s w ->
  exists SS11', exists SS12', exists SS21', exists SS22', exists w', 
  s1 = s_app (s_cast (SS_darrow SS11' SS12') (SS_darrow SS21' SS22') l) w'
  /\  (SS_darrow SS11  SS12 ) ==>S ( SS_darrow SS11' SS12' )
  /\   (SS_darrow  SS21 SS22 ) ==>S ( SS_darrow SS21' SS22' )
  /\  (w ==>s w').
Proof.
intros. 
assert (J : lc_s  (s_app (s_cast (SS_darrow SS11 SS12) (SS_darrow SS21 SS22) l) w)). auto.
inversion J. inversion H3.
inversion H. 
Case "Refl".
  subst. 
  exists SS11. exists SS12. exists SS21. exists SS22. exists w. auto. 
Case "Cast".
  inversion H12. subst.
  exists SS11. exists SS12. exists SS21. exists SS22. exists s2'. auto.
  subst. inversion H19. inversion H20. subst.
  exists SS11. exists SS12. exists SS21. exists SS22. exists s2'. auto.
  subst.  exists SS11. exists SS12. exists SS1'0. exists SS2'0. exists s2'. auto.
  subst. inversion H20. subst.
      exists SS1'0. exists SS2'0. exists SS21. exists SS22. exists s2'. auto.
  subst.  exists SS1'0. exists SS2'0. exists SS1'. exists SS2'1. exists s2'. auto.
  destruct H16; simpl in *; inversion H15.
  destruct H11; simpl in *; inversion H10.
  subst. simpl in *. contradiction.
Qed.


Lemma A7 : forall s1 s2 s1', s1 ==>s s2 -> s1 ~~>h s1' -> 
  exists s2', s2 -->h* s2' /\ s1' ==>s s2'.
Proof.
intros.
inversion H; subst.
Case "Refl".
  exists s1'. split; eauto. 
Case "RConst".
  exists (denot k5 k'). split; eauto.
  destruct w5; simpl in H1; try solve by inversion.
  inversion H3; subst.
  inversion H0. subst. auto.
Case "RBeta".
  exists (open_s_wrt_s s12' w2'). split. auto.
  inversion H0. subst.
  pick_fresh x1. 
  rewrite (ssubst_s_intro x1); auto.
  rewrite (ssubst_s_intro x1 s12'); auto.
  apply (proj1 A3); auto.
Case "RCheck".
  exists (s_check (SS_refinement B5 s2') (open_s_wrt_s s2' (s_const k5)) k5 l5).
  split. auto.
  inversion H0. subst.
  pick_fresh x1.
  rewrite (ssubst_s_intro x1); auto.
  rewrite (ssubst_s_intro x1 s2'); auto.
  apply P_Check; auto.
  eapply P_SSRefine; auto.
  apply (proj1 A3); auto.
Case "ROk".
  exists (s_const k5). split; auto.
  inversion H0. subst. auto.
Case "RFail".
  exists (s_blame (b_blame l5)).
  split; auto.
  inversion H0. subst. auto.
Case "RCDecomp".
(*  " < SS12' [x:= < SS21' => SS11'>l5 w2' ] => SS22' [x:= w2']>l5 >  (w1' (<SS21' => SS11'>l5 w2'))" *)
  exists (s_app (s_cast (open_SS_wrt_s SS12' (s_app (s_cast SS21' SS11' l5) w2'))
          (open_SS_wrt_s SS22' w2') l5)
       (s_app w1' (s_app (s_cast SS21' SS11' l5) w2'))).
  split; auto.
  inversion H0. subst.  
  eapply P_App. eapply P_Cast. 
  pick_fresh x1.
  rewrite (ssubst_SS_intro x1); auto.
  rewrite (ssubst_SS_intro x1 SS12'); auto.
  apply (proj2 A3); eauto. 
  pick_fresh x1.
  rewrite (ssubst_SS_intro x1); auto.
  rewrite (ssubst_SS_intro x1 SS22'); auto.
  apply (proj2 A3); eauto. 
  auto.
Case "Lam". 
  inversion H0.
Case "App".
  inversion H0.
  SCase "F_Const".
    exists (denot k5 k'). split.
    SSCase "left". 
      subst.
      destruct (app_inversion H). subst. apply F_Step with (s' := denot k5 k'). auto. auto.
    SSCase "right". auto.
  SCase "F_Beta".
    subst. destruct (parallel_lam_inversion H1) as [SS5' [s12' [J [R1 [L R2]]]]]. subst.
    exists (open_s_wrt_s s12' s2'). split. eapply F_Step with (s' := open_s_wrt_s s12' s2').
    assert (is_w_of_s s2'). eapply parallel_w. eauto. eauto.
    eauto.
    eapply F_Refl.
    assert (lc_s (s_lam SS5' s12')); eauto.
    inversion H3. eauto with lngen. 
    pick_fresh x1.
    rewrite (ssubst_s_intro x1); eauto.
    rewrite (ssubst_s_intro x1 s12'); eauto.
    eapply (proj1 A3); eauto.
  SCase "F_CCheck".
    subst.
    pose proof (parallel_const_inversion H2). subst.
    destruct (parallel_cast_inversion H1) as [SS1' [SS2' [K [R1 R2]]]].
    destruct (parallel_refinement_inversion R1) as [s1' [K1 [L R4]]].
    destruct (parallel_refinement_inversion R2) as [s3 [K2 [L' R5]]].
    subst.
    exists (s_check (SS_refinement B5 s3) (open_s_wrt_s s3 (s_const k5)) k5 l5).
    assert (lc_SS (SS_refinement B5 s3)); auto. inversion H3. subst.
    pick_fresh x1.
    assert (lc_s (open_s_wrt_s s3 (s_const k5))); 
      rewrite (ssubst_s_intro x1); auto. apply ssubst_s_lc_s; auto.
    split. SSCase "left".
    eapply F_Step; eauto. 
      rewrite <- ssubst_s_intro; auto. 
      rewrite <- ssubst_s_intro; auto.
    SSCase "right".
    eapply P_Check; auto.
    rewrite (ssubst_s_intro x1); auto.
    rewrite (ssubst_s_intro x1 s3); auto.
    eapply (proj1 A3); auto. 
  SCase "F_CDecomp". 
    subst.
    destruct (parallel_hocast_inversion H1 H5) as [SS11' [SS12' [SS21' [SS22' [s' [EQ [R1 [R2 R3]]]]]]]].
    subst.
    assert (is_w_of_s s'). eapply parallel_w. eauto. eauto.
    inversion H. subst.
    (* Not quite right. Need to do some inversions here. *)
    exists (s_app (s_cast (open_SS_wrt_s SS12' 
                             (s_app (s_cast SS21' SS11' l5) s2'))
                    (open_SS_wrt_s SS22' s2') l5)
                  (s_app s' (s_app (s_cast SS21' SS11' l5) s2'))).
    split. eauto. eauto.
    subst.
    assert (J1: lc_SS (SS_darrow SS21' SS22')); eauto.
    assert (J2: lc_SS (SS_darrow SS11' SS12')); eauto.
    inversion J1. inversion J2. subst.
    exists (s_app (s_cast (open_SS_wrt_s SS12' 
                             (s_app (s_cast SS21' SS11' l5) s2'))
                    (open_SS_wrt_s SS22' s2') l5)
                  (s_app s' (s_app (s_cast SS21' SS11' l5) s2'))).
    split. SSCase "left".
      eapply F_Step; auto. 
      eapply F_Reduce; eauto.
      eapply F_CDecomp; eauto.
      eapply parallel_w with (w:= s3)(w':= s2'); eauto.
      eapply F_Refl; eauto.
      eapply lc_s_app; eauto.
      eapply lc_s_cast; eauto.
      pick_fresh x1.
      rewrite (ssubst_SS_intro x1); auto.
      eapply ssubst_SS_lc_SS; eauto.
      pick_fresh x1.
      rewrite (ssubst_SS_intro x1); auto.
      eapply ssubst_SS_lc_SS; eauto.
   SSCase "right".
      destruct (inversion42 R1) as [L [R4 R5]].
      destruct (inversion42 R2) as [L' [R6 R7]].
      eapply P_App.
      eapply P_Cast.
      pick_fresh x1.
      rewrite (ssubst_SS_intro x1 SS12); eauto.
      rewrite (ssubst_SS_intro x1 SS12'); eauto.
      eapply (proj2 A3); eauto. 
      pick_fresh x1.
      rewrite (ssubst_SS_intro x1 SS22); eauto.
      rewrite (ssubst_SS_intro x1 SS22'); eauto.
      eapply (proj2 A3); eauto. 
      eapply P_App; eauto.
Case "Cast".
  inversion H0.
Case "Check".
  inversion H0; subst.
  SCase "F_OK". exists (s_const k5).
  inversion H. subst.
  split. SSCase "left". eauto. eauto. 
  SSCase "right".
  subst. inversion H14; subst.
  split; eauto.
  inversion H5; subst; simpl in H4; inversion H4.
  SCase "F_Fail".
  exists (s_blame (b_blame l5)).
  inversion H. subst.
  split; eauto.
  subst. inversion H14; subst.
  split; eauto.
  inversion H5; subst; simpl in H4; inversion H4.
Case "Blame".
  exists (s_blame (b_blame l5)). split. auto.
  inversion H1. subst; simpl in *; inversion H0.
    subst; simpl in *. inversion H0. inversion H7. inversion H8.
    subst; simpl in *. inversion H0.
Qed.

Lemma eval_app_congr1 : forall s1 s1',
  s1 -->h* s1' ->
  forall s2, lc_s s2 ->
  s_app s1 s2 -->h* s_app s1' s2.
Proof.
induction 1; intros.
Case "F_Refl".
  apply F_Refl; auto.
Case "F_Step".
  pose proof H1 as Hlc.
  apply IHevalh in H1.
  eapply F_Step; eauto.
  assert (s_app s5 s2 = Fplug (F_appl s2) s5) by auto. rewrite H2.
  assert (s_app s' s2 = Fplug (F_appl s2) s') by auto. rewrite H3.
  eapply F_Compat; eauto.
Qed.  

Lemma eval_app_congr2 : forall s2 s2',
  s2 -->h* s2' ->
  forall w1, lc_s w1 -> is_w_of_s w1 ->
  s_app w1 s2 -->h* s_app w1 s2'.
Proof.
induction 1; intros.
Case "F_Refl".
  apply F_Refl; auto.
Case "F_Step".
  pose proof H1 as Hlc.
  apply IHevalh in H1; try assumption.
  eapply F_Step; eauto.
  assert (s_app w1 s5 = Fplug (F_appr w1) s5) by auto. rewrite H3.
  assert (s_app w1 s' = Fplug (F_appr w1) s') by auto. rewrite H4.
  eapply F_Compat; eauto.
Qed.

Lemma eval_check_congr : forall s1 s1',
  s1 -->h* s1' ->
  forall SS k l, lc_SS SS ->
  s_check SS s1  k l -->h*
  s_check SS s1' k l.
Proof.
induction 1; intros.
Case "F_Refl".
  apply F_Refl; auto.
Case "F_Step".
  pose proof H1 as Hlc.
  eapply IHevalh in H1; try assumption.
  eapply F_Step; eauto.
  assert (s_check SS s5 k l = 
          Fplug (F_check SS k l) s5) by auto. rewrite H2.
  assert (s_check SS  s' k l = 
          Fplug (F_check SS k l) s') by auto. rewrite H3.
  eapply F_Compat; eauto.
Qed.

Lemma A8 : forall s1 s1', 
  s1 -->h s1' -> 
  forall s2, s1 ==>s s2 -> 
  exists s2', s2 -->h* s2' /\ s1' ==>s s2'.
induction 1; intros.
Case "F_Reduce". 
  eapply A7. eauto. eauto.
Case "F_Compat".
  inversion H; [SCase "F_appl" | SCase "F_appr" | SCase "F_check"];
  subst; simpl in H1; inversion H1; subst.
  SCase "F_appl".
    SSCase "P_Refl".
      exists (s_app s2 s5). simpl. split; auto.
      assert (s_app s1 s5 = Fplug (F_appl s5) s1) by reflexivity.
      eapply F_Step. rewrite H4. eapply F_Compat; eauto.
      simpl. apply F_Refl; auto.
    SSCase "P_RConst".
      assert (is_q_of_s (s_const k5)) by auto.
      assert False as C by (apply (results_dont_step H3 H0)).
      inversion C.
    SSCase "P_RBeta".
      assert (is_q_of_s (s_lam SS5 s12)) by (simpl; auto).
      assert False as C by (apply (results_dont_step H3 H0)).
      inversion C.
    SSCase "P_RCCheck".
      assert (is_q_of_s (s_cast (SS_refinement B5 s3) (SS_refinement B5 s4) l5)) by auto.
      assert False as C by (apply (results_dont_step H3 H0)).
      inversion C.
    SSCase "P_RCDecomp".
      remember (s_cast (SS11 :-> SS12) (SS21 :-> SS22) l5) as s0.
      assert (is_h_of_s s0) by (subst s0; simpl; auto).
      assert (is_q_of_s (s_app s0 w1)) by (subst s0; simpl; auto).
      assert False as C by (apply (results_dont_step H4 H0)).
      inversion C.
    SSCase "P_App".
      apply IHsteph in H5.
      destruct H5 as [s1'' [Hstep Hparred]].
      exists (s_app s1'' s2'). split.
      apply eval_app_congr1; auto.
      simpl; auto.
    SSCase "P_Blame".
      inversion H4; subst; try solve by inversion;
      simpl in H3; inversion H3; subst.
      SSSCase "F_appl".
        assert (is_q_of_s (s_blame (b_blame l5))) by (simpl; auto).
        assert False as C by (apply (results_dont_step H6 H0)).
        inversion C.
      SSSCase "F_appr".
        apply w_is_q in H6.
        assert False as C by (apply (results_dont_step H6 H0)).
        inversion C.
  SCase "F_appr".
    SSCase "P_Refl".
      exists (s_app w5 s2). simpl. split; auto.
      assert (s_app w5 s1 = Fplug (F_appr w5) s1) by reflexivity.
      eapply F_Step. rewrite H6. eapply F_Compat; eauto.
      simpl. apply F_Refl; auto.
    SSCase "P_RConst".
      apply w_is_q in H7.
      assert False as C by (apply (results_dont_step H7 H0)).
      inversion C.
    SSCase "P_RBeta".
      apply w_is_q in H7.
      assert False as C by (apply (results_dont_step H7 H0)).
      inversion C.
    SSCase "P_RCCheck".
      assert (is_q_of_s (s_const k5)) by auto.
      assert False as C by (apply (results_dont_step H5 H0)).
      inversion C.
    SSCase "P_RCDecomp".
      apply w_is_q in H8.
      assert False as C by (apply (results_dont_step H8 H0)).
      inversion C.
    SSCase "P_App".
      apply IHsteph in H9.
      destruct H9 as [s2'' [Hstep Hparred]].
      exists (s_app s1' s2''). split.
      apply eval_app_congr2; auto.
      eapply parallel_w; eassumption.
      simpl; auto.
    SSCase "P_Blame".
      inversion H6; subst; try solve by inversion;
      simpl in H5; inversion H5; subst.
      SSSCase "F_appl".
        inversion H2.
      SSSCase "F_appr".
        assert (is_q_of_s (s_blame (b_blame l5))) by (simpl; auto).
        assert False as C by (apply (results_dont_step H10 H0)).
        inversion C.
  SCase "F_check".
    SSCase "P_refl".
      exists (s_check SS5 s2 k5 l5). simpl. split; auto.
      assert (s_check SS5 s1 k5 l5 = Fplug (F_check SS5 k5 l5) s1) by reflexivity.
      eapply F_Step. rewrite H5. eapply F_Compat; eauto.
      simpl. apply F_Refl; auto.
    SSCase "P_ROK".
      assert (is_q_of_s (s_const k_true)) by auto.
      assert False as C by (apply (results_dont_step H4 H0)).
      inversion C.
    SSCase "P_RFail".
      assert (is_q_of_s (s_const k_false)) by auto.
      assert False as C by (apply (results_dont_step H4 H0)).
      inversion C.
    SSCase "P_Check".
      apply IHsteph in H11.
      rename s' into s1'.
      destruct H11 as [s1'' [Hstep Hparred]].
      exists (s_check SS' s1'' k5 l5). split.
      inversion H; subst.
      eapply eval_check_congr; eauto.
      simpl; eauto.
    SSCase "P_Blame".
      inversion H5; subst; try solve by inversion;
      simpl in H4; inversion H4; subst.
      SSSCase "F_check".
        assert (is_q_of_s (s_blame (b_blame l0))) by (simpl; auto).
        assert False as C by (apply (results_dont_step H8 H0)).
        inversion C.
Case "F_Blame".
  inversion H; [SCase "F_appl" | SCase "F_appr" | SCase "F_check"];
  subst; simpl in H0; inversion H0; subst; try solve by inversion.
  SCase "F_appl".
    SSCase "P_Refl".
      exists (s_blame (b_blame l5)). split; auto.
      assert (s_app (s_blame (b_blame l5)) s5 = 
              Fplug (F_appl s5) (s_blame (b_blame l5))) by reflexivity.
      rewrite H3. eapply F_Step. apply F_Blame; assumption.
      apply F_Refl; auto.
    SSCase "P_App".
      apply parallel_blame in H4; subst.
      exists (s_blame (b_blame l5)). split; auto.
      assert (s_app (s_blame (b_blame l5)) s2' = 
              Fplug (F_appl s2') (s_blame (b_blame l5))) by reflexivity.
      rewrite H2. eapply F_Step. apply F_Blame; auto.
      apply F_Refl; auto.
    SSCase "P_Blame".
      inversion H3; subst; try solve by inversion;
      simpl in H2; inversion H2; subst.
      SSSCase "F_appl".
        exists (s_blame (b_blame l5)); eauto.
      SSSCase "F_appr".
        inversion H4.
  SCase "F_appr".
    SSCase "P_Refl".
      exists (s_blame (b_blame l5)). split; auto.
      assert (s_app w5 (s_blame (b_blame l5)) =
              Fplug (F_appr w5) (s_blame (b_blame l5))) by reflexivity.
      rewrite H5. eapply F_Step. apply F_Blame; auto.
      apply F_Refl; auto.
    SSCase "P_App".
      apply parallel_blame in H8; subst.
      pose proof (parallel_w H1 H6). rename s1' into w5'.
      exists (s_blame (b_blame l5)).
      split; auto.
      assert (s_app w5' (s_blame (b_blame l5)) =
              Fplug (F_appr w5') (s_blame (b_blame l5))) by reflexivity.
      rewrite H5. eapply F_Step. apply F_Blame; auto.
      apply F_Refl; auto.
    SSCase "P_Blame".
      inversion H5; subst; try solve by inversion;
      simpl in H4; inversion H4; subst.
      SSSCase "F_appl".
        inversion H1.
      SSSCase "F_appr".
        exists (s_blame (b_blame l5)); eauto.
  SCase "F_check".
    SSCase "P_Refl".
      exists (s_blame (b_blame l5)). split; auto.
      assert (s_check SS5 (s_blame (b_blame l5)) k5 l0 =
              Fplug (F_check SS5 k5 l0) (s_blame (b_blame l5))) by reflexivity.
      rewrite H4. eapply F_Step. apply F_Blame; auto.
      apply F_Refl; auto.
    SSCase "P_Check".
      apply parallel_blame in H10. subst.
      exists (s_blame (b_blame l5)). split; auto.
      assert (s_check SS' (s_blame (b_blame l5)) k5 l0 =
              Fplug (F_check SS' k5 l0) (s_blame (b_blame l5))) by reflexivity.
      rewrite H3. eapply F_Step. apply F_Blame; auto.
      apply F_Refl; auto.
    SSCase "P_Blame".
      inversion H4; subst; try solve by inversion;
      simpl in H3; inversion H3; subst.
      SSSCase "F_check".
        exists (s_blame (b_blame l5)); eauto.
Qed.

Lemma A9_1 : forall s1 s2, 
  s1 ~~>h s2 -> 
  forall x s, lc_s s -> 
    (ssubst_s s x s1) ~~>h (ssubst_s s x s2).
Proof.
inversion 1; subst; intros.
Case "F_RConst".
  simpl. pose proof (denot_closed k5 k').
  destruct (denot_q k5 k') as [[k'' EQ] | [l EQ] ]; rewrite EQ in *; simpl; auto.
Case "F_RBeta".
  simpl.
  rewrite ssubst_s_open_s_wrt_s; try assumption.
  eapply F_Beta. apply ssubst_w; auto.
  change (lc_s (ssubst_s s x (s_lam SS5 s12))).
  inversion H1; subst.
  apply ssubst_s_lc_s; auto.
  apply ssubst_s_lc_s; auto.
Case "F_RCCheck".
  simpl.
  inversion H2; subst.
  rewrite ssubst_s_open_s_wrt_s; try assumption.
  eapply F_CCheck; auto.
  change (lc_SS (ssubst_SS s x (SS_refinement B5 s0))).
  apply ssubst_SS_lc_SS; auto.
  change (lc_SS (ssubst_SS s x (SS_refinement B5 s3))).
  apply ssubst_SS_lc_SS; auto.
Case "F_ROK".
  simpl. apply F_OK; auto.
  apply ssubst_SS_lc_SS; auto.
Case "F_RFail".
  simpl. apply F_Fail; auto.
  apply ssubst_SS_lc_SS; auto.
Case "F_RCDecomp".
  simpl.
  rewrite ssubst_SS_open_SS_wrt_s; try assumption. simpl.
  rewrite ssubst_SS_open_SS_wrt_s; try assumption.
  apply F_CDecomp; try solve [ apply ssubst_w; auto ].
  apply ssubst_s_lc_s; auto.
  change (lc_SS (ssubst_SS s x (SS11 :-> SS12))).
  apply ssubst_SS_lc_SS; auto.
  change (lc_SS (ssubst_SS s x (SS21 :-> SS22))).
  apply ssubst_SS_lc_SS; auto.
  apply ssubst_s_lc_s; auto.
Qed.

Lemma A9_1' : forall x1 s1 s2 s, 
  s1 [:s_var_f x1] ~~>h s2 -> 
  x1 `notin` sfv_s s1 ->
  lc_s s -> 
  s1 [:s] ~~>h ssubst_s s x1 s2.
Proof.
intros.
rewrite ssubst_s_intro with (x1:=x1); try assumption.
apply A9_1; assumption.
Qed.

Lemma A9 : forall s1 s2, 
  s1 -->h s2 -> 
  forall x s, 
    lc_s s -> 
    (ssubst_s s x s1) -->h (ssubst_s s x s2).
Proof.
induction 1; intros.
Case "F_Reduce".
  apply F_Reduce. apply A9_1; assumption.
Case "F_Compat".
  rewrite ssubst_Fplug; auto. rewrite ssubst_Fplug; auto.
  eapply F_Compat. apply ssubst_valid; auto.
  apply IHsteph; auto.
Case "F_Blame".
  rewrite ssubst_Fplug; auto.
  apply F_Blame. apply ssubst_valid; auto.
Qed.

Lemma A9' : forall x1 s1 s2 s, 
  s1 [:s_var_f x1] -->h s2 -> 
  x1 `notin` sfv_s s1 ->
  lc_s s -> 
  s1 [:s] -->h ssubst_s s x1 s2.
Proof.
intros.
rewrite ssubst_s_intro with (x1:=x1); try assumption.
apply A9; assumption.
Qed.

Lemma A10 : forall s1 s2, 
  s1 -->h* s2 -> 
  forall x s, 
    lc_s s -> 
    (ssubst_s s x s1) -->h* (ssubst_s s x s2).
Proof.
induction 1; intros.
Case "F_Refl".
  apply F_Refl. apply ssubst_s_lc_s; auto.
Case "F_Step".
  eapply F_Step. apply A9; eauto.
  apply IHevalh; auto.
Qed.

Lemma A10' : forall x1 s1 s2 s,
  s1 [:s_var_f x1] -->h* s2 ->
  x1 `notin` sfv_s s1 ->
  lc_s s ->
  s1 [:s] -->h* ssubst_s s x1 s2.
Proof.
intros.
rewrite ssubst_s_intro with (x1:=x1); try assumption.
apply A10; assumption.
Qed.

Lemma A13 : forall s1 x,
  s1 ==>s s_var_f x ->
  s1 -->h* s_var_f x.
Proof.
intros s x H. remember (s_var_f x) as s2. induction H; try solve by inversion; subst.
Case "P_Refl".
  apply F_Refl. assumption.
Case "P_RConst".
  destruct (denot_q k5 k') as [[k'' Heqd] | [l Heqd]]; rewrite Heqd in Heqs2; inversion Heqs2.
Case "P_RBeta".
  clear IHparreds. rename H3 into IH.
  assert (s12' = s_var_f x).
    destruct s12'; simpl in Heqs2; try solve by inversion.
    SCase "s_var_b".
      destruct n; unfold open_s_wrt_s in Heqs2; simpl in Heqs2; 
        subst; solve by inversion.
    SCase "s_var_f".
      unfold open_s_wrt_s in Heqs2. apply Heqs2.
  subst.
  pick_fresh x1. assert (x1 `notin` L) as HnoL by auto.
  assert (s_var_f x [:s_var_f x1] = s_var_f x) as Heqx by auto.
  pose proof (IH x1 HnoL Heqx).
  assert (ssubst_s w2' x1 (s_var_f x) = s_var_f x) as Heqsx by default_simp.
  assert (ssubst_s w2' x1 (s_var_f x) = ssubst_s w2 x1 (s_var_f x)) as Heqsx' by default_simp.
  rewrite (ssubst_s_intro x1); auto. rewrite Heqx in *. rewrite Heqsx'. clear Heqx Heqsx Heqsx'.
  eapply F_Step. apply F_Reduce. apply F_Beta; auto.
  apply (lc_s_lam_exists x1); auto.
  apply A10'; auto.
Qed.

Lemma ssubst_app_inversion : forall s w x s1 s2,
  is_w_of_s w ->
  lc_s w ->
  lc_s (s [:s_var_f x]) ->
  s [:w] = s_app s1 s2 ->
  (exists s1', exists s2',
    s [:s_var_f x] = (s_app s1' s2') [:s_var_f x] /\
    s1' [:w] = s1 /\
    s2' [:w] = s2) \/
  (s = s_var_b 0 /\ w = s_app s1 s2).
Proof.
intros s w x s1 s2 Hw Hlcw Hlcs Heqsw.
destruct s; subst; try solve by inversion; 
unfold open_s_wrt_s in Heqsw; simpl in Heqsw.
Case "s_var_b".
  right. 
  destruct n; simpl in Heqsw; subst; simpl in Hw; try inversion Heqsw.
  split; auto.
Case "s_app".
  inversion Heqsw; subst.
  left.
  exists s3. exists s4. auto.
Qed.

Lemma A11 : forall s1 s11' s12', 
  s1 ==>s s_app s11' s12' ->
  (exists s11, exists s12,
    s1 -->h* s_app s11 s12 /\
    s11 ==>s s11' /\
    s12 ==>s s12').
Proof.
intros s1 s11' s12' H. remember (s_app s11' s12') as s1'.
generalize dependent s12'. generalize dependent s11'.
induction H; intros; subst; try solve by inversion.
Case "P_Refl".
  exists s11'. exists s12'. split; auto.
  inversion H; subst.
  split; apply P_Refl; auto.
Case "P_RConst".
  destruct (denot_q k5 k') as [[k'' Heqdenot] | [l Heqdenot]]; 
    rewrite Heqdenot in Heqs1'; inversion Heqs1'.
Case "P_RBeta".
  rename s12 into s11. rename s11' into s11''. rename s12'0 into s12''.
  rename s12' into s11'. rename w2 into w12. rename w2' into w12'.
  rename H2 into Hs11. rename H4 into Hw12.
  rename IHparreds into IHw12'. rename H3 into IHs11'.
  pick_fresh x1.
  assert (x1 `notin` L) as HnoL by auto.
  destruct (lc_parreds (Hs11 x1 HnoL)) as [Hlcs11 Hlcs11'].
  destruct (lc_parreds Hw12) as [Hlcw12 Hlcw12'].
  apply ssubst_app_inversion with (x:=x1) in Heqs1'; auto.
  destruct Heqs1' as [[s11_1' [s11_2' [Heqs11_1' [Heqs1' Heqs2']]]]  | [Heqs11' Heqw12']].
  SCase "s11' is an app".
    change (s11' [:s_var_f x1] = s_app (s11_1' [:s_var_f x1]) (s11_2' [:s_var_f x1])) in Heqs11_1'.
    destruct (IHs11' x1 HnoL (s11_1' [:s_var_f x1]) (s11_2' [:s_var_f x1]) Heqs11_1') as [s11_1 [s11_2 [Hstep [Hpars11_1 Hpars11_2]]]].
    exists (ssubst_s w12 x1 s11_1). exists (ssubst_s w12 x1 s11_2).
    split.
    SSCase "-->*".
      eapply F_Step. apply F_Reduce. apply F_Beta; auto.
      apply (lc_s_lam_exists x1); auto.
      apply A10' with (s:=w12) in Hstep; auto.
    split.
    SSCase "s11_1 ==>s".
      subst s11''.
      rewrite (ssubst_s_intro x1).
      apply A3_sw; auto.
      apply (sfv_s_open_s_wrt_s w12'); auto.
    SSCase "s11_2 ==>s".
      subst s12''.
      rewrite (ssubst_s_intro x1).
      apply A3_sw; auto.
      apply (sfv_s_open_s_wrt_s w12'); auto.
  SCase "s11' is a var, w12' is an app'".
    destruct (IHw12' s11'' s12'' Heqw12') as [s12_1 [s12_2 [Hstep [Hpars12_1 Hpars12_2]]]].
    exists s12_1. exists s12_2.
    split.
    SSCase "-->*".
      eapply F_Step. apply F_Reduce. apply F_Beta; auto.
      apply (lc_s_lam_exists x1); auto.
      assert (s11 [:s_var_f x1] -->h* s_var_f x1) as Hsteps11.
        apply A13.
        change (s11 [:s_var_f x1] ==>s s_var_b 0 [:s_var_f x1]).
        rewrite <- Heqs11'.
        apply Hs11; auto.
      apply A10' with (s:=w12) in Hsteps11; auto.
      replace (ssubst_s w12 x1 (s_var_f x1)) with w12 in Hsteps11.
      apply evalh_trans with w12; auto.
      default_simp.
    SSCase "==>".
    split; auto.
Case "P_RCDecomp".
  inversion Heqs1'.
  exists (s_cast (SS12 [:=s_app (s_cast SS21 SS11 l5) w2]) (SS22 [:=w2]) l5).
  exists (s_app w1 (s_app (s_cast SS21 SS11 l5) w2)).
  destruct (lc_parredSS H3) as [HlcSS11 HlcSS11'].
  destruct (lc_parredSS H5) as [HlcSS21 HlcSS21'].
  pick_fresh x1. move Fr at top.
  assert (x1 `notin` L) as HnoL by auto.
  destruct (lc_parredSS (H4 x1 HnoL)) as [HlcSS12 HlcSS12'].
  destruct (lc_parredSS (H6 x1 HnoL)) as [HlcSS22 HlcSS22'].
  destruct (lc_parreds H7) as [Hlcw1 Hlcw1'].
  destruct (lc_parreds H8) as [Hlcw2 Hlcw2'].
  split.
  SSCase "-->*".
    eapply F_Step. apply F_Reduce. apply F_CDecomp; auto.
    apply (lc_SS_darrow_exists x1); auto.
    apply (lc_SS_darrow_exists x1); auto.
    apply F_Refl.
    rewrite (ssubst_SS_intro x1); auto. pattern (SS22 [:=w2]). rewrite (ssubst_SS_intro x1); auto.
    apply lc_s_app. apply lc_s_cast; apply ssubst_SS_lc_SS; auto.
    apply lc_s_app; auto.
  assert (s_app (s_cast SS21 SS11 l5) w2 ==>s s_app (s_cast SS21' SS11' l5) w2') as Harg.
    apply P_App; auto.
  split.
  SSCase "<SS12 => SS22> ==>s".
    apply P_Cast.
    rewrite (ssubst_SS_intro x1); auto.
    pattern (SS12' [:=s_app (s_cast SS21' SS11' l5) w2']). rewrite (ssubst_SS_intro x1); auto.
    apply A3_SSw; auto.
    rewrite (ssubst_SS_intro x1); auto.
    pattern (SS22' [:=w2']). rewrite (ssubst_SS_intro x1); auto.
    apply A3_SSw; auto.
  SSCase "w1 (<SS21 => SS11> w2) ==>s".
    apply P_App; auto.
Case "P_App".
  inversion Heqs1'; subst.
  exists s1. exists s2.
  split; auto.
Qed.

Lemma ssubst_check_inversion : forall s w x SS s1 k l,
  is_w_of_s w ->
  lc_s w ->
  lc_s (s [:s_var_f x]) ->
  s [:w] = s_check SS s1 k l ->
  exists SS', exists s1',
    (s [:s_var_f x] = (s_check SS' s1' k l) [:s_var_f x] /\
     SS' [:= w] = SS /\
     s1' [:  w] = s1).
Proof.
intros s w x SS s1 k l Hw Hlcw Hlcs Heqs.
destruct s; subst; try solve by inversion; 
unfold open_s_wrt_s in Heqs; simpl in Heqs.
Case "s_var_b".
  destruct n; simpl in Heqs; subst; 
    simpl in Hw; [ inversion Hw | inversion Heqs ].
Case "s_check".
  rename s into SS'. rename s0 into s1'.
  inversion Heqs; subst.
  exists SS'. exists s1'. split. reflexivity.
  split; reflexivity.  Qed.

Lemma A12 : forall s1 SS' s2' k l,
  s1 ==>s s_check SS' s2' k l ->
  (exists SS, exists s2,
    s1 -->h* s_check SS s2 k l /\
    SS ==>S SS' /\
    s2 ==>s s2').
Proof.
intros s1 SS' s2' k l H. remember (s_check SS' s2' k l) as s1'.
generalize dependent s2'. generalize dependent SS'.
induction H; intros; subst; try solve by inversion.
Case "P_Refl".
  exists SS'. exists s2'. split; auto.
  inversion H; subst.
  split; auto.
Case "P_RConst".
  destruct (denot_q k5 k') as [[k'' Heqdenot] | [l' Heqdenot]];
    rewrite Heqdenot in Heqs1'; inversion Heqs1'.
Case "P_RBeta".
  rename SS' into SS''. rename s2' into s2''.
  pick_fresh x1.
  assert (x1 `notin` L) as HnoL by auto.
  destruct (lc_parreds (H2 x1 HnoL)) as [Hlcs12 Hlcs12'].
  destruct (lc_parreds H4) as [Hlcw2 Hlcw2'].
  apply (@ssubst_check_inversion s12' w2' x1 SS'' s2'' k l H0 Hlcw2' Hlcs12') in Heqs1'; auto.
  destruct Heqs1' as [SS' [s2' [Heqs12' [HeqSS' Heqs2']]]].
  change (s12' [:s_var_f x1] = s_check (SS' [:= s_var_f x1]) (s2' [:s_var_f x1]) k l) in Heqs12'.
  destruct (H3 x1 HnoL (SS' [:= s_var_f x1]) (s2' [: s_var_f x1]) Heqs12') as [SSi [si [Hstep [HparSS Hpars]]]].
  exists (ssubst_SS w2 x1 SSi). exists (ssubst_s w2 x1 si).
  split.
  SCase "-->*".
    eapply F_Step. apply F_Reduce. apply F_Beta; auto.
    apply (lc_s_lam_exists x1); auto.
    apply A10' with (s:=w2) in Hstep; auto.
  split.
  SCase "==>SS".
    subst SS''.
    rewrite (ssubst_SS_intro x1).
    apply A3_SSw; auto.
    apply (sfv_SS_open_SS_wrt_s w2'); auto.
  SCase "==>s".
    subst s2''.
    rewrite (ssubst_s_intro x1).
    apply A3_sw; auto.
    apply (sfv_s_open_s_wrt_s w2'); auto.
Case "P_RCCheck".
  inversion Heqs1'; subst. clear Heqs1' H2.
  exists (SS_refinement B5 s2). exists (s2 [:s_const k]).
  pick_fresh x1.
  assert (x1 `notin` L) as HnoL by auto.
  destruct (lc_parreds (H1 x1 HnoL)) as [Hlcs2 Hlcs2'].
  assert (lc_s (s2 [:s_const k])) as Hlcs2k.
    rewrite (ssubst_s_intro x1); auto.
    apply ssubst_s_lc_s; auto.
  assert (lc_SS (SS_refinement B5 s2)).
    apply (lc_SS_refinement_exists x1). auto.
  assert (lc_SS (SS_refinement B5 s2')).
    apply (lc_SS_refinement_exists x1). auto.
  split.
  SCase "-->*".
    eapply F_Step. apply F_Reduce. apply F_CCheck; auto.
    apply F_Refl.
    apply lc_s_check; auto.
  split.
  SCase "==>SS".
    eapply P_SSRefine; auto.
  SCase "==>s".
    rewrite (ssubst_s_intro x1); auto.
    pattern (s2' [:s_const k]).
    rewrite (ssubst_s_intro x1); auto.
    apply A3_sw; auto.  
Case "P_Check".
  inversion Heqs1'; subst. clear Heqs1' IHparreds.
  exists SS5. exists s5.
  split; auto.
Qed.

Lemma q_parred_w_is_w : forall q w,
  q ==>s w ->
  is_q_of_s q ->
  is_w_of_s w ->
  is_w_of_s q.
Proof.
intros. destruct q; try solve by inversion; try auto.
Case "blame".
  inversion H; subst; solve by inversion.
Qed.

Lemma parallel_FS_rev : forall FS FS', is_FS_of_SS FS' -> FS ==>S FS' -> is_FS_of_SS FS.
intros. destruct FS'. simpl in H. contradiction.
inversion H0; subst; auto.
Qed.

Lemma parallel_h_rev : forall h h', 
  is_w_of_s h -> 
  is_h_of_s h' -> 
  h ==>s h' ->
  is_h_of_s h.
Proof.
intros. destruct h'; try solve by inversion.
inversion H1; subst; try solve by inversion; auto.
destruct (denot_q k5 k') as [[k'' Heqd] | [l' Heqd]]; rewrite Heqd in H2; inversion H2.
destruct w2; simpl in H; inversion H; solve by inversion.
simpl in H0. simpl. destruct H0.
split; eauto using parallel_FS_rev.
Qed.

Lemma parallel_blame_rev : forall q l,
  q ==>s s_blame (b_blame l) ->
  is_q_of_s q ->
  q = s_blame (b_blame l).
Proof.
intros. inversion H; subst; simpl in H0; try inversion H0; try solve by inversion.
auto.
destruct F5; simpl in H0; inversion H0; solve by inversion.
Qed.

Lemma parallel_const_rev : forall q k,
  q ==>s s_const k ->
  is_q_of_s q ->
  q = s_const k.
Proof.
intros. inversion H; subst; simpl in H0; try inversion H0; try solve by inversion.
auto.
Qed.

Lemma A15 : forall s1 k,
  s1 ==>s (s_const k) ->
  s1 -->h* s_const k.
Proof.
intros. remember (s_const k) as s2.
generalize dependent Heqs2. generalize dependent k.
induction H; intros; subst; try solve by inversion.
Case "P_Refl".
  auto.
Case "P_RConst".
  eapply evalh_trans.
  eapply eval_app_congr2.
  apply (IHparreds k' (refl_equal (s_const k'))); auto. auto. auto.
  eapply F_Step; auto.
Case "P_RBeta".
  pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
  specialize (H2 x1 HnoL). specialize (H3 x1 HnoL).
  destruct s12'; simpl in Heqs2; try solve by inversion.
  SCase "s12' is a var, w2 is k".
    destruct n; unfold open_s_wrt_s in Heqs2; simpl in Heqs2; try inversion Heqs2.
    subst. specialize (IHparreds k (refl_equal (s_const k))). clear H5.
    assert (w2 = s_const k) by (apply A2'; auto). subst w2. clear H3 H4 IHparreds.
    eapply F_Step. apply F_Reduce. apply F_Beta; auto.
    apply (lc_s_lam_exists x1); auto.
    assert (s_var_b 0 [:s_var_f x1] = s_var_f x1) by auto.
    rewrite H3 in H2. clear H3.
    apply A13 in H2. unfold open_s_wrt_s. simpl.
    pattern (s_const k) at 2.
    replace (s_const k) with (ssubst_s (s_const k) x1 (s_var_f x1)) by default_simp.
    apply A10'; auto. 
  SCase "s12' is k".
    unfold open_s_wrt_s in Heqs2; simpl in Heqs2. inversion Heqs2; subst. clear Heqs2.
    assert (s_const k [:s_var_f x1] = s_const k) by auto.
    specialize (H3 k H5). clear H5.
    replace (s_const k [:w2']) with (s_const k) by default_simp.
    eapply F_Step. apply F_Reduce. apply F_Beta; auto.
    apply (lc_s_lam_exists x1); auto.
    replace (s_const k) with (ssubst_s w2 x1 (s_const k)) by default_simp.
    replace (s_const k) with (ssubst_s w2 x1 (s_const k)) in H3 by default_simp.
    apply A10'; auto.
Case "P_ROK".    
  inversion Heqs2; subst.
  eapply F_Step. apply F_Reduce. apply F_OK; auto.
  apply F_Refl; auto.
Qed.

Lemma parallel_lam_rev : forall s1 SS1' s12' L,
  s1 ==>s s_lam SS1' s12' ->
  (forall x, x `notin` L ->
    exists SS1, exists s12,
    s1 -->h* s_lam SS1 s12 /\
    SS1 ==>S SS1' /\
    s12 [:s_var_f x] ==>s s12' [:s_var_f x]).
Proof.
intros. remember (s_lam SS1' s12') as s2.
generalize dependent s12'. generalize dependent SS1'. 
generalize dependent x. generalize dependent L.
induction H; intros; subst; try solve by inversion.
Case "P_Refl".
  exists SS1'. exists s12'.
  inversion H; subst.
  repeat (split; eauto).
Case "P_RConst".
  destruct (denot_q k5 k') as [[k'' Heqd] | [l Heqd]]; 
    rewrite Heqd in Heqs2; inversion Heqs2.
Case "P_RBeta".
  destruct s12'; simpl in Heqs2; try solve by inversion.
  SCase "s12' is a var, w2 is a lam".
    destruct n; unfold open_s_wrt_s in Heqs2; simpl in Heqs2; try solve [ inversion Heqs2 ].
    pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
    specialize (H2 x1 HnoL). specialize (H3 x1 HnoL).
    specialize (IHparreds L0 x H5).
    apply IHparreds in Heqs2.
    destruct Heqs2 as [SS1 [s12' [Hstep' [HparSS1' Hpars12'']]]].
    exists SS1. exists s12'.
    split.
    SSCase "-->*".
      eapply evalh_trans.
      eapply F_Step. apply F_Reduce. apply F_Beta; auto.
      apply (lc_s_lam_exists x1); auto.
      apply A10'; auto. apply A13; auto.
      replace (s_var_b 0 [:s_var_f x1]) with (s_var_f x1) in H2 by auto.
      apply H2. default_simp.
    split; eauto.
  SCase "s12 is a lambda".
    rename s into SS1. clear IHparreds.
    pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
    specialize (H2 x1 HnoL). specialize (H3 x1 HnoL).
    set (SS1x := SS1 [:=s_var_f x1]).
    set (s12'x := open_s_wrt_s_rec 1 (s_var_f x1) s12').
    assert (s_lam SS1 s12' [:s_var_f x1] = s_lam SS1x s12'x).
      unfold open_s_wrt_s. auto.
    specialize (H3 L0 x H5 SS1x s12'x H6).
    destruct H3 as [SS1'' [s12'' [Hstep [HparSS1 Hpars12]]]].
    exists (ssubst_SS w2 x1 SS1''). exists (ssubst_s w2 x1 s12'').
    assert (s12 [:w2] -->h* ssubst_s w2 x1 (s_lam SS1'' s12'')) as Hstepsubst.
      apply A10'; auto. 
    assert (SS1' = SS1 [:=w2']) as HeqSS1'.
      unfold open_s_wrt_s in Heqs2. simpl in Heqs2. inversion Heqs2.
      reflexivity.
    assert (ssubst_SS w2 x1 SS1'' ==>S SS1') as Hparsubst.
      subst SS1'.
      rewrite (ssubst_SS_intro x1).
      subst SS1x.
      apply A3_SSw; auto. default_simp.
    assert (s12'0 = open_s_wrt_s_rec 1 w2' s12') as Heqs12'0.
      unfold open_s_wrt_s in Heqs2. inversion Heqs2.
      reflexivity.
    split.
    SSCase "-->*".
      eapply evalh_trans.
      eapply F_Step. apply F_Reduce. apply F_Beta; auto.
      apply (lc_s_lam_exists x1); auto.
      apply Hstepsubst. simpl.
      eapply F_Refl; auto.
      apply (proj2 (lc_evalh Hstepsubst)).
    split; eauto.
    SSCase "==>s".
      subst s12'0. subst s12'x.
      rewrite (ssubst_s_intro_rec s12' x1); auto.
      rewrite ssubst_s_open_s_wrt_s_var; auto.
      rewrite ssubst_s_open_s_wrt_s_var; auto.
      apply A3_sw; auto.
Case "P_Lam".
  inversion Heqs2. subst SS1'0 s12'0. clear Heqs2.
  pick_fresh x1. assert (x1 `notin` L) as HnoL by auto.
  specialize (H0 x1 HnoL). clear H1.
  destruct (lc_parredSS H) as [HlcSS1 HlcSS1'].
  destruct (lc_parreds H0) as [Hlcs12 Hlcs12'].
  exists SS1. exists s12.
  split.
  SCase "-->*".
    apply F_Refl; eauto.
    apply (lc_s_lam_exists x1); auto.
  split; eauto.
  SCase "==>s".
    rewrite (ssubst_s_intro x1); auto.
    pattern (s12' [:s_var_f x]). rewrite (ssubst_s_intro x1); auto.
    apply A3_sw; auto.
Qed.

Lemma sfv_red : forall s1 s2 x,
  s1 ~~>h s2 ->
  x `notin` sfv_s s1 ->
  x `notin` sfv_s s2.
Proof.
intros. inversion H; subst; clear H.
Case "F_RConst".
  destruct (denot_q k5 k') as [[k'' Heqd] | [l Heqd]]; rewrite Heqd; auto.
Case "F_RBeta".
  simpl in H0.
  pose proof (sfv_s_open_s_wrt_s_upper s12 w2).
  assert (x `notin` union (sfv_s w2) (sfv_s s12)) by auto.
  auto.
Case "F_RCCheck".
  simpl in H0. simpl.
  assert (x `notin` union (sfv_s (s_const k5)) (sfv_s s3)) by auto.
  pose proof (sfv_s_open_s_wrt_s_upper s3 (s_const k5)).
  assert (x `notin` sfv_s (s3 [:s_const k5])) by auto.
  auto.
Case "F_ROK".
  auto.
Case "F_RFail".
  auto.
Case "F_RCDecomp".
  simpl. simpl in H0.
  pose proof (sfv_SS_open_SS_wrt_s_upper SS12 (s_app (s_cast SS21 SS11 l5) w')).
  pose proof (sfv_SS_open_SS_wrt_s_upper SS22 w').
  assert (x `notin` union (sfv_s w') (sfv_SS SS22)) by auto.
  assert (x `notin` union (sfv_s (s_app (s_cast SS21 SS11 l5) w')) (sfv_SS SS12)) by auto.
  assert (x `notin` sfv_SS (SS12 [:=s_app (s_cast SS21 SS11 l5) w'])) by auto.
  assert (x `notin` sfv_SS (SS22 [:=w'])) by auto.
  auto.
Qed.

Lemma sfv_step : forall s1 s2 x,
  s1 -->h s2 ->
  x `notin` sfv_s s1 ->
  x `notin` sfv_s s2.
Proof.
intros. induction H; subst; simpl in H0.
Case "F_Reduce".
  eauto using sfv_red.
Case "F_Compat".
  destruct F5; simpl in *; eauto.
Case "F_Blame".
  auto.
Qed.

Lemma sfv_eval : forall s1 s2 x,
  s1 -->h* s2 ->
  x `notin` sfv_s s1 ->
  x `notin` sfv_s s2.
Proof.
induction 1; intros; eauto using sfv_step.
Qed.

Lemma A14_lam : forall s1 SS1' s12' L,
  s1 ==>s s_lam SS1' s12' ->
  (exists SS1, exists s12,
    s1 -->h* s_lam SS1 s12 /\
    SS1 ==>S SS1' /\
    forall x, x `notin` L ->
      s12 [:s_var_f x] ==>s s12' [:s_var_f x]).
Proof.
  intros. 
  pick_fresh x1.
  apply parallel_lam_rev with (x:=x1) (L:=L) in H; auto.
  destruct H as [SS1 [s12 [Hstep [Hpar1 Hpar12]]]].
  exists SS1. exists s12.
  split; auto. split; auto.
  intros x HnoL. destruct (x == x1).
  Case "x = x1".
    subst. assumption.
  Case "x <> x1".
    rewrite (ssubst_s_intro x1); auto.
    pattern (s12' [:s_var_f x]).
    rewrite (ssubst_s_intro x1); auto.
    apply A3_sw; auto.
    apply sfv_eval with (x:=x1) in Hstep; auto.
    simpl in Hstep; auto.
Qed.

Lemma A14_cast : forall s1 SS1' SS2' l,
  s1 ==>s s_cast SS1' SS2' l ->
  (exists SS1, exists SS2,
    s1 -->h* s_cast SS1 SS2 l /\
    SS1 ==>S SS1' /\
    SS2 ==>S SS2').
Proof.
intros. remember (s_cast SS1' SS2' l) as s2.
generalize dependent l. generalize dependent SS2'. generalize dependent SS1'.
induction H; intros; subst; try solve by inversion.
Case "P_Refl".
  exists SS1'. exists SS2'.
  inversion H; subst.
  repeat (split; eauto).
Case "P_RConst".
  destruct (denot_q k5 k') as [[k'' Heqd] | [l' Heqd]]; 
    rewrite Heqd in Heqs2; inversion Heqs2.
Case "P_RBeta".
  pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
  specialize (H2 x1 HnoL). specialize (H3 x1 HnoL).
  destruct s12'; simpl in Heqs2; try solve by inversion.
  SCase "s12' is a var, w2 is a lam".
    destruct n; unfold open_s_wrt_s in Heqs2; simpl in Heqs2; try solve [ inversion Heqs2 ].
    apply IHparreds in Heqs2.
    destruct Heqs2 as [SS1 [SS2 [Hstep [HparSS1 HparsSS2]]]].
    exists SS1. exists SS2.
    split.
    SSCase "-->*".
      eapply evalh_trans.
      eapply F_Step. apply F_Reduce. apply F_Beta; auto.
      apply (lc_s_lam_exists x1); auto.
      apply A10'; auto. apply A13; auto.
      replace (s_var_b 0 [:s_var_f x1]) with (s_var_f x1) in H2 by auto.
      apply H2. default_simp.
    split; eauto.
  SCase "s12' is a cast".
    rename s into SS1. rename s0 into SS2. clear IHparreds.
    assert (l0 = l) as Heql0.
      unfold open_s_wrt_s in Heqs2. simpl in Heqs2.
      inversion Heqs2. reflexivity.
    subst l0.
    assert (SS1' = SS1 [:=w2'] /\ SS2' = SS2 [:=w2']) as [HeqSS1' HeqSS2'].
      unfold open_s_wrt_s in Heqs2. inversion Heqs2; subst; auto.
    subst SS1' SS2'.
    assert (s_cast SS1 SS2 l [:s_var_f x1] = 
            s_cast (SS1 [:=s_var_f x1]) (SS2 [:=s_var_f x1]) l) as Heqcast.
      unfold open_s_wrt_s. reflexivity.
    specialize (H3 (SS1 [:=s_var_f x1]) (SS2 [:=s_var_f x1]) l Heqcast). clear Heqcast.
    destruct H3 as [SS1'' [SS2'' [Hsteps12 [HparSS1'' HparSS2'']]]].
    destruct (lc_parredSS HparSS1'') as [HlcSS1'' HlcSS1x].
    destruct (lc_parredSS HparSS2'') as [HlcSS2'' HlcSS2x].
    exists (ssubst_SS w2 x1 SS1''). exists (ssubst_SS w2 x1 SS2'').
    split.
    SSCase "-->*".
      eapply evalh_trans.
      eapply F_Step. apply F_Reduce. apply F_Beta; auto.
      apply (lc_s_lam_exists x1); auto.
      apply A10'; auto. apply Hsteps12.
      simpl. apply F_Refl.
      apply lc_s_cast; apply ssubst_SS_lc_SS; auto.
    split.
    SSCase "==>s".
      rewrite (ssubst_SS_intro x1).
      apply A3_SSw; auto. default_simp.
    SSCase "==>s".
      rewrite (ssubst_SS_intro x1).
      apply A3_SSw; auto. default_simp.
Case "P_Cast".
  inversion Heqs2. subst SS1'0 SS2'0 l5. clear Heqs2.
  destruct (lc_parredSS H) as [HlcSS1 HlcSS1'].
  destruct (lc_parredSS H0) as [HlcSS2 HlcSS2'].
  exists SS1. exists SS2.
  split; eauto.
Qed.

Lemma A14_k : forall s1 k,
  s1 ==>s s_const k ->
  s1 -->h* s_const k.
Proof.
intros. remember (s_const k) as w2'. revert Heqw2'.
induction H; intros; subst; try solve by inversion.
Case "P_Refl".
  auto.
Case "P_RConst".
  apply parallel_const_rev in H1; auto using w_is_q. subst w5.
  eapply F_Step.  apply F_Reduce. apply F_Const; auto.
  auto.
Case "P_RBeta".
  pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
  rewrite (ssubst_s_intro x1) in Heqw2'; auto.
  assert (s12' = s_const k \/ 
         (s12' [:s_var_f x1] = s_var_f x1 /\ w2' = s_const k)) as [Heqs12' | [Heqs12' Hw2']].
    destruct s12'; subst; try solve by inversion.
    destruct n; default_simp.
    destruct (x == x1); default_simp.
    default_simp.
  SCase "s12' = s_const k".
    subst.
    eapply F_Step. apply F_Reduce. apply F_Beta; auto.
    apply (lc_s_lam_exists x1); auto.
    specialize (H2 x1 HnoL). auto using lc_parreds.
    assert (s_const k [:s_var_f x1] = s_const k) as Hk by auto.
    specialize (H3 x1 HnoL Hk). 
    replace (s_const k) with (ssubst_s w2 x1 (s_const k)) by auto.
    rewrite (ssubst_s_intro x1); auto.
    replace (ssubst_s w2 x1 (s_const k) [:w2']) with (ssubst_s w2 x1 (s_const k)) by auto.
    apply A10; auto.
  SCase "s12' [:s_var_f x1] = s_var_f x1".
    specialize (H2 x1 HnoL). rewrite Heqs12' in *.
    apply A13 in H2.
    subst w2'. apply parallel_const_rev in H4; auto using w_is_q. subst w2.
    eapply F_Step. apply F_Reduce. apply F_Beta; auto.
    apply (lc_s_lam_exists x1); auto using lc_parreds.
    rewrite (ssubst_s_intro x1); auto.
    pattern (s12' [:s_const k]). rewrite (ssubst_s_intro x1); auto.
    apply A10; auto. rewrite Heqs12'. apply H2.
Case "P_ROK".
  inversion Heqw2'; subst. eauto.
Qed.

Lemma A14_w : forall s1 w2',
  s1 ==>s w2' ->
  is_w_of_s w2' ->
  exists w2,
    s1 -->h* w2 /\
    w2 ==>s w2' /\
    is_w_of_s w2.
Proof.
intros s1 w2'. revert s1.
induction w2'; intros; subst; try solve by inversion.
Case "s_const".
  apply A14_k with (k:=k) in H; auto.
  exists (s_const k). eauto.
Case "s_lam".
  apply A14_lam with (L:=sfv_s w2') in H; auto.
  destruct H as [SS1 [s12 [Hstep [Hpar1 Hpar2]]]].
  exists (s_lam SS1 s12). eauto.
Case "s_app".
  simpl in H0. destruct H0 as [Hhw2'1 Hww2'2].
  apply A11 in H. destruct H as [s11 [s12 [Hstep [Hpar1 Hpar2]]]].
  specialize (IHw2'1 s11 Hpar1 (h_is_w _ Hhw2'1)).
  destruct IHw2'1 as [w11 [Hstep11 [Hpar11 Hw11]]].
  specialize (IHw2'2 s12 Hpar2 Hww2'2).
  destruct IHw2'2 as [w22 [Hstep12 [Hpar22 Hw22]]].
  exists (s_app w11 w22).
  split.
  SCase "-->h*".
    eapply evalh_trans. apply Hstep.
    eapply evalh_trans. apply eval_app_congr1. apply Hstep11; auto. auto.
    apply eval_app_congr2; auto.
  split; eauto.
  SCase "is_w".
    simpl. split; auto. apply parallel_h_rev with w2'1; auto.
Case "s_cast".
  rename s into SS1'. rename s0 into SS2'.
  apply A14_cast in H; auto.
  destruct H as [SS1 [SS2 [Hstep [Hpar1 Hpar2]]]].
  eauto.
Qed.

Lemma A14_blame : forall s1 q2' l,
  s1 ==>s q2' ->
  q2' = s_blame (b_blame l) ->
  s1 -->h* s_blame (b_blame l).
Proof.
induction 1; intros; subst; try solve by inversion.
Case "P_Refl".
  auto.
Case "P_RConst".
  apply A14_w in H1; auto. destruct H1 as [w2 [Hstep [Hpar Hw2]]].
  apply parallel_const_rev in Hpar; auto. subst w2.
  eapply evalh_trans. apply eval_app_congr2. apply Hstep. auto. auto.
  eapply F_Step. apply F_Reduce. apply F_Const; auto. rewrite H2; auto.
  auto using w_is_q.
Case "P_RBeta".
  pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
  rewrite (ssubst_s_intro x1) in H5; auto.
  destruct s12'; simpl in H5; try solve by inversion.
  SCase "s_var_b".
    destruct n; unfold open_s_wrt_s in H5; simpl in H5; try inversion H5.
    default_simp.
    SSCase "s12' is a var, w2 is a value".
      replace (if x == x1 then w2' else s_var_f x)
        with  (s_var_f x) in H5 by default_simp. inversion H5.
  SCase "s_blame".
    inversion H5; subst.
    specialize (H2 x1 HnoL). clear H5.
    eapply F_Step. apply F_Reduce. apply F_Beta; auto.
    apply (lc_s_lam_exists x1); auto.
    rewrite (ssubst_s_intro x1); auto.
    replace (s_blame (b_blame l))
      with  (s_blame (b_blame l) [:w2]) by default_simp.
    pattern (s_blame (b_blame l) [:w2]).
    rewrite (ssubst_s_intro x1); auto.
    apply A10; auto.
Case "P_RFail".
  inversion H1; subst.
  eapply F_Step. apply F_Reduce. apply F_Fail; auto.
  apply F_Refl; auto.
Case "P_Blame".
  inversion H0; subst.
  eauto.
Qed.

Lemma A14 : forall s1 q2', 
  s1 ==>s q2' -> 
  is_q_of_s q2' ->
  exists q2, 
    s1 -->h* q2 /\ 
    q2 ==>s q2' /\
    is_q_of_s q2.
Proof.
intros. apply q_inversion in H0. destruct H0 as [Hw | [l Heq]].
Case "is_w_of_s q2".
  apply A14_w in H; auto. destruct H as [w2 [Hstep [Hpar Hw2]]].
  exists w2. eauto using w_is_q.
Case "q2 = blame".
  apply A14_blame with (l:=l) in H; auto.
  exists (s_blame (b_blame l)). subst q2'. eauto; simpl; auto.
Qed.

Lemma parallel_ref_rev : forall SS1 B s' L,
  SS1 ==>S SS_refinement B s' ->
  exists s,
    SS1 = SS_refinement B s /\ 
    forall x, x `notin` L -> s [:s_var_f x] ==>s s' [:s_var_f x].
Proof.
intros. inversion H; subst.
Case "P_SSRefl".
  inversion H0; subst. eauto.
Case "P_SSRefine".
  exists s5. split; eauto.
  intros x HnoL.
  pick_fresh x1. assert (x1 `notin` L0) as HnoL0 by auto.
  specialize (H4 x1 HnoL0).
  rewrite (ssubst_s_intro x1); auto.
  pattern (s' [:s_var_f x]). rewrite (ssubst_s_intro x1); auto.
  apply A3_sw; auto.
Qed.

Lemma parallel_fun_rev : forall SS SS1' SS2' L,
  SS ==>S (SS1' :-> SS2') ->
  exists SS1, exists SS2,
    SS = SS1 :-> SS2 /\ 
    SS1 ==>S SS1' /\
    forall x, x `notin` L -> 
      (SS2 [:=s_var_f x]) ==>S (SS2' [:=s_var_f x]).
Proof.
intros. inversion H; subst.
Case "P_SSRefl".
  inversion H0; subst. exists SS1'. exists SS2'. eauto.
Case "P_SSFun".
  exists SS1. exists SS2. split; eauto. split; eauto.
  intros x HnoL. pick_fresh x1. assert (x1 `notin` L0) as HnoL0 by auto.
  specialize (H4 _ HnoL0).
  rewrite (ssubst_SS_intro x1); auto.
  pattern (SS2' [:=s_var_f x]). rewrite (ssubst_SS_intro x1); auto.
  apply A3_SSw; auto.
Qed.

Lemma w_only_reflstep : forall w s,
  w -->h* s -> 
  is_w_of_s w ->
  w = s.
Proof.
intros. inversion H; subst; auto.
pose proof (results_dont_step (w_is_q _ H0) H1). inversion H3.
Qed.

Lemma par_substw_inversion : forall s1 s2 w2 x,
  s1 ==>s s2 ->
  is_w_of_s w2 ->
  is_w_of_s (ssubst_s w2 x s2) ->
  forall w1,
    w1 ==>s w2 ->
    is_w_of_s w1 ->
    exists s1',
      ssubst_s w1 x s1 -->h* ssubst_s w1 x s1' /\
      ssubst_s w1 x s1' ==>s ssubst_s w2 x s2 /\
      is_w_of_s (ssubst_s w1 x s1').
Proof.
intros s1 s2. revert s1. induction s2; intros; try solve by inversion; 
  pose proof (lc_parreds H2) as [Hlcw1 Hlcww2];
  pose proof (proj1 (lc_parreds H)) as Hlcs1.
Case "s_var_f".
  simpl in H1. destruct (x == x0); try inversion H1. subst x0.
  exists (s_var_f x).  
  split.
  SCase "-->h*".
    apply A10; auto.
    apply A13; auto.
  split.
  SCase "==>s".
    apply A3_sw; auto.
  SCase "is_w".
    replace (ssubst_s w1 x (s_var_f x)) with w1 by default_simp.
    auto.
Case "s_const".
  clear H1.
  exists (s_const k).
  split.
  SCase "-->h*".
    apply A10; auto.
    apply A14_k; auto.
  split; simpl; eauto.
Case "s_lam".
  clear IHs2.
  apply A14_lam with (L:=singleton x) in H.
  destruct H as [SS1 [s12 [Hstep1 [HparSS1 Hpars12]]]].
  exists (s_lam SS1 s12).
  split; auto using A10.
  split; auto.
  SCase "==>s".
    simpl. apply P_Lam with (L:=singleton x).
    apply A3_SSw; auto.
    intros x1 Frx1. specialize (Hpars12 x1 Frx1).
    rewrite ssubst_s_open_s_wrt_s_var; auto.
    rewrite ssubst_s_open_s_wrt_s_var; auto.
    apply A3_sw; auto.
Case "s_app".
  apply A11 in H. destruct H as [s11 [s12 [Hstep1 [Hpar11 Hpar12]]]]. 
  simpl in H1. destruct H1 as [Hh2_1 Hw2_2].
  specialize (IHs2_1 _ _ _ Hpar11 H0 (h_is_w _ Hh2_1) _ H2 H3).
  destruct IHs2_1 as [s11' [Hstep11 [Hpar11' Hw11']]].
  specialize (IHs2_2 _ _ _ Hpar12 H0 Hw2_2 _ H2 H3).
  destruct IHs2_2 as [s12' [Hstep12 [Hpar12' Hw12']]].
  pose proof (parallel_h_rev Hw11' Hh2_1 Hpar11').
  exists (s_app s11' s12').
  split.
  SCase "-->h*".
    eapply evalh_trans. apply (A10 Hstep1); auto. simpl.
    eapply evalh_trans. apply (eval_app_congr1 Hstep11); auto. 
    eapply evalh_trans. apply (eval_app_congr2 Hstep12); auto.
    apply F_Refl; auto.
  split.
  SCase "==>s". simpl. apply P_App; auto.
  SCase "is_w". simpl. auto.
Case "s_cast".
  rename s into SS1'. rename s0 into SS2'.
  apply A14_cast in H.
  destruct H as [SS1 [SS2 [Hstep1 [HparSS1 HparSS2]]]].
  exists (s_cast SS1 SS2 l).
  split; auto using A10.
  split; auto using A3_sw.
Qed.

Lemma A16 : forall s1 s2 s2',
  s1 ==>s s2 ->
  s2 ~~>h s2' ->
  exists s1',
    s1 -->h* s1' /\
    s1' ==>s s2'.
Proof.
intros s1 s2 s2' H. revert s2'. induction H; intros; try solve by inversion.
Case "P_Refl".
  exists s5. split; auto using A4_red.
Case "P_RConst".
  destruct (denot_q k5 k') as [[k'' Heqd] | [l Heqd]]; rewrite Heqd in H2; inversion H2.
Case "P_RBeta".
  inversion H5; subst.
  SCase "F_RConst".
    destruct s12'; unfold open_s_wrt_s in H6; simpl in H6; try solve by inversion.
    destruct n; simpl in H6; try subst w2'; try inversion H0; solve by inversion.
    inversion H6; subst. clear H6 H7 H8 H3 IHparreds.
    pick_fresh x1. assert (x1 `notin` L) as HnoL by auto. specialize (H2 x1 HnoL). clear HnoL.
    unfold open_s_wrt_s in H2; simpl in H2.
    apply A11 in H2. destruct H2 as [s12_1 [s12_2 [Hstep12 [Hpar12_1 Hpar12_2]]]].
    destruct s12'1; simpl in H10; try solve by inversion.
    SSCase "s12'1 is a var, w2' = s_const k5".
      destruct n; simpl in H10; try solve by inversion; subst w2'.
      simpl in Hpar12_1. apply A13 in Hpar12_1. 
      apply parallel_const_rev in H4; auto using w_is_q. subst w2. clear H0 H5.
      destruct s12'2; simpl in H11; try solve by inversion.
      SSSCase "s12'2 is a var, k5 = k'".
        destruct n; simpl in H11; try solve by inversion; inversion H11; subst. clear H11.
        simpl in Hpar12_2. apply A13 in Hpar12_2.
        exists (denot k5 k5).
        split; auto.
        SSSSCase "-->h*".
          eapply F_Step. apply F_Reduce. apply F_Beta; auto.
          apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)).
          rewrite (ssubst_s_intro x1); auto.
          eapply evalh_trans. apply A10. apply Hstep12. auto.
          eapply evalh_trans. simpl. apply eval_app_congr1.
            apply A10. apply Hpar12_1. auto. apply ssubst_s_lc_s; auto.
          replace (ssubst_s (s_const k5) x1 (s_var_f x1)) with (s_const k5) by default_simp.
          eapply evalh_trans. apply eval_app_congr2. 
            apply A10. apply Hpar12_2. auto. auto. auto.
          replace (ssubst_s (s_const k5) x1 (s_var_f x1)) with (s_const k5) by default_simp.
          eapply F_Step. apply F_Reduce. apply F_Const; auto.
          apply F_Refl; auto.
      SSSCase "s12'2 = s_const k'".
        inversion H11; subst k. clear H11.
        simpl in Hpar12_2. apply A14_k in Hpar12_2.
        exists (denot k5 k').
        split; auto.
        SSSSCase "-->h*".
          eapply F_Step. apply F_Reduce. apply F_Beta; auto.
          apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)).
          rewrite (ssubst_s_intro x1); auto.
          eapply evalh_trans. apply A10. apply Hstep12. auto.
          eapply evalh_trans. simpl. apply eval_app_congr1.
            apply A10. apply Hpar12_1. auto. apply ssubst_s_lc_s; auto.
          replace (ssubst_s (s_const k5) x1 (s_var_f x1)) with (s_const k5) by default_simp.
          eapply evalh_trans. apply eval_app_congr2. 
            apply A10. apply Hpar12_2. auto. auto. auto.
          replace (ssubst_s (s_const k5) x1 (s_var_f x1)) with (s_const k5) by default_simp.
          eapply F_Step. apply F_Reduce. apply F_Const; auto.
          apply F_Refl; auto.
    SSCase "s12'1 = k5".
      inversion H10; subst k. clear H10.
      simpl in Hpar12_1. apply A14_k in Hpar12_1.
      destruct s12'2; simpl in H11; try solve by inversion.
      SSSCase "s12'2 is a var, k5 = k'".
        destruct n; simpl in H11; try solve by inversion; inversion H11; subst. clear H2.
        apply parallel_const_rev in H4; auto using w_is_q. subst w2. clear H0 H5 H.
        simpl in Hpar12_2. apply A13 in Hpar12_2.
        exists (denot k5 k').
        split; auto.
        SSSSCase "-->h*".
          eapply F_Step. apply F_Reduce. apply F_Beta; simpl; auto. 
          apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)).
          rewrite (ssubst_s_intro x1); auto.
          eapply evalh_trans. apply A10. apply Hstep12. auto.
          eapply evalh_trans. simpl. apply eval_app_congr1.
            apply A10. apply Hpar12_1. auto. apply ssubst_s_lc_s; auto.
          replace (ssubst_s (s_const k') x1 (s_const k5)) with (s_const k5) by default_simp.
          eapply evalh_trans. apply eval_app_congr2. 
            apply A10. apply Hpar12_2. auto. auto. simpl; auto.
          replace (ssubst_s (s_const k') x1 (s_var_f x1)) with (s_const k') by default_simp.
          eapply F_Step. apply F_Reduce. apply F_Const; auto.
          apply F_Refl; auto.
      SSSCase "s12'2 = s_const k'".
        inversion H11; subst k. clear H11.
        simpl in Hpar12_2. apply A14_k in Hpar12_2.
        exists (denot k5 k').
        split; auto.
        SSSSCase "-->h*".
          eapply F_Step. apply F_Reduce. apply F_Beta; simpl; auto. 
          apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)).
          rewrite (ssubst_s_intro x1); auto.
          eapply evalh_trans. apply A10. apply Hstep12. auto.
          eapply evalh_trans. simpl. apply eval_app_congr1.
            apply A10. apply Hpar12_1. auto. apply ssubst_s_lc_s; auto.
          eapply evalh_trans. apply eval_app_congr2. 
            apply A10. apply Hpar12_2. auto. apply ssubst_s_lc_s; auto. apply ssubst_w; auto.
            simpl; auto.
          simpl. eapply F_Step. apply F_Reduce. apply F_Const; auto.
          apply F_Refl; auto.
  SCase "F_RBeta".
    clear IHparreds.
    destruct s12'; simpl in H6; try solve by inversion; unfold open_s_wrt_s in H6; simpl in H6.
    destruct n; simpl in H6; try subst w2'; try inversion H0; solve by inversion.
    rename SS0 into SS12_11', s0 into s12_12', w0 into w12_2'.
    pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
    specialize (H2 x1 HnoL). unfold open_s_wrt_s in H2. simpl in H2.
    apply A11 in H2. destruct H2 as [s12_1 [s12_2 [Hstep12 [Hpar12_1 Hpar12_2]]]].
    inversion H6; subst. clear H6 H5. clear H3. (* FIXME may need H3... *) move Fr at top.
    destruct s12'1; simpl in H10; try solve by inversion.
    SSCase "s12'1 is a var, w2' is a lambda".
      destruct n; simpl in H10; try solve by inversion. subst w2'. move Fr at top.
      apply A14_lam with (L:=empty) in H4.
      destruct H4 as [SS12_11 [s12_12 [Hstep2 [Hpar12_11 Hpar12_12]]]].
      apply w_only_reflstep in Hstep2; auto.
      replace (open_s_wrt_s_rec 0 (s_lam SS12_11' s12_12') s12'2)
        with  (s12'2 [:s_lam SS12_11' s12_12']) in H7 by auto.
      rewrite (ssubst_s_intro x1) in H7; auto.
      assert (w2 ==>s s_lam SS12_11' s12_12') as Hparw2.
        subst w2. apply P_Lam with (L:=empty); auto.
      pose proof (par_substw_inversion x1 Hpar12_2 H0 H7 Hparw2 H).
      destruct H2 as [w12_2 [Hstep12_2 [Hparw12_2 Hw12_2]]].
      simpl in Hpar12_1. apply A13 in Hpar12_1.
      pick_fresh x2. move Fr0 at top. assert (x2 `notin` empty) as Hx2 by auto.
      specialize (Hpar12_12 _ Hx2).
      exists (ssubst_s (ssubst_s w2 x1 w12_2) x2 (s12_12 [:s_var_f x2])).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_Beta; auto.
        apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)); auto.
        rewrite (ssubst_s_intro x1).
        eapply evalh_trans. apply (A10 Hstep12); auto. simpl.
        eapply evalh_trans. apply eval_app_congr1. apply (A10 Hpar12_1); auto.
          apply ssubst_s_lc_s; auto.
        replace (ssubst_s w2 x1 (s_var_f x1)) with w2 by default_simp.
        eapply evalh_trans. apply (eval_app_congr2 Hstep12_2); auto.
        rewrite Hstep2 at 1.
        eapply F_Step. apply F_Reduce. apply F_Beta; auto.
        apply (lc_s_lam_exists x2); auto.
        rewrite (ssubst_s_intro x2); auto.
        apply F_Refl; auto.
        apply ssubst_s_lc_s; auto. auto.
      SSSCase "==>s".
        pattern (s12_12' [:open_s_wrt_s_rec 0 (s_lam SS12_11' s12_12') s12'2]).
        rewrite (ssubst_s_intro x2); auto.
        apply A3_sw; auto.
        change (ssubst_s w2 x1 w12_2 ==>s s12'2 [:s_lam SS12_11' s12_12']).
        rewrite (ssubst_s_intro x1); auto.
    SSCase "s12'1 is a lam".
      simpl in Hpar12_1.
      apply A14_lam with (L:=empty) in Hpar12_1.
      destruct Hpar12_1 as [SS12_11 [s12_12 [Hstep2 [Hpar12_11 Hpar12_12]]]].
      inversion H10.
      change (is_w_of_s (s12'2 [:w2'])) in H7.
      rewrite (ssubst_s_intro x1) in H7; auto.
      pose proof (par_substw_inversion x1 Hpar12_2 H0 H7 H4 H).
      destruct H2 as [w12_2 [Hstep12_2 [Hparw12_2 Hw12_2]]].
      pick_fresh x2. move Fr0 at top. assert (x2 `notin` empty) as Hx2 by auto.
      specialize (Hpar12_12 _ Hx2).
      exists (ssubst_s (ssubst_s w2 x1 w12_2) x2 (ssubst_s w2 x1 s12_12 [:s_var_f x2])).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_Beta; auto.
        apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)); auto.
        rewrite (ssubst_s_intro x1).
        eapply evalh_trans. apply (A10 Hstep12); auto. simpl.
        eapply evalh_trans. apply eval_app_congr1. apply (A10 Hstep2); auto.
          apply ssubst_s_lc_s; auto.
        eapply evalh_trans. apply (eval_app_congr2 Hstep12_2); auto.
          apply ssubst_s_lc_s; auto. simpl; auto. simpl.
        eapply F_Step. apply F_Reduce. apply F_Beta; auto.
        apply (lc_s_lam_exists x2); auto using ssubst_SS_lc_SS.
        rewrite ssubst_s_open_s_wrt_s_var; auto. apply ssubst_s_lc_s; auto.
        rewrite (ssubst_s_intro x2); auto.
        apply F_Refl; auto.
        apply ssubst_s_lc_s; auto.
        rewrite ssubst_s_open_s_wrt_s_var; auto.
        apply ssubst_s_lc_s; auto. default_simp. auto.
      SSSCase "==>s".
        pattern (open_s_wrt_s_rec 1 w2' s12'1 [:open_s_wrt_s_rec 0 w2' s12'2]).
        rewrite (ssubst_s_intro x2); auto.
        apply A3_sw; auto.
        rewrite ssubst_s_open_s_wrt_s_var; auto.
        rewrite ssubst_s_intro_rec with (x1:=x1).
        rewrite ssubst_s_open_s_wrt_s_var; auto.
        apply A3_sw; auto. default_simp.
        rewrite ssubst_s_intro_rec with (x1:=x1); auto. default_simp.
  SCase "F_RCCheck".
    clear IHparreds.
    unfold open_s_wrt_s in H6; destruct s12'; simpl in H6; try solve by inversion.
    destruct n; simpl in H6; try subst w2'; try inversion H0; try inversion H6; solve by inversion.
    inversion H6; subst. clear H6 H3.
    destruct s12'1; simpl in H11; try solve by inversion.
    SSCase "s12'1 is a var, w2' is a cast, s12'2 is s_const k5".
      destruct n; simpl in H11; try solve by inversion. subst w2'.
      destruct s12'2; simpl in H12; try solve by inversion.
      destruct n; simpl in H12; try solve by inversion. inversion H12. subst k. clear H12.
      apply A14_cast in H4. destruct H4 as [SS1 [SS2 [Hstep2 [HparSS1 HparSS2]]]].
      apply w_only_reflstep in Hstep2; auto.
      pose proof (proj1 (lc_parredSS HparSS1)) as HlcSS1.
      pose proof (proj1 (lc_parredSS HparSS2)) as HlcSS2.
      apply parallel_ref_rev with (L:=sfv_s s1) in HparSS1.
      destruct HparSS1 as [s21 [HeqSS1 Hpars21]].
      apply parallel_ref_rev with (L:=sfv_s s2) in HparSS2.
      destruct HparSS2 as [s22 [HeqSS2 Hpars22]].
      pick_fresh x1. assert (x1 `notin` L) as HnoL by auto. move Fr at top.
      specialize (H2 x1 HnoL). subst SS1 SS2. move Fr at top.
      assert (lc_s w2) as Hlcw2 by (subst w2; auto).
      replace (s_app (s_var_b 0) (s_const k5) [:s_var_f x1])
        with  (s_app (s_var_f x1) (s_const k5)) in H2 by auto.
      apply A11 in H2. destruct H2 as [s12_1 [s12_2 [Hstep12 [Hpar12_1 Hpar12_2]]]].
      apply A13 in Hpar12_1. apply A14_k in Hpar12_2.
      assert (x1 `notin` sfv_s s1) by auto. specialize (Hpars21 _ H2). clear H2.
      assert (x1 `notin` sfv_s s2) by auto. specialize (Hpars22 _ H2). clear H2.
      exists (s_check (SS_refinement B5 s22) (ssubst_s (s_const k5) x1 (s22 [:s_var_f x1])) k5 l5).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_Beta; auto.
        apply (lc_s_lam_exists x1); auto.
        rewrite (ssubst_s_intro x1); auto.
        eapply evalh_trans. apply A10. apply Hstep12. auto. simpl.
        eapply evalh_trans. apply eval_app_congr1.
          apply A10. apply Hpar12_1. auto. apply ssubst_s_lc_s; auto.
        replace (ssubst_s w2 x1 (s_var_f x1)) with w2 by default_simp.
        eapply evalh_trans. apply eval_app_congr2. apply A10. apply Hpar12_2.
          auto. auto. auto.
        replace (ssubst_s w2 x1 (s_const k5)) with (s_const k5) by default_simp. subst w2.
        eapply F_Step. apply F_Reduce. apply F_CCheck; auto.
        rewrite (ssubst_s_intro x1); auto. apply F_Refl; auto using ssubst_s_lc_s.
      SSSCase "==>s".
        apply P_Check; auto. apply P_SSRefine with (L:=singleton x1); auto.
        intros z Frz. rewrite (ssubst_s_intro x1); auto.
        pattern (s2 [:s_var_f z]). rewrite (ssubst_s_intro x1); auto.
        apply A3_sw; auto.
        pattern (s2 [:s_const k5]). rewrite (ssubst_s_intro x1); auto.
        apply A3_sw; auto.
    SSCase "s12'1 is a check".
      destruct s; simpl in H11; try solve by inversion.
      destruct s0; simpl in H11; try solve by inversion.
      inversion H11; subst. rename b0 into B. rename s into s121_1, s0 into s121_2. clear H11 H5.
      pick_fresh x1. assert (x1 `notin` L) as HnoL by auto. move Fr at top.
      specialize (H2 x1 HnoL). unfold open_s_wrt_s in H2. simpl in H2.
      apply A11 in H2. destruct H2 as [s121 [s122 [Hstep12 [Hpar121 Hpar122]]]].
      apply A14_cast in Hpar121. destruct Hpar121 as [SS1 [SS2 [Hstep121 [HparSS1 HparSS2]]]].
      pose proof (proj1 (lc_parredSS HparSS1)) as HlcSS1.
      pose proof (proj1 (lc_parredSS HparSS2)) as HlcSS2.
      apply parallel_ref_rev with (L:=empty) in HparSS1.
      destruct HparSS1 as [s21 [HeqSS1 Hpars21]].
      apply parallel_ref_rev with (L:=empty) in HparSS2.
      destruct HparSS2 as [s22 [HeqSS2 Hpars22]]. subst SS1 SS2.
      destruct s12'2; simpl in H12; try inversion H12; try solve by inversion.
      SSSCase "s12'2 is a var, w2' = s_const k5".
        destruct n; simpl in H12; try solve by inversion. subst w2'. clear H3.
        apply parallel_const_rev in H4; auto using w_is_q. subst w2.
        clear H0 H HnoL H7. move Fr at top.
        simpl in Hpar122. apply A13 in Hpar122.
        assert (lc_SS (SS_refinement B (ssubst_s (s_const k5) x1 s21))) as Hlcs21.
          pick_fresh x2. inversion HlcSS1. apply (lc_SS_refinement_exists x2); auto.
          rewrite ssubst_s_open_s_wrt_s_var; auto. apply ssubst_s_lc_s; auto. auto.
        assert (lc_SS (SS_refinement B (ssubst_s (s_const k5) x1 s22))) as Hlcs22.
          pick_fresh x2. inversion HlcSS2. apply (lc_SS_refinement_exists x2); auto.
          rewrite ssubst_s_open_s_wrt_s_var; auto. apply ssubst_s_lc_s; auto. auto.
        exists (s_check (SS_refinement B (ssubst_s (s_const k5) x1 s22))
                        (ssubst_s (s_const k5) x1 s22 [:s_const k5])
                        k5 l).
        split.
        SSSSCase "-->h*".
          eapply F_Step. apply F_Reduce. apply F_Beta; simpl; auto.
          apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)); auto.
          rewrite (ssubst_s_intro x1); auto.
          eapply evalh_trans. apply A10. apply Hstep12. auto. simpl.
          eapply evalh_trans. apply eval_app_congr1. apply A10. apply Hstep121.
            auto. apply ssubst_s_lc_s; auto.
          eapply evalh_trans. apply eval_app_congr2. apply A10. apply Hpar122.
            auto. apply ssubst_s_lc_s; auto. apply ssubst_w; simpl; auto.
          replace (ssubst_s (s_const k5) x1 (s_var_f x1)) with (s_const k5) by default_simp.
          simpl. eapply F_Step. apply F_Reduce. apply F_CCheck; simpl; auto.
          apply F_Refl; auto. apply lc_s_check; auto.
          replace (s_const k5) with (ssubst_s (s_const k5) x1 (s_const k5)) by auto.
          rewrite <- ssubst_s_open_s_wrt_s; auto.
          apply ssubst_s_lc_s; auto.
          inversion HlcSS2. pick_fresh x2. rewrite (ssubst_s_intro x2); auto.
          apply ssubst_s_lc_s; auto.
        SSSSCase "==>s".
          apply P_Check; auto. apply P_SSRefine with (L:=singleton x1); auto.
          (* stored type *)
            intros z Frz. assert (z `notin` empty) as Hz by auto. specialize (Hpars22 z Hz).
            rewrite ssubst_s_intro_rec with (x1:=x1); auto.
            rewrite ssubst_s_open_s_wrt_s_var; auto.
            rewrite ssubst_s_open_s_wrt_s_var; auto.
            apply A3_sw; auto.
          (* predicate *)
            rewrite ssubst_s_intro_rec with (x1:=x1); auto.
            pick_fresh x2. move Fr0 at top. 
            rewrite (ssubst_s_intro x2); auto.
            pattern (ssubst_s (s_const k5) x1 (open_s_wrt_s_rec 1 (s_var_f x1) s121_2) [:s_const k5]).
            rewrite (ssubst_s_intro x2); auto.
            apply A3_sw; auto.
            assert (x2 `notin` empty) as Hx2 by auto. specialize (Hpars22 x2 Hx2). 
            rewrite ssubst_s_open_s_wrt_s_var; auto.
            rewrite ssubst_s_open_s_wrt_s_var; auto.
            apply A3_sw; auto.
            apply sfv_s_ssubst_s_notin; auto.
            pose proof (sfv_s_open_s_wrt_s_rec_upper s121_2 (s_var_f x1) 1).
            assert (x2 `notin` union (sfv_s (s_var_f x1)) (sfv_s s121_2)) by auto.
            auto. apply sfv_s_ssubst_s_notin; auto.
      SSSCase "s12'2 = s_const k5".
        subst k. clear H12 HnoL H7.
        simpl in Hpar122. apply A14_k in Hpar122.
        assert (lc_SS (SS_refinement B (ssubst_s w2 x1 s21))) as HlcSS1_subst.
          pick_fresh x2. inversion HlcSS1. apply (lc_SS_refinement_exists x2); auto.
          rewrite ssubst_s_open_s_wrt_s_var; auto. apply ssubst_s_lc_s; auto. auto.
        assert (lc_SS (SS_refinement B (ssubst_s w2 x1 s22))) as HlcSS2_subst.
          pick_fresh x2. inversion HlcSS2. apply (lc_SS_refinement_exists x2); auto.
          rewrite ssubst_s_open_s_wrt_s_var; auto. apply ssubst_s_lc_s; auto. auto.
        exists (s_check (SS_refinement B (ssubst_s w2 x1 s22))
                        (ssubst_s w2 x1 s22 [:s_const k5]) k5 l).
        split.
        SSSSCase "-->h*".
          eapply F_Step. apply F_Reduce. apply F_Beta; simpl; auto.
          apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)); auto.
          rewrite (ssubst_s_intro x1); auto.
          eapply evalh_trans. apply A10. apply Hstep12. auto. simpl.
          eapply evalh_trans. apply eval_app_congr1. apply A10. apply Hstep121.
            auto. apply ssubst_s_lc_s; auto.
          eapply evalh_trans. apply eval_app_congr2. apply A10. apply Hpar122.
            auto. apply ssubst_s_lc_s; auto. apply ssubst_w; simpl; auto.
          replace (ssubst_s w2 x1 (s_const k5)) with (s_const k5) by default_simp.
          simpl. eapply F_Step. apply F_Reduce. apply F_CCheck; simpl; auto.
          apply F_Refl; auto. apply lc_s_check; auto.
          replace (s_const k5) with (ssubst_s w2 x1 (s_const k5)) by auto.
          rewrite <- ssubst_s_open_s_wrt_s; auto.
          apply ssubst_s_lc_s; auto.
          inversion HlcSS2. pick_fresh x2. rewrite (ssubst_s_intro x2); auto.
          apply ssubst_s_lc_s; auto.
        SSSSCase "==>s".
          apply P_Check; auto. apply P_SSRefine with (L:=singleton x1); auto.
          (* stored type *)
            intros z Frz. assert (z `notin` empty) as Hz by auto. specialize (Hpars22 z Hz).
            rewrite ssubst_s_intro_rec with (x1:=x1); auto.
            rewrite ssubst_s_open_s_wrt_s_var; auto.
            rewrite ssubst_s_open_s_wrt_s_var; auto.
            apply A3_sw; auto.
          (* predicate *)
            rewrite ssubst_s_intro_rec with (x1:=x1); auto.
            pick_fresh x2. move Fr0 at top. 
            rewrite (ssubst_s_intro x2); auto.
            pattern (ssubst_s w2' x1 (open_s_wrt_s_rec 1 (s_var_f x1) s121_2) [:s_const k5]).
            rewrite (ssubst_s_intro x2); auto.
            apply A3_sw; auto.
            assert (x2 `notin` empty) as Hx2 by auto. specialize (Hpars22 x2 Hx2). 
            rewrite ssubst_s_open_s_wrt_s_var; auto.
            rewrite ssubst_s_open_s_wrt_s_var; auto.
            apply A3_sw; auto.
            apply sfv_s_ssubst_s_notin; auto.
            pose proof (sfv_s_open_s_wrt_s_rec_upper s121_2 (s_var_f x1) 1).
            assert (x2 `notin` union (sfv_s (s_var_f x1)) (sfv_s s121_2)) by auto.
            auto. apply sfv_s_ssubst_s_notin; auto.
  SCase "F_ROK".
    destruct s12'; unfold open_s_wrt_s in H6; simpl in H6; try solve by inversion.
    destruct n; simpl in H6; try subst w2'; simpl in H0; solve by inversion.
    inversion H6; subst. rename s into SS1. inversion H6; subst.
    destruct s12'; simpl in H10; try solve by inversion.
    SSCase "s12' is a var".
      destruct n; simpl in H10; try solve by inversion. subst w2'.
      clear H11 H6 H7 H0 H3 IHparreds.
      apply parallel_const_rev in H4; auto using w_is_q. subst w2.
      pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
      specialize (H2 x1 HnoL).
      unfold open_s_wrt_s in H2; simpl in H2. apply A12 in H2; auto.
      destruct H2 as [SS2 [s2 [Hstep12 [HparSS2 Hpars2]]]].
      apply A13 in Hpars2.
      exists (s_const k).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_Beta; auto.
        apply (lc_s_lam_exists x1); auto.
        apply (proj1 (lc_evalh Hstep12)).
        eapply evalh_trans. rewrite (ssubst_s_intro x1); auto.
          apply A10. apply Hstep12. auto. simpl.
        eapply evalh_trans. apply eval_check_congr.
          apply A10. apply Hpars2. auto. apply ssubst_SS_lc_SS; auto.
        replace (ssubst_s (s_const k_true) x1 (s_var_f x1))
           with (s_const k_true) by default_simp.
        eapply F_Step. apply F_Reduce. apply F_OK; auto. apply ssubst_SS_lc_SS; auto.
        apply F_Refl; auto.
      SSSCase "==>s".
        auto.
    SSCase "k0 = k_true".
      inversion H10; subst. clear H10 H11 H6 H7 IHparreds H3.
      pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
      specialize (H2 x1 HnoL).
      unfold open_s_wrt_s in H2; simpl in H2. apply A12 in H2.
      destruct H2 as [SS2 [s2 [Hstep12 [HparSS2 Hpars2]]]].
      apply A14_k in Hpars2.
      exists (s_const k).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_Beta; auto.
        apply (lc_s_lam_exists x1); auto.
        apply (proj1 (lc_evalh Hstep12)).
        eapply evalh_trans. rewrite (ssubst_s_intro x1); auto.
          apply A10. apply Hstep12. auto. simpl.
        eapply evalh_trans. apply eval_check_congr.
          apply A10. apply Hpars2. auto. apply ssubst_SS_lc_SS; auto.
        replace (ssubst_s w2 x1 (s_const k_true))
           with (s_const k_true) by auto.
        eapply F_Step. apply F_Reduce. apply F_OK; auto. apply ssubst_SS_lc_SS; auto.
        apply F_Refl; auto.
      SSSCase "==>s".
        auto.
  SCase "F_RFail".
    destruct s12'; unfold open_s_wrt_s in H6; simpl in H6; try solve by inversion.
    destruct n; simpl in H6; try subst w2'; simpl in H0; solve by inversion.
    inversion H6; subst. rename s into SS1. inversion H6; subst.
    destruct s12'; simpl in H10; try solve by inversion.
    SSCase "s12' is a var".
      destruct n; simpl in H10; try solve by inversion. subst w2'.
      clear H11 H6 H7 H0 H3 IHparreds.
      apply parallel_const_rev in H4; auto using w_is_q. subst w2.
      pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
      specialize (H2 x1 HnoL).
      unfold open_s_wrt_s in H2; simpl in H2. apply A12 in H2; auto.
      destruct H2 as [SS2 [s2 [Hstep12 [HparSS2 Hpars2]]]].
      apply A13 in Hpars2.
      exists (s_blame (b_blame l)).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_Beta; auto.
        apply (lc_s_lam_exists x1); auto.
        apply (proj1 (lc_evalh Hstep12)).
        eapply evalh_trans. rewrite (ssubst_s_intro x1); auto.
          apply A10. apply Hstep12. auto. simpl.
        eapply evalh_trans. apply eval_check_congr.
          apply A10. apply Hpars2. auto. apply ssubst_SS_lc_SS; auto.
        replace (ssubst_s (s_const k_false) x1 (s_var_f x1))
           with (s_const k_false) by default_simp.
        eapply F_Step. apply F_Reduce. apply F_Fail; auto. apply ssubst_SS_lc_SS; auto.
        apply F_Refl; auto.
      SSSCase "==>s".
        auto.
    SSCase "k0 = k_true".
      inversion H10; subst. clear H10 H11 H6 H7 IHparreds H3.
      pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
      specialize (H2 x1 HnoL).
      unfold open_s_wrt_s in H2; simpl in H2. apply A12 in H2.
      destruct H2 as [SS2 [s2 [Hstep12 [HparSS2 Hpars2]]]].
      apply A14_k in Hpars2.
      exists (s_blame (b_blame l)).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_Beta; auto.
        apply (lc_s_lam_exists x1); auto.
        apply (proj1 (lc_evalh Hstep12)).
        eapply evalh_trans. rewrite (ssubst_s_intro x1); auto.
          apply A10. apply Hstep12. auto. simpl.
        eapply evalh_trans. apply eval_check_congr.
          apply A10. apply Hpars2. auto. apply ssubst_SS_lc_SS; auto.
        replace (ssubst_s w2 x1 (s_const k_false))
           with (s_const k_false) by auto.
        eapply F_Step. apply F_Reduce. apply F_Fail; auto. apply ssubst_SS_lc_SS; auto.
        apply F_Refl; auto.
      SSSCase "==>s".
        auto.
  SCase "F_RCDecomp".
    clear IHparreds H3. rename SS11 into SS11', SS12 into SS12', SS21 into SS21', SS22 into SS22'.
    unfold open_s_wrt_s in H6.
    destruct s12'; try solve by inversion.
    SSCase "s12' = var (contra)".
      destruct n; simpl in H6; try solve by inversion; inversion H6.
      unfold open_s_wrt_s in H5; simpl in H5. subst w2'.
      destruct w'; inversion H0; try solve by inversion.
    SSCase "s12' = s_app s12'1 s12'2".
      simpl in H6.
      destruct s12'1; try solve by inversion.
      SSSCase "s12'1 is a var".
        destruct n; try solve by inversion.
        simpl in H6. inversion H6.
        pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
        specialize (H2 x1 HnoL).
        unfold open_s_wrt_s in H2; simpl in H2. apply A11 in H2.
        destruct H2 as [s12_1 [s12_2 [Hstep12 [Hpar12_1 Hpar12_2]]]].
        apply A13 in Hpar12_1.
        subst. move Fr at top.
        unfold open_s_wrt_s in H5; simpl in H5. clear H6 H9.
        apply A11 in H4. destruct H4 as [s21 [s22 [Hstep2 [Hpar21 Hpar22]]]].
        apply w_only_reflstep in Hstep2; auto. subst w2. move Fr at top.
        simpl in H. destruct H as [Hh21 Hw22].
        apply A14_cast in Hpar21. destruct Hpar21 as [SS1 [SS2 [Hstep21 [HparSS1 HparSS2]]]].
        apply w_only_reflstep in Hstep21; auto using h_is_w. subst s21. move Fr at top.
        apply parallel_fun_rev with (L:=sfv_SS SS12') in HparSS1.
        destruct HparSS1 as [SS11 [SS12 [HeqSS1 [HparSS11 HparSS12]]]].
        apply parallel_fun_rev with (L:=sfv_SS SS22') in HparSS2.
        destruct HparSS2 as [SS21 [SS22 [HeqSS2 [HparSS21 HparSS22]]]]. subst SS1 SS2. move Fr at top.
        clear H5.
        assert (lc_SS (SS11 :-> SS12)) as HlcSS1.
          assert (x1 `notin` sfv_SS SS12') by auto. specialize (HparSS12 x1 H).
          apply (lc_SS_darrow_exists x1); auto.
        assert (lc_SS (SS21 :-> SS22)) as HlcSS2.
          assert (x1 `notin` sfv_SS SS22') by auto. specialize (HparSS22 x1 H).
          apply (lc_SS_darrow_exists x1); auto.
        assert ((SS11 :-> SS12) ==>S (SS11' :-> SS12')) as HparSS1.
          pick_fresh x2.
          apply P_SSFun with (L:=singleton x2); auto.
          intros z Frz. rewrite (ssubst_SS_intro x2); auto.
          pattern (SS12' [:=s_var_f z]). rewrite (ssubst_SS_intro x2); auto.
          apply A3_SSw; auto.
        assert ((SS21 :-> SS22) ==>S (SS21' :-> SS22')) as HparSS2.
          pick_fresh x2.
          apply P_SSFun with (L:=singleton x2); auto.
          intros z Frz. rewrite (ssubst_SS_intro x2); auto.
          pattern (SS22' [:=s_var_f z]). rewrite (ssubst_SS_intro x2); auto.
          apply A3_SSw; auto.
        remember (s_app (s_cast (SS11 :-> SS12) (SS21 :-> SS22) l5) s22) as h2.
        assert (h2 ==>s
                s_app (s_cast (SS11' :-> SS12') (SS21' :-> SS22') l5) w5) as Hparh by (subst h2; auto).
        assert (is_w_of_s h2) as Hh by (subst h2; simpl; auto).
        change (is_w_of_s (s12'2 [:s_app (s_cast (SS11' :-> SS12') (SS21' :-> SS22') l5) w5])) in H8.
        rewrite (ssubst_s_intro x1) in H8.
        pose proof (par_substw_inversion x1 Hpar12_2 H0 H8 Hparh Hh).
        destruct H as [s12_2' [Hstep12_2' [Hpar12_2' Hw12_2']]].
        exists (s_app (s_cast (SS12 [:=s_app (s_cast SS21 SS11 l5) (ssubst_s h2 x1 s12_2')])
                              (SS22 [:=ssubst_s h2 x1 s12_2']) l5)
                      (s_app s22 
                             (s_app (s_cast SS21 SS11 l5)
                                    (ssubst_s h2 x1 s12_2')))).
        split.
        SSSSCase "-->h*".
          eapply F_Step. apply F_Reduce. apply F_Beta; simpl; auto.
          apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)).
          eapply evalh_trans. rewrite (ssubst_s_intro x1); auto. apply (A10 Hstep12); auto. simpl.
          eapply evalh_trans. apply eval_app_congr1. apply (A10 Hpar12_1); auto.
            apply ssubst_s_lc_s; auto.
          replace (ssubst_s h2 x1 (s_var_f x1)) with h2 by default_simp.
          eapply evalh_trans. apply (eval_app_congr2 Hstep12_2'); auto.
          rewrite Heqh2 at 1.
          eapply F_Step. apply F_Reduce. apply F_CDecomp; auto.
          inversion HlcSS1; subst. inversion HlcSS2; subst.
          apply F_Refl; auto. apply lc_s_app; auto. apply lc_s_cast; auto.
          pick_fresh x2. rewrite (ssubst_SS_intro x2); auto. apply ssubst_SS_lc_SS; auto.
          pick_fresh x2. rewrite (ssubst_SS_intro x2); auto. apply ssubst_SS_lc_SS; auto.
        SSSSCase "==>s".
          replace (open_s_wrt_s_rec 0 (s_app (s_cast (SS11' :-> SS12') (SS21' :-> SS22') l5) w5) s12'2)
            with (s12'2 [:s_app (s_cast (SS11' :-> SS12') (SS21' :-> SS22') l5) w5]) by auto.
          apply P_App. pick_fresh x2.
          apply P_Cast. rewrite (ssubst_SS_intro x2); auto.
          pattern (SS12' [:=s_app (s_cast SS21' SS11' l5)
                                  (s12'2 [:s_app (s_cast (SS11' :-> SS12') (SS21' :-> SS22') l5) w5])]).
          rewrite (ssubst_SS_intro x2); auto.
          apply A3_SSw; auto.
          apply P_App; auto.
          rewrite (ssubst_s_intro x1); auto.
          rewrite (ssubst_SS_intro x2); auto.
          pattern (SS22' [:=s12'2 [:s_app (s_cast (SS11' :-> SS12') (SS21' :-> SS22') l5) w5]]).
          rewrite (ssubst_SS_intro x2); auto.
          apply A3_SSw; auto.
          rewrite (ssubst_s_intro x1); auto.
          rewrite (ssubst_s_intro x1); auto.
          auto.
      SSSCase "s12'1 is an app".
        pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
        specialize (H2 x1 HnoL).
        unfold open_s_wrt_s in H2; simpl in H2. apply A11 in H2.
        destruct H2 as [s12_1 [s12_2 [Hstep12 [Hpar12_1 Hpar12_2]]]].
        apply A11 in Hpar12_1.
        destruct Hpar12_1 as [s12_11 [s12_12 [Hsteps12_1 [Hpars12_1 Hpars12_2]]]].
        destruct s12'1_1; simpl in H6; try solve by inversion.
        SSSSCase "s12'1_1 is a var, w2' is a cast".
          destruct n; simpl in H6; try solve by inversion. inversion H6.
          subst w2'. move Fr at top.
          apply A14_cast in H4. destruct H4 as [SS1 [SS2 [Hstepw2 [HparSS1 HparSS2]]]].
          apply w_only_reflstep in Hstepw2; auto.
          pose proof (proj1 (lc_parredSS HparSS1)) as HlcSS1.
          pose proof (proj1 (lc_parredSS HparSS2)) as HlcSS2.
          apply parallel_fun_rev with (L:=L) in HparSS1.
          destruct HparSS1 as [SS11 [SS12 [HeqSS1 [HparSS11 HparSS12]]]].
          apply parallel_fun_rev with (L:=L) in HparSS2.
          destruct HparSS2 as [SS21 [SS22 [HeqSS2 [HparSS21 HparSS22]]]].
          remember (s_cast (SS11' :-> SS12') (SS21' :-> SS22') l5) as h2'.
          assert (is_h_of_s w2) as Hhw2 by (subst w2 SS1 SS2; simpl; auto).
          assert (w2 ==>s h2') as Hparw2.
            subst w2 SS1 SS2 h2'; apply P_Cast; auto.
            apply P_SSFun with (L:=L); eauto.
            apply P_SSFun with (L:=L); eauto.
          clear H5 H9. rename H14 into Heqw5, H15 into Heqw'. rename H0 into Hh2'.
          simpl in Hpars12_1. apply A13 in Hpars12_1.
          rewrite ssubst_s_intro_rec with (x1:=x1) in Heqw5; auto. subst w5. move Fr at top.
          rewrite ssubst_s_intro_rec with (x1:=x1) in Heqw'; auto. subst w'. move Fr at top.
          pose proof (par_substw_inversion x1 Hpars12_2 Hh2' H7 Hparw2 H).
          destruct H0 as [s12_12' [Hstep12_12 [Hpar12_12' Hw12_12']]].
          pose proof (par_substw_inversion x1 Hpar12_2 Hh2' H8 Hparw2 H).
          destruct H0 as [s12_2' [Hstep12_2 [Hpar12_2' Hw12_2']]].
          subst SS1 SS2. move Fr at top.
          exists (s_app (s_cast (SS12 [:=s_app (s_cast SS21 SS11 l5) (ssubst_s w2 x1 s12_2')])
                                (SS22 [:=ssubst_s w2 x1 s12_2']) l5)
                        (s_app (ssubst_s w2 x1 s12_12')
                               (s_app (s_cast SS21 SS11 l5)
                                      (ssubst_s w2 x1 s12_2')))).
          split.
          (* SSSSSCase "-->h*". *)
            eapply F_Step. apply F_Reduce. apply F_Beta; simpl; auto.
            apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)).
            eapply evalh_trans. rewrite (ssubst_s_intro x1); auto. apply (A10 Hstep12); auto. simpl.
            eapply evalh_trans. apply eval_app_congr1. apply (A10 Hsteps12_1); auto.
              apply ssubst_s_lc_s; auto. simpl.
            eapply evalh_trans. apply eval_app_congr1. apply eval_app_congr1.
              apply (A10 Hpars12_1); auto. apply ssubst_s_lc_s; auto. apply ssubst_s_lc_s; auto. 
            replace (ssubst_s w2 x1 (s_var_f x1)) with w2 by default_simp.
            eapply evalh_trans. apply eval_app_congr1. apply (eval_app_congr2 Hstep12_12); auto.
              apply ssubst_s_lc_s; auto.
            eapply evalh_trans. apply (eval_app_congr2 Hstep12_2); simpl; auto. 
            rewrite Hstepw2 at 1.
            eapply F_Step. apply F_Reduce. apply F_CDecomp; auto.
            inversion HlcSS1; subst. inversion HlcSS2; subst.
            apply F_Refl; auto. apply lc_s_app; auto. apply lc_s_cast; auto.
            pick_fresh x2. rewrite (ssubst_SS_intro x2); auto. apply ssubst_SS_lc_SS; auto.
            pick_fresh x2. rewrite (ssubst_SS_intro x2); auto. apply ssubst_SS_lc_SS; auto.
          (* SSSSSCase "==>s". *)
            replace (open_s_wrt_s_rec 0 h2' s12'2)
              with (s12'2 [:h2']) by auto.
            apply P_App. pick_fresh x2. move Fr0 at top.
            apply P_Cast. rewrite (ssubst_SS_intro x2); auto.
            pattern (SS12' [:=s_app (s_cast SS21' SS11' l5)
                                    (s12'2 [:h2'])]).
            rewrite (ssubst_SS_intro x2); auto.
            apply A3_SSw; auto.
            apply P_App; auto.
            rewrite (ssubst_s_intro x1); auto.
            rewrite (ssubst_SS_intro x2); auto.
            pattern (SS22' [:=s12'2 [:h2']]).
            rewrite (ssubst_SS_intro x2); auto.
            apply A3_SSw; auto.
            rewrite (ssubst_s_intro x1); auto.
            rewrite (ssubst_s_intro x1); auto.
            rewrite ssubst_s_intro_rec with (x1:=x1); auto.
        SSSSCase "s12'1_1 is a cast".
          rename s into SS1', s0 into SS2'. inversion H6; subst. move Fr at top. clear H5 H9.
          simpl in Hpars12_1.
          apply A14_cast in Hpars12_1.
          destruct Hpars12_1 as [SS1 [SS2 [Hsteps12_11 [HparSS1 HparSS2]]]].
          pose proof (proj1 (lc_parredSS HparSS1)) as HlcSS1.
          pose proof (proj1 (lc_parredSS HparSS2)) as HlcSS2.
          destruct SS1'; simpl in H3; try solve by inversion.
          destruct SS2'; simpl in H14; try solve by inversion.
          simpl in HparSS1, HparSS2.
          apply parallel_fun_rev with (L:=L) in HparSS1.
          destruct HparSS1 as [SS11 [SS12 [HeqSS1 [HparSS11 HparSS12]]]].
          apply parallel_fun_rev with (L:=L) in HparSS2.
          destruct HparSS2 as [SS21 [SS22 [HeqSS2 [HparSS21 HparSS22]]]].
          remember (s_cast SS1 SS2 l) as h2.
          remember (s_cast (SS11' :-> SS12') (SS21' :-> SS22') l) as h2'.
          assert (is_h_of_s h2) as Hh2 by (subst h2 SS1 SS2; simpl; auto).
          rewrite ssubst_s_intro_rec with (x1:=x1) in H7.
          pose proof (par_substw_inversion x1 Hpars12_2 H0 H7 H4 H).
          destruct H2 as [s12_12' [Hstep12_12 [Hpar12_12' Hw12_12']]].
          rewrite ssubst_s_intro_rec with (x1:=x1) in H8.
          pose proof (par_substw_inversion x1 Hpar12_2 H0 H8 H4 H).
          destruct H2 as [s12_2' [Hstep12_2 [Hpar12_2' Hw12_2']]].
          subst SS1 SS2. move Fr at top.
          assert (is_w_of_s (s_app (ssubst_s w2 x1 h2) (ssubst_s w2 x1 s12_12'))) as Hwrapped.
            subst h2; simpl; auto using ssubst_w.
          exists (s_app (s_cast (ssubst_SS w2 x1 SS12 [:=s_app (s_cast (ssubst_SS w2 x1 SS21) (ssubst_SS w2 x1 SS11) l) 
                                                               (ssubst_s w2 x1 s12_2')])
                                (ssubst_SS w2 x1 SS22 [:=ssubst_s w2 x1 s12_2']) l)
                        (s_app (ssubst_s w2 x1 s12_12')
                               (s_app (s_cast (ssubst_SS w2 x1 SS21) (ssubst_SS w2 x1 SS11) l)
                                      (ssubst_s w2 x1 s12_2')))).
          split.
          (* SSSSSCase "-->h*". *)
            eapply F_Step. apply F_Reduce. apply F_Beta; simpl; auto.
            apply (lc_s_lam_exists x1); auto. apply (proj1 (lc_evalh Hstep12)).
            eapply evalh_trans. rewrite (ssubst_s_intro x1); auto. apply (A10 Hstep12); auto. simpl.
            eapply evalh_trans. apply eval_app_congr1. apply (A10 Hsteps12_1); auto.
              apply ssubst_s_lc_s; auto. simpl.
            eapply evalh_trans. apply eval_app_congr1. apply eval_app_congr1.
              apply (A10 Hsteps12_11); auto. apply ssubst_s_lc_s; auto. apply ssubst_s_lc_s; auto. 
            eapply evalh_trans. apply eval_app_congr1. apply (eval_app_congr2 Hstep12_12); auto.
              apply ssubst_s_lc_s; auto. simpl in Hwrapped; auto. subst h2; auto using ssubst_w. simpl; auto.
              apply ssubst_s_lc_s; auto.
            eapply evalh_trans. apply (eval_app_congr2 Hstep12_2); simpl; auto.
              apply lc_s_app; auto using ssubst_s_lc_s.
              subst h2; auto using ssubst_w. simpl.
            eapply F_Step. apply F_Reduce. apply F_CDecomp; auto.
              change (lc_SS (ssubst_SS w2 x1 (SS11 :-> SS12))). auto using ssubst_SS_lc_SS.
              change (lc_SS (ssubst_SS w2 x1 (SS21 :-> SS22))). auto using ssubst_SS_lc_SS.
            inversion HlcSS1; subst. inversion HlcSS2; subst.
            apply F_Refl; auto. apply lc_s_app; auto. apply lc_s_cast; auto.
            pick_fresh x2. rewrite (ssubst_SS_intro x2);  auto using ssubst_SS_lc_SS.
              rewrite ssubst_SS_open_SS_wrt_s_var; auto using ssubst_SS_lc_SS.
              apply sfv_SS_ssubst_SS_notin; auto.
            pick_fresh x2. rewrite (ssubst_SS_intro x2);  auto using ssubst_SS_lc_SS.
              rewrite ssubst_SS_open_SS_wrt_s_var; auto using ssubst_SS_lc_SS.
              apply sfv_SS_ssubst_SS_notin; auto.
            apply lc_s_app; auto. apply lc_s_app; auto. apply lc_s_cast; auto using ssubst_SS_lc_SS.
          (* SSSSSCase "==>s". *)
            inversion H3; subst. inversion H14; subst. move Fr at top.
            replace (open_s_wrt_s_rec 0 w2' s12'2) with (s12'2 [:w2']) by auto.
            apply P_App. pick_fresh x2. move Fr0 at top.
            apply P_Cast. rewrite (ssubst_SS_intro x2); auto.
            pattern (open_SS_wrt_s_rec 1 w2' SS1'2 [:=s_app (s_cast (open_SS_wrt_s_rec 0 w2' SS2'1)
                                                                    (open_SS_wrt_s_rec 0 w2' SS1'1) l)
                                                            (s12'2 [:w2'])]).
            rewrite (ssubst_SS_intro x2); auto.
            apply A3_SSw; auto.
            rewrite ssubst_SS_open_SS_wrt_s_var; auto.
            rewrite ssubst_SS_intro_rec with (x1:=x1).
            rewrite ssubst_SS_open_SS_wrt_s_var; auto.
            apply A3_SSw; auto. default_simp.
            apply P_App; auto. apply P_Cast; auto.
            rewrite ssubst_SS_intro_rec with (x1:=x1); auto.
            apply A3_SSw; auto. default_simp.
            rewrite ssubst_SS_intro_rec with (x1:=x1); auto.
            apply A3_SSw; auto. default_simp.
            rewrite (ssubst_s_intro x1); auto.
            pose proof (sfv_SS_open_SS_wrt_s_rec_upper SS1'2 w2' 1).
            assert (x2 `notin` union (sfv_s w2') (sfv_SS SS1'2)) by auto.
            auto.
            apply sfv_SS_ssubst_SS_notin; auto.
            rewrite (ssubst_SS_intro x2); auto.
            rewrite ssubst_SS_intro_rec with (x1:=x1); auto.
            pattern (ssubst_SS w2' x1 (open_SS_wrt_s_rec 1 (s_var_f x1) SS2'2) [:=s12'2 [:w2']]).
            rewrite (ssubst_SS_intro x2); auto.
            rewrite (ssubst_s_intro x1); auto.
            apply A3_SSw; auto.
            rewrite ssubst_SS_open_SS_wrt_s_var; auto.
            rewrite ssubst_SS_open_SS_wrt_s_var; auto.
            apply A3_SSw; auto.
            apply sfv_SS_ssubst_SS_notin; auto.
            pose proof (sfv_SS_open_SS_wrt_s_rec_upper SS2'2 (s_var_f x1) 1).
            assert (x2 `notin` union (sfv_s (s_var_f x1)) (sfv_SS SS2'2)) by auto.
            auto. default_simp.
            apply sfv_SS_ssubst_SS_notin; auto.
            apply P_App; auto.
            rewrite ssubst_s_intro_rec with (x1:=x1); auto.
            apply P_App; auto. apply P_Cast; auto.
            rewrite ssubst_SS_intro_rec with (x1:=x1); auto. apply A3_SSw; auto.
            default_simp.
            rewrite ssubst_SS_intro_rec with (x1:=x1); auto. apply A3_SSw; auto.
            default_simp.
            rewrite (ssubst_s_intro x1); auto using A3_sw. default_simp. default_simp.
Case "P_RCCheck".
  inversion H3; subst.
  SCase "F_ROK".
    destruct s2'; subst; try solve by inversion.
    SSCase "k5 = k_true".
      destruct n; unfold open_s_wrt_s in H5; simpl in H5; try solve by inversion.
      inversion H5; subst k5. clear H H9 H5 H2.
      pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
      specialize (H1 x1 HnoL).
      replace (s_var_b 0 [:s_var_f x1]) with (s_var_f x1) in H1 by auto.
      apply A13 in H1.
      assert (lc_SS (SS_refinement B5 s2)) as HlcSS2.
        apply (lc_SS_refinement_exists x1); auto.
      exists (s_const k_true).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_CCheck; auto.
        eapply evalh_trans. apply eval_check_congr.
        rewrite (ssubst_s_intro x1); auto.
        apply A10. apply H1. auto. auto.
        replace (ssubst_s (s_const k_true) x1 (s_var_f x1))
          with  (s_const k_true) by default_simp.
        eapply F_Step. apply F_Reduce. apply F_OK; auto.
        auto.
      SSSCase "==>s".
        auto.
    SSCase "s2' = s_const (k_true)".
      unfold open_s_wrt_s in H5. simpl in H5. inversion H5; subst.
      clear H5 H2 H H9.
      pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
      specialize (H1 x1 HnoL).
      replace (s_const k_true [:s_var_f x1]) with (s_const k_true) in H1 by auto.
      apply A14_k in H1.
      assert (lc_SS (SS_refinement B5 s2)) as HlcSS2.
        apply (lc_SS_refinement_exists x1); auto.
      exists (s_const k5).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_CCheck; auto.
        eapply evalh_trans. apply eval_check_congr.
        rewrite (ssubst_s_intro x1); auto.
        apply A10. apply H1. auto. auto.
        replace (ssubst_s (s_const k5) x1 (s_const k_true))
          with  (s_const k_true) by auto.
        eapply F_Step. apply F_Reduce. apply F_OK; auto.
        auto.
      SSSCase "==>s".
        auto.
  SCase "F_RFail".
    destruct s2'; subst; try solve by inversion.
    SSCase "k5 = k_true".
      destruct n; unfold open_s_wrt_s in H5; simpl in H5; try solve by inversion.
      inversion H5; subst k5. clear H H9 H5 H2.
      pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
      specialize (H1 x1 HnoL).
      replace (s_var_b 0 [:s_var_f x1]) with (s_var_f x1) in H1 by auto.
      apply A13 in H1.
      assert (lc_SS (SS_refinement B5 s2)) as HlcSS2.
        apply (lc_SS_refinement_exists x1); auto.
      exists (s_blame (b_blame l5)).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_CCheck; auto.
        eapply evalh_trans. apply eval_check_congr.
        rewrite (ssubst_s_intro x1); auto.
        apply A10. apply H1. auto. auto.
        replace (ssubst_s (s_const k_false) x1 (s_var_f x1))
          with  (s_const k_false) by default_simp.
        eapply F_Step. apply F_Reduce. apply F_Fail; auto.
        auto.
      SSSCase "==>s".
        auto.
    SSCase "s2' = s_const (k_false)".
      unfold open_s_wrt_s in H5. simpl in H5. inversion H5; subst.
      clear H5 H2 H H9.
      pick_fresh x1. move Fr at top. assert (x1 `notin` L) as HnoL by auto.
      specialize (H1 x1 HnoL).
      replace (s_const k_false [:s_var_f x1]) with (s_const k_false) in H1 by auto.
      apply A14_k in H1.
      assert (lc_SS (SS_refinement B5 s2)) as HlcSS2.
        apply (lc_SS_refinement_exists x1); auto.
      exists (s_blame (b_blame l5)).
      split.
      SSSCase "-->h*".
        eapply F_Step. apply F_Reduce. apply F_CCheck; auto.
        eapply evalh_trans. apply eval_check_congr.
        rewrite (ssubst_s_intro x1); auto.
        apply A10. apply H1. auto. auto.
        replace (ssubst_s (s_const k5) x1 (s_const k_false))
          with  (s_const k_false) by auto.
        eapply F_Step. apply F_Reduce. apply F_Fail; auto.
        auto.
      SSSCase "==>s".
        auto.
Case "P_App".
  clear IHparreds1 IHparreds2. 
  inversion H1; subst.
  SCase "F_RConst".
    exists (denot k5 k').
    apply A14_k in H. apply A14_k in H0.
    split.
    SSCase "-->h*".
      eapply evalh_trans. apply eval_app_congr1. apply H. auto.
      eapply evalh_trans. apply eval_app_congr2. apply H0. auto. auto.
      eapply F_Step. apply F_Reduce. apply F_Const; auto.
      auto.
    SSCase "==>s".
      auto.
  SCase "F_RBeta".
    rename SS5 into SS1'. rename s12 into s12'.
    apply A14_lam with (L:=sfv_s s12') in H.
    destruct H as [SS1 [s12 [Hstep1 [HparSS1 Hpars12]]]].
    apply A14_w in H0; auto.
    destruct H0 as [w2 [Hstep2 [Hpar2 Hw2]]].
    pick_fresh x1. assert (x1 `notin` sfv_s s12') by auto.
    specialize (Hpars12 x1 H). clear H.
    exists (s12 [:w2]).
    split.
    SSCase "-->h*".
      eapply evalh_trans. apply eval_app_congr1. apply Hstep1. auto.
      eapply evalh_trans. apply eval_app_congr2. apply Hstep2. auto. simpl; auto.
      eapply F_Step. apply F_Reduce. apply F_Beta; auto.
      apply F_Refl; auto. inversion H5; subst.
      rewrite (ssubst_s_intro x1); auto. apply ssubst_s_lc_s; auto.
    SSCase "==>s".
      rewrite (ssubst_s_intro x1); auto.
      pattern (s12' [:s2']). rewrite (ssubst_s_intro x1); auto.
      apply A3_sw; auto.
  SCase "F_RCCheck".
    apply A14_cast in H.
    destruct H as [SS1 [SS2 [Hstep1 [Hpar1 Hpar2]]]].
    apply A14_k in H0.
    pose proof (proj1 (lc_parredSS Hpar1)) as HlcSS1.
    pose proof (proj1 (lc_parredSS Hpar2)) as HlcSS2.
    apply parallel_ref_rev with (L:=sfv_s s0) in Hpar1.
    destruct Hpar1 as [s11 [HeqSS1 Hpars11]].
    apply parallel_ref_rev with (L:=sfv_s s3) in Hpar2.
    destruct Hpar2 as [s12 [HeqSS2 Hpars12]].
    subst.
    pick_fresh x1.
    assert (x1 `notin` sfv_s s0) as Hfr1 by auto.
    assert (x1 `notin` sfv_s s3) as Hfr2 by auto.
    specialize (Hpars11 _ Hfr1).
    pose proof Hpars12 as Hpars12'.
    specialize (Hpars12 _ Hfr2). clear Hfr1 Hfr2.
    exists (s_check (SS_refinement B5 s12) (s12 [:s_const k5]) k5 l5).
    split.
    SSCase "-->h*".
      eapply evalh_trans. apply eval_app_congr1. apply Hstep1. auto.
      eapply evalh_trans. apply eval_app_congr2. apply H0. auto. auto.
      eapply F_Step. apply F_Reduce. apply F_CCheck; auto.
      apply F_Refl. apply lc_s_check; auto.
      rewrite (ssubst_s_intro x1); auto.
      apply ssubst_s_lc_s; auto.
    SSCase "==>s".
      apply P_Check; auto. eapply P_SSRefine; auto.
      rewrite (ssubst_s_intro x1); auto.
      pattern (s3 [:s_const k5]). rewrite (ssubst_s_intro x1); auto.
      apply A3_sw; auto.
  SCase "F_RCDecomp".
    rename SS11 into SS11', SS12 into SS12', SS21 into SS21', SS22 into SS22'.
    apply A11 in H. destruct H as [s11 [s12 [Hstep1 [Hpar11 Hpar12]]]].
    apply A14_w in H0; auto. destruct H0 as [w2 [Hstep2 [Hpar2 Hq2]]].
    apply A14_cast in Hpar11; auto. destruct Hpar11 as [SS1 [SS2 [Hstep11 [HparSS1 HparSS2]]]].
    apply parallel_fun_rev with (L:=sfv_SS SS12') in HparSS1.
    destruct HparSS1 as [SS11 [SS12 [HeqSS1 [HparSS11 HparSS12]]]]. subst SS1.
    apply parallel_fun_rev with (L:=sfv_SS SS22') in HparSS2.
    destruct HparSS2 as [SS21 [SS22 [HeqSS2 [HparSS21 HparSS22]]]]. subst SS2.
    apply A14_w in Hpar12; auto. destruct Hpar12 as [w12 [Hstep12 [Hpar12 Hw12]]].
    pick_fresh x1. move Fr at top.
    assert ((SS11 :-> SS12) ==>S (SS11' :-> SS12')) as HparSS1.
      apply P_SSFun with (L:=union (sfv_SS SS12) (sfv_SS SS12')); auto.
    assert ((SS21 :-> SS22) ==>S (SS21' :-> SS22')) as HparSS2.
      apply P_SSFun with (L:=union (sfv_SS SS22) (sfv_SS SS22')); auto.
    exists (s_app (s_cast (SS12 [:=s_app (s_cast SS21 SS11 l5) w2]) (SS22 [:=w2]) l5)
                  (s_app w12 (s_app (s_cast SS21 SS11 l5) w2))).
    split.
    SSCase "-->h*".
      eapply evalh_trans. apply eval_app_congr1. apply Hstep1. auto.
      eapply evalh_trans. apply eval_app_congr1.
        eapply evalh_trans. apply eval_app_congr1. apply Hstep11. auto.
        apply eval_app_congr2. apply Hstep12. auto. simpl. auto. auto.
      eapply evalh_trans. apply eval_app_congr2. apply Hstep2. auto. simpl. auto.
      eapply F_Step. apply F_Reduce. apply F_CDecomp; auto.
      apply F_Refl; auto. apply lc_s_app; auto.
      pose proof (proj1 (lc_parredSS HparSS1)) as HlcSS1.
      pose proof (proj1 (lc_parredSS HparSS2)) as HlcSS2.
      inversion HlcSS1. inversion HlcSS2. subst.
      apply lc_s_cast.
      rewrite (ssubst_SS_intro x1); auto. apply ssubst_SS_lc_SS; auto.
      rewrite (ssubst_SS_intro x1); auto. apply ssubst_SS_lc_SS; auto.
    SSCase "==>s".
      apply P_App; auto. apply P_Cast; auto.
      rewrite (ssubst_SS_intro x1); auto. 
      pattern (SS12' [:=s_app (s_cast SS21' SS11' l5) s2']).
      rewrite (ssubst_SS_intro x1); auto.
      apply A3_SSw; auto.
      rewrite (ssubst_SS_intro x1); auto.
      pattern (SS22' [:=s2']). rewrite (ssubst_SS_intro x1); auto.
      apply A3_SSw; auto.
Case "P_Check".
  clear IHparreds.
  inversion H2; subst.
  SCase "F_ROK".
    apply A14_k in H1.
    exists (s_const k5).
    split.
    SSCase "-->h*".
      eapply evalh_trans. apply eval_check_congr. apply H1. auto.
      eapply F_Step. apply F_Reduce. apply F_OK; auto.
      apply F_Refl; auto.
    SSCase "==>s".
      auto.
  SCase "F_RFail".
    apply A14_k in H1.
    exists (s_blame (b_blame l5)).
    split.
    SSCase "-->h*".
      eapply evalh_trans. apply eval_check_congr. apply H1. auto.
      eapply F_Step. apply F_Reduce. apply F_Fail; auto.
      apply F_Refl; auto.
    SSCase "==>s".
      auto.
Qed.

Lemma A17 : forall s1 s2 s2',
  s1 ==>s s2 ->
  s2 -->h s2' ->
  exists s1',
    s1 -->h* s1' /\
    s1' ==>s s2'.
Proof.
intros. generalize dependent s1.
induction H0; intros.
Case "F_Reduce".
  apply A16 with s1; auto.
Case "F_Compat".
  rename s2 into s2'. rename s1 into s2. rename s0 into s1.
  destruct F5; simpl in H1.
  SCase "F_appl".
    rename s2 into s21. rename s into s22. rename s2' into s21'.
    destruct (A11 H1) as [s11 [s12 [Hstep1 [Hpar11 Hpar12]]]].
    destruct (IHsteph s11 Hpar11) as [s11' [Hstep1' Hpar11']].
    exists (s_app s11' s12).
    split.
    SSCase "-->*".
      eapply evalh_trans. apply Hstep1.
      eapply eval_app_congr1; auto.
    SSCase "==>s".
      simpl. auto.
  SCase "F_appr".
    rename s2 into s22. rename s into s21. rename s2' into s22'.
    destruct (A11 H1) as [s11 [s12 [Hstep1 [Hpar11 Hpar12]]]].
    inversion H; subst. clear H4.
    destruct (A14 Hpar11 (w_is_q _ H3)) as [w11' [Hstep11' [Hpar11' Hw11']]].
    apply q_parred_w_is_w with (w:=s21) in Hw11'; auto.
    destruct (IHsteph s12 Hpar12) as [s12' [Hstep12' Hpar12']].
    exists (s_app w11' s12').
    split.
    SSCase "-->*".
      eapply evalh_trans. apply Hstep1.
      eapply evalh_trans. apply eval_app_congr1. apply Hstep11'; auto. auto.
      apply eval_app_congr2; auto.
    SSCase "==>s".
      simpl. auto.
  SCase "F_check".
    rename s into SS1'. rename s2 into s22. rename s2' into s22'.
    destruct (A12 H1) as [SS1 [s12 [Hstep1 [HparSS1 Hpars12]]]].
    destruct (IHsteph s12 Hpars12) as [s12' [Hstep12' Hpar12']].
    exists (s_check SS1 s12' k l).
    split.
    SSCase "-->*".
      eapply evalh_trans. apply Hstep1.
      eapply eval_check_congr; auto.
    SSCase "==>".
      simpl. auto.
Case "F_Blame".
  assert (is_q_of_s (s_blame (b_blame l5))) as Hq by default_simp.
  exists (s_blame (b_blame l5)).
  destruct F5; simpl in H0.
  SCase "F_appl".
    rename s into s22.
    destruct (A11 H0) as [s11 [s12 [Hstep1 [Hpar11 Hpar12]]]].
    destruct (A14 Hpar11 Hq) as [q11' [Hstep11 [Hpar11' Hq11']]].
    apply parallel_blame_rev in Hpar11'; auto. subst q11'.
    split.
    SSCase "-->*".
      eapply evalh_trans. apply Hstep1.
      eapply evalh_trans. apply eval_app_congr1. apply Hstep11. auto.
      replace (s_app (s_blame (b_blame l5)) s12) with (Fplug (F_appl s12) (s_blame (b_blame l5))).
      eapply F_Step. apply F_Blame. auto. auto. auto.
    SSCase "==>".
      auto.
  SCase "F_appr".
    rename s into s21.
    destruct (A11 H0) as [s11 [s12 [Hstep1 [Hpar11 Hpar12]]]].
    destruct (A14 Hpar12 Hq) as [q12' [Hstep12 [Hpar12' Hq12']]].
    apply parallel_blame_rev in Hpar12'; auto. subst q12'.
    inversion H; subst. clear H3.
    destruct (A14 Hpar11 (w_is_q _ H2)) as [w11' [Hstep11 [Hpar11' Hw11']]].
    apply q_parred_w_is_w with (w:=s21) in Hw11'; auto.
    split.
    SSCase "-->*".
      eapply evalh_trans. apply Hstep1.
      eapply evalh_trans. apply eval_app_congr1. apply Hstep11. auto.
      eapply evalh_trans. apply eval_app_congr2. apply Hstep12. auto. auto.
      replace (s_app w11' (s_blame (b_blame l5))) with (Fplug (F_appr w11') (s_blame (b_blame l5))).
      eapply F_Step. apply F_Blame. auto. auto. auto.
    SSCase "==>".
      auto.
  SCase "F_check".
    rename s into SS1'.
    destruct (A12 H0) as [SS1 [s12 [Hstep1 [HparSS1 Hpars12]]]].
    destruct (A14 Hpars12 Hq) as [q12' [Hstep12 [Hpar12' Hq12']]].
    apply parallel_blame_rev in Hpar12'; auto. subst q12'. clear Hq12'.
    split.
    SSCase "-->*".
      eapply evalh_trans. apply Hstep1.
      eapply evalh_trans. apply eval_check_congr. apply Hstep12. auto.
      replace (s_check SS1 (s_blame (b_blame l5)) k l) 
        with (Fplug (F_check SS1 k l) (s_blame (b_blame l5))).
      eapply F_Step. apply F_Blame. auto. auto. auto.
    SSCase "==>".
      auto.
Qed.    

Lemma A18_k : forall s1 s2 k,
  s1 ==>s s2 ->
  s2 -->h* s_const k -> s1 -->h* s_const k.
Proof.
intros. remember (s_const k) as s2'.
generalize dependent k. generalize dependent s1.
induction H0; intros; subst.
Case "F_Refl".
  apply A14 in H0; auto.
  destruct H0 as [q1 [Hstep [Hpar Hq]]].
  apply parallel_const_rev in Hpar; auto. subst; auto. simpl. auto.
Case "F_Step".
  rename s5 into s2. rename s' into s2'.
  apply A17 with (s2':=s2') in H1. destruct H1 as [s1' [Hstep Hpar]].
  specialize (IHevalh s1' Hpar k (refl_equal (s_const k))).
  eapply evalh_trans; eauto.
  auto.
Qed.
  
Lemma A18_blame : forall s1 s2 l,
  s1 ==>s s2 ->
  s2 -->h* s_blame (b_blame l) -> s1 -->h* s_blame (b_blame l).
Proof.
intros. remember (s_blame (b_blame l)) as s2'.
generalize dependent l. generalize dependent s1.
induction H0; intros; subst.
Case "F_Refl".
  apply A14 in H0; auto.
  destruct H0 as [q1 [Hstep [Hpar Hq]]].
  apply parallel_blame_rev in Hpar; auto. subst; auto. simpl. auto.
Case "F_Step".
  rename s5 into s2. rename s' into s2'.
  apply A17 with (s2':=s2') in H1. destruct H1 as [s1' [Hstep Hpar]].
  specialize (IHevalh s1' Hpar l (refl_equal (s_blame (b_blame l)))).
  eapply evalh_trans; eauto.
  auto.
Qed.

Lemma A19_k : forall s1 s2 k,
  s1 ==>s s2 ->
  s1 -->h* s_const k -> s2 -->h* s_const k.
Proof.
intros. remember (s_const k) as s1'.
generalize dependent k. generalize dependent s2.
induction H0; intros; subst.
Case "F_Refl".
  apply parallel_const_inversion in H0. subst. auto.
Case "F_Step".
  rename s5 into s1. rename s' into s1'.
  apply A8 with (s1':=s1') in H1; auto. 
  destruct H1 as [s2' [Hstep Hpar]].
  specialize (IHevalh s2' Hpar k (refl_equal (s_const k))).
  eapply evalh_trans; eauto.
Qed.
  
Lemma A19_blame : forall s1 s2 l,
  s1 ==>s s2 ->
  s1 -->h* s_blame (b_blame l) -> s2 -->h* s_blame (b_blame l).
Proof.
intros. remember (s_blame (b_blame l)) as s1'.
generalize dependent l. generalize dependent s2.
induction H0; intros; subst.
Case "F_Refl".
  apply parallel_blame in H0. subst. auto.
Case "F_Step".
  rename s5 into s1. rename s' into s1'.
  apply A8 with (s1':=s1') in H1; auto. 
  destruct H1 as [s2' [Hstep Hpar]].
  specialize (IHevalh s2' Hpar l (refl_equal (s_blame (b_blame l)))).
  eapply evalh_trans; eauto.
Qed.

Lemma A20 : forall s1 s2,
  s1 ==>s s2 ->
  (forall k, s1 -->h* s_const k <-> 
             s2 -->h* s_const k) /\
  (forall l, s1 -->h* s_blame (b_blame l) <-> 
             s2 -->h* s_blame (b_blame l)).
Proof.
intros s1 s2 H.
split; intros.
split; eauto using A18_k, A19_k.
split; eauto using A18_blame, A19_blame.
Qed.

Lemma coevaluation_ltr : forall s1 s2 w1,
  s1 ==>s s2 ->
  s1 -->h* w1 ->
  is_w_of_s w1 ->
  exists w2,
    s2 -->h* w2 /\
    w1 ==>s w2 /\
    is_w_of_s w2.
Proof.
intros s1 s2 w2 Hpar Hstep. revert s2 Hpar.
induction Hstep; intros.
Case "F_Refl".
  apply parallel_w with (w':=s2) in H0; auto.
  exists s2; auto.
Case "F_Step".
  rename s5 into s1, s' into s1', s'' into w1.
  destruct (A8 H Hpar) as [s2' [Hsteps2 Hpars2']].
  specialize (IHHstep s2' Hpars2' H0).
  destruct IHHstep as [w2 [Hsteps2' [Hparw2 Hw2]]].
  exists w2; eauto using evalh_trans.
Qed.

Lemma coevaluation_rtl : forall s1 s2 w2,
  s1 ==>s s2 ->
  s2 -->h* w2 ->
  is_w_of_s w2 ->
  exists w1,
    s1 -->h* w1 /\
    w1 ==>s w2 /\
    is_w_of_s w1.
Proof.
intros s1 s2 w2 Hpar Hstep. revert s1 Hpar.
induction Hstep; intros.
Case "F_Refl".
  apply A14_w; auto.
Case "F_Step".
  rename s5 into s2, s' into s2', s'' into w2.
  destruct (A17 Hpar H) as [s1' [Hsteps1 Hpars1']].
  specialize (IHHstep s1' Hpars1' H0).
  destruct IHHstep as [w1 [Hsteps1' [Hparw1 Hw1]]].
  exists w1; eauto using evalh_trans.
Qed.  

(* multi-step stuff that we don't need yet... *)
(*
Lemma A3_sw_multi : forall s1 s1' w2 w2' x,
  s1 ==>s* s1' ->
  w2 ==>s* w2' ->
  ssubst_s w2 x s1 ==>s* ssubst_s w2' x s1'.
Proof.
induction 1; intros.
Case "P_ssRefl".
  induction H0.
  Case "P_ssRefl".
    apply P_ssRefl; apply ssubst_s_lc_s; auto.
  SCase "P_ssStep".
    apply P_ssStep with (ssubst_s s' x s5); auto.
    apply A3_sw; auto.
Case "P_ssStep".
  apply P_ssStep with (ssubst_s w2 x s'); auto.
  apply A3_sw; auto.
  inversion H1; auto.
Qed.

Lemma A3_SSw_multi : forall SS1 SS1' w2 w2' x,
  SS1 ==>S* SS1' ->
  w2 ==>s* w2' ->
  ssubst_SS w2 x SS1 ==>S* ssubst_SS w2' x SS1'.
Proof.
induction 1; intros.
Case "P_SSRefl".
  induction H0.
  Case "P_SSRefl".
    apply P_SsRefl; apply ssubst_SS_lc_SS; auto.
  SCase "P_ssStep".
    apply P_SsStep with (ssubst_SS s' x SS5); auto.
    apply A3_SSw; auto.
Case "P_ssStep".
  apply P_SsStep with (ssubst_SS w2 x SS'); auto.
  apply A3_SSw; auto.
  inversion H1; auto.
Qed.

Lemma P_App_multi : forall s1 s2 s1' s2',
  s1 ==>s* s1' ->
  s2 ==>s* s2' ->
  s_app s1 s2 ==>s* s_app s1' s2'.
Proof.
intros. induction H.
Case "P_ssRefl".
  induction H0; eauto.
Case "P_ssStep".
  eapply P_ssStep. apply P_App. apply H. apply P_Refl.
  inversion H0; auto.
  assumption.
Qed.  

Lemma P_Cast_multi : forall SS1 SS2 SS1' SS2' l,
  SS1 ==>S* SS1' ->
  SS2 ==>S* SS2' ->
  s_cast SS1 SS2 l ==>s* s_cast SS1' SS2' l.
Proof.
intros. induction H.
Case "P_ssRefl".
  induction H0; eauto.
Case "P_ssStep".
  eapply P_ssStep. apply P_Cast. apply H. apply P_SSRefl.
  inversion H0; auto.
  assumption.
Qed.

Lemma A2'_multi : forall w k', is_w_of_s w ->  w ==>s* (s_const k') -> w = s_const k'.
intros. remember (s_const k') as w'.
induction H0; auto; subst.
  apply A2'; auto.
  rewrite <- IHparredsrs; auto.
  apply parallel_w with s5; auto.
Qed.

Lemma q_parredrs_w_is_w : forall q w,
  q ==>s* w ->
  is_q_of_s q ->
  is_w_of_s w ->
  is_w_of_s q.
Proof.
induction 1; intros.
Case "P_ssRefl".
  auto.
Case "P_ssStep".
  apply q_parred_w_is_w with s'; auto.
  apply IHparredsrs; auto.
  apply parallel_q with s5; auto.
Qed.

*)

