(******************************************************************************)
(**
    Proof of Howson-Rosenthal-like transform for generalized Bel-games
 *)
(******************************************************************************)
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing GRing.Theory.
Import Num.Theory.

From BelGames Require Import fintype finset ssrnum.
From BelGames Require Import massfun decision games.

Local Open Scope ring_scope.


Section HowsonRosenthal.

  Variable R : realFieldType.
  Variable I : finType.
  Variable A : I -> eqType.
  Variable T : I -> finType.

  Notation profile := (cprofile A).
  Notation Tn := {dffun forall i : I, T i}.
  Notation iprof := (iprofile I T).

  (* Definitions for all transforms *)

  Definition HR_player : finType := {i : I & T i}.

  Definition HR_action (i_ti : HR_player) : eqType := A (projT1 i_ti).

  (*
  Section HRclassical.

    Variable G : bgame R A T.

    Variable properG : proper_bgame G.

    Definition HRclassical_localgame : finType := Tn.
    Definition HRclassical_plays_in : HRclassical_localgame -> pred HR_player
      := fun lg i_ti => lg (projT1 i_ti) == projT2 i_ti.


    Notation HRclassical_localagent := (fun lg => {i_ti | HRclassical_plays_in lg i_ti}).
    Notation HRclassical_localprof := (fun lg => local_cprofile HR_action (HRclassical_plays_in lg)).


    Definition HRclassical_plays_in_given_lg (lg : HRclassical_localgame) j : HRclassical_plays_in lg (existT _ j (lg j))
      := eqxx (projT2 (existT (fun i : I => T i) j (lg j))).

    Definition HRclassical_mkprofile (lg : HRclassical_localgame) (p : HRclassical_localprof lg) : cprofile A
      := proj_flatlocalprofile (fun i => exist _ (lg i) (HRclassical_plays_in_given_lg lg i)) p.

    Lemma HRclassical_mkprofileE (lg : HRclassical_localgame) (p : iprofile _ _) :
      HRclassical_mkprofile (lg:=lg) [ffun x : {x : HR_player | HRclassical_plays_in lg x} =>
                       (iprofile_flatten p )(val x)]
      = (proj_iprofile p lg).
    Proof.
    apply eq_dffun => i /= ; by rewrite !ffunE /=.
    Qed.

    Definition HRclassical_localutility : forall lg : HRclassical_localgame, HRclassical_localprof lg -> HRclassical_localagent lg -> R
      := fun lg p x =>
         let (i_ti, _) := x in
         let (i, ti) := i_ti in
         dist (Pr_conditioning (is_Pr_revisable properG ti)) lg * G.2 (HRclassical_mkprofile p) lg i.

    Definition HRclassical_transform : cgame R HR_action := hg_game HRclassical_localutility.

    Theorem HRclassical_transform_correct (Hproper : proper_bgame G) :
      forall i (ti : T i) p,
      bgame_utility Hproper p ti = HRclassical_transform [ffun j_tj => p (projT1 j_tj) (projT2 j_tj)] (existT _ i ti).
    Proof.
    move => i ti p.
    set i_ti := existT _ i ti.
    rewrite /bgame_utility /HRclassical_transform/= hg_gameE [RHS]big_mkcond /=.
    apply eq_bigr => lg _.
    case (boolP (HRclassical_plays_in lg i_ti)) => H.
    - by rewrite ffunE HRclassical_mkprofileE.
    - rewrite /HRclassical_plays_in in H.
      rewrite /Pr_conditioning proba_of_distE /Pr_conditioning_dist.
      have H2 : lg \notin event_ti ti. by rewrite inE.
      by rewrite (negbTE H2) !mul0r.
    Qed.

  End HRclassical.

   *)

  Theorem HR_eqNash_prop (G : igame R A T) (G' : cgame R HR_action) (cond : conditioning R Tn) fXEU (proper_G : proper_igame G cond) :
    (forall p i ti, igame_utility fXEU proper_G p ti = G' (iprofile_flatten p) (existT _ i ti))
    ->
    forall p,
    Igame_Nash_equilibrium fXEU proper_G p <-> Nash_equilibrium G' (iprofile_flatten p).
  Proof.
  move => Hcorrect p ; split => HNash => [i_ti ai| i ti ai].
  - have :=  HNash (projT1 i_ti) (projT2 i_ti) ai.
    by rewrite !Hcorrect -!sigT_eta change_strat_istrat.
  - have := HNash (existT _ i ti) ai.
    by rewrite !Hcorrect change_strat_istrat.
  Qed.


  Section DirectTransform.

    Variable G : igame R A T.
    Variable proper_G : proper_igame G (Dempster_conditioning R Tn).

    Variable fXEU : xeu_function R Tn.
    Variable proper_fXEU : eq_xeu fXEU.

    Definition HRdirect_localgame : finType
      := {set Tn}.

    Definition HRdirect_plays_in : HRdirect_localgame -> pred HR_player
      := fun lg i_ti => [exists t : Tn, [&& t \in lg & t (projT1 i_ti) == projT2 i_ti]].

    Lemma HRdirect_plays_in_event_ti lg i_ti :
      HRdirect_plays_in lg i_ti = (lg :&: event_ti (projT2 i_ti) != set0).
    Proof.
    symmetry.
    case (boolP (HRdirect_plays_in lg i_ti)) => [/existsP [t /andP [Ht1 Ht2]]|/existsPn H].
    - apply/set0Pn ; exists t ; by rewrite in_setI inE Ht1 Ht2.
    - apply/set0Pn/existsP/negP => /negP /existsP [x Hx].
      move: (H x).
      rewrite in_setI /event_ti inE in Hx.
      by rewrite Hx.
    Qed.

    Lemma HRdirect_lg_nonempty (lg : HRdirect_localgame) i_ti (Hlg : HRdirect_plays_in lg i_ti) : lg != set0.
    Proof.
    by have := existsP (existsb_l _ Hlg) => /set0Pn ->.
    Qed.


    Notation HRdirect_localagent := (fun lg => {i_ti | HRdirect_plays_in lg i_ti}).
    Notation HRdirect_localprof := (fun lg => local_cprofile HR_action (HRdirect_plays_in lg)).


    Lemma HRdirect_plays_in_given_t (lg : HRdirect_localgame) t (Ht : t \in lg) j : HRdirect_plays_in lg (existT T j (t j)).
    Proof.
    apply/existsP ; exists t ; by rewrite Ht /=.
    Qed.

    Definition HRdirect_mkprofile1 lg (p : HRdirect_localprof lg) (t : Tn) (Ht : t \in lg) : profile :=
      proj_flatlocalprofile (fun i => exist _ (t i) (HRdirect_plays_in_given_t Ht i)) p.

    (* Lorsque t n'est pas dans lg, on construit un profil quelconque (d'après un t permettant à i_ti de jouer dans lg. Afin de rendre la fonction mkprofile totale *)
    Definition HRdirect_mkprofile2 lg i_ti (Hi_ti : HRdirect_plays_in lg i_ti) (p : HRdirect_localprof lg) (t : Tn) (Ht : t \notin lg) : profile.
    Proof.
    apply finfun => j.
    have [t' Ht'] := pick_nonemptyset_sig (HRdirect_lg_nonempty Hi_ti).
    have Htj' : HRdirect_plays_in lg (existT _ j (t' j))
      by apply/existsP ; exists t' ; rewrite Ht' /=.
    exact: p (exist _ (existT _ j (t' j)) Htj').
    Qed.


    Definition HRdirect_mkprofile lg i_ti (Hi_ti : HRdirect_plays_in lg i_ti) (p : HRdirect_localprof lg) (t : Tn) : profile
      := match boolP (t \in lg) with
         | AltTrue H => HRdirect_mkprofile1 p H
         | AltFalse H => HRdirect_mkprofile2 Hi_ti p H
         end.

    Lemma HRdirect_mkprofileE lg i_ti (Hi_ti : HRdirect_plays_in lg i_ti) (p : iprofile _ _) t (Ht : t \in lg) :
      HRdirect_mkprofile Hi_ti [ffun x : {x : HR_player | HRdirect_plays_in lg x} =>
                       (iprofile_flatten p )(val x)] t
      = (proj_iprofile p t).
    Proof.
    rewrite /HRdirect_mkprofile /proj_iprofile /HRdirect_mkprofile1 /proj_flatlocalprofile.
    case (boolP
        (@in_mem
           (@dfinfun_of I (fun i : Finite.sort I => Finite.sort (T i))
              (Phant (forall i : Finite.sort I, Finite.sort (T i)))) t
           (@mem (Finite.sort (@finfun_dfinfun_of__canonical__fintype_Finite I T))
              (predPredType (Finite.sort (@finfun_dfinfun_of__canonical__fintype_Finite I T)))
              (@pred_of_set.body (@finfun_dfinfun_of__canonical__fintype_Finite I T) lg)))) => Htinlg ; last by rewrite (negbTE Htinlg) in Ht.
    apply eq_dffun => j ; by rewrite !ffunE.
    Qed.

    
    Definition evt i (ti : T i) := @event_ti I T i ti.

    Definition HRdirect_u : forall lg : HRdirect_localgame, HRdirect_localprof lg -> HRdirect_localagent lg -> R
      := fun lg p x =>
         let (i_ti, Hi_ti) := x in let (i, ti) := i_ti in
         G.1 lg * fXEU [ffun t => G.2 (HRdirect_mkprofile Hi_ti p t) t i] (lg :&: (evt ti)) / Psup G.1 (evt ti).

    Definition HRdirect : cgame R HR_action := hg_game HRdirect_u.

    Theorem HRdirect_correct (i : I) (ti : T i) (p : iprofile A T) :
      igame_utility fXEU proper_G p ti = HRdirect (iprofile_flatten p) (existT _ i ti).
    Proof.
    set i_ti := existT _ i ti.
    rewrite /igame_utility /XEUm /HRdirect hg_gameE => //=.
    rewrite Dempster_cond_sumE.
    rewrite -big_mkcondr sum_fun_focal_cond big_mkcond [in RHS]big_mkcond => //=.
    rewrite big_distrl.
    apply eq_bigr => B _ //=.
    case (boolP (HRdirect_plays_in B i_ti)) => H.
    - have := H ; rewrite HRdirect_plays_in_event_ti => ->.
      apply: mulr_rr ; apply: mulr_ll.
      apply: proper_fXEU => t Hdomain.
      rewrite !ffunE.
      rewrite HRdirect_mkprofileE //.
      rewrite in_setI in Hdomain.
      by have [Hdomain1 _] := andP Hdomain.
    - rewrite HRdirect_plays_in_event_ti in H.
      by rewrite (negbTE H) mul0r.
    Qed.

    Theorem HRdirect_eqNash (p : iprofile A T) :
      Igame_Nash_equilibrium fXEU proper_G p <-> Nash_equilibrium HRdirect (iprofile_flatten p).
    Proof.
    apply: HR_eqNash_prop => p' i ti.
    by rewrite HRdirect_correct.
    Qed.

  End DirectTransform.









  Section ConditionedTransform.


    Variable G : igame R A T.
    Variable cond : conditioning R Tn.
    Variable xeu : xeu_function R Tn.
    Variable xeu_equality : eq_xeu xeu.
    Variable proper_G : proper_igame G cond.


    Definition HRcond_localgame : finType
      := {set Tn}.

    Definition HRcond_plays_in : HRcond_localgame -> pred HR_player :=
      fun lg it => [exists t : Tn , [&& t \in lg & t (projT1 it) == projT2 it]].

    Lemma HRcond_lg_nonempty (lg :HRcond_localgame) i_ti (Hlg : HRcond_plays_in lg i_ti) : lg != set0.
    Proof.
    by have := existsP (existsb_l _ Hlg) => /set0Pn ->.
    Qed.

    Notation HRcond_localagent := (fun lg => {i_ti : HR_player | HRcond_plays_in lg i_ti}).
    Notation HRcond_localprof := (fun lg => local_cprofile HR_action (HRcond_plays_in lg)).

    Lemma negb_HRcond_plays_in lg i_ti (H : ~~ HRcond_plays_in lg i_ti) :
      lg \notin focal (cond G.1 (evt (projT2 i_ti)) (is_revisable proper_G (projT2 i_ti))).
    Proof.
    rewrite negb_focal_revise => // t Ht.
    move: H ; rewrite negb_exists => /forallP => H.
    move: (H t).
    rewrite negb_and => /orP ; case.
    - by rewrite Ht.
    - by rewrite eq_sym.
    Qed.


    Lemma HRcond_plays_in_given_t (lg : HRcond_localgame) t (Ht : t \in lg) j : HRcond_plays_in lg (existT T j (t j)).
    Proof.
    apply/existsP ; exists t ; by rewrite Ht /=.
    Qed.

    Definition HRcond_mkprofile1 lg (p : HRcond_localprof lg) (t : Tn) (Ht : t \in lg) : profile :=
      proj_flatlocalprofile (fun i => exist _ (t i) (HRcond_plays_in_given_t Ht i)) p.


    (* Lorsque t n'est pas dans lg, on construit un profil quelconque (d'après un t permettant à i_ti de jouer dans lg. Afin de rendre la fonction mkprofile totale *)
    Definition HRcond_mkprofile2 lg i_ti (Hi_ti : HRcond_plays_in lg i_ti) (p : HRcond_localprof lg) (t : Tn) (Ht : t \notin lg) : profile.
    Proof.
    apply finfun => j.
    have [t' Ht'] := pick_nonemptyset_sig (HRcond_lg_nonempty Hi_ti).
    have Htj' : HRcond_plays_in lg (existT _ j (t' j)). apply/existsP ; exists t' ; by rewrite Ht' /=.
    exact: p (exist _ (existT _ j (t' j)) Htj').
    Qed.


    Definition HRcond_mkprofile lg i_ti (Hi_ti : HRcond_plays_in lg i_ti) (p : HRcond_localprof lg) (t : Tn) : profile
      := match boolP (t \in lg) with
         | AltTrue H => HRcond_mkprofile1 p H
         | AltFalse H => HRcond_mkprofile2 Hi_ti p H
         end.

    Definition HRcond_u : forall lg : HRcond_localgame, HRcond_localprof lg -> HRcond_localagent lg -> R
      := fun lg p x =>
         let (i_ti, Hi_ti) := x in
         let (i, ti) := i_ti in
         let kn := cond G.1 (evt ti) (is_revisable proper_G ti) in
         kn lg * xeu [ffun t => G.2 (HRcond_mkprofile Hi_ti p t) t i] lg.


    Definition HRcond : cgame R HR_action := hg_game HRcond_u.


    Lemma HRcond_mkprofileE lg i_ti (Hi_ti : HRcond_plays_in lg i_ti) (p : iprofile _ _) t (Ht : t \in lg) :
      HRcond_mkprofile Hi_ti [ffun x : {x : HR_player | HRcond_plays_in lg x} => (iprofile_flatten p )(val x)] t
      = (proj_iprofile p t).
    Proof.
    rewrite /HRcond_mkprofile /proj_iprofile /HRcond_mkprofile1 /proj_flatlocalprofile.
    case (boolP
        (@in_mem
           (@dfinfun_of I (fun i : Finite.sort I => Finite.sort (T i))
              (Phant (forall i : Finite.sort I, Finite.sort (T i)))) t
           (@mem (Finite.sort (@finfun_dfinfun_of__canonical__fintype_Finite I T))
              (predPredType (Finite.sort (@finfun_dfinfun_of__canonical__fintype_Finite I T)))
              (@pred_of_set.body (@finfun_dfinfun_of__canonical__fintype_Finite I T) lg)))) => Htinlg ; last by rewrite (negbTE Htinlg) in Ht.
    apply eq_dffun => j ; by rewrite !ffunE.
    Qed.

    Theorem HRcond_correct (i : I) (ti : T i) (p : iprofile A T):
      igame_utility xeu proper_G p ti = HRcond (iprofile_flatten p) (existT _ i ti).
    Proof.
    set i_ti := existT _ i ti.
    rewrite /HRcond hg_gameE /igame_utility /XEUm.
    rewrite sum_fun_focal [in RHS]big_mkcond.
    apply eq_bigr => lg _.
    case (boolP (HRcond_plays_in lg i_ti)) => H.
    - rewrite /HRcond_u /=.
      set kn := cond G.1 (evt ti) (is_revisable proper_G ti).
      + apply: mulr_ll ; apply: xeu_equality => t Ht.
        by rewrite !ffunE HRcond_mkprofileE.
    - have := negb_HRcond_plays_in H.
      rewrite notin_focal => /eqP -> ; by rewrite mul0r.
    Qed.

    Theorem HRcond_eqNash :
      forall p,
      Igame_Nash_equilibrium xeu proper_G p <-> Nash_equilibrium HRcond (iprofile_flatten p).
    Proof.
    apply HR_eqNash_prop => p i ti.
    by rewrite HRcond_correct.
    Qed.

  End ConditionedTransform.

  Definition HRcondCEU_eqNash G cond := @HRcond_eqNash G cond _ (@eq_CEU _ _).
  Definition HRcondJEU_eqNash alpha G cond := @HRcond_eqNash G cond _ (eq_JEU alpha).
  Definition HRcondTBEU_eqNash G cond := @HRcond_eqNash G cond _ (@eq_TBEU _ _).


  Section TBMTransform.

    Variable G : igame R A T.
    Variable cond : conditioning R Tn.
    Variable proper_G : proper_igame G cond.

    Definition HRTBM_localgame : finType := Tn.

    Definition m_ti (i_ti : HR_player) : rmassfun R Tn :=
      let ti := projT2 i_ti in cond G.1 (evt ti) (forallP (forallP proper_G _) ti).
    
    Definition HRTBM_plays_in : HRTBM_localgame -> pred HR_player
      := fun lg i_ti =>
           [|| lg (projT1 i_ti) == projT2 i_ti |
             [exists A : {set Tn}, [&& A \in focal (m_ti i_ti), lg \in A & [exists t : Tn, (t \in A) && (t (projT1 i_ti) == projT2 i_ti)]]]].
    (* Note: for Weak conditioning, i_ti may plays in lg = t' such as t' i != ti *)

           

    Notation HRTBM_localagent := (fun lg => {i_ti | HRTBM_plays_in lg i_ti}).
    Notation HRTBM_localprof := (fun lg => local_cprofile HR_action (HRTBM_plays_in lg)).


    Lemma HRTBM_plays_in_given_lg (lg : HRTBM_localgame) j : HRTBM_plays_in lg (existT _ j (lg j)).
    Proof. by rewrite /HRTBM_plays_in /= eqxx orTb. Qed.

    Definition HRTBM_mkprofile (lg : HRTBM_localgame) (p : HRTBM_localprof lg) : cprofile A
      := proj_flatlocalprofile (fun i => exist _ (lg i) (HRTBM_plays_in_given_lg lg i)) p.

    Lemma HRTBM_mkprofileE (lg : HRTBM_localgame) (p : iprofile _ _) :
      HRTBM_mkprofile (lg:=lg) [ffun x : {x : HR_player | HRTBM_plays_in lg x} =>
                       (iprofile_flatten p )(val x)]
      = (proj_iprofile p lg).
    Proof.
    apply eq_dffun => i /= ; by rewrite !ffunE /=.
    Qed.

    (* local utilities *)
    Definition HRTBM_u : forall lg : HRTBM_localgame, HRTBM_localprof lg -> HRTBM_localagent lg -> R
      := fun lg p x =>
         let (i_ti, _) := x in
         let (i, ti) := i_ti in
         let betp := BetP_fun (m_ti i_ti) in
         betp lg * G.2 (HRTBM_mkprofile p) lg i.

    Definition HRTBM : cgame R HR_action := hg_game HRTBM_u.

    Theorem HRTBM_correct (i : I) (ti : T i) (p : iprofile A T) :
      igame_utility (@fTBEU _ _) proper_G p ti = HRTBM (iprofile_flatten p) (existT _ i ti).
    Proof.
    set i_ti := existT _ i ti.
    rewrite /igame_utility /HRTBM /= hg_gameE [RHS]big_mkcond.
    rewrite TBEU_EUBetP.
    apply eq_bigr => lg _.
    case (boolP (HRTBM_plays_in lg i_ti)) => /=.
    - by rewrite HRTBM_mkprofileE ffunE.
    - rewrite negb_or.
      rewrite negb_exists => /andP [H1 /forallP H2].
      have H0 : (BetP_fun (m_ti i_ti)) lg = 0.
      rewrite /BetP_fun.
      apply: big_pred0 => X.
      have :=  H2 X.
      rewrite !negb_and => /or3P ; case => HX.
      + by rewrite (negbTE HX) andFb.
      + by rewrite (negbTE HX) andbF.
      + rewrite negb_exists in HX.
        move/forallP in HX.
        have : X \notin focal (m_ti i_ti).
        apply: conditioning_axiomE.
        * by case cond.
        * rewrite /evt.
          rewrite -setD_eq0.
          rewrite set0_exists negb_exists.
          apply/forallP => t.
          rewrite in_setD negb_and.
          case (boolP (t \in X)) => /= Ht ; last by rewrite orbT.
          rewrite orbF.
          apply/negPn.
          rewrite !inE.
          move: (HX t) ; by rewrite negb_and Ht orFb.
        by move => HX2 ; rewrite (negbTE HX2) andFb.
      by rewrite H0 mul0r.
    Qed.

  Theorem HRTBM_eqNash (p : iprofile A T) :
    Igame_Nash_equilibrium (@fTBEU _ _) proper_G p <-> Nash_equilibrium HRTBM (iprofile_flatten p).
  Proof.
  apply: HR_eqNash_prop => p' i ti.
  by rewrite HRTBM_correct.
  Qed.

  End TBMTransform.


  Lemma HRTBM_Dempster_plays_in G (HG : proper_igame G (Dempster_conditioning _ _)) lg :
    HRTBM_plays_in HG lg =1 [pred i_ti | lg (projT1 i_ti) == projT2 i_ti].
  Proof.
  rewrite /HRTBM_plays_in => i_ti /=.
  case (boolP (lg (projT1 i_ti) == projT2 i_ti)) => // H.
  rewrite orFb ; apply: negbTE ; rewrite negb_exists.
  apply/forallP => X ; apply/negP => /and3P [Hcontra1 Hcontra2 Hcontra3].
  move: Hcontra1 ; rewrite /(_\in_) /focal /= ffunE.
  have X_neq_set0 : X != set0 by apply/set0Pn ; exists lg.
  rewrite (negbTE X_neq_set0)  big_pred0 => [|Y] ; first by rewrite eqxx.
  suff H1 : Y :&: [set t : {dffun forall i, T i} | t (projT1 i_ti) == projT2 (i_ti)] == X = false
    by rewrite H1.
  apply/negP => /eqP Hcontra.
  move: Hcontra2 ; by rewrite -Hcontra in_setI !inE (negbTE H) andbF.
  Qed.  

  Lemma HRTBM_Strong_plays_in G (HG : proper_igame G (Strong_conditioning _ _)) lg :
    HRTBM_plays_in HG lg =1 [pred i_ti | lg (projT1 i_ti) == projT2 i_ti].
  Proof.
  rewrite /HRTBM_plays_in => i_ti /=.
  case (boolP (lg (projT1 i_ti) == projT2 i_ti)) => // H.
  rewrite orFb ; apply: negbTE ; rewrite negb_exists.
  apply/forallP => X ; apply/negP => /and3P [Hcontra1 Hcontra2 Hcontra3].
  move: Hcontra1 ; rewrite /(_\in_) /focal /= ffunE.
  have X_neq_set0 : X != set0 by apply/set0Pn ; exists lg.
  rewrite (negbTE X_neq_set0) andTb.
  suff H1 : ~~ (X \subset evt (projT2 i_ti))
    by rewrite (negbTE H1) eqxx.
  by apply/subsetPn ; exists lg ; try rewrite !inE.
  Qed.
      

  
End HowsonRosenthal.

From HB Require Import structures.

Section HRTBMWeakConditioningLocalGames.

  Variable R : realFieldType.
  Notation I := 'I_2.
  Notation A := (fun _ : I => 'I_2).
  Notation T := (fun _ : I => 'I_2).

  Notation Tn := {ffun forall i, T i}.

  Notation m_example := [ffun X : {set Tn} => if X == setT then 1 else 0:R].

  Lemma HRTBM_Weak_example_massfun0 :
    m_example set0 = 0.
  Proof. by rewrite ffunE/= eq_sym (negbTE (setT0F [ffun t => ord0])). Qed.

  Lemma HRTBM_Weak_example_massfun1 :
    \sum_(A : {set Tn}) m_example A = 1.
  Proof.
  rewrite (bigD1 setT)//= big1=>[|A HA].
  - by rewrite addr0 ffunE eqxx.
  - by rewrite ffunE (negbTE HA).
  Qed.

  HB.instance Definition _ :=
    MassFun_of_Ffun.Build R Tn 0 +%R m_example.

  HB.instance Definition _ :=
    AddMassFun_of_MassFun.Build R Tn m_example HRTBM_Weak_example_massfun0 HRTBM_Weak_example_massfun1.
  
  Lemma HRTBM_Weak_example_ge0 A :
    m_example A >= 0.
  Proof.
  rewrite ffunE/=.
  case (boolP (A == setT))=>[->//|H].
  by rewrite (negbTE H).
  Qed.

  HB.instance Definition _ :=
    Bpa_of_AddMassFun.Build R Tn m_example HRTBM_Weak_example_ge0.

  Notation m := (m_example : rmassfun R Tn).

  Definition HRTBM_Weak_example_igame : igame R A T :=
    (m, (fun => fun => fun => 0)).
  
  Lemma HRTBM_Weak_example_proper : proper_igame HRTBM_Weak_example_igame (Weak_conditioning _ _).
  Proof.
  apply/forallP => i ; apply/forallP => ti.
  rewrite/revisable/Weak_conditioning/Weak_cond_revisable ffunE.
  apply: lt0r_neq0.
  rewrite (bigD1 setT) /=.
  - rewrite ffunE eqxx big1 => [|X /andP [HX1 HX2]].
    + by rewrite addr0 ltr01.
    + by rewrite ffunE (negbTE HX2).
  - rewrite -setI_eq0.
    apply/set0Pn.
    exists [ffun j => ti].
    by rewrite setTI !inE ffunE.
  Qed.

  Lemma Pl_1 X : X != set0 -> Psup m X = 1.
  Proof.
  move => HX.
  rewrite ffunE (bigD1 setT) /=.
  - rewrite ffunE eqxx big1 => [|Y /andP [HY1 HY2]] ; first by rewrite addr0.
    by rewrite ffunE (negbTE HY2).
  - rewrite -setI_eq0.
    apply/set0Pn.
    rewrite -card_gt0 in HX.
    have [t Ht _] := eq_bigmax_cond (fun=>1%N) HX.
    exists t ; by rewrite setTI.
  Qed.
              

  Lemma HRTBM_WEAK_example_plays_in lg i_ti : HRTBM_plays_in HRTBM_Weak_example_proper lg i_ti.
  rewrite /HRTBM_plays_in.
  apply/orP ; right.
  apply/existsP ; exists setT.
  apply/and3P ; split.
  - rewrite /focal/(_\in_)//= ffunE.
    have : setT :&: evt (projT2 i_ti) != set0
      by apply/set0Pn ; exists [ffun _ => projT2 i_ti] ; rewrite in_setI !inE andTb ffunE.
    move => ->/=.
    rewrite ffunE eqxx Pl_1 ;
      first by apply: lt0r_neq0 ; apply: divr_gt0 ; exact: ltr01.
    apply/set0Pn ; exists [ffun _ => projT2 i_ti].
    by rewrite !inE ffunE.
  - by rewrite in_setT.
  - apply/existsP.
    exists [ffun _ => projT2 i_ti].
    by rewrite in_setT ffunE eqxx.
  Qed.

  Lemma HRTBM_Weak_example_plays_in2 i_ti : exists lg,
      [&& HRTBM_plays_in HRTBM_Weak_example_proper lg i_ti & lg (projT1 i_ti) != projT2 i_ti].
  Proof.
  case (boolP (projT2 i_ti == 0)) => H.
  - exists [ffun => 1].
    apply/andP ; split.
    + by apply HRTBM_WEAK_example_plays_in.
    + by rewrite ffunE (eqP H).
  - exists [ffun => 0].
    apply/andP ; split.
    + by apply HRTBM_WEAK_example_plays_in.
    + by rewrite ffunE eq_sym.
  Qed.

End HRTBMWeakConditioningLocalGames.
