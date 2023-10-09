(******************************************************************************)
(** OLD COMMENT VERSION

    This file provide a theory for Dempster-Shafer belief functions

   1. A belief function (and its dual plausibility function) are defined from
      a bpa (aka mass function).

   bpa R W           == the structure for bpas, which coerce to {ffun {set W} -> R}
   bpa_axiom m       == [&& m set0 == 0 , \sum_A m A == 1 & [forall A, m A >= 0]]
   Bel m             == Belief function based on m
   Pl m              == Plausibility function based on m
   focal_element m A == (m A > 0)
   focalset m        == Set of focal elements

   We then prove several lemmas, eg:
   BelE m: forall A, Bel m A = 1 - Pl m (~:A)
   PlE m:  forall A, Pl m A = 1 - Bel m (~:A)


   2. k-additivity describe the max-cardinality of focal elements.

   If k=1, then Bel = Pl is a proba
   k.-additive m     == (\max_(A in focalset m) #|A| == k)
   proba R W         == the structure for probability measures, which coerce to bpa
   proba_axiom m     == 1.-additive m

   PrE m: 1.-additive m -> forall A, Bel m A = Pl m A


   3. Conditioning ``given C''

   revisable m C     == ``m given C'' is constructible
   conditioning      == the structure fond conditioning, which coerce to
                        forall m C, revisable m C -> bpa
   conditioning_axiom r c m C HC == Bel (cond m HC) (~:C) = 0

   We then define:
   Dempster_conditioning : conditioning.
   Strong_conditioning : conditioning.
   Weak_conditioning : conditioning.


  4. XEU scoring functions, as weighted sums over focalsets

  xeu f m           == \sum_(A in focalset m) m A * f A
  xeu_box           == the structure for xeu computations, which coerce to
                       (W -> R) -> {set W} -> R

  We then define:
  CEU : xeu_box. (Min-value for each focal set)
  JEU: xeu_box. (Linear combination of min-value and max-value)
  TBEU: xeu_box. (Equiprobability hypothesis)

 *)


(******************************************************************************)
From HB Require Import structures.
From Coq Require Import Program.Wf.
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing GRing.Theory.
Import Num.Theory.

Open Scope ring_scope.

From decision Require Import fintype finset setfun ssrnum order minmax.
From decision Require Import massfun.

Section Capacity.

  Variable (R : realFieldType).
  Variable (T : finType).

  Open Scope ring_scope.


  (*
  Section CapaDefs.
    
    (* WARNING: monotony is missing -> massfun's assumptions are weaker than those of capacities *)
    Definition massfun_axiom (m : {ffun {set W} -> R}) :=
      [&& m set0 == 0 & \sum_A m A == 1].

    Structure massfun :=
      { massfun_val :> {ffun {set W} -> R} ;
        massfun_ax : massfun_axiom massfun_val }.

    Definition bpa_axiom (m : {ffun {set W} -> R})
      := [forall A, m A >= 0].

    Structure bpa :=
      { bpa_val :> massfun ;
        bpa_ax : bpa_axiom bpa_val }.


    (** Focal elements are elements with non-zero mass
        The set of focal elements is called focalset **)
    Definition focal_element (m : massfun) : pred {set W}
      := fun A => m A != 0.

    Definition focalset (m : massfun) : {set {set W}}
      := [set A : {set W} | focal_element m A].

    (** The Belief function and its dual Plausibility function are defined directly from the bpa.
        The Bel, Pl and bpa contains the same information -- given one of those, we have the two other **)
    Definition Pinf (m : massfun) : {set W} -> R :=
      fun A => \sum_(B : {set W} | B \subset A) m B.

    Definition Psup (m : massfun) : {set W} -> R :=
      fun A => \sum_(B | B :&: A != set0) m B.

  End CapaDefs.

  #[deprecated(since="belgames2", note="Use Pinf instead.")]
  Notation Bel := Pinf.
  #[deprecated(since="belgames2", note="Use Psup instead.")]
  Notation Pl := Psup.

  Section CapaTypes.

    Definition massfun_eq : rel massfun :=
      fun m1 m2 => massfun_val m1 == massfun_val m2.

    Lemma massfun_eqP : Equality.axiom massfun_eq.
    Proof.
    move => m1 m2 ; apply (iffP eqP) ; last by move ->.
    case: m1; case: m2 => f1 Hf1 f2 Hf2 /= E.
    rewrite E in Hf2 *.
    by rewrite (eq_irrelevance Hf1 Hf2).
    Qed.

    HB.instance Definition massfun_eqType : hasDecEq massfun := hasDecEq.Build massfun massfun_eqP.

    Definition bpa_eq : rel bpa := fun m1 m2 => bpa_val m1 == bpa_val m2.

    Lemma bpa_eqP : Equality.axiom bpa_eq.
    Proof.
    move => m1 m2 ; apply (iffP eqP) ; last by move ->.
    case: m1; case: m2 => f1 Hf1 f2 Hf2 /= E.
    rewrite E in Hf2 *.
    by rewrite (eq_irrelevance Hf1 Hf2).
    Qed.

    Lemma bpa_eqE (m1 m2 : bpa) :
      bpa_val m1 = bpa_val m2 -> m1 = m2.
    Proof.
    case: m1=>m1 Hm1 ; case: m2 => m2 Hm2 /= Heq.
    move: Hm1 Hm2.
    rewrite Heq=>Hm1 Hm2.
    by rewrite (eq_irrelevance Hm1 Hm2).
    Qed.

    HB.instance Definition bpa_eqType : hasDecEq bpa := hasDecEq.Build bpa bpa_eqP.

  End CapaTypes.
 *)
  
  (*
  Lemma Pinf_ge0 (m : massfun) :
    forall C, Pinf m C >= 0.
  Proof.
  have [Hm0 _ HmM] := and3P (massfun_ax m).
  move => C.
  have := forallP (forallP HmM set0) C.
  under [E in _<=E->_]eq_bigl do rewrite set0U.
  rewrite big1=>//i. 
  rewrite subset0=>/eqP->.
  exact/eqP.
  Qed.
   *)

  (*
  Lemma Pinf_le1 (m : massfun) :
    forall C, Pinf m C <= 1.
  Proof.
  have [_ Hm1 HmM] := and3P (massfun_ax m).
  move => C.
  have := forallP (forallP HmM C) setT.
  under [E in _<=E->_]eq_bigl do rewrite setUT subsetT.
  by rewrite (eqP Hm1).
  Qed.
   *)
  
  (** Ensure definitions **)
  Lemma PsupE (m : rmassfun R T) (A : {set T}) :
    Psup m A = 1 - Pinf m (~:A).
  Proof.
  have := (massfun_Pinf01 m)=>/=/andP [Hm0 Hm1].
  by rewrite -massfun_PinfD ffunE (eqP Hm1).
  Qed.

  Lemma PinfE (m : rmassfun R T) (A : {set T}) :
    Pinf m A = 1 - Psup m (~:A).
  Proof.
  have := (massfun_Pinf01 m)=>/=/andP [Hm0 Hm1].
  by rewrite -massfun_PinfD [in RHS]ffunE setCK (eqP Hm1) opprB [E in _ = 1+E]addrC addrA subrr add0r.
  Qed.

  
  Lemma Pl_ge0 (m : bpa R T) :
    forall C, Psup m C >= 0.
  Proof. move=>C ; rewrite ffunE ; apply sumr_ge0=>B _ ; exact: bpa_ge0. Qed.

  (*
  Lemma Psup_ge0 (m : massfun) :
    forall C, Psup m C >= 0.
  Proof.
  move=>C.
  rewrite PsupE subr_ge0.
  exact: Pinf_le1.
  Qed.
  #[deprecated(since="belgames2", note="Use Psup_ge0 instead.")]
  Notation Pl_ge0 := Psup_ge0.
   *)
  
  (*
  Lemma Psup_le1 (m : bpa) :
    forall C, Psup m C <= 1.
  Proof.
  move=>C.
  rewrite PsupE.
  have H11 : 1 <= (1 : R) by [].
  Check lerB H11 (Pinf_ge0 m (~:C)).
  rewrite -[E in _<=E]subr0.
  exact: lerB H11 (Pinf_ge0 m (~:C)).
  Qed.  
   *)
  
  Lemma mass_set0 (m : rmassfun R T) :
    m set0 = 0.
  Proof. exact: massfun0. Qed.

  Lemma focal_neq_set0 (m : rmassfun R T) B :
    focal m B -> B != set0.
  Proof.
  case (boolP (B == set0)) => [/eqP ->| //].
  by rewrite /focal massfun0 eqxx.
  Qed.

  Lemma notin_focalset (m : rmassfun R T) B :
    (B \notin focal m) = (m B == 0).
  Proof. by rewrite Bool.negb_involutive. Qed.

  Lemma in_focalset_focalelement (m : rmassfun R T) B :
    (B \in focal m) = focal (idx:=0) m B.
  Proof. by []. Qed.

  Lemma in_focalset_mass (m : bpa R T) B :
    (B \in focal m) = (m B > 0).
  Proof. by rewrite lt0r bpa_ge0 andbT. Qed.

  
  Lemma focalelement_card (m : rmassfun R T) A :
    focal m A -> (#|A| > 0)%N.
  Proof. by rewrite card_gt0 ; exact: focal_neq_set0. Qed.
  
  Lemma focalset_nonempty (m : rmassfun R T) :
    (#|focal m| > 0)%N.
  Proof.
  apply /card_gt0P=>/=.
  have Hm1' : \sum_A m A != 0 by rewrite massfun1 ; exact: oner_neq0.
  destruct (big_eq1F Hm1') as [A HA] ; move: HA=>/and3P[_ _ HA0].
  have HA0F : A != set0 by apply/eqP=>Hcontra ; rewrite Hcontra massfun0 eqxx in HA0.
  by exists A.
  Qed.

  (** If a bpa is given, then there is (at least) one (x : X) **)
  Lemma massfun_nonempty (m : rmassfun R T) :
    (#|T| > 0)%N.
  Proof.
  apply /card_gt0P.
  have [A HA] := eq_bigmax_cond (fun=>1%N) (focalset_nonempty m).
  have [t _] := eq_bigmax_cond (fun=>1%N) (focalelement_card HA).
  by exists t.
  Qed.  
  
  Definition massfun_nonemptyT (m : rmassfun R T) : T
    := let (t,_) := (eq_bigmax (fun=>0%N) (massfun_nonempty m)) in t.



  (** A sum over the focalset, weighted using the mass function, is equal to the same sum over X *)
  Lemma sum_fun_focalset_cond (P : pred {set T}) (m : rmassfun R T) (f : {set T} -> R) :
    \sum_(B in focal m | P B) m B * f B = \sum_(B : {set T} | P B) m B * f B.
  Proof.
  rewrite big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => B _.
  case (boolP (B \in focal m)) => [_|].
  - by rewrite andTb.
  - rewrite andFb notin_focalset => /eqP -> ; case (P B) => // ; by rewrite mul0r.
  Qed.

  Lemma sum_fun_focalset (m : rmassfun R T) (f : {set T} -> R) :
    \sum_(B in focal m) m B * f B = \sum_(B : {set T}) m B * f B.
  Proof.
  rewrite big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => B _.
  case (boolP (B \in focal m)) => [_//|].
  rewrite notin_focalset => /eqP -> ; by rewrite mul0r.
  Qed.

  Lemma sum_mass_focalset_cond (P : pred {set T}) (m : rmassfun R T) :
    \sum_(B in focal m | P B) m B = \sum_(B : {set T} | P B) m B.
  Proof.
  rewrite big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => B _.
  case (boolP (B \in focal m)) => [_|].
  - by rewrite andTb.
  - rewrite andFb notin_focalset => /eqP -> ; by case (P B).
  Qed.

  Lemma sum_mass_focalset (m : rmassfun R T) :
    \sum_(B in focal m) m B = \sum_(B : {set T}) m B.
  Proof.
  rewrite big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => B _.
  case (boolP (B \in focal m)) => [_//|].
  by rewrite notin_focalset => /eqP ->.
  Qed.

  Lemma Pinf_focalsetE (m : rmassfun R T) A :
    Pinf m A = \sum_(B in focal m | B \subset A) m B.
  Proof. by rewrite ffunE sum_mass_focalset_cond. Qed.

  Lemma Psup_focalsetE (m : rmassfun R T) A :
    Psup m A = \sum_(B in focal m | B :&: A != set0) m B.
  Proof. by rewrite ffunE sum_mass_focalset_cond ; under eq_bigl do rewrite -setI_eq0. Qed.

  Lemma Pinf0 (m : rmassfun R T) :
    Pinf m set0 = 0.
  Proof. by have := massfun_Pinf01 m=>/andP [/eqP->_]. Qed.


  Lemma Psup0 (m : rmassfun R T) :
    Psup m set0 = 0.
  Proof. by have := massfun_Psup01 m=>/andP [/eqP->_]. Qed.

  Lemma Pinf1 (m : rmassfun R T) w :
    Pinf m [set w] = m [set w].
  Proof.
  have := massfun_Pinf01 m =>/andP[/eqP H0>_].
  by rewrite massfun_moebius moebius1 H0 subr0.
  Qed.

  (*
  Lemma Psup_set1 (m : massfun) w :
    Psup m [set w] = m [set w].
  Proof.
  have [Hm0 _ _] := and3P (massfun_ax m).
  rewrite /Psup (bigD1 [set w]) /= ; last by rewrite setIid set1_neq_set0.
  rewrite //= big1 ?addr0=>//A.
  case (setI1 A w). =>->.
  Search set1 setI.
  About set1_neq_set0.
  rewrite subset1=>/andP[/orP [HA1|HA0]HA1F]//.
  - by rewrite (eqP HA1) eqxx in HA1F.
  - by rewrite (eqP HA0) ; exact: (eqP Hm0).
  Qed.
  *)

  (*
  Section KAdditivity.
    (**
       k-additive m = (\max_(B in focalset m) #|B| == k)

       1-additive m <==> Bel m = Pl m is a proba <==> (fun w => m [set w]) is its support
     **)

    Definition k_additivity m : nat
      := \max_(B in focalset m) #|B|.

    Notation "k '.-additive' m" := (k_additivity m == k) (at level 80, format " k '.-additive'  m ").


    Lemma k_additive1E m :
      1%N.-additive m <-> (forall B, B \in focalset m -> (#|B| == 1)%N).
    Proof.
    have [Hm0 Hm1] := andP (rmassfun R T_ax m).
    rewrite /k_additivity ; split => /= [Hkadd B Hfocal | H].
    - have := leq_bigmax_cond (P:=fun B => B \in focalset m) (F:=fun B : {set W} => #|B|) B Hfocal.
      rewrite (eqP Hkadd).
      rewrite /focalset inE in Hfocal.
      rewrite leq_eqVlt => /orP ; case => //.
      case (boolP (#|B| == 0)%N) ; last by case #|B|.
      rewrite cards_eq0.
      by rewrite (negbTE (focal_neq_set0 Hfocal)).
    - apply/eqP.
      destruct (eq_bigmax_cond (fun B : {set W} => #|B|) (focalset_nonempty m)) as [A HA1 HA2].
      rewrite HA2.
      exact: (eqP (H A HA1)).
    Qed.
    

    Notation proba_axiom p := (1%N.-additive p) (only parsing).

    Structure proba :=
      { proba_val :> bpa ;
        proba_ax : proba_axiom proba_val }.

    Definition proba_eq : rel proba := fun p1 p2 => proba_val p1 == proba_val p2.

    Lemma proba_eqP : Equality.axiom (T:=proba) proba_eq.
    move => p1 p2 ; apply (iffP eqP) ; last by move ->.
    case p1 ; case p2 => m1 Hm1 m2 Hm2 /= Heq.
    rewrite Heq in Hm2 *.
    by rewrite (eq_irrelevance Hm1 Hm2).
    Qed.

    Lemma proba_eqE (p1 p2 : proba) :
      proba_val p1 = proba_val p2 -> p1 = p2.
    Proof.
    case: p1=>m1 Hm1 ; case: p2 => m2 Hm2 /= Heq.
    move: Hm1 Hm2.
    rewrite Heq=>Hm1 Hm2.
    by rewrite (eq_irrelevance Hm1 Hm2).
    Qed.

    HB.instance Definition proba_eqType : hasDecEq proba := hasDecEq.Build proba proba_eqP.
    

    Lemma proba_set1_eq0 (p : proba) (s : {set W}) : #|s| != 1%N -> p s = 0.
    Proof.
      move=> Hneq1.
      have := proba_ax p.
      rewrite k_additive1E => H1.
      move/(_ s) in H1.
      apply/eqP; rewrite -[_ == 0]negbK.
      apply/negP=> K0.
      have Hfocal : s \in focalset p by rewrite in_focalset_focalelement.
      by rewrite (eqP (H1 Hfocal)) in Hneq1.
    Qed.

    Definition dist (p : proba) : W -> R := fun w => p [set w].

    Definition is_dist (f : W -> R) := [&& \sum_w f w == 1 & [forall w, f w >= 0]].

    Lemma is_dist_dist (p : proba) : is_dist (dist p).
    Proof.
    destruct p as [m Hp].
    have [Hm0 Hm1] := andP (massfun_ax m).
    have Hm_ge0 := bpa_ax m.
    rewrite /dist ; apply/andP ; split => /=.
    - rewrite -(eqP Hm1).
      rewrite (split_big _ (fun w => [set w] \in focalset m)) /= addrC big1 => [|w] ; last by rewrite notin_focalset => /eqP ->.
      apply/eqP ; symmetry.
      rewrite add0r -sum_mass_focalset.
      rewrite (reindex_omap set1 set1_oinv) /= => [|A HA].
      + apply eq_bigl => w.
        by rewrite set1_oinv_pcancel eqxx andbT.
      + apply set1_oinv_omap.
        by apply (k_additive1E m).
    - apply/forallP => w.
      exact: (forallP Hm_ge0).
    Qed.

    Definition Pr (p : proba) := fun A : {set W} => \sum_(w in A) dist p w.

    Lemma Pr_PinfE (p : proba) :
      Pr p =1 Pinf p.
    Proof.
    move => A.
    rewrite /Pr Pinf_focalsetE.
    rewrite (split_big _ (fun w => [set w] \in focalset p)) /=.
    rewrite addrC big1 => [|w /andP [Hw1 Hw2]].
    - rewrite add0r.
      rewrite (reindex_omap set1 set1_oinv) /= => [|B /andP [HB1 HB2]].
      + apply eq_big => [w|w Hw //].
        by rewrite set1_oinv_pcancel eqxx andbT sub1set andbC.
      + apply set1_oinv_omap.
        apply (k_additive1E p) => // ; by rewrite (proba_ax p).
    - rewrite notin_focalset in Hw2.
      exact: eqP Hw2.
    Qed.
    #[deprecated(since="belgames2", note="Use Pr_PinfE instead.")]
    Notation Pr_BelE := Pr_PinfE.

  
    Lemma Pr_PsupE (p : proba) :
      Pr p =1 Psup p.
    Proof.
    move => B ; rewrite Pr_PinfE.
    destruct p as [m Hp].
    have := Hp ;  rewrite k_additive1E => Hkadd.
    rewrite Pinf_focalsetE Psup_focalsetE /=.
    rewrite (split_big _ (fun B : {set W} => #|B|==1%N )) ;
      rewrite [in RHS](split_big _ (fun B : {set W} => #|B|==1%N )) /=.
    have Hpred0 P (A : {set W}) : (A \in focalset m) && (P A) && (#|A| != 1%N) = false.
    case (boolP (A \in focalset m)) => Hfocal ; last by rewrite andFb.
    by rewrite (Hkadd A Hfocal) andbF.
    rewrite addrC big_pred0 => [|A] ; last exact: (Hpred0 (fun A => A \subset B)).
    rewrite [in RHS]addrC [in RHS]big_pred0 => [|A] ; last exact: (Hpred0 (fun A => A :&: B != set0)).
    rewrite !add0r.
    apply eq_bigl => A.
    case (boolP (A \in focalset m)) => Hfocal // ; last by rewrite (negbTE Hfocal) andFb.
    rewrite Hfocal !andTb.
    destruct (cards1P (Hkadd A Hfocal)) as [w Hw] ; rewrite Hw sub1set.
    by rewrite setI_eq0 disjoints1 Bool.negb_involutive.
    Qed.
    #[deprecated(since="belgames2", note="Use Pr_PsupE instead.")]
    Notation Pr_PlE := Pr_PsupE.

    Lemma proba_sum_dist_eq1 (p : proba) :
      \sum_w dist p w = 1.
    Proof.
    have [Hm0 Hm1] := andP (massfun_ax p).
    have H : Pr p setT = 1
      by rewrite Pr_PinfE /Pinf ; under eq_bigl do rewrite subsetT ; rewrite (eqP Hm1).
    move: H => /=. rewrite /Pr.
    by under eq_bigl do rewrite in_setT.
    Qed.

    (** For TBEU correctness -- to do LATER! *)
    Definition massfun_of_dist_fun (f : W -> R) (Hf : [&& \sum_w f w == 1 & [forall w, f w >= 0]]) : {ffun {set W} -> R}
      := [ffun A : {set W} => if #|A| == 1%N
                              then match boolP (A != set0) with
                                   | AltTrue h => f (pick_nonemptyset h)
                                   | _ => 0
                                   end
                              else 0].

    (*
    Lemma massfun_of_dist_monotone (f : W -> R) (Hf : [&& \sum_w f w == 1 & [forall w, f w >= 0]]) :
      monotonic_massfun (massfun_of_dist_fun Hf).
    Proof.
    have [Hf1 /forallP Hf0] := andP Hf.
    apply/forallP=>A ; apply/forallP=>B.
    rewrite [E in _<=E](bigID (fun i : {set W} => i \subset A)) /=.
    rewrite [E in _<=E+_](eq_bigl (fun i : {set W} => i \subset A)).
    rewrite (bigID (fun i : {set W} => #|i|==1)%N)
    [E in _<=_+E](bigID (fun i : {set W} => #|i|==1)%N) /=.
    rewrite [E in _+E<=_]big1 ;
      rewrite ?[E in _<=_+_+(_+E)]big1 ;
      rewrite ?[E in _<=_+E+_]big1 ?addr0.
    + rewrite big_mkcondl big_card1 -big_mkcond/=.
      rewrite [E in _<=_+E]big_mkcondl big_card1 -[E in _<=_+E]big_mkcond/=.
      rewrite lerDl sumr_ge0=>//w H.
      rewrite ffunE cards1 /=.
      by case (boolP ([set w] != set0)).
    + move=>C/andP[_ H].
      by rewrite ffunE (negbTE H).
    + move=>C/andP[_ H].
      by rewrite ffunE (negbTE H).
    + move=>C/andP[_ H].
      by rewrite ffunE (negbTE H).
    + move=>C.
      Search subset setU.
      case (boolP (C \subset A))=>H.
      * by rewrite subsetU // H.
      * by rewrite andbF.
    Qed.
     *)
    
    Lemma massfun_of_dist_ax (f : W -> R) (Hf : [&& \sum_w f w == 1 & [forall w, f w >= 0]]) :
      massfun_axiom (massfun_of_dist_fun Hf).
    Proof.
    have [Hf1 Hf2] := (andP Hf).
    apply/andP ; split.
    - by rewrite ffunE cards0.
    - under eq_bigr do rewrite ffunE.
      rewrite -big_mkcond.
      rewrite (split_big _ (fun A : {set W} => A != set0%N)) /= addrC big1 => [|w /andP [Hw1 Hw2]].
      + rewrite add0r (reindex_omap set1 set1_oinv) => /= [|A /andP [HA1 HA2]].
        * rewrite -(eqP Hf1).
          apply/eqP.
          have Hneset0 w : [set w] != set0. apply/set0Pn ; exists w ; by rewrite in_set1.
          apply: eq_big => [w|w Hw] ; first by rewrite cards1 Hneset0 set1_oinv_pcancel !eqxx.
          case (boolP ([set w] != set0)) => [H|] ; last by rewrite Hneset0.
          by rewrite (pick_set1 (x:=w)).
        * exact: set1_oinv_omap.
      + case (boolP (w != set0)) => // H ; by rewrite H in Hw2.
        (* - exact: massfun_of_dist_monotone. *)
    Qed.

    Definition massfun_of_dist (f : W -> R) (Hf : [&& \sum_w f w == 1 & [forall w, f w >= 0]]) : massfun
      := {| massfun_ax := massfun_of_dist_ax Hf |}.

    Lemma bpa_of_dist_ax (f : W -> R) (Hf : [&& \sum_w f w == 1 & [forall w, f w >= 0]]) :
      bpa_axiom (massfun_of_dist Hf).
    Proof.
    have [Hf1 Hf2] := (andP Hf).
    rewrite /bpa_axiom.
    - apply/forallP => A ; rewrite ffunE.
      case (#|A|==1%N) ; last by rewrite le0r eqxx orTb.
      case (boolP ((A : {set W}) != set0)) => H ; last by rewrite le0r eqxx orTb.
      exact: (forallP Hf2).
    Qed.

    Definition bpa_of_dist (f : W -> R) (Hf : [&& \sum_w f w == 1 & [forall w, f w >= 0]]) : bpa
      := {| bpa_ax := bpa_of_dist_ax Hf |}.

    Lemma massfun_of_dist_1add (f : W -> R) (Hf : [&& \sum_w f w == 1 & [forall w, f w >= 0]]) :
      1%N.-additive massfun_of_dist Hf.
    Proof.
    apply k_additive1E => B ; rewrite inE/focal_element ffunE.
    case (boolP (#|B| == 1)%N) => H /=.
    - case (boolP ((B : {set W}) != set0)) => [HB //|/negPn/eqP HB].
      by rewrite HB cards0 in H.
    - by rewrite eqxx.
    Qed.

    Lemma bpa_of_dist_1add (f : W -> R) (Hf : [&& \sum_w f w == 1 & [forall w, f w >= 0]]) :
      1%N.-additive bpa_of_dist Hf.
    Proof.
    exact: massfun_of_dist_1add.
    Qed.

    Definition proba_of_dist (f : W -> R) (Hf : [&& \sum_w f w == 1 & [forall w, f w >= 0]]) : proba
      := {| proba_ax := bpa_of_dist_1add Hf |}.

    Lemma proba_of_distE f (Hf :[&& \sum_w f w == 1 & [forall w, f w >= 0]]) w :
      dist (proba_of_dist Hf) w = f w.
    Proof.
    rewrite /dist/proba_of_dist/=/massfun_of_dist_fun ffunE cards1 eqxx.
    case (boolP ([set w] != set0)) => [H|/negPn /eqP H].
      by rewrite (pick_set1 (x:=w)).
      have : (0 = 1)%N. by rewrite -(cards1 w) -(cards0 W) H.
      by [].
    Qed.

  End KAdditivity.

  Notation "k '.-additive' m" := (k_additivity m == k) (at level 80, format " k '.-additive'  m ").



  Section Moebius.

    Program Fixpoint moebius_wf mu (A : {set W}) {measure #|A|} : R :=
      mu A - \sum_(B : {B0: {set W} | B0 \proper A}) moebius_wf mu B.
    Next Obligation.
    move=>mu A H [B HB].
    exact: ltP (proper_card HB).
    Defined.
    Next Obligation.
    apply: measure_wf.
    exact: Wf_nat.lt_wf.
    Defined.

    Definition moebius mu : {set W} -> R := fun A : {set W} => moebius_wf mu A.

    Lemma moebius_def mu A :
      moebius mu A = mu A - \sum_(B : {set W} | B \proper A) moebius mu B.
    Proof.
    rewrite -sig_big/moebius.
    rewrite/moebius_wf/moebius_wf_func Fix_eq //=.
    move => [mu' A'] /= y z Hyz.
    congr (_ - _).
    apply:eq_bigr => [B _] /=.
    by rewrite Hyz.
    Qed.

    Lemma moebiusE mu (A : {set W}) :
      mu A = \sum_(B : {set W} | B \subset A) moebius mu B.
    Proof.
    rewrite (bigD1 A) ?subxx // moebius_def -Monoid.mulmA /=.
    under [E in _ = _ + (-_ + E)]eq_bigl do rewrite -properEbis.
    by rewrite addNr addr0.
    Qed.

    Lemma massfun_moebiusE (m : massfun) (A : {set W}) :
      moebius (Pinf m) A = m A.
    Proof.
    move: A.
    apply: subset_ind=>A IH.
    rewrite moebius_def.
    rewrite [E in E-_=_]/Pinf (bigD1 A)//= -addrA.
    under eq_bigl do rewrite -properEbis.
    have Heq : \sum_(B: {set W} | B \proper A) moebius (Bel m) B = \sum_(B : {set W} | B \proper A) m B
      by apply: eq_bigr=>/=B HB ; rewrite IH=>//=.
    by rewrite Heq subrr addr0.
    Qed.

  End Moebius.
   *)

  
  Section Conditioning.
    (** Conditionings (aka knowledge revision) **)

    Implicit Type m : rmassfun R T.
    Implicit Type A B C : {set T}.

    Section ConditioningDefs.
      (** A conditioning transform Bel to Bel(.|C):
          - C should verify some predicate 'revisable'
          - Bel(.|C) should be such as no focal element is included in C^c (i.e. Bel(C^c)=0 for belief function)
       **)
      (*
      Definition conditioning_axiom (revisable : massfun -> pred {set W}) (cond : forall m C, revisable m C -> massfun)
        := forall m C (HC : revisable m C), Pinf (cond m C HC) (~:C) = 0.
       *)
      Definition conditioning_axiom (revisable : rmassfun R T -> pred {set T}) (cond : forall m C, revisable m C -> rmassfun R T)
        := forall m C (HC : revisable m C) (A : {set T}), A \subset ~:C -> cond m C HC A = 0.

      Structure conditioning
        := { revisable : rmassfun R T -> pred {set T} ;
             cond_val m C :>  revisable m C -> rmassfun R T ;
             cond_ax : @conditioning_axiom revisable cond_val }.


      Lemma conditioning_axiomE (revisable : rmassfun R T -> pred {set T}) (cond : forall m C, revisable m C -> rmassfun R T)
        : conditioning_axiom cond ->
          forall (m : rmassfun R T) (C : {set T}) (HC : revisable m C),
          forall B : {set T},
          (B \subset ~: C) -> B \notin focal (cond m C HC).
      Proof.
      move=>Hcond m C HC B HB /=.
      rewrite Bool.negb_involutive.
      by apply/eqP/Hcond.
      Qed.

      Lemma conditioning_axiomE2 (revisable : rmassfun R T -> pred {set T}) (cond : forall m C, revisable m C -> rmassfun R T)
        : (forall (m : rmassfun R T) (C : {set T}) (HC : revisable m C),
              forall B : {set T}, (B \subset ~: C) -> B \notin focal (cond m C HC))
        -> conditioning_axiom cond.
      Proof.
      move=>H m C HC A HA /=.
      have HcondE : A \notin focal (cond m C HC) -> cond m C HC A = 0
        by move=>/negbNE/eqP->.
      apply HcondE ; exact: H.
      Qed.

    End ConditioningDefs.



    Section DempsterConditioning.

      Definition Dempster_cond_revisable m C := Psup m C != 0.

      Definition Dempster_cond_fun (m : rmassfun R T) (C : {set T}) (HC : Dempster_cond_revisable m C) :=
       [ffun A : {set T} => if A == set0 then 0
                           else \sum_(B : {set T} | (B :&: C == A)) m B / Psup m C].


      Lemma Dempster_cond_massfun0 m C (HC : Dempster_cond_revisable m C) :
        Dempster_cond_fun HC set0 = 0.
      Proof. by rewrite ffunE eqxx. Qed.

      Lemma Dempster_cond_massfun1 m C (HC : Dempster_cond_revisable m C) :
        \sum_(A : {set T}) Dempster_cond_fun HC A = 1.
      Proof.
      apply/eqP.
      under eq_bigr do rewrite ffunE -if_neg.
      rewrite -big_mkcond /=.
      under eq_bigr do rewrite sum_div.
      rewrite sum_div_eq1 ; last exact: HC.
      rewrite (eq_bigr (fun A => (\sum_(B | B :&: C == A) m B) * 1)) ; last by move => B ; rewrite mulr1.
      rewrite -big_setI_distrl ffunE /=.
      apply/eqP ; apply eq_big => B ; rewrite ?mulr1//.
      by rewrite setI_eq0.
      Qed.

      HB.instance
      Definition NumMassFun_of_DempsterCond m C (HC : Dempster_cond_revisable m C) :=
        NumMassFun_of_Ffun.Build R T (Dempster_cond_fun HC) (Dempster_cond_massfun0 HC) (Dempster_cond_massfun1 HC).

      Definition Dempster_cond m C (HC : Dempster_cond_revisable m C) : rmassfun R T :=
        Dempster_cond_fun HC.

      Lemma Dempster_cond_ge0 (m : bpa R T) C (HC : Dempster_cond_revisable m C) A :
        Dempster_cond HC A >= 0.
      Proof.
      rewrite ffunE/=.
      case: ifP => _//.
      apply: sumr_ge0 => B HB.
      apply divr_ge0 ; first by rewrite bpa_ge0.
      exact: Pl_ge0.
      Qed.

      HB.instance
      Definition _ (m : bpa R T) C (HC : Dempster_cond_revisable m C) :=
        Bpa_of_NumMassFun.Build R T (Dempster_cond HC) (Dempster_cond_ge0 HC).

      (*
      Definition Dempster_cond_bpa (m : bpa) (C : {set W}) (HC : Dempster_cond_revisable m C) : bpa
        := {| bpa_ax := Dempster_cond_bpa_ax HC |}.
       *)
      
      Lemma Dempster_cond_sumE m C (HC : Dempster_cond_revisable m C) f :
        \sum_(B in focal (Dempster_cond HC))
         Dempster_cond HC B * f B
        =
        (\sum_(A in focal m)
          if A :&: C != set0
          then m A * f (A :&: C)
          else 0) / Psup m C.
      Proof.
      rewrite -[in RHS]big_mkcondr sum_fun_focalset_cond.
      Opaque Dempster_cond.
      rewrite (big_setI_distrl (fun b => b != set0)) sum_fun_focalset (bigD1 set0) //=.
      rewrite mass_set0 mul0r add0r.
      under [in RHS]eq_bigr do rewrite mulrC.
      rewrite big_distrl /=.
      under [in RHS]eq_bigr do rewrite -mulrA big_distrl mulrC /=.
      apply eq_big => // B HB.
      Transparent Dempster_cond.
      by rewrite ffunE (negbTE HB).
      Qed.

      Lemma Dempster_cond_axiom : @conditioning_axiom Dempster_cond_revisable Dempster_cond.
      Proof.
      apply conditioning_axiomE2 => m C HC B HB.
      rewrite notin_focalset ffunE => //=.
      case (boolP (B == set0)) => // /set0Pn [w Hw].
      rewrite big_pred0 => // A.
      case (boolP (A :&: C == B)) => //HA.
      rewrite -(eqP HA) in HB ; rewrite -(eqP HA) in Hw.
      contradiction (subsetF (subsetIr A C) HB Hw).
      Qed.

      Definition Dempster_conditioning : conditioning
        := {| cond_val := Dempster_cond ;
             cond_ax := Dempster_cond_axiom |}.


    End DempsterConditioning.

    Section FHConditioning.

      Definition FH_cond_revisable m C := Pinf m C != 0.

      Definition FH_Pinf m C :=
        [ffun A : {set T} => Pinf m (A :&: C) / ( Pinf m (A :&: C) + Psup m ((~:A) :&: C))].

      Lemma FH_PinfT m C :
        FH_cond_revisable m C
        -> FH_Pinf m C setT = 1.
      Proof.
      rewrite /FH_Pinf=>H.
      by rewrite ffunE setTI setCT set0I Psup0 addr0 divff.
      Qed.

      Definition FH_cond_fun (m : rmassfun R T) (C : {set T}) (HC : FH_cond_revisable m C) :=
       [ffun A : {set T} => moebius (FH_Pinf m C) A].


      Lemma FH_cond_massfun0 (m : rmassfun R T) (C : {set T}) (HC : FH_cond_revisable m C) :
        FH_cond_fun HC set0 = 0.
      Proof. by rewrite ffunE moebius0 ffunE set0I Pinf0 mul0r. Qed.
      
      Lemma FH_cond_massfun1 (m : rmassfun R T) (C : {set T}) (HC : FH_cond_revisable m C) :
        \sum_(A : {set T}) FH_cond_fun HC A = 1.
      Proof.
      - under eq_bigr do rewrite ffunE.
        have :=  moebiusE (FH_Pinf m C) setT.
        rewrite FH_PinfT=>//->.
        by apply: eq_big=>/=[B|//] ; rewrite subsetT.
      Qed.

      HB.instance
      Definition _ m C (HC : FH_cond_revisable m C) :=
        NumMassFun_of_Ffun.Build R T (FH_cond_fun HC) (FH_cond_massfun0 HC) (FH_cond_massfun1 HC).
      
      Definition FH_cond m C (HC : FH_cond_revisable m C) : rmassfun R T :=
        FH_cond_fun HC.
      
      Lemma FH_cond_axiom : @conditioning_axiom FH_cond_revisable FH_cond.
      Proof.
      rewrite /conditioning_axiom/=/FH_cond.
      move=>m C HC.
      apply: subset_ind=>A IH HA.
      rewrite ffunE moebius_def.
      apply/eqP ; rewrite subr_eq0 ; apply/eqP.
      rewrite {1}/FH_Pinf.
      have HAC : (A :&: C) = set0
        by apply: disjoint_setI0 ; rewrite disjoints_subset.
      rewrite ffunE HAC Pinf0 mul0r big1=>//B HB.
      rewrite -ffunE.
      apply: IH=>//.
      apply: (subset_trans _ HA).
      exact: proper_sub.
      Qed.

      Definition FH_conditioning : conditioning
        := {| cond_val := FH_cond ;
              cond_ax := FH_cond_axiom |}.

    End FHConditioning.



    Section StrongConditioning.


      Definition Strong_cond_revisable (m : rmassfun R T) := fun C : {set T} => Pinf m C != 0.

      
      Definition Strong_cond_fun (m : rmassfun R T) (C : {set T}) (HC : Strong_cond_revisable m C) :=
        [ffun A : {set T} => if (A != set0) && (A \subset C)
                            then m A / Pinf m C else 0].

      Lemma Strong_cond_massfun0 m C (HC : Strong_cond_revisable m C) :
        Strong_cond_fun HC set0 = 0.
      Proof. by rewrite ffunE eqxx. Qed.

      Lemma Strong_cond_massfun1 m C (HC : Strong_cond_revisable m C) :
        \sum_(A : {set T}) Strong_cond_fun HC A = 1.
      Proof.
      apply/eqP.
      under eq_bigr do rewrite ffunE.
      rewrite -big_mkcond sum_div_eq1 /Pinf ; last exact: HC.
      rewrite ffunE/=.
      apply/eqP.
      rewrite [in RHS](bigD1 set0) /= ; last exact: sub0set.
      by rewrite massfun0 add0r ; under eq_bigl do rewrite andbC.
      Qed.

      HB.instance
      Definition NumMassFun_of_StrongCond m C (HC : Strong_cond_revisable m C) :=
        NumMassFun_of_Ffun.Build R T (Strong_cond_fun HC) (Strong_cond_massfun0 HC) (Strong_cond_massfun1 HC).

      Definition Strong_cond m C (HC : Strong_cond_revisable m C) : rmassfun R T :=
        Strong_cond_fun HC.
      
      Lemma Strong_cond_axiom : @conditioning_axiom Strong_cond_revisable Strong_cond.
      Proof.
      apply conditioning_axiomE2 => m C HC B H.
      rewrite notin_focalset ffunE => //=.
      case (boolP (B == set0)) => //= /set0Pn [t Ht].
      case (boolP (B \subset C)) => //= HB.
      contradiction (subsetF HB H Ht).
      Qed.

      Definition Strong_conditioning : conditioning
        := {| cond_val := Strong_cond ;
              cond_ax := Strong_cond_axiom |}.

    End StrongConditioning.


    Section WeakConditioning.

      Definition Weak_cond_revisable (m : rmassfun R T) := fun C : {set T} => Psup m C != 0.
      
      Definition Weak_cond_fun (m : rmassfun R T) (C : {set T}) (HC : Weak_cond_revisable m C) :=
        [ffun A : {set T} => if A :&: C != set0 then m A / Psup m C else 0].

      Lemma Weak_cond_massfun0 m C (HC : Weak_cond_revisable m C) :
        Weak_cond_fun HC set0 = 0.
      Proof. by rewrite ffunE set0I eqxx. Qed.

      Lemma Weak_cond_massfun1 m C (HC : Weak_cond_revisable m C) :
        \sum_(A : {set T}) Weak_cond_fun HC A = 1.
      Proof.
      apply/eqP.
      under eq_bigr do rewrite ffunE.
      rewrite -big_mkcond sum_div_eq1 //.
      rewrite ffunE.
      apply/eqP; apply: eq_bigl=>A.
      by rewrite setI_eq0.
      Qed.

      HB.instance
      Definition NumMassFun_of_WeakCond m C (HC : Weak_cond_revisable m C) :=
        NumMassFun_of_Ffun.Build R T (Weak_cond_fun HC) (Weak_cond_massfun0 HC) (Weak_cond_massfun1 HC).

      Definition Weak_cond m C (HC : Weak_cond_revisable m C) : rmassfun R T :=
        Weak_cond_fun HC.

      Lemma Weak_cond_axiom : @conditioning_axiom Weak_cond_revisable Weak_cond.
      Proof.
      apply conditioning_axiomE2 => m C HC B H.
      rewrite notin_focalset ffunE => //=.
      case (boolP (B :&: C == set0)) => //= /set0Pn [w Hw].
      move: Hw ; rewrite in_setI => /andP [Hw1 Hw2].
      move: H ; rewrite subsetE => /pred0P H.
      have := H w => /= ; rewrite Hw1 andbT => /negP/negP.
      by rewrite in_setC Hw2.
      Qed.
      
      Definition Weak_conditioning : conditioning
        := {| cond_val := Weak_cond ;
              cond_ax := Weak_cond_axiom |}.

    End WeakConditioning.





    (*
    Section ProbaConditioning.

      Notation Pr := Pinf.

      Definition Pr_revisable (p : prBpa R T) (C : {set T})
        := Pr p C != 0.

      Definition Pr_conditioning_dist (p : prBpa R T) C (HC : Pr_revisable p C) :=
        fun w => (if w \in C then dist p w else 0) / Pr p C.

      HB.about PrBpa_of_Bpa.Build.

      Lemma Pr_conditinoing_dist_is_dist p C (HC : Pr_revisable p C) :
        is_dist (Pr_conditioning_dist HC).
      Proof.
      apply/andP ; split.
      - by rewrite sum_div_eq1 // -big_mkcond.
      - apply/forallP => w.
        rewrite /Pr_conditioning_dist/Pr/dist.
        destruct p as [m Hm] => /=.
        have /forallP Hm3 := bpa_ax m.
        case (w \in C).
        + apply: divr_ge0 => //=.
          by apply: sumr_ge0 => w' _.
        + by rewrite mul0r le0r eqxx orTb.
      Qed.

      Definition Pr_conditioning (p : proba) C (HC : Pr_revisable p C) : proba
        := proba_of_dist (Pr_conditinoing_dist_is_dist HC).

      Lemma Pr_revisable_of_Dempster_revisable (p : proba) C (HC : Dempster_cond_revisable p C) :
        Pr_revisable p C.
      Proof. by rewrite /Pr_revisable Pr_PsupE. Qed.

    End ProbaConditioning.
     *)
  End Conditioning.


  Section ScoringFunctions.

    (*
    Import Order Order.TotalTheory.

    Definition omin : option R -> option R -> option R
      := fun or1 or2 => match or1,or2 with
                           | Some r1, Some r2 => Some (min r1 r2)
                           | Some r, None | None, Some r => Some r
                           | _, _ => None
                           end.

    (*
    Definition min_monoid_law : Monoid.law (None : option R).
    exists omin ; rewrite /omin => //=.
    do 2 split.
    - move => [x|] [y|] [z|] // ; by rewrite minA.
    - by move => [x|] //.
    - by move => [x|] //.
    Defined.
     *)
    
    Definition min_comlaw : Monoid.com_law (None : option R).
    Proof.
    exists omin ; rewrite/omin =>//=.
    do 2 split.
    - move => [x|] [y|] [z|] // ; by rewrite minA.
    - by move => [x|] //.
    - by move => [x|] //.
    - move => [x|] [y|] //=.
      apply f_equal.
      by rewrite minC.
    Defined.

    Definition minS (u : W -> R) (B : {set W}) : option R
      := \big[min_comlaw/None]_(w in B) Some (u w).

    Definition omax : option R -> option R -> option R
      := fun or1 or2 => match or1,or2 with
                           | Some r1, Some r2 => Some (max r1 r2)
                           | Some r, None | None, Some r => Some r
                           | _, _ => None
                           end.

    (*
    Definition max_monoid_law : Monoid.law (None : option R).
    exists omax ; rewrite /omax.
    - move => [x|] [y|] [z|] // ; by rewrite maxA.
    - by move => [x|] //.
    - by move => [x|] //.
    Defined.
     *)
    
    Definition max_comlaw : Monoid.com_law (None : option R).
    Proof.
    exists omax ; rewrite /omax.
    do 2 split.
    - move => [x|] [y|] [z|] // ; by rewrite maxA.
    - by move => [x|] //.
    - by move => [x|] //.
    - move => [x|] [y|] //=.
      apply f_equal.
      by rewrite maxC.
    Defined.

    Definition maxS (u : W -> R) (B : {set W}) : option R
      := \big[max_comlaw/None]_(w in B) Some (u w).

     *)
    Lemma minSeq (u1 u2 : T -> R) (B : {set T}) :
      {in B, u1 =1 u2} -> minS u1 B = minS u2 B.
    Proof.
    rewrite /minS => Hu.
    apply eq_bigr => t Ht ;
    apply f_equal.
    by rewrite Hu.
    Qed.

    Lemma maxSeq (u1 u2 : T -> R) (B : {set T}) :
      {in B, u1 =1 u2} -> maxS u1 B = maxS u2 B.
    Proof.
    rewrite /maxS => Hu.
    apply eq_bigr => t Ht.
    apply f_equal.
    by rewrite Hu.
    Qed.

    (*
    Lemma minS1 (u : W -> R) (w : W) :
      minS u [set w] = Some (u w).
    Proof.
    rewrite /minS (big_pred1 w) => // x.
    by rewrite in_set1.
    Qed.

    Lemma maxS1 (u : W -> R) (w : W) :
      maxS u [set w] = Some (u w).
    Proof.
    rewrite /maxS (big_pred1 w) => // x.
    by rewrite in_set1.
    Qed.

    Definition ChoquetIntg (u : W -> R) (m : rmassfun R T) :=
      \sum_(B in focalset m) m B * match minS u B with
                                   | Some r => r
                                   | None => 0
                                   end.

    Lemma Bfocal_minS_Some (m : rmassfun R T) (u : W -> R) :
      forall B, focal_element m B -> minS u B != None.
    Proof.
    rewrite /minS => B HB.
    have [w Hw] := pick_nonemptyset_sig (focal_neq_set0 HB).
    rewrite (bigD1 w Hw) => /=.
    by case (@bigop.body _ _ (@None (Num.RealField.sort R))).
    Qed.

     *)

    Notation utility_function T := {ffun T -> R} (only parsing).

    Definition xeu_function (T : finType) := ({ffun T -> R} -> {ffun {set T} -> R}).

    Definition EU (p : prBpa R T) (u : utility_function T) : R
      := \sum_t dist p t * u t.

    Notation "[ 'EU' 'of' u 'wrt' p ]" := (EU p u) (at level 80).

    Definition eq_xeu (f_xeu : xeu_function T) :=
      forall (u1 u2 : utility_function T),
      forall B : {set T}, {in B, u1 =1 u2} -> f_xeu u1 B = f_xeu u2 B.

    Definition XEUm (m : rmassfun R T) (phi_u_a : {ffun {set T} -> R}) : R
      := \sum_(B in focal m) m B * phi_u_a B.

    Definition fCEU : xeu_function T
      := fun u => [ffun B => match minS u B with
                             | Some r => r
                             | None => 0
                             end].

    Definition CEU m u_a := XEUm m (fCEU u_a).
    Notation "[ 'CEU' 'of' u 'wrt' m ]" := (CEU m u) (at level 80).

    Lemma eq_CEU : eq_xeu fCEU.
    Proof.
    move => u1 u2 B H.
    by rewrite !ffunE (minSeq H).
    Qed.

    (*
    Lemma ceuE (m : rmassfun R T) (u : utility_function T) :
      [CEU of u wrt m] = ChoquetIntg u m.
    Proof.
    apply eq_bigr => B HB ; by rewrite ffunE.
    Qed.
     *)
    
    Definition fJEU (alpha : R -> R -> R) : xeu_function T
      := fun u_a => [ffun B => match minS u_a B, maxS u_a B with
                           | Some rmin, Some rmax =>
                               let alp := alpha rmin rmax in alp * rmin + (1-alp) * rmax
                           | _, _ => 0
                           end].

    Definition JEU alpha m u_a := XEUm m (fJEU alpha u_a).
    Notation "[ 'JEU' alpha 'of' u 'wrt' m ]" := (JEU alpha m u) (at level 80).

    Lemma eq_JEU alpha : eq_xeu (fJEU alpha).
    Proof.
    move => u1 u2 B H.
    by rewrite !ffunE (minSeq H) (maxSeq H).
    Qed.

    Definition fTBEU : xeu_function T
      := fun u_a => [ffun B : {set T} => \sum_(t in B) u_a t / #|B|%:R].

    Definition TBEU m u := XEUm m (fTBEU u).
    Notation "[ 'TBEU' 'of' u 'wrt' m ]" := (TBEU m u) (at level 80).

    Lemma eq_TBEU : eq_xeu fTBEU.
    Proof.
    move => u1 u2 B H.
    rewrite !ffunE.
    by apply eq_bigr => w Hw ; rewrite H.
    Qed.

    (*
    Lemma XEU_EU (p : proba) (u : utility_function W) (xeu : xeu_function W) (Hxeu : forall w, (xeu u) [set w] = u w) :
      XEUm p (xeu u) = EU p u.
    Proof.
    destruct p as [m Hm].
    rewrite /XEUm /EU /dist /=.
    rewrite (split_big predT (fun w => [set w] \in focalset m)) /=.
    rewrite addrC [in RHS]big1 => [|w].
    - rewrite add0r (reindex_omap set1 set1_oinv) /= => [|B HB].
      + apply eq_big => [w | w Hw].
        * by rewrite set1_oinv_pcancel eqxx andbT.
        * by rewrite Hxeu.
      + apply set1_oinv_omap.
        by apply (k_additive1E m).
    - rewrite notin_focalset => /eqP ->.
      by rewrite mul0r.
    Qed.

    Lemma CEU_EU (p : proba) (u_a : utility_function W) :
      [CEU of u_a wrt p] = [EU of u_a wrt p].
    Proof.
    apply: XEU_EU => w /=.
    by rewrite ffunE minS1.
    Qed.

    Lemma JEU_EU alpha (p : proba) (u_a : utility_function W) :
      [JEU alpha of u_a wrt p] = [EU of u_a wrt p].
    Proof.
    apply: XEU_EU => w /=.
    by rewrite ffunE minS1 maxS1 /= mulrDl addrC -addrA -mulrDl (addrC (-_)) subrr mul1r mul0r addr0.
    Qed.

    Lemma TBEU_EU (p : proba) (u_a : utility_function W) :
      [TBEU of u_a wrt p] = [EU of u_a wrt p].
    Proof.
    apply: XEU_EU => w /=.
    rewrite ffunE (bigD1 w) /= ; last by rewrite in_set1.
    rewrite big1 => [|w'] ; first by rewrite addr0 cards1 divr1.
    rewrite in_set1 ; by case (w' == w).
    Qed.
     *)
  End ScoringFunctions.

  Notation "[ 'EU' 'of' u 'wrt' p ]" := (EU p u) (at level 80).
  Notation "[ 'CEU' 'of' u 'wrt' m ]" := (XEUm m (fCEU u)) (at level 80).
  Notation "[ 'JEU' alpha 'of' u 'wrt' m ]" := (XEUm m (fJEU alpha u)) (at level 80).
  Notation "[ 'TBEU' 'of' u 'wrt' m ]" := (XEUm m (fTBEU u)) (at level 80).

  Section TBM.

    Definition BetP_fun (m : rmassfun R T) : T -> R
      := (fun t => \sum_(A in focal m | t \in A) m A / #|A|%:R).

    (*
    Lemma is_dist_BetP (m : bpa) :
      is_dist (BetP_fun m).
    Proof.
    have [Hm1 Hm2] := andP (rmassfun R T_ax m).
    have Hm3 := bpa_ax m.
    rewrite /BetP_fun ; apply/andP ; split.
    - rewrite sum_of_sumE.
      under eq_bigr do rewrite -big_distrr /=.
      rewrite (eq_bigr m) => [|A HA] ; first by rewrite sum_mass_focalset.
      rewrite sum_cardiv ; first by rewrite mulr1.
      rewrite in_focalset_focalelement in HA.
      have := focal_neq_set0 HA.
      by rewrite -card_gt0.
    - apply/forallP => w.
      apply: sum_ge0 => A _.
      apply divr_ge0.
      + exact: (forallP Hm3).
      + exact: ler0n.
    Qed.

    Definition BetP (m : bpa) : proba
      := proba_of_dist (is_dist_BetP m).
     *)


    Lemma TBEU_EUBetP (m : rmassfun R T) u :
      [TBEU of u wrt m] = \sum_t BetP_fun m t * u t.
    Proof.
    rewrite /TBEU/XEUm.
    under eq_bigr do rewrite ffunE.
    rewrite sum_fun_focalset.
    under [RHS]eq_bigr do rewrite /BetP_fun sum_fun_focalset_cond.
    have Hl B : m B * (\sum_(t in B) u t / #|B|%:R) = (\sum_(t in B) m B * u t / #|B|%:R).
    by rewrite big_distrr /= ; under eq_bigr do rewrite mulrA.
    have Hr t : (\sum_(B : {set T} | t \in B) m B / #|B|%:R) * u t =  (\sum_(B : {set T} | t \in B) m B * u t / #|B|%:R).
    by rewrite big_distrl /= ; under eq_bigr do rewrite mulrC mulrA (mulrC (u _)).
    under [LHS]eq_bigr do rewrite Hl.
    under [RHS]eq_bigr do rewrite Hr.
    exact: big_partitionS.
    Qed.

  (*
    Lemma TBEU_EUBetP_bpa (m : bpa R T) u :
      [TBEU of u wrt m] = [EU of u wrt BetP m].
    Proof.
    under [RHS]eq_bigr do rewrite proba_of_distE.
    exact: TBEU_EUBetP.
    Qed.

     *)
  End TBM.
End Capacity.

(*

#[deprecated(since="belgames2", note="Use Pinf instead.")]
Notation Bel := Pinf.
#[deprecated(since="belgames2", note="Use Psup instead.")]
Notation Pl := Psup.
#[deprecated(since="belgames2", note="Use massfun_nonempty instead.")]
Notation bpa_nonempty := massfun_nonempty.
#[deprecated(since="belgames2", note="Use massfun_nonemptyW instead.")]
Notation bpa_nonemptyW := massfun_nonemptyW.
#[deprecated(since="belgames2", note="Use Pinf_focalset instead.")]
Notation Bel_focalsetE := Pinf_focalsetE.
#[deprecated(since="belgames2", note="Use Psup_focalset instead.")]
Notation Pl_focalsetE := Psup_focalsetE.
#[deprecated(since="belgames2", note="Use Pinf0 instead.")]
Notation Bel_set0 := Pinf0.
#[deprecated(since="belgames2", note="Use Psup0 instead.")]
Notation Pl_set0 := Psup0.
#[deprecated(since="belgames2", note="Use PinfE instead.")]
Notation BelE := PinfE.
#[deprecated(since="belgames2", note="Use PsupE instead.")]
Notation PlE := PsupE.
#[deprecated(since="belgames2", note="Use Pr_PinfE instead.")]
Notation Pr_BelE := Pr_PinfE.
#[deprecated(since="belgames2", note="Use Pr_PsupE instead.")]
Notation Pr_PlE := Pr_PsupE.

Notation "k '.-additive' m" := (k_additivity m == k) (at level 80, format " k '.-additive'  m ").
Notation proba_axiom p := (1%N.-additive p) (only parsing).
Notation "[ 'EU' 'of' u 'wrt' p ]" := (EU p u) (at level 80).
Notation "[ 'CEU' 'of' u 'wrt' m ]" := (XEUm m (fCEU u)) (at level 80).
Notation "[ 'JEU' alpha 'of' u 'wrt' m ]" := (XEUm m (fJEU alpha u)) (at level 80).
Notation "[ 'TBEU' 'of' u 'wrt' m ]" := (XEUm m (fTBEU u)) (at level 80).
*)



Section BelOnFFuns.

  Variable R : realFieldType.
  Variable X : finType.
  Variable T : X -> finType.

  Notation Tn := [finType of {dffun forall i : X, T i}].

  (* NOTE :: conditioning event "given t i == ti" *)
  Definition event_ti i (ti : T i) := [set t : Tn | t i == ti].

  Lemma negb_focal_revise (m : rmassfun R Tn) (cond : conditioning R Tn) i ti (H : revisable cond m (event_ti ti)) :
    forall A : {set Tn},
    (forall t, t \in A -> ti != t i) -> A \notin focal (cond m (event_ti ti) H).
  Proof.
  move => A HA.
  apply conditioning_axiomE ; first exact: cond_ax.
  rewrite subsetE.
  apply/pred0P => t /=.
  rewrite !inE.
  case (boolP (t \in A)) => Ht ; last by rewrite (negbTE Ht) andbF.
  by rewrite eq_sym (HA t Ht) andFb.
  Qed.

  (*
  Definition ffun_of_proba (p : forall i : X, proba R (T i)) :
    (forall i : X, {ffun {set T i} -> R}).
  Proof. move=> i; apply p. Defined.

   Lemma proba_set1 (p : forall i : X, proba R (T i)) :
    forall i : X, \sum_(k in T i) p i [set k] = \sum_A p i A.
  Proof.
    move=> i.
    have x0 : T i.
    { have P_i := p i.
      have [b _] := P_i.
      apply: massfun_nonemptyW b. }
    set h' : {set (T i)} -> T i :=
      fun s =>
        match [pick x | x \in s] with
        | Some x => x
        | None => x0
        end.
    rewrite
      -(big_rmcond _ (I := {set (T i)}) _ (P := fun s => #|s| == 1%N));
      last by move=> s Hs; exact: proba_set1_eq0.
    rewrite (reindex_onto (I := {set (T i)}) (J := T i)
                          (fun j => [set j]) h'
                          (P := fun s => #|s| == 1%N) (F := fun s => p i s)) /=; last first.
    { by move=> j Hj; rewrite /h'; case/cards1P: Hj => xj ->; rewrite pick_set1E. }
    under [in RHS]eq_bigl => j do rewrite /h' pick_set1E cards1 !eqxx andbT.
    exact: eq_bigr.
  Qed.

  Definition mk_prod_proba (p : forall i : X, proba R (T i)) : {ffun Tn -> R}
    := [ffun t : Tn => \prod_i dist (p i) (t i)].

  Lemma mk_prod_proba_dist p (witnessX : X) : is_dist (mk_prod_proba p).
  Proof.
  apply/andP ; split.
  - under eq_bigr do rewrite /mk_prod_proba ffunE.
    set pp := (fun i => [ffun a => (ffun_of_proba p i [set a])]).
    have L := (@big_fprod R X (fun i => T i) pp).
    do [under [LHS]eq_bigr => i Hi do under eq_bigr => j Hj do rewrite /pp ffunE /ffun_of_proba] in L.
    do [under [RHS]eq_bigr => i Hi do under eq_bigr => j Hj do rewrite /pp /ffun_of_proba] in L.
    erewrite (reindex).
    2: exists (@fprod_of_dffun X _).
    2: move=> *; apply: dffun_of_fprodK.
    2: move => *; apply: fprod_of_dffunK.
    under (* Improve PG indentation *)
      eq_bigr do under eq_bigr do rewrite /dffun_of_fprod !ffunE.
    rewrite L.
    under eq_bigr do under eq_bigr do rewrite /ffun_of_proba.
    apply/eqP; rewrite [X in _ = X](_ : 1 = \big[*%R/1%R]_(i in X) 1)%R; last by rewrite big1.
    rewrite -(bigA_distr_big_dep _ (fun i j => otagged [ffun a => p i [set a]] 0%R j)).
    apply eq_bigr => i _ /=.
    rewrite (big_tag pp).
    have := fun i => @massfun_ax R (T i)  => H.
    have Hi := H i (p i).
    have/andP [Hm0 Hm1] := Hi.
    move/eqP in Hm1.
    apply/eqP; rewrite -Hm1.
    under eq_bigr => k Hk do rewrite ffunE /ffun_of_proba.
    apply/eqP.
    exact: proba_set1.
  - apply/forallP => t.
    rewrite ffunE.
    apply: prodr_ge0=>x _.
    rewrite /dist.
    exact: (forallP (bpa_ax (p x))) [set t x].
  Qed.
  
  Definition prod_proba (p : forall i : X, proba R (T i)) (witnessX : X)  : proba R Tn
    := proba_of_dist (mk_prod_proba_dist p witnessX).
   *)
End BelOnFFuns.

Close Scope ring_scope.

