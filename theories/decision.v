(******************************************************************************)
(*
Conditioning and decision rule for generalized bel-games
             modules 'games' and 'HRtransform'
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

From BelGames Require Import fintype finset setfun ssrnum order minmax.
From BelGames Require Import massfun.

Section Capacity.

  Variable (R : realFieldType).
  Variable (T : finType).

  Open Scope ring_scope.


  Section Conditioning.
    (** Conditionings (aka knowledge revision) **)

    Implicit Type m : rmassfun R T.
    Implicit Type A B C : {set T}.

    Section ConditioningDefs.
      (** A conditioning transform Bel to Bel(.|C):
          - C should verify some predicate 'revisable'
          - Bel(.|C) should be such as no focal element is included in C^c (i.e. Bel(C^c)=0 for belief function)
       **)
      
      Definition conditioning_axiom (revisable : rmassfun R T -> pred {set T})
      (cond : forall m C, revisable m C -> rmassfun R T)
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

      Definition Dempster_cond (m : rmassfun R T) (C : {set T}) (HC : Dempster_cond_revisable m C) :=
       [ffun A : {set T} => if A == set0 then 0
                           else \sum_(B : {set T} | (B :&: C == A)) m B / Psup m C].


      Lemma Dempster_cond_massfun0 m C (HC : Dempster_cond_revisable m C) :
        Dempster_cond HC set0 == 0.
      Proof. by rewrite ffunE eqxx. Qed.

      Lemma Dempster_cond_massfun1 m C (HC : Dempster_cond_revisable m C) :
        \sum_(A : {set T}) Dempster_cond HC A == 1.
      Proof.
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
      Definition _ m C (HC : Dempster_cond_revisable m C) :=
        MassFun_of_Ffun.Build R T 0 +%R (Dempster_cond HC).

      HB.instance
      Definition _ m C (HC : Dempster_cond_revisable m C) :=
        AddMassFun_of_MassFun.Build R T (Dempster_cond HC) (Dempster_cond_massfun0 HC) (Dempster_cond_massfun1 HC).

      Lemma Dempster_cond_ge0b (m : bpa R T) C (HC : Dempster_cond_revisable m C) :
        [forall A : {set T}, Dempster_cond HC A >= 0].
        Proof.
      apply/forallP=>/=A.
      rewrite ffunE/=.
      case: ifP => _//.
      apply: sumr_ge0 => B HB.
      apply divr_ge0 ; first by rewrite bpa_ge0.
      exact: Psup_ge0.
      Qed.

      HB.instance
      Definition _ (m : bpa R T) C (HC : Dempster_cond_revisable m C) :=
        Bpa_of_AddMassFun.Build R T (Dempster_cond HC) (Dempster_cond_ge0b HC).

      Lemma Dempster_cond_card1 (m : prBpa R T) C (HC : Dempster_cond_revisable m C) A :
        Dempster_cond HC A != 0 -> #|A| == 1%N.
      Proof.
      rewrite ffunE.
      apply/implyP.
      rewrite -implybNN.
      apply/implyP=>Hcard.
      apply/negPn.
      case (boolP (A == set0)) ; rewrite ?eqxx=>// HA0.
      have HcardA_gt1 : (#|A| > 1)%N
        by rewrite ltn_neqAle eq_sym Hcard andTb card_gt0 HA0.
      apply/eqP.
      rewrite sum_ge0_eq0E=>/=B /eqP HB.
      - have HcardB_gt1 : (#|B| > 1)%N
          by apply: (@Order.POrderTheory.lt_le_trans _ nat _ _ _ HcardA_gt1) ;
          apply: subset_leq_card ; rewrite -HB ; exact: subsetIl.
        have HmB : m B == 0
          by apply/negP=>/negP Hcontra ; move: HcardB_gt1 ;
          rewrite ltn_neqAle eq_sym (prbpa_card1 Hcontra) andFb.
        by rewrite (eqP HmB) mul0r.
      - apply: mulr_ge0 ; first exact: bpa_ge0.
        rewrite invr_ge0.
        exact: Psup_ge0.
      Qed.

      Lemma Dempster_cond_card1b (m : prBpa R T) C (HC : Dempster_cond_revisable m C) :
        [forall A : {set T}, (Dempster_cond HC A != 0) ==> (#|A| == 1%N)].
      Proof. apply/forallP=>/=A ; apply/implyP ; exact: Dempster_cond_card1. Qed.

      HB.instance
      Definition _ (m : prBpa R T) C (HC : Dempster_cond_revisable m C) :=
        PrBpa_of_Bpa.Build R T (Dempster_cond HC) (Dempster_cond_card1b HC).

      
      
      Lemma Dempster_cond_sumE m C (HC : Dempster_cond_revisable m C) f :
        \sum_(B in focal (Dempster_cond HC))
         Dempster_cond HC B * f B
        =
        (\sum_(A in focal m)
          if A :&: C != set0
          then m A * f (A :&: C)
          else 0) / Psup m C.
      Proof.
      rewrite -[in RHS]big_mkcondr sum_fun_focal_cond.
      Opaque Dempster_cond.
      rewrite (big_setI_distrl (fun b => b != set0)) sum_fun_focal (bigD1 set0) //=.
      rewrite (eqP massfun0) mul0r add0r.
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
      rewrite notin_focal ffunE => //=.
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
      by rewrite ffunE setTI setCT set0I (pointed0 (Psup01 m)) addr0 divff.
      Qed.

      Definition FH_cond_fun (m : rmassfun R T) (C : {set T}) (HC : FH_cond_revisable m C) :=
       [ffun A : {set T} => moebius (FH_Pinf m C) A].


      Lemma FH_cond_massfun0 (m : rmassfun R T) (C : {set T}) (HC : FH_cond_revisable m C) :
        FH_cond_fun HC set0 == 0.
      Proof. by rewrite ffunE moebius0 ffunE set0I (pointed0 (Pinf01 m)) mul0r. Qed.
      
      Lemma FH_cond_massfun1 (m : rmassfun R T) (C : {set T}) (HC : FH_cond_revisable m C) :
        \sum_(A : {set T}) FH_cond_fun HC A == 1.
      Proof.
      apply/eqP.
      under eq_bigr do rewrite ffunE.
      have :=  moebiusE (FH_Pinf m C) setT.
      rewrite FH_PinfT=>//->.
      by apply: eq_big=>/=[B|//] ; rewrite subsetT.
      Qed.

      HB.instance
      Definition _ m C (HC : FH_cond_revisable m C) :=
        MassFun_of_Ffun.Build R T 0 +%R (FH_cond_fun HC).

      HB.instance
      Definition _ m C (HC : FH_cond_revisable m C) :=
        AddMassFun_of_MassFun.Build R T (FH_cond_fun HC) (FH_cond_massfun0 HC) (FH_cond_massfun1 HC).
      
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
      rewrite ffunE HAC (pointed0 (Pinf01 m)) mul0r big1=>//B HB.
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
        Strong_cond_fun HC set0 == 0.
      Proof. by rewrite ffunE eqxx. Qed.

      Lemma Strong_cond_massfun1 m C (HC : Strong_cond_revisable m C) :
        \sum_(A : {set T}) Strong_cond_fun HC A == 1.
      Proof.
      under eq_bigr do rewrite ffunE.
      rewrite -big_mkcond sum_div_eq1 /Pinf ; last exact: HC.
      rewrite ffunE/=.
      apply/eqP.
      rewrite [in RHS](bigD1 set0) /= ; last exact: sub0set.
      by rewrite (eqP massfun0) add0r ; under eq_bigl do rewrite andbC.
      Qed.

      HB.instance
      Definition _ m C (HC : Strong_cond_revisable m C) :=
        MassFun_of_Ffun.Build R T 0 +%R (Strong_cond_fun HC).

      HB.instance
      Definition _ m C (HC : Strong_cond_revisable m C) :=
        AddMassFun_of_MassFun.Build R T (Strong_cond_fun HC) (Strong_cond_massfun0 HC) (Strong_cond_massfun1 HC).

      Definition Strong_cond m C (HC : Strong_cond_revisable m C) : rmassfun R T :=
        Strong_cond_fun HC.
      
      Lemma Strong_cond_axiom : @conditioning_axiom Strong_cond_revisable Strong_cond.
      Proof.
      apply conditioning_axiomE2 => m C HC B H.
      rewrite notin_focal ffunE => //=.
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
        Weak_cond_fun HC set0 == 0.
      Proof. by rewrite ffunE set0I eqxx. Qed.

      Lemma Weak_cond_massfun1 m C (HC : Weak_cond_revisable m C) :
        \sum_(A : {set T}) Weak_cond_fun HC A == 1.
      Proof.
      under eq_bigr do rewrite ffunE.
      rewrite -big_mkcond sum_div_eq1 //.
      rewrite ffunE.
      apply/eqP; apply: eq_bigl=>A.
      by rewrite setI_eq0.
      Qed.

      HB.instance
      Definition _ m C (HC : Weak_cond_revisable m C) :=
        MassFun_of_Ffun.Build R T 0 +%R (Weak_cond_fun HC).

      HB.instance
      Definition _ m C (HC : Weak_cond_revisable m C) :=
        AddMassFun_of_MassFun.Build R T (Weak_cond_fun HC) (Weak_cond_massfun0 HC) (Weak_cond_massfun1 HC).

      Definition Weak_cond m C (HC : Weak_cond_revisable m C) : rmassfun R T :=
        Weak_cond_fun HC.

      Lemma Weak_cond_axiom : @conditioning_axiom Weak_cond_revisable Weak_cond.
      Proof.
      apply conditioning_axiomE2 => m C HC B H.
      rewrite notin_focal ffunE => //=.
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





    Section ProbaConditioning.

      Notation Pr := Pinf.
      (*
      Definition Pr_revisable (p : prBpa R T) (C : {set T})
        := Pr p C != 0.
       *)
      Definition Pr_conditioning := Dempster_conditioning.

      Lemma Pr_revisableE (p : prBpa R T) (C : {set T}) :
        revisable Pr_conditioning p C == (Pr p C != 0).
      Proof.
      rewrite /Pr_conditioning/Dempster_conditioning/=/Dempster_cond_revisable.
      by rewrite -PrPinf -PrPsup.
      Qed.

      (*
      Lemma Pr_conditioningE (p : prBpa R T) C (HC : revisable Pr_conditioning p C) :
        forall w, dist (Pr_conditioning p C HC) w = (if w \in C then dist p w else 0) / Pr p C.
      Proof.
      move=>w.
      rewrite ffunE.
      rewrite /Pr_conditioning/Dempster_conditioning/=/Dempster_cond_revisable=>//=.
      rewrite ffunE (negbTE (set10F w)).
      rewrite (bigID (fun B : {set T} => #|B|==1%N))/=.
      - rewrite [E in _+E=_]big1 ?addr0.
        case (boolP (w \in C))=>H.
        + rewrite H -PrPsup -PrPinf -big_distrl/=.
          apply: mulr_rr.
          rewrite (bigD1 [set w]) ?big1/= ?addr0 ?ffunE//.
          * move=>B/andP [/andP [H1 H2] H3].
            have : B = [set w]=>[|Hcontra] ; last rewrite Hcontra eqxx// in H3.
            apply/setP=>t.
            Check in_setI.
            rewrite in_set1.
            move: (eqP H1)=>/setP=>H1'.
            move: (H1' t).
            rewrite in_set1 in_setI.
            case (boolP (t \in C))=>H4 ; rewrite ?andbT//andbF=><-.
            apply/negP=>Hcontra.
            Check set1P.
            Search set1.
            
            Check in_setI.
            Check set1P.
            destruct (cards1P H2) as [x ->].
            apply/set1P.
            Search ([set _] = [set _]).
            Search set1 setI.
            Search set1 reflect.
            Check cards1P H2.
            Search (_ == [set _]).
      Search prBpa dist.
       *)
      

      (*
      Definition Pr_conditioning_bpa_fun (p : prBpa R T) C (HC : Pr_revisable p C) :=
        fun A => match #|A|, [pick t in A] with
              | 1%N, Some t => Pr_conditioning_dist HC t
              | _, _ => 0
              end.

      Definition Pr_conditioning_bpa p C (HC : Pr_revisable p C) :=
        [ffun A : {set T} => Pr_conditioning_bpa_fun HC A].

      HB.instance Definition _ p C (HC : Pr_revisable p C) :=
        MassFun_of_Ffun.Build R T 0 +%R (Pr_conditioning_bpa HC).
      HB.about AddMassFun_of_MassFun.Build.

      Lemma Pr_conditioning_bpa0 p C (HC : Pr_revisable p C) :
        Pr_conditioning_bpa HC set0 = 0.
      Proof. by rewrite ffunE/Pr_conditioning_bpa_fun cards0. Qed.
      
      (* HERE *)

      
      
      
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

     *)
    End ProbaConditioning.
  End Conditioning.


  Section ScoringFunctions.

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
      := fun u => (*[ffun B => match minS u B with
                             | Some r => r
                             | None => 0
                             end].*)
           [ffun B => minSb 0 u B].

    Definition CEU m u_a := XEUm m (fCEU u_a).
    Notation "[ 'CEU' 'of' u 'wrt' m ]" := (CEU m u) (at level 80).

    Lemma eq_CEU : eq_xeu fCEU.
    Proof.
    move => u1 u2 B H.
    by rewrite !ffunE (minSb_eq 0 H).
    Qed.
    
    Definition fJEU (alpha : R -> R -> R) : xeu_function T
      := fun u => [ffun B =>(*match minS u_a B, maxS u_a B with
                           | Some rmin, Some rmax =>
                               let alp := alpha rmin rmax in alp * rmin + (1-alp) * rmax
                           | _, _ => 0
                           end*)
                    let rmin := minSb 0 u B in
                    let rmax := maxSb 0 u B in
                    alpha rmin rmax * rmin + (1-alpha rmin rmax) * rmax
                     ].

    Definition JEU alpha m u_a := XEUm m (fJEU alpha u_a).
    Notation "[ 'JEU' alpha 'of' u 'wrt' m ]" := (JEU alpha m u) (at level 80).

    Lemma eq_JEU alpha : eq_xeu (fJEU alpha).
    Proof.
    move => u1 u2 B H.
    by rewrite !ffunE (minSb_eq _ H) (maxSb_eq _ H).
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
    rewrite sum_fun_focal.
    under [RHS]eq_bigr do rewrite /BetP_fun sum_fun_focal_cond.
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



From BelGames Require Import fprod.

Section BelOnFFuns.

  Variable R : realFieldType.
  Variable X : finType.
  Variable T : X -> finType.

  Notation Tn := {dffun forall i : X, T i}.

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


  
  Definition ffun_of_proba (p : forall i : X, prBpa R (T i)) :
    (forall i : X, {ffun {set T i} -> R}).
  Proof. move=> i; apply p. Defined.

   Lemma proba_set1 (p : forall i : X, prBpa R (T i)) :
    forall i : X, \sum_(k in T i) p i [set k] = \sum_A p i A.
  Proof.
    move=> i.
    have x0 : T i.
    { have P_i := p i.
      have [b _] := P_i.
      have := massfun_nonempty (p i).
      rewrite -cardsT card_gt0=>HT0F.
      exact: (pick_nonemptyset HT0F). }
    set h' : {set (T i)} -> T i :=
      fun s =>
        match [pick x | x \in s] with
        | Some x => x
        | None => x0
        end.
    rewrite
      -(big_rmcond _ (I := {set (T i)}) _ (P := fun s => #|s| == 1%N)) ;
         last by move=> s Hs; exact: prbpa_card1F.
      rewrite (reindex_onto (I := {set (T i)}) (J := T i)
                          (fun j => [set j]) h'
                          (P := fun s => #|s| == 1%N) (F := fun s => p i s)) /=; last first.
    { by move=> j Hj; rewrite /h'; case/cards1P: Hj => xj ->; rewrite pick_set1E. }
    under [in RHS]eq_bigl => j do rewrite /h' pick_set1E cards1 !eqxx andbT.
    exact: eq_bigr.
  Qed.

  Definition mk_prod_prdist (p : forall i : X, prBpa R (T i)) : {ffun Tn -> R}
    := [ffun t : Tn => \prod_i dist (p i) (t i)].


  Lemma mk_prod_prdist_ge0 (p : forall i : X, prBpa R (T i)) tn : 
    mk_prod_prdist p tn >= 0.
  Proof.
  rewrite ffunE.
  apply: prodr_ge0=>i _.
  rewrite ffunE.
  exact: bpa_ge0.
  Qed.

  Lemma mk_prod_prdist_sum1 (p : forall i : X, prBpa R (T i)) : 
    \sum_tn mk_prod_prdist p tn = 1.
  Proof.
  Check big_fprod.
  under eq_bigr do rewrite ffunE.
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
  rewrite [X in _ = X](_ : 1 = \big[*%R/1%R]_(i in X) 1)%R; last by rewrite big1.
  rewrite -(bigA_distr_big_dep _ (fun i j => otagged [ffun a => p i [set a]] 0%R j)).
  apply eq_bigr => i _ /=.
  rewrite (big_tag pp)/=.
  under eq_bigr => k Hk do rewrite ffunE /ffun_of_proba.
  rewrite proba_set1.
  apply/eqP.
  exact: massfun1.
  Qed.
  
  HB.instance Definition _ p :=
    PrDist_of_Ffun.Build R Tn (mk_prod_prdist p) (mk_prod_prdist_ge0 p) (mk_prod_prdist_sum1 p).

  (*
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
  
   *)
  Definition prod_proba (p : forall i : X, prBpa R (T i)) : prBpa R Tn
    := (* proba_of_dist (mk_prod_proba_dist p witnessX). *)
    mk_prbpa (mk_prod_prdist p).

End BelOnFFuns.

Close Scope ring_scope.

