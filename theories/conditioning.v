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

From decision Require Import fintype finset setfun ssrnum order minmax.
From decision Require Import massfun capacity.



Section Conditioning.

  Variable (R : realFieldType).
  Variable (T : finType).

  Implicit Type m : rmassfun R T.
  Implicit Type mu : pointed_function R T.
  Implicit Type A B C : {set T}.

  Open Scope ring_scope.


  

  Section ConditioningDefs.
    (** A conditioning transform Bel to Bel(.|C):
          - C should verify some predicate 'revisable'
          - Bel(.|C) should be such as no focal element is included in C^c (i.e. Bel(C^c)=0 for belief function)
     **)
    (*
      Definition conditioning_axiom (revisable : massfun -> pred {set W}) (cond : forall m C, revisable m C -> massfun)
        := forall m C (HC : revisable m C), Pinf (cond m C HC) (~:C) = 0.
     *)

    Definition cond_axiom (revisable : pointed_function R T -> pred {set T})
                          (cond : forall mu C, revisable mu C -> pointed_function R T) :=
      forall mu C (HC : revisable mu C) A, mu (~:C) = 0.

    Definition mcond_axiom (revisable : rmassfun R T -> pred {set T})
                          (cond : forall m C, revisable m C -> rmassfun R T) :=
      forall m C (HC : revisable m C) A, A \subset ~:C -> cond m C HC A = 0.

    Definition eq_revisable (rev_mu  : pointed_function R T -> pred {set T})
    (rev_m : rmassfun R T -> pred {set T}) :=
      forall mu C, (rev_mu mu C) == (rev_m (moebius mu) C).

    Lemma mk_mprecond rev_mu rev_m (Heq : eq_revisable rev_mu rev_m) mu C (H : rev_mu mu C) :
      rev_m (moebius mu) C.
    Proof. by rewrite -(eqP (Heq mu C)). Qed.
    
    Structure conditioning
      := { revisable : pointed_function R T -> pred {set T} ;
           cond_val mu C :>  revisable mu C -> capacity R T ;
           cond_ax : @cond_axiom revisable cond_val }.

    Structure mconditioning
      := { mrevisable : rmassfun R T -> pred {set T} ;
           mcond_val m C :>  mrevisable m C -> rmassfun R T ;
           mcond_ax : @mcond_axiom mrevisable mcond_val }.


    Lemma mcond_axiomE (revisable : rmassfun R T -> pred {set T})
                              (cond : forall m C, revisable m C -> rmassfun R T) :
      mcond_axiom cond ->
      forall (m : rmassfun R T) (C : {set T}) (HC : revisable m C),
      forall B : {set T},
        (B \subset ~: C) -> B \notin focal (cond m C HC).
    Proof.
    move=>Hcond m C HC B HB /=.
    rewrite Bool.negb_involutive.
    by apply/eqP/Hcond.
    Qed.

    Lemma mcond_axiomE2 (revisable : rmassfun R T -> pred {set T})
                               (cond : forall m C, revisable m C -> rmassfun R T) :
      (forall (m : rmassfun R T) (C : {set T}) (HC : revisable m C),
        forall B : {set T}, (B \subset ~: C) -> B \notin focal (cond m C HC))
      -> mcond_axiom cond.
    Proof.
    move=>H m C HC A HA /=.
    have HcondE : A \notin focal (cond m C HC) -> cond m C HC A = 0
      by move=>/negbNE/eqP->.
    apply HcondE ; exact: H.
    Qed.

  End ConditioningDefs.



  Section DempsterConditioning.

    Definition Dempster_precond mu C := dual mu C != 0.
    Definition Dempster_mprecond m C := Psup m C != 0.

    Lemma Dempster_eqrev :
      eq_revisable Dempster_precond Dempster_mprecond.
    Proof.
    move=>mu C.
    by rewrite /Dempster_precond/Dempster_mprecond -PinfD Pinf_moebiusE.
    Qed.
    
    Definition Dempster_cond_fun mu C (HC : Dempster_precond mu C) :=
      dual [ffun A : {set T} => (dual mu (A :&: C)) / (dual mu C)].

    (*
    Lemma Dempster_condM  mu C (HC : Dempster_precond mu C) :
      monotonic (Dempster_cond_fun HC).
    Proof.
    apply: dual_monotonic=>A B ; rewrite ffunE [E in _<=E]ffunE.
    apply: ler_pM=>//=.
    - rewrite -(dual0 mu).
      apply: monotonic0 ; apply: dual_monotonic ; exact: capaM.
    - rewrite invr_ge0 -(dual0 mu).
      apply: monotonic0 ; apply: dual_monotonic ; exact: capaM.
    - rewrite setIUl.
      apply: dual_monotonic ; exact: capaM.
    Qed.
     *)
    
    Lemma Dempster_cond0 mu C (HC : Dempster_precond mu C) :
      Dempster_cond_fun HC set0 = 0.
    Proof. exact: dual0. Qed.

    Lemma Dempster_cond1 mu C (HC : Dempster_precond mu C) :
      Dempster_cond_fun HC setT = 1.
    Proof.
    rewrite dualT ffunE.
    - by rewrite setTI divff.
    - by rewrite set0I dual0 mul0r.
    Qed.

    Lemma Dempster_cond01 mu C (HC : Dempster_precond mu C) :
      pointed (Dempster_cond_fun HC).
    Proof. by apply/andP ; rewrite Dempster_cond0 Dempster_cond1. Qed.

    HB.instance Definition _ mu C (HC : Dempster_precond mu C) :=
      PointedFun_of_Ffun.Build R T (Dempster_cond_fun HC) (Dempster_cond01 HC).

    Definition Dempster_cond mu C (HC : Dempster_precond mu C) : pointed_function R T :=
      Dempster_cond_fun HC.



    
    Definition Dempster_mcond_fun m C (HC : Dempster_mprecond m C) :=
      [ffun A : {set T} => if A == set0 then 0
                          else \sum_(B : {set T} | (B :&: C == A)) m B / Psup m C].


    Lemma Dempster_mcond_massfun0 m C (HC : Dempster_mprecond m C) :
      Dempster_mcond_fun HC set0 = 0.
    Proof. by rewrite ffunE eqxx. Qed.

    Lemma Dempster_mcond_massfun1 m C (HC : Dempster_mprecond m C) :
      \sum_(A : {set T}) Dempster_mcond_fun HC A = 1.
    Proof.
    apply/eqP.
    under eq_bigr do rewrite ffunE -if_neg.
    rewrite -big_mkcond /=.
    under eq_bigr do rewrite sum_div.
    rewrite sum_div_eq1 ; last exact: HC.
    rewrite (eq_bigr (fun A => (\sum_(B | B :&: C == A) m B) * 1)) ;
      last by move => B ; rewrite mulr1.
    rewrite -big_setI_distrl ffunE /=.
    apply/eqP ; apply eq_big => B ; rewrite ?mulr1//.
    by rewrite setI_eq0.
    Qed.

    HB.instance
    Definition AddMassFun_of_DempsterMCond m C (HC : Dempster_mprecond m C) :=
      AddMassFun_of_Ffun.Build R T (Dempster_mcond_fun HC) (Dempster_mcond_massfun0 HC) (Dempster_mcond_massfun1 HC).

    Definition Dempster_mcond m C (HC : Dempster_mprecond m C) : rmassfun R T :=
      Dempster_mcond_fun HC.

    Lemma Dempster_mcond_ge0 (m : bpa R T) C (HC : Dempster_mprecond m C) A :
      Dempster_mcond HC A >= 0.
    Proof.
    rewrite ffunE/=.
    case: ifP => _//.
    apply: sumr_ge0 => B HB.
    apply divr_ge0 ; first by rewrite bpa_ge0.
    Check Pinf_ge0.
    exact: Psup_ge0.
    Qed.

    HB.instance
    Definition _ (m : bpa R T) C (HC : Dempster_mprecond m C) :=
      Bpa_of_AddMassFun.Build R T (Dempster_mcond HC) (Dempster_mcond_ge0 HC).
    
    Lemma Dempster_mcond_sumE m C (HC : Dempster_mprecond m C) f :
      \sum_(B in focal (Dempster_mcond HC))
      Dempster_mcond HC B * f B
      =
        (\sum_(A in focal m)
         if A :&: C != set0
         then m A * f (A :&: C)
         else 0) / Psup m C.
    Proof.
    rewrite -[in RHS]big_mkcondr sum_fun_focal_cond.
    Opaque Dempster_mcond.
    rewrite (big_setI_distrl (fun b => b != set0)) sum_fun_focal (bigD1 set0) //=.
    rewrite massfun0 mul0r add0r.
    under [in RHS]eq_bigr do rewrite mulrC.
    rewrite big_distrl /=.
    under [in RHS]eq_bigr do rewrite -mulrA big_distrl mulrC /=.
    apply eq_big => // B HB.
    Transparent Dempster_mcond.
    by rewrite ffunE (negbTE HB).
    Qed.

    Lemma Dempster_mcond_axiom : @mcond_axiom Dempster_mprecond Dempster_mcond.
    Proof.
    apply mcond_axiomE2 => m C HC B HB.
    rewrite notin_focal ffunE => //=.
    case (boolP (B == set0)) => // /set0Pn [w Hw].
    rewrite big_pred0 => // A.
    case (boolP (A :&: C == B)) => //HA.
    rewrite -(eqP HA) in HB ; rewrite -(eqP HA) in Hw.
    contradiction (subsetF (subsetIr A C) HB Hw).
    Qed.

    Definition Dempster_mconditioning : mconditioning
      := {| mcond_val := Dempster_mcond ;
           mcond_ax := Dempster_mcond_axiom |}.



  End DempsterConditioning.

  Section FHConditioning.

    Definition FH_precondisable m C := Pinf m C != 0.

    Definition FH_Pinf m C :=
      [ffun A : {set T} => Pinf m (A :&: C) / ( Pinf m (A :&: C) + Psup m ((~:A) :&: C))].

    Lemma FH_PinfT m C :
      FH_precondisable m C
      -> FH_Pinf m C setT = 1.
    Proof.
    rewrite /FH_Pinf=>H.
    by rewrite ffunE setTI setCT set0I (pointed0 (Psup01 m)) addr0 divff.
    Qed.

    Definition FH_cond_fun (m : rmassfun R T) (C : {set T}) (HC : FH_precondisable m C) :=
      [ffun A : {set T} => moebius (FH_Pinf m C) A].


    Lemma FH_cond_massfun0 (m : rmassfun R T) (C : {set T}) (HC : FH_precondisable m C) :
      FH_cond_fun HC set0 = 0.
    Proof. by rewrite ffunE moebius0 ffunE set0I (pointed0 (Pinf01 m)) mul0r. Qed.
    
    Lemma FH_cond_massfun1 (m : rmassfun R T) (C : {set T}) (HC : FH_precondisable m C) :
      \sum_(A : {set T}) FH_cond_fun HC A = 1.
    Proof.
    - under eq_bigr do rewrite ffunE.
                       have :=  moebiusE (FH_Pinf m C) setT.
                       rewrite FH_PinfT=>//->.
                       by apply: eq_big=>/=[B|//] ; rewrite subsetT.
    Qed.

    HB.instance
    Definition _ m C (HC : FH_precondisable m C) :=
      AddMassFun_of_Ffun.Build R T (FH_cond_fun HC) (FH_cond_massfun0 HC) (FH_cond_massfun1 HC).
    
    Definition FH_cond m C (HC : FH_precondisable m C) : rmassfun R T :=
      FH_cond_fun HC.
    
    Lemma FH_cond_axiom : @mcond_axiom FH_precondisable FH_cond.
    Proof.
    rewrite /mcond_axiom/=/FH_cond.
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

    Definition FH_conditioning : mconditioning
      := {| mcond_val := FH_cond ;
           mcond_ax := FH_cond_axiom |}.

  End FHConditioning.



  Section StrongConditioning.


    Definition Strong_precondisable (m : rmassfun R T) := fun C : {set T} => Pinf m C != 0.

    
    Definition Strong_cond_fun (m : rmassfun R T) (C : {set T}) (HC : Strong_precondisable m C) :=
      [ffun A : {set T} => if (A != set0) && (A \subset C)
                           then m A / Pinf m C else 0].

    Lemma Strong_cond_massfun0 m C (HC : Strong_precondisable m C) :
      Strong_cond_fun HC set0 = 0.
    Proof. by rewrite ffunE eqxx. Qed.

    Lemma Strong_cond_massfun1 m C (HC : Strong_precondisable m C) :
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
    Definition AddMassFun_of_StrongCond m C (HC : Strong_precondisable m C) :=
      AddMassFun_of_Ffun.Build R T (Strong_cond_fun HC) (Strong_cond_massfun0 HC) (Strong_cond_massfun1 HC).

    Definition Strong_cond m C (HC : Strong_precondisable m C) : rmassfun R T :=
      Strong_cond_fun HC.
    
    Lemma Strong_cond_axiom : @mcond_axiom Strong_precondisable Strong_cond.
    Proof.
    apply mcond_axiomE2 => m C HC B H.
    rewrite notin_focal ffunE => //=.
    case (boolP (B == set0)) => //= /set0Pn [t Ht].
    case (boolP (B \subset C)) => //= HB.
    contradiction (subsetF HB H Ht).
    Qed.

    Definition Strong_conditioning : mconditioning
      := {| mcond_val := Strong_cond ;
           mcond_ax := Strong_cond_axiom |}.

  End StrongConditioning.


  Section WeakConditioning.

    Definition Weak_precondisable (m : rmassfun R T) := fun C : {set T} => Psup m C != 0.
    
    Definition Weak_cond_fun (m : rmassfun R T) (C : {set T}) (HC : Weak_precondisable m C) :=
      [ffun A : {set T} => if A :&: C != set0 then m A / Psup m C else 0].

    Lemma Weak_cond_massfun0 m C (HC : Weak_precondisable m C) :
      Weak_cond_fun HC set0 = 0.
    Proof. by rewrite ffunE set0I eqxx. Qed.

    Lemma Weak_cond_massfun1 m C (HC : Weak_precondisable m C) :
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
    Definition AddMassFun_of_WeakCond m C (HC : Weak_precondisable m C) :=
      AddMassFun_of_Ffun.Build R T (Weak_cond_fun HC) (Weak_cond_massfun0 HC) (Weak_cond_massfun1 HC).

    Definition Weak_cond m C (HC : Weak_precondisable m C) : rmassfun R T :=
      Weak_cond_fun HC.

    Lemma Weak_cond_axiom : @mcond_axiom Weak_precondisable Weak_cond.
    Proof.
    apply mcond_axiomE2 => m C HC B H.
    rewrite notin_focal ffunE => //=.
    case (boolP (B :&: C == set0)) => //= /set0Pn [w Hw].
    move: Hw ; rewrite in_setI => /andP [Hw1 Hw2].
    move: H ; rewrite subsetE => /pred0P H.
    have := H w => /= ; rewrite Hw1 andbT => /negP/negP.
    by rewrite in_setC Hw2.
    Qed.
    
    Definition Weak_conditioning : mconditioning
      := {| mcond_val := Weak_cond ;
           mcond_ax := Weak_cond_axiom |}.

  End WeakConditioning.


End Conditioning.




Section BelOnFFuns.

  Variable R : realFieldType.
  Variable X : finType.
  Variable T : X -> finType.

  Notation Tn := [finType of {dffun forall i : X, T i}].

  (* NOTE :: conditioning event "given t i == ti" *)
  Definition event_ti i (ti : T i) := [set t : Tn | t i == ti].

  Lemma negb_focal_revise (m : rmassfun R Tn) (cond : mconditioning R Tn) i ti (H : mrevisable cond m (event_ti ti)) :
    forall A : {set Tn},
    (forall t, t \in A -> ti != t i) -> A \notin focal (cond m (event_ti ti) H).
  Proof.
  move => A HA.
  apply mcond_axiomE ; first exact: mcond_ax.
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

