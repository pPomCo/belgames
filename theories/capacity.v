From Coq Require Import Program.Wf.
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing GRing.Theory.
Import Num.Theory.

From decision Require Import fintype finset minmax setfun massfun.

Import Order Order.POrderTheory Order.TotalTheory.

(** Capacity structures with Hierarchical Builder *)
From HB Require Import structures.


Implicit Type R : numDomainType.
Implicit Type T : finType.
Local Open Scope ring_scope.

(** Pointed Function *)
Check "Pointed Function".
HB.mixin
Record PointedFun_of_Ffun R T (mu : {ffun {set T} -> R}) :=
  { capa01 : pointed mu }.

#[short(type="pointed_function")]
HB.structure
Definition PointedFun R T := {mu of PointedFun_of_Ffun R T mu}.

(** Belief function from Bpa *)
HB.instance Definition _ R T (m : rmassfun R T) :=
  PointedFun_of_Ffun.Build R T (Pinf m) (Pinf01 m).

Section PointedFunTheory.
  
  Variable R : numDomainType.
  Variable T : finType.
  Variable mu : pointed_function R T.
  Implicit Type A B C : {set T}.
  
  (** Massfun of capacity *)
  Lemma capa_massfun0 : moebius mu set0 = 0.
  Proof. by rewrite moebius0 pointed0//capa01. Qed.
  Lemma capa_massfun1 : \sum_(A : {set T}) moebius mu A = 1.
  Proof.
  rewrite -(pointedT (capa01 (s:=mu))) moebiusE.
  apply: eq_bigl=>/=A ; by rewrite subsetT.
  Qed.

  HB.instance
  Definition _ := MassFun_of_Ffun.Build R T 0 +%R (moebius mu).

  HB.instance
  Definition _ := AddMassFun_of_MassFun.Build R T (moebius mu) capa_massfun0 capa_massfun1.

  Lemma Pinf_moebiusE :
    Pinf (moebius mu : rmassfun R T) = mu.
  Proof. by apply/ffunP=>/=A ; rewrite ffunE moebiusE/=. Qed.

  
  (** Dual pointed function *)
  Lemma dual_capa01 : pointed (setfun.dual mu).
  Proof. apply: dual_pointed ; exact: capa01. Qed.

  HB.instance
  Definition _ := PointedFun_of_Ffun.Build R T (setfun.dual mu) dual_capa01.

End PointedFunTheory.



(** Numerical Capacities *)
Check "Capacity".
HB.mixin
Record Capacity_of_PointedFun R T (mu : {ffun {set T} -> R}) of PointedFun_of_Ffun R T mu :=
  { capaM : monotonic mu }.

#[short(type="capacity")]
HB.structure
Definition Capacity R T := {mu of Capacity_of_PointedFun R T mu & PointedFun_of_Ffun R T mu}.

Section CapacityTheory.

  Section OnNumDomain.
    
    Variable R : numDomainType.
    Variable T : finType.
    Variable mu : capacity R T.
    Implicit Type A B C : {set T}.


    (** Dual capacities *)
    Lemma dual_capaM : monotonic (setfun.dual mu).
    Proof. apply: dual_monotonic ; exact: capaM. Qed.

    HB.instance
    Definition _ := Capacity_of_PointedFun.Build R T (setfun.dual mu) dual_capaM.

  End OnNumDomain.

  Section OnRealDomain.
    Variable R : realDomainType.
    Variable T : finType.
    Variable mu : capacity R T.
    Implicit Type A B C : {set T}.

    Lemma qmassfun_trivial :
      is_mass_function 0 max mu mu.
    Proof.
    move=>A.
    apply/eqP ; rewrite eq_le ; apply/andP ; split.
    - exact: le_bigmax_cond.
    - apply: bigmax_le=>[|/=B HB] ; last exact: (monotonicS capaM HB).
      rewrite -(pointed0 (capa01 (s:=mu))).
      exact: (monotonic0 capaM).
    Qed.

    Check qmoebius.
    Check qmoebius mu.


    (** qmoebius *)

    HB.instance Definition _ :=
      MassFun_of_Ffun.Build R T 0 max (qmoebius mu).

    Lemma capa_qmoebius0 : qmoebius mu set0 = 0.
    Proof. by rewrite qmoebius0 (pointed0 capa01). Qed.
    Lemma capa_qmoebius1 : \big[max/0]_(A : {set T}) qmoebius mu A = 1.
    Proof.
    have := qmoebiusE (capaM (s:=mu)) setT.
    under eq_bigl do rewrite subsetT.
    rewrite (pointed0 capa01) ; move=><-.
    exact: (pointedT capa01).
    Qed.
    HB.about MaxMassFun_of_MassFun.Build.
    
    HB.instance Definition _ :=
      MaxMassFun_of_MassFun.Build R T (qmoebius mu) capa_qmoebius0 capa_qmoebius1.

  End OnRealDomain.

End CapacityTheory.


(** 2-monotone capacities *)
Check "Capa2inf".
HB.mixin
Record Capa2inf_of_Capacity R T mu of Capacity_of_PointedFun R T mu & PointedFun_of_Ffun R T mu :=
  { capa2mon : is_2monotone mu }.
#[short(type="capa2inf")]
HB.structure
Definition Capa2inf R T := {mu of Capa2inf_of_Capacity R T mu
                            & Capacity_of_PointedFun R T mu
                            & PointedFun_of_Ffun R T mu}.


(** 2-alternating capacities *)
Check "Capa2sup".
HB.mixin
Record Capa2sup_of_Capacity R T mu of Capacity_of_PointedFun R T mu & PointedFun_of_Ffun R T mu :=
  { capa2alt : is_2alternating mu }.
#[short(type="capa2sup")]
HB.structure
Definition Capa2sup R T := {mu of Capa2sup_of_Capacity R T mu 
                            & Capacity_of_PointedFun R T mu
                            & PointedFun_of_Ffun R T mu}.

Section Capa2Theory.
  
  Variable R : realDomainType.
  Variable T : finType.
  Variable Pinf : capa2inf R T.
  Variable Psup : capa2sup R T.
  Implicit Type A B C : {set T}.

  (** Dual 2-monotone and 2-alternating capacities *)
  Lemma dual2alt : is_2alternating (setfun.dual Pinf).
  Proof. by have := (capa2mon (s:=Pinf)) ; rewrite dual_2alternating. Qed.
  Lemma dual2mon : is_2monotone (setfun.dual Psup).
  Proof. by have := (capa2alt (s:=Psup)) ; rewrite -dual_2monotone. Qed.

  HB.instance
  Definition _ := Capa2sup_of_Capacity.Build R T (setfun.dual Pinf) dual2alt.

  HB.instance
  Definition _ := Capa2inf_of_Capacity.Build R T (setfun.dual Psup) dual2mon.

End Capa2Theory.
(*
Check fun (mu : capa2inf _ _) => (moebius mu : massfun _ _).
Check fun (mu : capa2inf _ _) => (setfun.dual mu : capa2sup _ _).
Check fun (mu : capa2sup _ _) => (setfun.dual mu : capa2inf _ _).
*)

(** Probability intervals distributions *)
(*
Definition reachable (R : realDomainType) T (p : T -> R * R) :=
  [forall t, [&& (p t).2 + \sum_(t' | t' != t) (p t').1 <= 1
         &  (p t).1 + \sum_(t' | t' != t) (p t').2 >= 1 ]].
HB.mixin
Record PrIntvDist_of_Ffun (R : realDomainType) T (p : {ffun T -> R * R}) :=
  { printvdist_0le1 : forall t : T, 0 <= (p t).1 ;
    printvdist_1le2 : forall t : T, (p t).1 <= (p t).2 ;
    printvdist1 : \sum_t (p t).1 <= 1 <= \sum_t (p t).2 ;
    printvdistR : reachable p ;
  }.
#[short(type="printvdist")]
HB.structure
Definition PrintvDist (R : realDomainType) T := {mu of PrIntvDist_of_Ffun R T mu}.

HB.mixin
Record ProbaIntervalsInf_of_Ffun (R : realDomainType) T (mu : {ffun {set T} -> R}) :=
  { printv_dist :  printvdist R T ;
    printv_distE : forall A, mu A = min (\sum_(t in A) (printv_dist t).1) (1 - \sum_(t in ~:A) (printv_dist t).2) ;
    }.
HB.builders
Context (R : realDomainType) T mu of ProbaIntervalsInf_of_Ffun R T mu.
Lemma capaM : monotonic mu.
Proof.
move=>A B.
- have HAleAB : \sum_(t in A) (printv_dist t).1 <= \sum_(t in (A :|: B)) (printv_dist t).1.
  rewrite [E in _<=E](bigID (fun t => t \in A)) [E in _<=E+_](eq_bigl (fun t => t \in A))=>/=[|t] ;
    last rewrite !inE ; last case (t \in A)=>// ; last by rewrite andbF.
  rewrite lerDl.
  apply: sumr_ge0=>t _.
  exact: printvdist_0le1.
  rewrite !printv_distE !minEle.
- case (boolP (\sum_(t in A) (printv_dist t).1 <= 1 - \sum_(t in ~: A) (printv_dist t).2))=>HA ;
    case (boolP (\sum_(t in (A :|: B)) (printv_dist t).1 <= 1 - \sum_(t in ~: (A :|: B)) (printv_dist t).2))=>HAB//.
  + under [E in _<=(1-E)]eq_bigl do rewrite setCU.
    admit.
  + rewrite -TotalTheory.ltNge in HA.
    apply: ltW.
    apply ( lt_le_trans (lt_le_trans HA HAleAB)).
    by rewrite le_eqVlt eqxx orTb.
  + rewrite -TotalTheory.ltNge in HA.
    rewrite -TotalTheory.ltNge in HAB.
    apply: lerB=>//.
    under eq_bigl do rewrite setCU.
    rewrite [E in _<=E](bigID (fun t => t \in ~:B)).
    rewrite [E in _<=E+_](eq_bigl (fun t => t \in ~:A :&: ~:B))=>//=.
    * rewrite lerDl.
      apply: sumr_ge0=>t _.
      apply (le_trans (printvdist_0le1 (s:=printv_dist) t)).
      exact: printvdist_1le2.
Admitted.
*)


(** Belief functions *)
Check "BeliefFunction".
HB.mixin
Record BeliefFunction_of_Capacity R T (mu : {ffun {set T} -> R}) of Capacity_of_PointedFun R T mu & PointedFun_of_Ffun R T mu :=
  { massfun_ge0 : mpositive mu }.
HB.factory
Record BeliefFunction_of_Ffun R T (mu : {ffun {set T} -> R}) :=
  { capa01 : pointed mu ;
    massfun_ge0 : mpositive mu }.

HB.builders
Context R T mu of BeliefFunction_of_Ffun R T mu.
HB.instance Definition _ := PointedFun_of_Ffun.Build R T mu capa01.
HB.instance Definition _ := Capacity_of_PointedFun.Build R T mu (mpositive_monotonic massfun_ge0).
HB.instance Definition _ := Capa2inf_of_Capacity.Build R T mu (mpositive_2monotone massfun_ge0).
HB.instance Definition _ := BeliefFunction_of_Capacity.Build R T mu massfun_ge0.
HB.end.

#[short(type="belief_function")]
HB.structure
Definition BeliefFunction R T := {mu of BeliefFunction_of_Ffun R T mu}.

(** Belief function from Bpa *)
HB.instance Definition _ R T (m : bpa R T) :=
  BeliefFunction_of_Ffun.Build R T (Pinf m) (Pinf01 m) (massfun_mpositive m).



(** Plausibility measures *)
Check "Plausibility".
HB.mixin
Record Plausibility_of_Capacity R T (mu : {ffun {set T} -> R}) of Capacity_of_PointedFun R T mu & PointedFun_of_Ffun R T mu :=
  { massfunD_ge0 : mpositive (setfun.dual mu) }.
HB.factory
Record Plausibility_of_Ffun R T (mu : {ffun {set T} -> R}) :=
  { capa01 : pointed mu ;
    massfunD_ge0 : mpositive (setfun.dual mu) }.

HB.builders
Context R T mu of Plausibility_of_Ffun R T mu.

Lemma capaM : monotonic mu.
Proof.
have [/eqP H0 _] := andP capa01.
rewrite -(dualK H0).
apply: dual_monotonic.
apply: mpositive_monotonic.
exact: massfunD_ge0.
Qed.

Lemma capa2alt : is_2alternating mu.
Proof. rewrite dual_2monotone ; apply: mpositive_2monotone ; exact: massfunD_ge0. Qed.

HB.instance Definition _ := PointedFun_of_Ffun.Build R T mu capa01.
HB.instance Definition _ := Capacity_of_PointedFun.Build R T mu capaM.
HB.instance Definition _ := Capa2sup_of_Capacity.Build R T mu (capa2alt).
HB.instance Definition _ := Plausibility_of_Capacity.Build R T mu massfunD_ge0.
HB.end.

#[short(type="plausibility")]
HB.structure
Definition Plausibility R T := {mu of Plausibility_of_Ffun R T mu}.

(** Plausibility from Bpa *)
HB.instance Definition _ R T (m : bpa R T) :=
  Plausibility_of_Ffun.Build R T (Psup m) (Psup01 m) (massfun_mpositiveD m).



Section BeliefFunctionTheory.
  
  Variable R : numDomainType.
  Variable T : finType.
  Variable Bel : belief_function R T.
  Variable Pl : plausibility R T.
  Implicit Type A B C : {set T}.

  (** Dual belief functions and plausibility measures *)
  Lemma dual_massfunD_ge0 : mpositive (setfun.dual (setfun.dual Bel)).
  Proof. rewrite dualK. exact: massfun_ge0. exact: pointed0 capa01. Qed.

  HB.instance Definition _ :=
    Plausibility_of_Capacity.Build R T (setfun.dual Bel) dual_massfunD_ge0.
  HB.instance Definition _ :=
    BeliefFunction_of_Capacity.Build R T (setfun.dual Pl) massfunD_ge0.


  (** Belief function -> bpa **)
  HB.instance Definition _ :=
    Bpa_of_AddMassFun.Build R T (moebius Bel) massfun_ge0.

End BeliefFunctionTheory.


(** Probability measures *)
Check "Probability".
HB.mixin
Record Proba_of_BeliefFunction R T (mu : {ffun {set T} -> R}) of BeliefFunction_of_Ffun R T mu :=
  { massfun_card1 : forall A, moebius mu A != 0%R -> #|A| = 1%N }.

HB.mixin
Record Proba_of_Plausibility R T (mu : {ffun {set T} -> R}) of Plausibility_of_Ffun R T mu :=
  { massfunD_card1 : forall A, moebius (setfun.dual mu) A != 0%R -> #|A| = 1%N }.

HB.mixin
Record Proba_of_Capacity R T (mu : {ffun {set T} -> R}) of Capacity_of_PointedFun R T mu & PointedFun_of_Ffun R T mu :=
  { capaAdd : additiveUI mu }.


HB.builders
Context R T mu of Proba_of_Capacity R T mu.

Lemma pr_distE : forall A, mu A = \sum_(t in A) mu [set t].
Proof. exact: additiveUIE capaAdd (pointed0 capa01). Qed.

Lemma pr_moebiusE : moebius mu = [ffun A : {set T} => if #|A|==1%N then mu A else (0%R:R)].
Proof. exact: additiveUI_moebius capaAdd (pointed0 capa01). Qed.

Lemma pr_dualE : setfun.dual mu = mu.
Proof. exact: additiveUI_dual capaAdd (pointed0 capa01). Qed.

Lemma massfun_ge0 : mpositive mu.
Proof. exact: additiveUI_mpositive capaAdd (pointed0 capa01) capaM. Qed.

Lemma massfun_card1 A : moebius mu A != 0%R -> #|A| = 1%N.
Proof. exact: additiveUI_moebius1 capaAdd (pointed0 capa01) A. Qed.

Lemma massfunD_ge0 : mpositive (setfun.dual mu).
Proof. by rewrite pr_dualE ; exact: massfun_ge0. Qed.

Lemma massfunD_card1 A : moebius (setfun.dual mu) A != 0%R -> #|A| = 1%N.
Proof. by rewrite pr_dualE ; exact: massfun_card1. Qed.

Lemma capa2alt : is_2alternating mu.
Proof.
rewrite -pr_dualE -dual_2alternating.
exact: mpositive_2monotone massfun_ge0.
Qed.


HB.instance Definition _ := Capa2inf_of_Capacity.Build R T mu (mpositive_2monotone massfun_ge0).
HB.instance Definition _ := Capa2sup_of_Capacity.Build R T mu capa2alt.
HB.instance Definition _ := BeliefFunction_of_Capacity.Build R T mu massfun_ge0.
HB.instance Definition _ := Plausibility_of_Capacity.Build R T mu massfunD_ge0.
HB.instance Definition _ := Proba_of_BeliefFunction.Build R T mu massfun_card1.
HB.instance Definition _ := Proba_of_Plausibility.Build R T mu massfunD_card1.

HB.end.

#[short(type="probability")]
HB.structure Definition Probability R T := {mu of Proba_of_Capacity R T mu
                                            & Capacity_of_PointedFun R T mu
                                            & PointedFun_of_Ffun R T mu}.


Section ProbabilityTheory.

  Variable (R : numDomainType) (T : finType).

  Section LetPrBeAProbability.

    Variable (Pr : probability R T).

    Lemma pr_distE : forall A, Pr A = \sum_(t in A) Pr [set t].
    Proof. exact: additiveUIE capaAdd (pointed0 capa01). Qed.

    Lemma pr_moebiusE : moebius Pr = [ffun A : {set T} => if #|A|==1%N then Pr A else (0%R:R)].
    Proof. exact: additiveUI_moebius capaAdd (pointed0 capa01). Qed.

    Lemma pr_dualE : setfun.dual Pr = Pr.
    Proof. exact: additiveUI_dual capaAdd (pointed0 capa01). Qed.

    

    (** Dual probability measures *)
    (*
    Lemma pr_dual_massfun_ge0 : mpositive (setfun.dual Pr).
    Proof. by rewrite pr_dualE ; exact: massfun_ge0. Qed.
    Lemma pr_dual_massfunD_ge0 : mpositive (setfun.dual (setfun.dual Pr)).
    Proof. by rewrite dualK ?(pointed0 capa01)// ; exact: massfun_ge0. Qed.
    Lemma pr_dual_massfunD_card1 A :
      moebius (setfun.dual (setfun.dual Pr)) A != 0 -> #|A| = 1%N.
    Proof. by rewrite dualK ?(pointed0 capa01)// ; exact: massfun_card1. Qed.
     *)
    Lemma dual_capaAdd : additiveUI (setfun.dual Pr).
    Proof. by rewrite pr_dualE ; exact: capaAdd. Qed.

    HB.instance Definition _ :=
      Proba_of_Capacity.Build R T (setfun.dual Pr) dual_capaAdd.

    (** Probability measure <-> probability bpa *)
    Lemma proba_moebius_card1 :
      forall A, moebius Pr A != 0 -> #|A|==1%N.
    Proof. by move=>/=A H ; apply/eqP ; exact: (massfun_card1 (s:=Pr)). Qed.

    HB.instance Definition _ := PrBpa_of_Bpa.Build R T (moebius Pr) proba_moebius_card1.
    

    (** Probability measure <-> probability distribution *)
    Notation p := [ffun t => Pr [set t]].

    Lemma proba_prdist_ge0 t : p t >= 0.
    Proof.
    rewrite ffunE -(pointed0 (mu:=Pr) capa01).
    exact: (monotonic0 capaM).
    Qed.

    Lemma proba_prdist_sum1 : \sum_t p t = 1.
    Proof.
    under eq_bigr do rewrite ffunE.
    rewrite -finset.big_card1 -(pointedT (mu:=Pr) capa01) moebiusE big_mkcond [in RHS]big_mkcond/=.
    apply/eq_bigr=>A _.
    by rewrite subsetT pr_moebiusE ?ffunE//.
    Qed.

    HB.instance
    Definition _ :=
      PrDist_of_Ffun.Build R T _ proba_prdist_ge0 proba_prdist_sum1.

    Definition prdist_of_probability : prdist R T := p.

  End LetPrBeAProbability.

  Lemma prBpa_moebius_card1 (m : prBpa R T) A :
    moebius (Pinf m) A != 0 -> #|A| = 1%N.
  Proof. by rewrite -massfun_moebius=>HA ; apply/eqP ; exact: (prbpa_card1 (s:=m)). Qed.  
  HB.instance Definition _ (p : prBpa R T) :=
    Proba_of_BeliefFunction.Build R T (Pinf p) (@prBpa_moebius_card1 p).
  

  HB.instance Definition _ (p : prdist R T) :=
    PointedFun_of_Ffun.Build R T [ffun A : {set T} => \sum_(t in A) p t] (prdist_capa01 p).
  HB.instance Definition _ (p : prdist R T) :=
    Capacity_of_PointedFun.Build R T [ffun A : {set T} => \sum_(t in A) p t] (prdist_capaM p).
  HB.instance Definition _ (p : prdist R T) :=
    Proba_of_Capacity.Build R T [ffun A : {set T} => \sum_(t in A) p t] (prdist_capaAdd p).

  Definition probability_of_prdist (p : prdist R T) : probability R T :=
    [ffun A : {set T} => \sum_(t in A) p t].

  (*
  Lemma probability_of_prdistK :
    cancel probability_of_prdist prdist_of_probability.
   *)

End ProbabilityTheory.







(** Possibility measure *)
Check "Possibility".

HB.mixin Record Possibility_of_Ffun (R : realDomainType) T (mu : {ffun {set T} -> R}) :=
  { poss_pidist : pidist R T ;
    poss_pidistE : mu = [ffun A : {set T} => \big[Order.max/0%R]_(t in A) poss_pidist t] }.

HB.builders Context (R : realDomainType) T mu of Possibility_of_Ffun R T mu.

Lemma capaM : monotonic mu.
Proof. by rewrite poss_pidistE ; exact: pidist_PiM. Qed.

Lemma capa01 : pointed mu.
Proof. by rewrite poss_pidistE ; exact: pidist_Pi01. Qed.

Lemma capa2alt : is_2alternating mu.
Proof. by rewrite poss_pidistE ; exact: pidist_Pi2alt. Qed.

HB.instance Definition _ := PointedFun_of_Ffun.Build R T mu capa01.
HB.instance Definition _ := Capacity_of_PointedFun.Build R T mu capaM.
HB.instance Definition _ := Capa2sup_of_Capacity.Build R T mu capa2alt.

HB.end.

#[short(type="possibility")]
HB.structure Definition Possibility (R : realDomainType) T := {mu of Possibility_of_Ffun R T mu}.



(** Necessity measures *)
Check "Necessity".

HB.mixin Record Necessity_of_Ffun (R : realDomainType) T (mu : {ffun {set T} -> R}) :=
  { nec_pidist : pidist R T ;
    nec_pidistE : mu = [ffun A : {set T} => 1 - \big[Order.max/0%R]_(t in ~:A) nec_pidist t] }.

HB.builders Context (R : realDomainType) T mu of Necessity_of_Ffun R T mu.

Lemma capaM : monotonic mu.
Proof. by rewrite nec_pidistE ; exact: pidist_NM. Qed.

Lemma capa01 : pointed mu.
Proof. by rewrite nec_pidistE ; exact: pidist_N01. Qed.

Lemma capa2mon : is_2monotone mu.
Proof. by rewrite nec_pidistE ; exact: pidist_N2mon. Qed.

HB.instance Definition _ := PointedFun_of_Ffun.Build R T mu capa01.
HB.instance Definition _ := Capacity_of_PointedFun.Build R T mu capaM.
HB.instance Definition _ := Capa2inf_of_Capacity.Build R T mu capa2mon.

HB.end.

#[short(type="necessity")]
HB.structure Definition Necessity (R : realDomainType) T := {mu of Necessity_of_Ffun R T mu}.






(** Categorical capacities *)
Check "Categorical".

HB.mixin
Record Categorical_of_Ffun R  T (mu : {ffun {set T} -> R}) :=
  { categorical_dist : T -> bool ;
    categorical_distE : exists t, categorical_dist t ;
    categoricalE : forall A, mu A = if [set t | categorical_dist t] \subset A then 1 else 0}.

(*
HB.mixin
Record Categorical_of_Necessity (R : realDomainType)  T (mu : {ffun {set T} -> R})
  of Necessity_of_Ffun R T mu :=
  { categorical_nec_pidistE : forall t : T, [|| nec_pidist (s:=mu) t == 0 | nec_pidist (s:=mu) t == 1] }.
 *)

HB.builders
Context R T mu of Categorical_of_Ffun R T mu.

Lemma capa01 : pointed mu.
apply/andP ; split ; rewrite categoricalE.
- rewrite subset0.
  have [t Ht] := categorical_distE.
  have H0 : [set t | categorical_dist t] != set0
    by apply/set0Pn ; exists t ; rewrite !inE.
  by rewrite (negbTE H0).
- by rewrite subsetT.
Qed.

Lemma cat_massfunE :
  is_mass_function 0 +%R mu [ffun A : {set T} => if A == [set t | categorical_dist t] then 1 else 0].
Proof.
move=>/=A.
case (boolP ([set t | categorical_dist t] \subset A))=>H.
- rewrite (bigD1 [set t | categorical_dist t])//=.
  rewrite ffunE eqxx categoricalE H big1 ?addr0=>//= B/andP[_ HB].
  by rewrite ffunE (negbTE HB).
- rewrite categoricalE (negbTE H) big1=>//B HB.
  rewrite ffunE.
  case (boolP (B == [set t | categorical_dist t]))=>//=Hcontra.
  rewrite (eqP Hcontra) in HB.
  by rewrite HB in H.
Qed.

Lemma massfun_ge0 : mpositive mu.
Proof.
move=>A.
rewrite -(moebius_unique cat_massfunE) ffunE.
by case (A == [set t | categorical_dist t]).
Qed.

(*
HB.instance
Definition _ := Capacity_of_Ffun.Build R T mu (mpositive_monotonic massfun_ge0) capa01.

HB.instance
Definition _ := Capa2inf_of_Capacity.Build R T mu (mpositive_2monotone massfun_ge0).

HB.instance
Definition _ := BeliefFunction_of_Capacity.Build R T mu massfun_ge0.
 *)

HB.instance Definition _ := BeliefFunction_of_Ffun.Build R T mu capa01 massfun_ge0.

(*
Definition cat_pidist :=
  [ffun t : T => if categorical_dist t then (1:R) else (0:R)].
Lemma cat_pidist_in01 :
  [forall t, 0 <= cat_pidist t <= (1:R)].
Proof.
apply/forallP=>t ; rewrite ffunE.
by case (categorical_dist t) ; apply/andP.
Qed.

Lemma cat_pidist_norm :
  [exists t,  cat_pidist t == (1:R)].
apply/existsP.
have [t Ht] := categorical_distE.
exists t.
by rewrite ffunE Ht.
Qed.
HB.instance Definition _  :=
  PiDist_of_Ffun.Build R T _ (cat_pidist_in01) (cat_pidist_norm).

Lemma cat_nec_pidistE :
  forall A : {set T}, mu A = 1 - \big[Num.max/0]_(t in ~:A) cat_pidist t.
Proof.
move=>/=A.
rewrite categoricalE.
have [t Ht] := categorical_distE.
case (boolP ([set t | categorical_dist t] \subset A))=>H.
- have H0 : \big[Num.max/0]_(t in ~: A) cat_pidist t = 0.
  apply/eqP ; rewrite eq_le ; apply/andP ; split.
  + apply: bigmax_le=>//=t'.
    have :=subsetP H t'.
    rewrite !inE=>HtA HtAC.
    have HcF : ~~(categorical_dist t')
      by apply/negP=>Hcontra ; rewrite (HtA Hcontra) in HtAC.
    by rewrite ffunE (negbTE HcF).
  + by rewrite bigmax_idl le_maxr lexx orTb.
  + by rewrite H0 subr0.
- have H1 : \big[Num.max/0]_(t in ~: A) cat_pidist t = 1.
  apply/eqP ; rewrite eq_le ; apply/andP ; split.
  + apply: bigmax_le=>//=t' _.
    rewrite ffunE.
    by case (categorical_dist t').
  + have [t' Ht'1 Ht'2] := subsetPn H.
    have : cat_pidist t' = 1
      by rewrite inE in Ht'1 ; rewrite ffunE Ht'1.
    move=><-.
    apply: le_bigmax_cond.
    by rewrite !inE.
  + by rewrite H1 subrr.
Qed.

HB.instance Definition _  :=
  Necessity_of_Ffun.Build R T mu cat_nec_pidistE.
*)
(*
Lemma categorical_nec_pidistE :
  forall t : T, [|| cat_pidist t == 0 | cat_pidist t == 1].
Proof.
move=>t.
rewrite ffunE.
by case (categorical_dist t) ; rewrite eqxx// orbT.
Qed.

HB.instance Definition _  :=
  Categorical_of_Necessity.Build R T mu categorical_nec_pidistE.
 *)

HB.end.

#[short(type="categorical_capacity")]
HB.structure Definition Categorical R T := {mu of Categorical_of_Ffun R T mu & }.



Section CategoricalCapacityTheory.

  Variable R : realDomainType.
  Variable T : finType.
  Variable mu : categorical_capacity R T.


  Lemma categorical_massfunE : 
    is_mass_function 0 +%R mu [ffun A : {set T} => if A == [set t | categorical_dist (s:=mu) t] then 1 else 0].
  Proof.
  move=>/=A.
  case (boolP ([set t | categorical_dist (s:=mu) t] \subset A))=>H.
  - rewrite (bigD1 [set t | categorical_dist (s:=mu) t])//=.
    rewrite ffunE eqxx categoricalE H big1 ?addr0=>//= B/andP[_ HB].
    by rewrite ffunE (negbTE HB).
  - rewrite categoricalE (negbTE H) big1=>//B HB.
    rewrite ffunE.
    case (boolP (B == [set t | categorical_dist (s:=mu) t]))=>//=Hcontra.
    rewrite (eqP Hcontra) in HB.
    by rewrite HB in H.
  Qed.


  (** Categorical Pi-distribution *)

  Definition cat_pidist :=
    [ffun t : T => if categorical_dist (s:=mu) t then (1:R) else (0:R)].

  Lemma cat_pidist_in01  :
    [forall t, 0 <= cat_pidist t <= (1:R)].
  Proof.
  apply/forallP=>t ; rewrite ffunE.
  by case (categorical_dist t) ; apply/andP.
  Qed.

  Lemma cat_pidist_norm  :
    [exists t,  cat_pidist t == (1:R)].
  apply/existsP.
  have [t Ht] := (categorical_distE (s:=mu)).
  exists t.
  by rewrite ffunE Ht.
  Qed.

  HB.instance Definition _  :=
    PiDist_of_Ffun.Build R T _ cat_pidist_in01 cat_pidist_norm.

End CategoricalCapacityTheory.


  
Lemma cat_nec_pidistE (R : realDomainType) T (mu : categorical_capacity R T) :
  (mu : {ffun {set T} -> R}) = [ffun A : {set T} => 1 - \big[Num.max/0]_(t in ~:A) cat_pidist mu t].
Proof.
apply/ffunP=>/=A.
rewrite ffunE categoricalE.
have [t Ht] := categorical_distE (s:=mu).
case (boolP ([set t | categorical_dist (s:=mu) t] \subset A))=>H.
- have H0 : \big[Num.max/0]_(t in ~: A) cat_pidist mu t = 0.
  apply/eqP ; rewrite eq_le ; apply/andP ; split.
  + apply: bigmax_le=>//=t'.
    have :=subsetP H t'.
    rewrite !inE=>HtA HtAC.
    have HcF : ~~(categorical_dist (s:=mu) t')
      by apply/negP=>Hcontra ; rewrite (HtA Hcontra) in HtAC.
    by rewrite ffunE (negbTE HcF).
  + by rewrite bigmax_idl le_maxr lexx orTb.
  + by rewrite H0 subr0.
- have H1 : \big[Num.max/0]_(t in ~: A) cat_pidist mu t = 1.
  apply/eqP ; rewrite eq_le ; apply/andP ; split.
  + apply: bigmax_le=>//=t' _.
    rewrite ffunE.
    by case (categorical_dist t').
  + have [t' Ht'1 Ht'2] := subsetPn H.
    have : cat_pidist mu t' = 1
      by rewrite inE in Ht'1 ; rewrite ffunE Ht'1.
    move=><-.
    apply: le_bigmax_cond.
    by rewrite !inE.
  + by rewrite H1 subrr.
Qed.

HB.instance Definition _  (R : realDomainType) T (mu : categorical_capacity R T) :=
  Necessity_of_Ffun.Build R T mu (cat_nec_pidistE mu).



(** Decidable equality *)
(*
Definition eq_capacity R T (c1 c2 : capacity R T) : bool :=
  Capacity.sort c1 == Capacity.sort c2.
Lemma eq_capacityP [R T] : Equality+-ba.axiom (@eq_capacity R T).
move=>c1 c2 ; apply (iffP eqP)=>[|->//] ; move: c1 c2.
case=>mu1 ; do 2 case ; move => axM ax01.
case=>mu2 ; do 2 case ; move => axM' ax01'/= H.
rewrite H in ax01 axM *.
by rewrite (eq_irrelevance ax01 ax01') (eq_irrelevance axM axM').
Qed.

HB.instance Definition hasDecEq_of_Capacity R T :=
  hasDecEq.Build (capacity R T) (@eq_capacityP R T).
*)



(*
Definition eq_capa2inf R T (c1 c2 : capa2inf R T) : bool := eq_capacity c1 c2.
Lemma eq_capa2infP [R T] : Equality.axiom (@eq_capa2inf R T).
move=>c1 c2 ; apply (iffP eqP)=>[|->//] ; move: c1 c2.
case=>mu1 ; do 2 case ; move => axM ax01 ; case=> ax2mon.
case=>mu2 ; do 2 case ; move => axM' ax01' ; case=> ax2mon'/=H.
rewrite H in axM ax01 ax2mon *.
by rewrite (eq_irrelevance ax01 ax01') (eq_irrelevance ax2mon ax2mon') (eq_irrelevance axM axM').
Qed.

HB.instance Definition hasDecEq_of_Capa2Inf R T :=
  hasDecEq.Build (capa2inf R T) (@eq_capa2infP R T).

Check (_ : capacity _ _) == (_ : capa2inf _ _).
Check (_ : capa2inf _ _) == (_ : capa2inf _ _).
Fail Check (_ : capa2inf _ _) == (_ : capacity _ _). (* Pas satisfaisant *)
Check (_ : capa2inf _ _) == (_ : capacity _ _) :> capacity _ _.

Check (_ : capacity _ _) == (_ : capacity _ _).
Check (_ : belief_function _ _) == (_ : capa2inf _ _) :> capacity _ _.

Check (_ : belief_function _ _) == (_ : capa2inf _ _) :> capa2inf _ _.
*)
