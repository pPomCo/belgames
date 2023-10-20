(* ************************************************************************************ *)
(* Mass functions theory

   Type and subtypes for mass functions {set T} -> R

   - massfun T idx op: mass funtcion with arbitrary operator
   - addMassfun == massfun R 0 +
   - maxMassfun == massfun R 0 max
   - bpa == addMassfun with positive values
   - prBpa == 1-additive bpa

   Type and subtypes for distributions T -> R
   
   - prDist: probability distribution (p t >= 0 /\ \sum_t p t = 1)
   - piDist: possibility distribution (p t >= 0 /\ \max_t p t = 1)
   - catPiDist: categorical piDist (p t = 0 \/ p t = 1)

 *)
(* ************************************************************************************ *)
From Coq Require Import Program.Wf.
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing GRing.Theory.
Import Num.Theory.

From decision Require Import fintype finset order minmax setfun.

Import Order Order.POrderTheory Order.TotalTheory.

(** Mass function structures with Hierarchical Builder *)
From HB Require Import structures.






(** Algebraic mass functions *)
Implicit Type T : finType.

(** Mass function *)
Check "Mass function".
HB.mixin
Record MassFun_of_Ffun R T (idx : R) (op : SemiGroup.com_law R) (m : {ffun {set T} -> R}) :=
  {  }.

#[short(type="massfun")]
HB.structure
Definition MassFun R T idx op := {m of MassFun_of_Ffun R T idx op m}.


Section MassFunTheory.

  Variable R : eqType.
  Variable T : finType.
  Variable idx : R.

  Section OnSemiGroup.
    Variable op : SemiGroup.com_law R.
    Implicit Type m : massfun T idx op.
    Implicit Type mu : {ffun {set T} -> R}.

    Implicit Type A B C : {set T}.

    Definition focal m A := m A != idx.
    Definition dist m := [ffun t => m [set t]].
    
    Definition Pinf m : {ffun {set T} -> R} :=
      [ffun A : {set T} => \big[op/idx]_(B : {set T} | B \subset A) m B].

    Definition Psup m : {ffun {set T} -> R} :=
      [ffun A : {set T} => \big[op/idx]_(B : {set T} | ~~[disjoint B & A]) m B].

    Lemma massfunE m : is_massfun idx op (Pinf m) m.
    Proof. by move=>A ; rewrite ffunE. Qed.

  End OnSemiGroup.

  Section OnMonoid.
    Variable op : Monoid.com_law idx.
    Implicit Type m : massfun T idx op.
    Implicit Type mu : {ffun {set T} -> R}.

    Implicit Type A B C : {set T}.

    Section Inversible.
      Variable (inv : R -> R).
      Variable (massfunV : right_inverse idx inv op).

      HB.instance
      Definition _ mu :=  MassFun_of_Ffun.Build R T idx op (mkmassfun op inv mu).

      Lemma mkmassfunE mu :
        mu = Pinf (mkmassfun op inv mu).
      Proof.
      apply/ffunP=>/=A.
      rewrite ffunE.
      exact: mkmassfunE.
      Qed.
      
    End Inversible.
  End OnMonoid.
End MassFunTheory.






(** +-based mass functions *)


Implicit Type R : numDomainType.
Local Open Scope ring_scope.

Check "+-based mass function".
HB.mixin
Record AddMassFun_of_MassFun R T (m : {ffun {set T} -> R}) of MassFun_of_Ffun R T 0 +%R m :=
  { massfun0 : m set0 = 0 ;
    massfun1 : \sum_(A : {set T}) m A = 1 }.

#[short(type="addMassfun")]
HB.structure
Definition AddMassFun R T := {m of AddMassFun_of_MassFun R T m & MassFun_of_Ffun R T 0 +%R m}.

(* TODO: For compatibility *)
Notation rmassfun := addMassfun.


Section AddMassFunTheory.

  Variable R : numDomainType.
  Variable T : finType.
  Variable m : rmassfun R T.

  Lemma Pinf01 : pointed (Pinf m).
  Proof.
  apply/andP ; split ; rewrite ffunE.
  - rewrite (bigD1 set0)//= big1 ?addr0 ?massfun0=>// A.
    rewrite subset0 ; by case (boolP (A == set0))=>->.
  - under eq_bigl do rewrite subsetT ; by rewrite massfun1.
  Qed.

  Lemma Pinf0 : Pinf m set0 = 0.
  Proof. exact: pointed0 Pinf01. Qed.

  Lemma PinfT : Pinf m setT = 1.
  Proof. exact: pointedT Pinf01. Qed.

  Lemma Psup01 : pointed (Psup m).
  Proof.
  apply/andP ; split ; rewrite ffunE /=.
  - rewrite big1=>//A ; by rewrite disjoint0.
  - under eq_bigl do rewrite disjointT.
    rewrite -(massfun1 (s:=m)) [E in _==E](bigD1 set0)//=.
    by rewrite massfun0 add0r.
  Qed.

  Lemma Psup0 : Psup m set0 = 0.
  Proof. exact: pointed0 Psup01. Qed.

  Lemma PsupT : Psup m setT = 1.
  Proof. exact: pointedT Psup01. Qed.
  
  Lemma massfun_moebius :
    m =1 moebius (Pinf m).
  Proof. by rewrite (moebius_unique (massfunE m)). Qed.

  Lemma PinfD : setfun.dual (Pinf m) = (Psup m).
  apply/ffunP=>/=A.
  by rewrite (dualE (massfunE m)) ffunE.
  Qed.  

  Lemma PsupD : setfun.dual (Psup m) = (Pinf m).
  apply/ffunP=>/=A.
  by rewrite -PinfD dualK// Pinf0.
  Qed.

  Lemma focal_set0F A :
    focal m A -> A != set0.
  Proof.
  case (boolP (A == set0)) => [/eqP ->| //].
  by rewrite /focal massfun0 eqxx.
  Qed.

  Lemma notin_focal B :
    (B \notin focal m) = (m B == 0).
  Proof. by rewrite Bool.negb_involutive. Qed.

  Lemma focal_card A :
    focal m A -> (#|A| > 0)%N.
  Proof. by rewrite card_gt0 ; exact: focal_set0F. Qed.
  
  Lemma focal_nonempty :
    (#|focal m| > 0)%N.
  Proof.
  apply /card_gt0P=>/=.
  have Hm1' : \sum_A m A != 0 by rewrite massfun1 ; exact: oner_neq0.
  destruct (big_eq1F Hm1') as [A HA] ; move: HA=>/and3P[_ _ HA0].
  have HA0F : A != set0 by apply/eqP=>Hcontra ; rewrite Hcontra massfun0 eqxx in HA0.
  by exists A.
  Qed.

  Lemma massfun_nonempty :
    (#|T| > 0)%N.
  Proof.
  apply /card_gt0P.
  have [A HA] := eq_bigmax_cond (fun=>1%N) focal_nonempty.
  have [t _] := eq_bigmax_cond (fun=>1%N) (focal_card HA).
  by exists t.
  Qed.  

  Definition massfun_pick : T
    := let (t,_) := (bigop.eq_bigmax (fun=>0%N) massfun_nonempty) in t.


  (** A sum over the focalset, weighted using the mass function, is equal to the same sum over X *)
  Lemma sum_fun_focal_cond (P : pred {set T}) (f : {set T} -> R) :
    \sum_(B in focal m | P B) m B * f B = \sum_(B : {set T} | P B) m B * f B.
  Proof.
  rewrite big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => B _.
  case (boolP (B \in focal m)) => [_|].
  - by rewrite andTb.
  - rewrite andFb notin_focal => /eqP -> ; case (P B) => // ; by rewrite mul0r.
  Qed.

  Lemma sum_fun_focal (f : {set T} -> R) :
    \sum_(B in focal m) m B * f B = \sum_(B : {set T}) m B * f B.
  Proof.
  rewrite big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => B _.
  case (boolP (B \in focal m)) => [_//|].
  rewrite notin_focal => /eqP -> ; by rewrite mul0r.
  Qed.

  Lemma sum_mass_focal_cond (P : pred {set T}) :
    \sum_(B in focal m | P B) m B = \sum_(B : {set T} | P B) m B.
  Proof.
  rewrite big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => B _.
  case (boolP (B \in focal m)) => [_|].
  - by rewrite andTb.
  - rewrite andFb notin_focal => /eqP -> ; by case (P B).
  Qed.

  Lemma sum_mass_focal :
    \sum_(B in focal m) m B = \sum_(B : {set T}) m B.
  Proof.
  rewrite big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => B _.
  case (boolP (B \in focal m)) => [_//|].
  by rewrite notin_focal => /eqP ->.
  Qed.

  Lemma Pinf_focalE A :
    Pinf m A = \sum_(B in focal m | B \subset A) m B.
  Proof. by rewrite ffunE sum_mass_focal_cond. Qed.

  Lemma Psup_focalE A :
    Psup m A = \sum_(B in focal m | B :&: A != set0) m B.
  Proof. by rewrite ffunE sum_mass_focal_cond ; under eq_bigl do rewrite -setI_eq0. Qed.

  Lemma Pinf1 t :
    Pinf m [set t] = m [set t].
  Proof.
  have := Pinf01 =>/andP[/eqP H0>_].
  by rewrite massfun_moebius moebius1 H0 subr0.
  Qed.

End AddMassFunTheory.


(** max-based mass function *)
Check "max-based mass function".

HB.mixin
Record MaxMassFun_of_MassFun (R : realDomainType) T (m : {ffun {set T} -> R}) of MassFun_of_Ffun R T 0 max m :=
  { massfun0 : m set0 = 0 ;
    massfun1 : \big[max/0]_(A : {set T}) m A = 1 }.

#[short(type="maxMassfun")]
HB.structure
Definition MaxMassFun (R : realDomainType) T := {m of MaxMassFun_of_MassFun R T m & MassFun_of_Ffun R T 0 max m}.



(** +-based mass function with positive values *)

Check "BPA".

HB.mixin
Record Bpa_of_AddMassFun R T (m : {ffun {set T} -> R})
of AddMassFun_of_MassFun R T m
& MassFun_of_Ffun R T 0 +%R m :=
  { bpa_ge0 : forall A, m A >= 0 }.

#[short(type="bpa")]
HB.structure
Definition Bpa R T := {m of Bpa_of_AddMassFun R T m
                       & AddMassFun_of_MassFun R T m
                       & MassFun_of_Ffun R T 0 +%R m}.


Section BpaTheory.

  Variable R : numDomainType.
  Variable T : finType.
  Variable m : bpa R T.

  Notation Bel := (Pinf m).
  Notation Pl := (Psup m).

  Lemma massfun_mpositive : mpositive Bel.
  Proof. by move=>A ; rewrite -(moebius_unique (massfunE m)) ; exact: bpa_ge0. Qed.

  Lemma massfun_mpositiveD : mpositive (setfun.dual Pl).
  Proof. by rewrite PsupD ; exact: massfun_mpositive. Qed.
  
  Lemma in_focal_mass B :
    (B \in focal m) = (m B > 0).
  Proof. by rewrite lt0r bpa_ge0 andbT. Qed.
  
  Lemma Pinf_ge0 A : Bel A >= 0.
  Proof. by rewrite ffunE ; apply sumr_ge0=>B _ ; exact: bpa_ge0. Qed.

  Lemma Psup_ge0 A : Pl A >= 0.
  Proof. by rewrite ffunE ; apply sumr_ge0=>B _ ; exact: bpa_ge0. Qed.

  Lemma PinfM : monotonic Bel.
  Proof. by apply: mpositive_monotonic ; exact: massfun_mpositive. Qed.

  Lemma PsupM : monotonic Pl.
  Proof. by rewrite -PinfD ; apply: dual_monotonic ; exact: PinfM. Qed.

End BpaTheory.



(** Probability mass function *)

Check "PrBpa".

HB.mixin
Record PrBpa_of_Bpa R T (m : {ffun {set T} -> R})
of Bpa_of_AddMassFun R T m
& AddMassFun_of_MassFun R T m
& MassFun_of_Ffun R T 0 +%R m :=
  { prbpa_card1 : forall A : {set T}, m A != 0 -> #|A| == 1%N }.

#[short(type="prBpa")]
HB.structure
Definition PrBpa R T := {m of PrBpa_of_Bpa R T m
                         & Bpa_of_AddMassFun R T m
                         & AddMassFun_of_MassFun R T m
                         & MassFun_of_Ffun R T 0 +%R m}.

Section PrBpaTheory.

  Variable R : numDomainType.
  Variable T : finType.
  Variable p : prBpa R T.

  Notation Pr := [ffun A : {set T} => \sum_(t in A) dist p t].

  Lemma PrPinf : Pr = (Pinf p).
  Proof.
  apply/ffunP=>/=A.
  rewrite !ffunE/=.
  rewrite [in RHS](bigID (fun A : {set T} => #|A|==1%N))/= big_card1_dep [E in _=_+E]big1 ?addr0/=.
  - apply: eq_big=>[t|B HB] ; first by rewrite sub1set.
    by rewrite ffunE.
  - move=>B /andP [_ HB].
    apply/eqP/negP=>/negP Hcontra.
    by rewrite (prbpa_card1 _ Hcontra) in HB.
  Qed.

  Lemma PrPsup : Pr = (Psup p).
  Proof.
  apply/ffunP=>/=A.
  rewrite !ffunE/=.
  rewrite [in RHS](bigID (fun A : {set T} => #|A|==1%N))/= big_card1_dep [E in _=_+E]big1 ?addr0/=.
  - apply: eq_big=>[t|B HB] ; first by rewrite disjoints1 Bool.negb_involutive.
    by rewrite ffunE.
  - move=>B /andP [_ HB].
    apply/eqP/negP=>/negP Hcontra.
    by rewrite (prbpa_card1 _ Hcontra) in HB.
  Qed.

  Lemma PinfPsup_eq : Pinf p = Psup p.
  Proof. by rewrite -PrPinf -PrPsup. Qed.

  Lemma PrD : setfun.dual Pr = Pr.
  Proof. by rewrite [in LHS]PrPinf PrPsup ; exact: PinfD. Qed.

  Lemma massfun_additiveUI : additiveUI Pr.
  Proof.
  move=>A B ; rewrite !ffunE.
  rewrite [E in E+_=_](bigID (fun t => t \in A))/=.
  rewrite [E in _=_+E](bigID (fun t => t \in A)) [E in _=_+(E)]addrC addrA/=.
  rewrite [E in E+_+_=_](eq_bigl (fun t => t \in A))=>[|t].
  rewrite [E in _+E+_=_](eq_bigl (fun t => t \in B :\: A))=>[|t].
  rewrite [E in _=_+E+_](eq_bigl (fun t => t \in B :\: A))=>[|t].
  rewrite [E in _=_+_+E](eq_bigl (fun t => t \in A :&: B))=>[//|t].
  + by rewrite in_setI andbC.
  + by rewrite in_setD andbC.
  + by rewrite in_setD in_setU ; case (t \in A) ; case (t \in B).
  + by rewrite in_setU ; case (t \in A) ; rewrite // andbF.
  Qed.

  Lemma prBpa_dist_ge0 t : dist p t >= 0.
  Proof. by rewrite ffunE ; exact: bpa_ge0. Qed.

  Lemma prBpa_dist_sum1 : \sum_t dist p t = 1.
  Proof.
  have : Pr setT = 1
    by rewrite PrPinf (pointedT (Pinf01 p)).
  by rewrite ffunE big_setT.
  Qed.

End PrBpaTheory.





(** Probability distribution *)

Check "PrDist".

HB.mixin
Record PrDist_of_Ffun R T (p : {ffun T -> R}) :=
  { prdist_ge0 : forall t, p t >= 0 ;
    prdist_sum1 : \sum_t p t = 1 }.

#[short(type="prdist")]
HB.structure
Definition PrDist R T := {p of PrDist_of_Ffun R T p}.


Section PrDistTheory.

  Variable R : numDomainType.
  Variable T : finType.

  HB.instance Definition _ (p : prBpa R T) :=
    PrDist_of_Ffun.Build R T (dist p) (prBpa_dist_ge0 p) (prBpa_dist_sum1 p).

  Variable p : prdist R T.

  Notation Pr := [ffun A : {set T} => \sum_(t in A) p t].

  Lemma prdist_capa01 : pointed Pr.
  apply/andP ; split ; rewrite ffunE ; apply/eqP.
  - exact: big_set0.
  - by rewrite big_setT ; exact: prdist_sum1.
  Qed.

  Lemma prdist_capaM : monotonic Pr.
  move=>A B ; rewrite !ffunE.
  rewrite [E in _<=E](bigID (fun t=>t \in A)).
  rewrite [E in _<=E+_](eq_bigl (fun t=>t \in A))=>/=[|t] ;
    last by rewrite in_setU ; case (t \in A) ; rewrite // andbF.  
  by rewrite lerDl sumr_ge0=>//t ; rewrite prdist_ge0.
  Qed.

  Lemma prdist_capaAdd : additiveUI Pr.
  Proof.
  move=>A B ; rewrite !ffunE.
  rewrite [E in E+_=_](bigID (fun t => t \in A))/=.
  rewrite [E in _=_+E](bigID (fun t => t \in A)) [E in _=_+(E)]addrC addrA/=.
  rewrite [E in E+_+_=_](eq_bigl (fun t => t \in A))=>[|t].
  rewrite [E in _+E+_=_](eq_bigl (fun t => t \in B :\: A))=>[|t].
  rewrite [E in _=_+E+_](eq_bigl (fun t => t \in B :\: A))=>[|t].
  rewrite [E in _=_+_+E](eq_bigl (fun t => t \in A :&: B))=>[//|t].
  + by rewrite in_setI andbC.
  + by rewrite in_setD andbC.
  + by rewrite in_setD in_setU ; case (t \in A) ; case (t \in B).
  + by rewrite in_setU ; case (t \in A) ; rewrite // andbF.
  Qed.

End PrDistTheory.




(** Possibility distribution *)

Check "PiDist".

HB.mixin Record PiDist_of_Ffun (R : realDomainType) T (p : {ffun T -> R}) :=
  { pidist_in01 : [forall t, (0 <= p t <= 1)%R] ;
    pidist_norm : [exists t, (p t == 1)%R] }.

#[short(type="pidist")]
HB.structure Definition PiDist (R : realDomainType) T := {p of PiDist_of_Ffun R T p}.


Section PiDistTheory.

  Variable R : realDomainType.
  Variable T : finType.
  Variable p : pidist R T.
  Implicit Type A B C : {set T}.

  Notation Pi := [ffun A : {set T} => \big[Num.max/0%R]_(t in A) p t].
  Notation N := [ffun A : {set T} => 1 - \big[Num.max/0%R]_(t in ~:A) p t].

  Definition sure_event := [set t | p t > 0].

  Lemma pidist_max1 : \big[Num.max/0%R]_t p t = 1%R.
  Proof.
  apply/eqP ; rewrite eq_le ; apply/andP ; split.
  - apply: bigmax_le=>//t _.
    by have := forallP (pidist_in01 (s:=p)) t=>/andP[_->].
  - have [t /eqP Ht] := existsP (pidist_norm (s:=p)).
    rewrite -Ht.
    exact: le_bigmax 0%R (fun t => p t) t.
  Qed.

  Lemma pidist_Pi0 : Pi set0 = 0.
  Proof. by rewrite ffunE big_set0. Qed.
  
  Lemma pidist_PiT : Pi setT = 1.
  Proof. by rewrite ffunE big_setT pidist_max1. Qed.

  Lemma pidist_Pi01 : pointed Pi.
  Proof. by apply/andP ; rewrite pidist_Pi0 pidist_PiT. Qed.

  Lemma pidist_PiM : monotonic Pi.
  move=>A B.
  rewrite !ffunE -!finset.big_condT.
  apply: subset_bigmax.
  by rewrite subsetU// subxx.
  Qed.
  
  Lemma pidist_N0 : N set0 = 0.
  Proof.
  rewrite ffunE ; under eq_bigl do rewrite setC0 in_setT.
  by rewrite pidist_max1 subrr.
  Qed.
  
  Lemma pidist_NT : N setT = 1.
  Proof.
  by rewrite ffunE ; under eq_bigl do rewrite setCT ; rewrite big_set0 subr0.
  Qed.

  Lemma pidist_N01 : pointed N.
  Proof. by apply/andP ; rewrite pidist_N0 pidist_NT. Qed.

  Lemma pidist_NM : monotonic N.
  Proof.
  move=>A B.
  rewrite !ffunE -!finset.big_condT.
  apply: lerB=>//.
  apply: subset_bigmax.
  rewrite setCU ; exact: subsetIl.
  Qed.

  Lemma pidist_ND : setfun.dual Pi = N.
  Proof. apply/ffunP=>/=A ; by  rewrite ffunE pidist_PiT !ffunE. Qed.

  Lemma pidist_PiD : setfun.dual N = Pi.
  Proof.
  apply/ffunP=>/=A.
  rewrite ffunE pidist_NT !ffunE opprB.
  rewrite [E in 1+E]addrC addrA subrr add0r.
  by under eq_bigl do rewrite setCK. 
  Qed.


  Lemma pidist_N2mon : is_2monotone N.
  Proof.
  move=>A B ; rewrite !ffunE.
  rewrite !addrA [E in E-_<=_]addrC [E in _<=E-_]addrC !addrA.
  rewrite -[E in E<=_]addrA -[E in _<=E]addrA.
  apply: lerD=>//.
  rewrite -opprB -[E in _<=E]opprB lerNl !opprK.
  under eq_bigl do rewrite setCI ; under [E in _+E<=_]eq_bigl do rewrite setCU.
  rewrite bigmaxU maxEle.
  set maxAc := \big[Num.max/0]_(t in ~: A) p t.
  set maxBc := \big[Num.max/0]_(t in ~: B) p t.
  case (boolP (maxAc <= maxBc))=>H.
  - rewrite H.
    apply: lerD=>//.
    exact: bigmaxIl.
  - rewrite -ltNge in H.
    rewrite (lt_geF H) addrC.
    apply: lerD=>//.
    exact: bigmaxIr.
  Qed.

  Lemma pidist_Pi2alt : is_2alternating Pi.
  apply dual_2monotone.
  rewrite pidist_ND.
  exact: pidist_N2mon.
  Qed.

  
End PiDistTheory.



(** Categorical possibility distribution *)

Check "CatPiDist".

HB.mixin Record CatPiDist_of_PiDist (R : realDomainType) T (p : {ffun T -> R}) of PiDist_of_Ffun R T p :=
  { pidistCat : forall t, p t = 0 \/ p t = 1 }.

#[short(type="catpidist")]
HB.structure Definition CatPiDist (R : realDomainType) T :=
  {p of CatPiDist_of_PiDist R T p & PiDist_of_Ffun R T p}.


Section CatPiDistTheory.

  Variable R : realDomainType.
  Variable T : finType.
  Variable p : catpidist R T.
  Implicit Type A B C : {set T}.

  Notation Pi := [ffun A : {set T} => \big[Num.max/0%R]_(t in A) p t].
  Notation N := [ffun A : {set T} => 1 - \big[Num.max/0%R]_(t in ~:A) p t].

  Definition catpidist_sure1 t : (t \in sure_event p) = (p t == 1).
  Proof.
  rewrite !inE.
  case (pidistCat (s:=p) t)=>->.
  - by rewrite eq_sym oner_eq0.
  - rewrite eqxx ; exact: ltr01.
  Qed.

  Definition catpidist_sure0 t : (t \notin sure_event p) = (p t == 0).
  Proof.
  rewrite catpidist_sure1.
  case (pidistCat (s:=p) t)=>-> ;
    by rewrite eqxx ?oner_eq0// eq_sym oner_eq0.
  Qed.

  Lemma catpidist_PiE : Pi = [ffun A : {set T} => if A :&: sure_event p == set0 then 0 else 1].
  Proof.
  apply/ffunP=>/=A.
  rewrite !ffunE.
  case (boolP (A :&: sure_event p == set0))=>[H|/set0Pn [t Ht]].
  - apply/eqP ; rewrite eq_le.
    apply/andP ; split.
    + apply: bigmax_le=>//t Ht.
      rewrite le_eqVlt.
      apply/orP ; left.
      apply/negP=>/negP Hcontra.
      have : A :&: sure_event p != set0.
      apply/set0Pn ; exists t ; rewrite !inE Ht/=.
      move: Hcontra.
      by case (pidistCat (s:=p) t)=>->// ; rewrite eqxx.
      by rewrite (eqP H) eqxx.
    + have := monotonic0 (pidist_PiM p) A.
      by rewrite pointed0 ?pidist_Pi01// ffunE=>->.
  - apply/eqP ; rewrite eq_le.
    apply/andP ; split.
    + apply: bigmax_le=>//t' Ht'.
      by case (pidistCat (s:=p) t')=>->.
    + move: Ht.
      rewrite !in_setI catpidist_sure1=>/andP[Ht/eqP<-].
      exact: le_bigmax_cond.
  Qed.

End CatPiDistTheory.
