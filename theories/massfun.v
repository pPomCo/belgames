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
Record MassFun_of_Ffun R T (idx : R) (op : Monoid.com_law idx) (m : {ffun {set T} -> R}) :=
  {  }.

#[short(type="massfun")]
HB.structure
Definition MassFun R T idx op := {m of MassFun_of_Ffun R T idx op m}.

Section MassFunTheory.

  Variable R : eqType.
  Variable T : finType.
  Variable idx : R.
  Variable op : Monoid.com_law idx.
  Implicit Type m : massfun T op.
  Implicit Type mu : {ffun {set T} -> R}.

  Implicit Type A B C : {set T}.

  Definition focal m A := m A != idx.

  Lemma focalE m A :
    focal m A == setfun.focal (idx:=idx) m A.
  Proof. by []. Qed.

  Definition is_massfun_of m (mu : {set T} -> R) :=
    is_mass_function op mu m.

  (* Notation focal := (@focal T R idx m). *)
  
  Definition Pinf m : {ffun {set T} -> R} :=
    [ffun A : {set T} => \big[op/idx]_(B : {set T} | B \subset A) m B].

  Definition Psup m : {ffun {set T} -> R} :=
    [ffun A : {set T} => \big[op/idx]_(B : {set T} | ~~[disjoint B & A]) m B].

  Lemma massfunE m : is_massfun_of m (Pinf m).
  Proof. by move=>A ; rewrite ffunE. Qed.

  Section Inversible.
    Variable (inv : R -> R).
    Variable (massfunV : right_inverse idx inv op).


    Program Fixpoint mkmassfun_wf (mu : {ffun {set T} -> R}) A {measure #|A|} : R :=
      op (mu A) (inv (\big[op/idx]_(B : {B0: {set T} | B0 \proper A}) mkmassfun_wf mu B)).
    Next Obligation.
    move=>mu A H [B HB].
    exact: ssrnat.ltP (proper_card HB).
    Defined.
    Next Obligation.
    apply: measure_wf.
    exact: Wf_nat.lt_wf.
    Defined.

    Definition mkmassfun mu := [ffun A : {set T} => mkmassfun_wf mu A].

    HB.instance
    Definition _ mu :=  MassFun_of_Ffun.Build R T idx op (mkmassfun mu).

    Lemma mkmassfun_def mu A :
      mkmassfun mu A = op (mu A) (inv (\big[op/idx]_(B : {set T} | B \proper A) mkmassfun mu B)).
    Proof.
    rewrite -sig_big ffunE ; under eq_bigr do rewrite ffunE.
    rewrite/mkmassfun_wf/mkmassfun_wf_func Fix_eq //=.
    move => [mu' A'] /= y z Hyz.
    congr (op _ _).
    congr (inv _).
    apply:eq_bigr => [B _] /=.
    by rewrite Hyz.
    Qed.

    Lemma mkmassfunE mu A :
      mu A = \big[op/idx]_(B : {set T} | B \subset A) mkmassfun mu B.
    Proof.
    rewrite (bigD1 A) ?subxx // mkmassfun_def -Monoid.mulmA /=.
    under [E in _ = op _ (op _ E)]eq_bigl do rewrite -properEbis.
    by rewrite [E in _ = op _ E]Monoid.mulmC/= massfunV Monoid.mulm1.
    Qed.

    Lemma mkmassfun_Pinf m A :
      m A = mkmassfun (Pinf m) A.
    Proof.
    rewrite /Pinf.
    move:A ; apply: subset_ind=>A IH.
    rewrite mkmassfun_def ffunE (bigD1 A)//.
    under eq_bigl do rewrite -properEbis.
    by rewrite -(eq_bigr _ IH) -Monoid.mulmA/= massfunV Monoid.mulm1.
    Qed.

    Lemma Pinf_mkmassfun mu A :
      mu A = Pinf (mkmassfun mu) A.
    Proof.
    rewrite ffunE mkmassfunE.
    move:A ; apply: subset_ind=>A IH.
    by rewrite (bigD1 A) ?subxx// [in RHS](bigD1 A).
    Qed.
    
    Lemma massfun_unique (m1 m2 : massfun T op) :
      Pinf m1 =1 Pinf m2 -> m1 =1 m2.
    Proof.
    move=>Hm1m2.
    apply: subset_ind=>A IH.
    rewrite mkmassfun_Pinf [in RHS]mkmassfun_Pinf.
    congr (mkmassfun _ _).
    exact/ffunP.
    Qed.

    Definition dist m := [ffun t => m [set t]].

  End Inversible.

End MassFunTheory.





(** NumField mass functions *)




Implicit Type R : numFieldType.
Local Open Scope ring_scope.

HB.mixin
Record NumMassFun_of_Ffun R T (m : {ffun {set T} -> R}) :=
  { massfun0 : m set0 = 0 ;
    massfun1 : \sum_(A : {set T}) m A = 1 }.

#[short(type="rmassfun")]
HB.structure
Definition NumMassFun R T := {p of NumMassFun_of_Ffun R T p}.

#[non_forgetful_inheritance]
HB.instance
Definition _ R T (m : rmassfun R T) := MassFun_of_Ffun.Build R T (0:R) +%R m.

Section NumMassFunTheory.

  Variable R : numFieldType.
  Variable T : finType.
  Variable m : rmassfun R T.

  Lemma massfun_Pinf01 : pointed (Pinf m).
  Proof.
  apply/andP ; split ; rewrite ffunE.
  - rewrite (bigD1 set0)//= big1 ?addr0 ?massfun0=>// A.
    rewrite subset0 ; by case (boolP (A == set0))=>->.
  - under eq_bigl do rewrite subsetT ; by rewrite massfun1.
  Qed.

  Lemma massfun_Psup01 : pointed (Psup m).
  Proof.
  apply/andP ; split ; rewrite ffunE /=.
  - rewrite big1=>//A ; by rewrite disjoint0.
  - under eq_bigl do rewrite disjointT.
    rewrite -(massfun1 (s:=m)) [E in _==E](bigD1 set0)//=.
    by rewrite massfun0 add0r.
  Qed.

  Lemma massfun_Pinf : is_mass_function +%R (Pinf m) m.
  Proof. move=>/=A. by rewrite ffunE. Qed.
  
  Lemma massfun_moebius :
    m =1 moebius (Pinf m).
  Proof. by rewrite (moebius_unique massfun_Pinf). Qed.

  Lemma massfun_PinfD : setfun.dual (Pinf m) = (Psup m).
  apply/ffunP=>/=A.
  by rewrite (dualE massfun_Pinf) ffunE.
  Qed.  

  Lemma massfun_PsupD : setfun.dual (Psup m) = (Pinf m).
  apply/ffunP=>/=A.
  by rewrite -massfun_PinfD dualK// pointed0// massfun_Pinf01.
  Qed.  

End NumMassFunTheory.





(** Mass function with positive values *)

Check "BPA".

HB.mixin
Record Bpa_of_NumMassFun R T (m : {ffun {set T} -> R}) of NumMassFun_of_Ffun R T m :=
  { bpa_ge0 : forall A, m A >= 0 }.

#[short(type="bpa")]
HB.structure
Definition Bpa R T := {m of Bpa_of_NumMassFun R T m & NumMassFun_of_Ffun R T m}.

#[non_forgetful_inheritance]
HB.instance
Definition _ R T (m : bpa R T) := MassFun_of_Ffun.Build R T (0:R) +%R m.


Section BpaTheory.

  Variable R : numFieldType.
  Variable T : finType.
  Variable m : bpa R T.

  (*
  Notation Bel := [ffun A : {set T} => \sum_(B : {set T} | B \subset A) m B].
  Notation Pl  := [ffun A : {set T} => \sum_(B : {set T} | ~~[disjoint B & A]) m B].
   *)
  Notation Bel := (Pinf m).
  Notation Pl := (Psup m).

  Lemma massfun_mpositive : mpositive Bel.
  Proof.
  move=>A.
  rewrite -(moebius_unique (massfun_Pinf m)).
  exact: bpa_ge0.
  Qed.

End BpaTheory.

(** Probability mass function *)

Check "PrBpa".

HB.mixin
Record PrBpa_of_Bpa R T (m : {ffun {set T} -> R}) of Bpa_of_NumMassFun R T m & NumMassFun_of_Ffun R T m :=
  { prbpa_card1 : forall A : {set T}, m A != 0 -> #|A| == 1%N }.

#[short(type="prBpa")]
HB.structure
Definition PrBpa R T := {m of PrBpa_of_Bpa R T m & Bpa_of_NumMassFun R T m}.

#[non_forgetful_inheritance]
HB.instance
Definition _ R T (m : prBpa R T) := MassFun_of_Ffun.Build R T (0:R) +%R m.


Section PrBpaTheory.

  Variable R : numFieldType.
  Variable T : finType.
  Variable m : prBpa R T.

  Notation Pr := [ffun A : {set T} => \sum_(t in A) m [set t]].

  (*
  Lemma PrPinf : Pr = Pinf m.
  Proof.
   *)

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

  Variable R : numFieldType.
  Variable T : finType.
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

HB.mixin Record PiDist_of_Ffun (R : realFieldType) T (p : {ffun T -> R}) :=
  { pidist_in01 : [forall t, (0 <= p t <= 1)%R] ;
    pidist_norm : [exists t, (p t == 1)%R] }.

#[short(type="pidist")]
HB.structure Definition PiDist (R : realFieldType) T := {p of PiDist_of_Ffun R T p}.


Section PiDistTheory.

  Variable R : realFieldType.
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

HB.mixin Record CatPiDist_of_PiDist (R : realFieldType) T (p : {ffun T -> R}) of PiDist_of_Ffun R T p :=
  { pidistCat : forall t, p t = 0 \/ p t = 1 }.

#[short(type="catpidist")]
HB.structure Definition CatPiDist (R : realFieldType) T :=
  {p of CatPiDist_of_PiDist R T p & PiDist_of_Ffun R T p}.


Section CatPiDistTheory.

  Variable R : realFieldType.
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
