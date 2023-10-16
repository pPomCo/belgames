From Coq Require Import Program.Wf.
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing GRing.Theory.
Import Num.Theory.

From decision Require Import fintype.
From decision Require Import finset.
From decision Require Import minmax.

Import Order Order.POrderTheory.



(** Lemmas about set-functions (f : {set T} -> R) **)
Section SetFunctions.

  Context {T : finType}.
  Implicit Type t : T.
  Implicit Type A B C : {set T}.

  (** Set-function may have "mass-function" representations which also is a set function **)
  Section MassFunction.
    Variable R : eqType.
    Variable idx : R.
    Variable op : R -> R -> R.
    
    Notation Pinf m := (fun A => \big[op/idx]_(B : {set T} | B \subset A) m B).
    Notation Psup m := (fun A => \big[op/idx]_(B : {set T} | ~~[disjoint B & A]) m B).

    
    Definition is_massfun mu m :=
      mu =1 Pinf m.

    Lemma Pinf_isMassfun m :
      is_massfun (Pinf m) m.
    Proof. by []. Qed.

    Definition focal m A := m A != idx.

    Definition k_additivity m := \max_(A in focal m) #|A|.


  End MassFunction.

  Section MassFunctionOnComMonoid.
    Variable R : eqType.
    Variable idx : R.
    Variable op : Monoid.com_law idx.

    Notation Pinf m := (fun A => \big[op/idx]_(B : {set T} | B \subset A) m B).
    Notation Psup m := (fun A => \big[op/idx]_(B : {set T} | ~~[disjoint B & A]) m B).

    
    Lemma massfun_focal mu m :
      is_massfun idx op mu m
      -> mu =1 (fun A : {set T} => \big[op/idx]_(B in focal idx m | B \subset A) m B).
    Proof.
    move=>Hm A.
    rewrite big_mkcondl Hm.
    apply: eq_bigr=>/= B HB.
    rewrite unfold_in.
    by case (boolP (m B == idx))=>[/eqP->|].
    Qed.

    Lemma Pinf_focal m :
      Pinf m =1 (fun A : {set T} => \big[op/idx]_(B in focal idx m | B \subset A) m B).
    Proof.
    apply: massfun_focal.
    exact: Pinf_isMassfun.
    Qed.

    Lemma Psup_focal m :
      Psup m =1 (fun A : {set T} => \big[op/idx]_(B in focal idx m | ~~[disjoint B & A]) m B).
    Proof.
    move=> A.
    rewrite [in RHS]big_mkcondl.
    apply: eq_bigr=>/= B HB.
    rewrite unfold_in.
    by case (boolP (m B == idx))=>[/eqP->|].
    Qed.



    Section Inversible.
      Variable (inv : R -> R).
      Variable (massfunV : right_inverse idx inv op).

      (* \approx moebius *)
      Program Fixpoint mkmassfun_wf (mu : {set T} -> R) A {measure #|A|} : R :=
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

      Check Pinf _.
      Lemma mkmassfun_Pinf m A :
        m A = mkmassfun (Pinf m) A.
      Proof.
      move:A ; apply: subset_ind=>A IH.
      rewrite mkmassfun_def (bigD1 A)//.
      under eq_bigl do rewrite -properEbis.
      by rewrite -(eq_bigr _ IH) -Monoid.mulmA/= massfunV Monoid.mulm1.
      Qed.

      Lemma Pinf_mkmassfun mu A :
        mu A = Pinf (mkmassfun mu) A.
      Proof.
      rewrite mkmassfunE.
      move:A ; apply: subset_ind=>A IH.
      by rewrite (bigD1 A) ?subxx// [in RHS](bigD1 A).
      Qed.
      
      Lemma mkmassfunT mu :
        mu setT = \big[op/idx]_(B : {set T}) mkmassfun mu B.
      Proof. rewrite mkmassfunE ; apply: eq_bigl=>B ; by rewrite subsetT. Qed.

      Lemma massfun_unique m1 m2 :
        Pinf m1 =1 Pinf m2 -> m1 =1 m2.
      Proof.
      move=>Hm1m2.
      apply: subset_ind=>A IH.
      rewrite mkmassfun_Pinf [in RHS]mkmassfun_Pinf.
      rewrite !mkmassfun_def.
      congr (op _ _)=>//=.
      congr (inv _).
      apply: eq_bigr=>/=B HB.
      rewrite -mkmassfun_Pinf -mkmassfun_Pinf.
      exact: IH.
      Qed.

      Lemma massfun_unique2 (mu m1 m2 : {ffun {set T} -> R}) :
        is_massfun idx op mu m1 -> is_massfun idx op mu m2
        -> m1 =1 m2.
      Proof. move=>H1 H2 ; apply: massfun_unique=>A ; by rewrite -H1 -H2. Qed.


      
    End Inversible.
    
  End MassFunctionOnComMonoid.

  (** Set-functions with numerical co-domain **)
  Section OrderedSetFunctions.

    Open Scope order_scope.
    Variable disp : Datatypes.unit.
    Variable (R : porderType disp).
    
    Implicit Type mu m : {ffun {set T} -> R}.

    Definition monotonic mu := forall A B, mu (A :|: B) >= mu A.
    Definition monotonicb mu := [forall A : {set T}, [forall B : {set T}, mu (A :|: B) >= mu A]].

    Lemma monotonicP mu : reflect (monotonic mu) (monotonicb mu).
    Proof.
    case (boolP (monotonicb mu)) => [/forallP /= H|/forallPn /= H] ; constructor.
    - by move=>A B ; have := (H A)=>/forallP->.
    - move=>Hcontra.
      destruct H as [A HA].
      move/forallPn=>/= in HA.
      destruct HA as [B HAB].
      have := Hcontra A B.
      by rewrite (negbTE HAB).
    Qed.

    Lemma monotonic0 mu :
      monotonic mu -> forall A, mu A >= mu set0.
    Proof. move=>Hmonotony A ; by rewrite -(set0U A) Hmonotony. Qed.

    (*
    Lemma monotonic0b mu :
      monotonicb mu -> forall A, mu A >= mu set0.
    Proof. move=>/monotonicP H ; exact: monotonic0. Qed.
     *)

    Lemma monotonicT mu :
      monotonic mu -> forall A, mu A <= mu setT.
    Proof. move=>Hmonotony A ; by rewrite -(setUT A) Hmonotony. Qed.
    
    Lemma monotonicU1 mu :
      (forall A t, mu A <= mu (t |: A)) -> monotonic mu.
    Proof.
    Search "V" set0.
    move=>H1 A ; apply: card_ind=>B IH.
    case (set_0Vmem B)=>[->|[t Ht]] ;
      first by rewrite setU0.
    rewrite setUC -(setU1_eq Ht) -(setUD [set t] B) -setUA.
    have H1t := H1 (B :\ t :|: A) t.
    apply: Order.le_trans _ H1t.
    rewrite setUC.
    apply: IH.
    by rewrite [E in (_<E)%N](cardsD1 t) Ht.
    Qed.

    #[deprecated(since="belgames2", note="Use monotonicU1 instead.")]
    Notation monotonic1 := monotonicU1 (only parsing).
    
    Lemma monotonicI mu :
      monotonic mu -> forall A B, mu (A :&: B) <= mu A.
    Proof.
    move=>H A B.
    have := H (A :&: B) A.
    by rewrite setIK.
    Qed.

    Lemma monotonicI' mu :
      monotonic mu <-> forall A B, mu (A :&: B) <= mu A.
    Proof.
    split=>[|H A B] ; first exact: monotonicI.
    by rewrite -[E in mu E<=_](setUK A B).
    Qed.

    Lemma monotonicS mu :
      monotonic mu -> forall A B, A \subset B -> mu A <= mu B.
    Proof. by move=>Hmon A B/setUidPr=><-. Qed.

    Lemma monotonicS' mu :
      monotonic mu <-> forall A B, A \subset B -> mu A <= mu B.
    Proof.
    split=>[|H A B] ; first exact: monotonicS.
    have := subsetUl A B.
    exact: H.
    Qed.

    Lemma monotonicD mu :
      monotonic mu -> forall A B, mu (A :\: B) <= mu A.
    Proof.
    move=>H A B.
    apply: monotonicS=>//.
    exact: subsetDl.
    Qed.

    Lemma monotonicD' mu :
      monotonic mu <-> forall A B, mu (A :\: B) <= mu A.
    Proof.
    split=>[|H A B] ; first exact: monotonicD.
    by rewrite -[E in mu E<=_](setUDD A B).
    Qed.

  End OrderedSetFunctions.

  (** Set-functions with numerical co-domain **)
  Section NumSetFunctions.

    Open Scope ring_scope.
    Variable (R : numDomainType).
    
    Implicit Type mu m : {ffun {set T} -> R}.

    Definition pointed mu := [&& mu set0 == 0 & mu setT == 1].

    Lemma pointed0 mu : pointed mu -> mu set0 = 0.
    Proof. by move=>/andP[/eqP->_]. Qed. 
    Lemma pointedT mu : pointed mu -> mu setT = 1.
    Proof. by move=>/andP[_/eqP->]. Qed.


    Definition is_2monotone mu :=
      forall A B : {set T}, mu (A :|: B) + mu (A :&: B) >= mu A + mu B.
    
    Definition is_2alternating mu :=
      forall A B : {set T}, mu (A :|: B) + mu (A :&: B) <= mu A + mu B.

    Definition is_2monotoneb mu :=
      [forall A : {set T}, [forall B : {set T}, mu (A:|:B) + mu (A:&:B) >= mu A + mu B]].

    Lemma is_2monotoneP mu :
      reflect (is_2monotone mu) (is_2monotoneb mu).
    Proof.
    case (boolP (is_2monotoneb mu))=>H ; constructor.
    - move=>A B ; exact: (forallP (forallP H A) B).
    - move=>Hcontra.
      move: H ; rewrite negb_forall=>/existsP/=[A HA].
      move: HA ; rewrite negb_forall=>/existsP/=[B HB].
      by rewrite (Hcontra A B) in HB.
    Qed.
    
    Definition is_2alternatingb mu :=
      [forall A : {set T}, [forall B : {set T}, mu (A:|:B) + mu (A:&:B) <= mu A + mu B]].

    Lemma is_2alternatingP mu :
      reflect (is_2alternating mu) (is_2alternatingb mu).
    Proof.
    case (boolP (is_2alternatingb mu))=>H ; constructor.
    - move=>A B ; exact (forallP (forallP H A) B).
    - move=>Hcontra.
      move: H ; rewrite negb_forall=>/existsP/=[A HA].
      move: HA ; rewrite negb_forall=>/existsP/=[B HB].
      by rewrite (Hcontra A B) in HB.
    Qed.

    Definition superadditive mu :=
      forall A B, [disjoint A & B] -> mu (A :|: B) >= mu A + mu B.

    Definition subadditive mu :=
      forall A B, [disjoint A & B] -> mu (A :|: B) <= mu A + mu B.

    Definition additive mu :=
      forall A B, [disjoint A & B] -> mu (A :|: B) = mu A + mu B.

    Lemma additive0 mu : additive mu -> mu set0 = 0.
    Proof.
    move=>Hadd.
    apply/eqP/negP=>/negP Hcontra.
    have :=  Hadd set0 set0 (disjoint0 set0).
    rewrite setU0=>/eqP.
    by rewrite -subr_eq subrr eq_sym (negbTE Hcontra).
    Qed.

    Definition additiveUI mu :=
      forall A B, mu (A :|: B) + mu (A :&: B) = mu A + mu B.
    
    
    Lemma additiveUI_additive mu :
      mu set0 = 0 -> (additiveUI mu <-> additive mu).
    Proof.
    move=>H0 ; split=>Hadd A B=> [HAB|].
    - by rewrite -Hadd disjoint_setI0 //H0 addr0.
    - have := Hadd A (B :\: A) (disjointDl _ _).
      rewrite setUD=>->.
      have Hdisjoint : [disjoint (B :\: A) & (A :&: B)]
        by apply/setDidPl/setP=>t ; rewrite !in_setD in_setI ; case (t \in A) ; case (t \in B).
      rewrite -addrA.
      have := Hadd _ _ Hdisjoint=><-.
      congr (_+_).
      congr (mu _).
      apply/setP=>t.
      rewrite in_setU in_setD in_setI.
      by case (t \in A) ; case (t \in B).
    Qed.
    
    Lemma additive_additiveUI mu :
      additive mu -> additiveUI mu.
    Proof. move=>Hadd ; apply additiveUI_additive=>// ; exact: additive0. Qed.

    Definition additiveUIb mu :=
      [forall A : {set T}, [forall B : {set T}, mu (A:|:B) + mu (A:&:B) == mu A + mu B]].

    Lemma additiveUIP mu : reflect (additiveUI mu) (additiveUIb mu).
    Proof.
    case (boolP (additiveUIb mu))=>H ; constructor.
    - move=>A B ; exact: (eqP (forallP (forallP H A) B)).
    - move=>Hcontra.
      move:H ; rewrite negb_forall=>/existsP/=[A HA].
      move: HA ; rewrite/negb_forall=>/existsP/=[B HB].
      by rewrite (Hcontra A B) eqxx in HB.
    Qed.

    Lemma supersubadditive mu :
      superadditive mu -> subadditive mu -> additive mu.
    Proof.
    move=> Hsuper Hsub A B HAB.
    by apply/eqP ; rewrite Order.POrderTheory.eq_le Hsuper // Hsub.
    Qed.

    Lemma superadditive_lt0 (Hnonempty : (#|T| > 0)%N) mu :
      superadditive mu -> mu set0 <= 0.
    Proof.
    move=>H.
    rewrite -cardsT card_gt0 in Hnonempty.
    have t := pick_nonemptyset Hnonempty.
    have := H set0 [set t] (dis0joint _).
    by rewrite set0U gerDr.
    Qed.

      
    (*    
    Lemma superadditive_monotonic mu :
      mu set0 >= 0 -> superadditive mu -> monotonic mu.
    Proof.
    move=>H0 Hmonotony A B.
    have := Hmonotony A (B :\: A) (disjointDl _ _).
    rewrite setUD.    
    apply: le_trans.
  
    Search disjoint setD.
    Search disjoint "D".
     *)

    

    Lemma additiveUIE mu :
      additiveUI mu -> mu set0 = 0 -> forall A, mu A = \sum_(t in A) mu [set t].
    Proof.
    move=>Hadd H0.
    apply: card_ind=>/=A IH.
    case (boolP (#|A|==0)%N).
    + by rewrite cards_eq0=>/eqP-> ; rewrite big_set0.
    + case (boolP (#|A|==1)%N).
      move=>/cards1P[t ->] _ ; by rewrite big_set1.
    + rewrite cards_eq0=>Hcard1 Hcard0.
      have [t Ht] := pick_nonemptyset_sig Hcard0.
      rewrite -[in LHS](setD1K Ht) -[E in E=_]addr0 -[in LHS]H0//.
      rewrite -[E in _+mu E=_](disjoint_setI0 (disjointDl [set t] A)).
      rewrite Hadd ![in LHS]IH.
      rewrite big_set1.
      under eq_bigl do rewrite in_setD andbC in_set1.
      by rewrite [in RHS](bigD1 t)//=.
      * by rewrite cardsDS ?sub1set// cards1 ltn_subrL/= card_gt0.
      * by rewrite cards1 ltn_neqAle eq_sym card_gt0 Hcard0 Hcard1.
    Qed.
    
    Lemma additiveE mu :
      additive mu -> forall A, mu A = \sum_(t in A) mu [set t].
    Proof.
    move=>Hadd.
    apply: additiveUIE ; last exact: additive0.
    exact: additive_additiveUI.
    Qed.


    (*
    (** Numerical set-functions always have a unique mass function **)
    Section NumMassFunction.

      Lemma massfun_unique (m1 m2 : {ffun {set T} -> R}):
        (Pinf m1) =1 (Pinf m2) -> m1 =1 m2.
      Proof.
      move=>/= H12.
      apply: subset_ind=>A H.
      (* apply: (card_ind (P:=fun A => m1 A = m2 A)) => A H. *)
      move: (H12 A).
      rewrite (bigD1 A) //[in RHS](bigD1 A) //=.
      under eq_bigl do rewrite -properEbis ; under [in RHS]eq_bigl do rewrite -properEbis.
      have: \sum_(B : {set T} | B \proper A) m1 B = \sum_(B: {set T} | B \proper A) m2 B
        by apply: eq_bigr=>/=B HB ; exact: H.
      move=>-> HA ; exact: (addIr _ HA).
      Qed.

      Lemma massfun_unique2 (mu m1 m2 : {ffun {set T} -> R}) :
        is_massfun 0 +%R mu m1 -> is_massfun 0 +%R mu m2
        -> m1 =1 m2.
      Proof. move=>H1 H2 ; apply: massfun_unique=>A ; by rewrite -H1 -H2. Qed.

      Lemma massfunE mu m :
        m =1 (fun A => mu A - \sum_(B : {set T} | B \proper A) m B)
        -> is_massfun 0 +%R mu m.
      Proof.
      move=>H A.
      rewrite (bigD1 A) //=.
      under eq_bigl do rewrite -properEbis.
      by rewrite H -addrA [E in _+E]addrC subrr addr0.
      Qed.
    End NumMassFunction.
     *)
    
    (** Duality of numerical set-functions **)
    Section DualSetFunction.

      Definition dual mu : {ffun {set T} -> R} :=
        [ffun A : {set T} => mu setT - mu (~: A)].

      Lemma dual2E mu : dual (dual mu) = [ffun A : {set T} => mu A - mu set0].
      apply/ffunP=>A.
      rewrite !ffunE setCT setCK addrC addrA opprB.
      congr (_ - _).
      by rewrite -addrA [E in _+E]addrC subrr addr0.
      Qed.

      Lemma dualK_set0 mu : mu set0 = 0 <-> dual (dual mu) = mu.
      Proof.
      split=>[H|/ffunP /= H]. 
      - by rewrite dual2E ; apply/ffunP=>A ; rewrite ffunE H subr0.
      - have:= H setT=>/eqP.
        by rewrite !ffunE setCT setC0 subrr subr0
           -subr_eq0 addrC addrA [E in E-_==_]addrC subrr sub0r oppr_eq0=>/eqP->.
      Qed.

      Lemma dualK mu : mu set0 = 0 -> dual (dual mu) = mu.
      Proof.
      by rewrite -dualK_set0.
      Qed.

      Lemma dualE mu m :
        is_massfun 0 +%R mu m -> dual mu =1 (fun A => \sum_(B : {set T} | ~~[disjoint B & A]) m B).
      Proof.
      move=>/=Hm A.
      rewrite ffunE !Hm/=.
      under [E in E-_=_]eq_bigl do rewrite subsetT.
      rewrite (bigID (fun B : {set T} => B \subset ~: A)) /= [E in E+_]addrC -addrA subrr addr0.
      apply: eq_bigl=>B.
      by rewrite disjoints_subset.
      Qed.

      Lemma dual0 mu : dual mu set0 = 0.
      Proof.
      by rewrite ffunE setC0 subrr.
      Qed.

      Lemma dualT mu :
        mu set0 = 0 -> dual mu setT = mu setT.
      Proof.
      rewrite ffunE setCT=>-> ; by rewrite subr0.
      Qed.

      Lemma dualTb mu :
        (mu set0 == 0) = (dual mu setT == mu setT).
      Proof.
      by rewrite ffunE setCT -[in RHS]subr_eq0 -addrA [E in _+(E)]addrC addrA subrr subr_eq0 eq_sym.
      Qed.

      Lemma dual_monotonic mu :
        monotonic mu -> monotonic (dual mu).
      Proof.
      move=>H A B.
      rewrite !ffunE setCU.
      apply lerB ; first by rewrite Order.POrderTheory.lexx.
      exact: monotonicI.
      Qed.
      
      Lemma dual_monotonicb mu :
        monotonicb mu -> monotonicb (dual mu).
      Proof. move=>/monotonicP H ; apply/monotonicP ; exact: dual_monotonic. Qed.
      
      Lemma dual_pointed mu : pointed mu -> pointed (dual mu).
      Proof.
      by move=>/andP[/eqP H0 HT] ; apply/andP ; split ; rewrite ?dual0// dualT.
      Qed.

      Lemma dual_2alternating mu :
        is_2monotone mu <-> is_2alternating (dual mu).
      Proof.
      split=>H A B.
      - rewrite !ffunE !addrA.
        rewrite [E in E-_<=_]addrC [E in _<=E-_]addrC !addrA.
        rewrite -[E in E<=_]addrA -[E in _<=E]addrA.
        apply: lerD=>//.
        rewrite -subr_le0 opprB opprK setCU setCI.
        have HAB := H (~:A) (~:B) ; rewrite -subr_le0 -(opprK (mu (~:A :&: ~:B))) opprB addrA in HAB.
        by rewrite addrC addrA [E in E-_-_<=_]addrC.
      - rewrite -subr_le0.
        have := H (~:A) (~:B).
        rewrite !ffunE -subr_le0 -setCU -setCI !setCK !addrA opprB !opprD !addrA opprK.
        rewrite addrC !addrA [E in E-_+_-_+_-_+_<=_]addrC subrr sub0r.
        rewrite -addrA [E in _+(E)<=_]addrC !addrA addrC.
        rewrite [E in _+(E-_+_+_)<=0]addrC !addrA.
        rewrite [E in E-_-_+_+_<=0]addrC subrr sub0r.
        by rewrite [E in E+_+_<=0]addrC -addrA addrC [E in E+_<=0]addrC !addrA.
      Qed.

      Lemma dual_2monotone mu :
        is_2alternating mu <-> is_2monotone (dual mu).
      Proof.
      split=>H A B.
      - rewrite !ffunE !addrA.
        rewrite [E in E-_<=_]addrC [E in _<=E-_]addrC !addrA.
        rewrite -[E in E<=_]addrA -[E in _<=E]addrA.
        apply: lerD=>//.
        rewrite -subr_le0 opprB opprK setCU setCI.
        have := H (~:A) (~:B) ; rewrite -subr_le0 opprD addrA => HAB.
        by rewrite addrC addrA.
      - rewrite -subr_le0.
        have := H (~:A) (~:B).
        rewrite !ffunE -subr_le0 -setCU -setCI !setCK !addrA opprB !opprD !addrA opprK.
        rewrite addrC !addrA [E in E-_+_-_+_-_+_<=_]addrC subrr sub0r.
        rewrite -addrA [E in _+(E)<=_]addrC !addrA addrC.
        rewrite [E in _+(E-_+_+_)<=0]addrC !addrA.
        rewrite [E in E-_-_+_+_<=0]addrC subrr sub0r.
        by rewrite [E in E+_+_<=0]addrC -addrA addrC [E in _+_+E<=0]addrC !addrA.
      Qed.

      Lemma additiveUI_dual mu :
        additiveUI mu -> mu set0 = 0 -> dual mu = mu.
      Proof.
      move=>Hadd H0.
      apply/ffunP=>/=A.
      rewrite ffunE.
      rewrite additiveUIE// [E in _-E=_]additiveUIE// [E in _=E]additiveUIE//.
      rewrite [E in E-_](bigID (fun t : T => t \in A)) /=.
      rewrite [E in E+_-_](eq_bigl (fun t : T => t \in A))=>[|t] /= ;
        last by rewrite in_setT andTb.
      rewrite [E in _+E-_](eq_bigl (fun t : T => t \in ~:A))=>[|t] /= ;
        last by rewrite in_setT andTb in_setC.
      by rewrite -addrA subrr addr0.
      Qed.

      Lemma additive_dual mu :
        additive mu -> dual mu = mu.
      Proof.
      move=>Hadd.
      apply: additiveUI_dual ; last exact: additive0 Hadd.
      exact: additive_additiveUI.
      Qed.


      Lemma dual_additiveUI mu :
        additiveUI mu -> additiveUI (dual mu).
      Proof.
      move=>Hmu A B.
      rewrite !ffunE setCU setCI !addrA.
      rewrite [in RHS]addrC addrC !addrA.
      congr (_ + _).
      rewrite -addrA [E in _+E=_]addrC -[E in _=E]addrA [E in _=_+E]addrC !addrA.
      congr (_ + _).
      apply/eqP ; rewrite -subr_eq0 addrC addr_eq0 !opprB !opprK.
      by rewrite -Hmu addrC.
      Qed.

      Lemma dual_additive mu :
        additive mu -> additive (dual mu).
      Proof.
      move=>Hmu.
      apply additiveUI_additive.
      - exact: dual0.
      - apply :dual_additiveUI.
        exact: additive_additiveUI.
      Qed.


      (*
      Lemma dual_subadditive mu :
        superadditive mu -> subadditive (dual mu).
      Proof.
      move=>H A B HAB.
      rewrite !ffunE=>//=.
      rewrite -[E in _ <= E]addrA.
      rewrite [E in _ <= _ + E]addrC.
      Check lerD.
      apply lerD ; first by rewrite lexx.
      Search (- _ <= _).
      rewrite lerNl.
      Search (- (_ - _)).
      rewrite !opprB addrA.
      rewrite setCU.
      
      rewrite opprB.
      Search (_ - (_ + _)).
      
      rewrite !addrA.
      Check H _ _.
      Check lerD.
      
      Check H _ _ HAB.
      Search (_ - _ <= _ - _).
      rewrite -[E in _ <= E]addrA.
      rewrite [E in _ <= _ + E]addrC.
      rewrite !addrA.
      Search (_ + (- _ + _)).
      apply lerD ; first by rewrite Order.POrderTheory.lexx.
      Check H _.
      rewrite addrA.
      Search (- _ <= _).
      rewrite lerNl.
      rewrite opprB.
      Check addrA (mu (~:B)).
      Search (-(_+_)).
      Search -%R.
      Search "oppr".
      rewrite -opprB.
      Check opprK _.
      Check subrK _ _.
      Check addrK _ _.
      rewrite -opp_is_additive.
      Check oppr_inj _.
      
       *)

      Lemma dual_le mu A B : (dual mu A <= dual mu B) = (mu (~:A) >= mu (~:B)).
      Proof.
      by rewrite !ffunE lerBlDl addrA [E in _<=E+_]addrC -[E in _<=E]addrA lerDl subr_ge0.
      Qed.

      Lemma le_dual mu A B : (mu A <= mu B) = (dual mu (~:A) >= dual mu (~:B)).
      Proof. by rewrite dual_le !setCK. Qed.


    End DualSetFunction.


    (** Computation of the mass-function (so-called Moebius-inverse aka Moebius-transform)
        Use of an alternative recursive definition (much easier, weaker assumptions)
        The classical definition involves the "times" operator :
          (fun A : {set T} => \sum_(B : {set T} | B \subset A) (-1)^#|setD A B| * mu B) 
     **)
    Section MoebiusTransform.
      (*
      Program Fixpoint moebius_wf mu A {measure #|A|} : R :=
        mu A - \sum_(B : {B0: {set T} | B0 \proper A}) moebius_wf mu B.
      Next Obligation.
      move=>mu A H [B HB].
      exact: ltP (proper_card HB).
      Defined.
      Next Obligation.
      apply: measure_wf.
      exact: Wf_nat.lt_wf.
      Defined.

      Definition moebius mu : {ffun {set T} -> R} := [ffun A : {set T} => moebius_wf mu A].
       *)

      Definition moebius := (mkmassfun (@add R) -%R).
      Definition moebius_def := (mkmassfun_def (@add R) -%R).
      Definition moebiusE := (mkmassfunE (@subrr R)).

      Lemma moebius0 mu :
        moebius mu set0 = mu set0.
      Proof.
      rewrite moebius_def big1=>[/=|A].
      - by rewrite subr0.
      - by rewrite proper0E.
      Qed.

      Lemma moebius1 mu t :
        moebius mu [set t] = mu [set t] - mu set0.
      Proof.
      rewrite moebius_def/=.
      congr (_ - _).
      under eq_bigl do rewrite proper1E.
      rewrite (bigD1 set0) // big_pred0=>/=[|B] ;
        last by case (boolP (B == set0))=>->.
      by rewrite moebius0 addr0.
      Qed.

      Lemma moebius1E mu t :
        mu [set t] = moebius mu [set t] + mu set0.
      Proof.
      by rewrite moebius1 -addrA [E in _+(E)]addrC subrr addr0.
      Qed.
      
      Lemma moebius_focalE mu A :
        ~~ focal 0 (moebius mu) A -> moebius mu A = 0.
      Proof.
      by move=>/negPn/eqP.
      Qed.
      
      Lemma is_massfun_moebius mu :
        is_massfun 0 +%R mu (moebius mu).
      Proof. move=>/=A ; by rewrite moebiusE. Qed.

      Lemma moebius_unique mu m :
        is_massfun 0 +%R mu m -> m = moebius mu.
      Proof.
      move=>H.
      apply/ffunP=>C/=.
      apply (massfun_unique2 (@subrr R) H (is_massfun_moebius _)C).
      Check (fun Hm => massfun_unique2 _ Hm (is_massfun_moebius _)) _.
      Qed.

      Lemma dual_moebius mu A :
        dual mu A = \sum_(B : {set T} | ~~[disjoint B & A]) moebius mu B.
      Proof.
      exact: dualE (is_massfun_moebius mu) A.
      Qed.

      Lemma moebius_dual mu A :
        mu A - mu set0 = \sum_(B : {set T} | ~~[disjoint B & A]) moebius (dual mu) B.
      Proof.
      have Hmu : mu A - mu set0 = [ffun A : {set T} => mu A - mu set0] A by rewrite ffunE.
      rewrite Hmu -dual2E.
      exact: (dualE (is_massfun_moebius (dual mu))).
      Qed.

      
      Lemma additiveUI_moebius mu :
        additiveUI mu -> mu set0 = 0 -> moebius mu = [ffun A : {set T} => if #|A|==1%N then mu A else 0].
      Proof.
      move=>Hadd H0.
      symmetry.
      apply: moebius_unique=>A/=.
      under eq_bigr do rewrite ffunE.
      rewrite -big_mkcondr big_card1_dep /=.
      under eq_bigl do rewrite sub1set.
      exact: additiveUIE.
      Qed.

      Lemma additiveUI_moebius1 mu :
        additiveUI mu -> mu set0 = 0 -> forall A, moebius mu A != 0%R -> #|A| = 1%N.
      Proof.
      move=>Hadd H0 /=A.
      rewrite additiveUI_moebius ?ffunE//.
      by case (boolP (#|A|==1%N))=>[/eqP->//|] ; rewrite eqxx.
      Qed.

      Lemma additive_moebius mu :
        additive mu -> moebius mu = [ffun A : {set T} => if #|A|==1%N then mu A else 0].
      Proof.
      move=>Hadd.
      apply: additiveUI_moebius ; last exact: additive0.
      exact: additive_additiveUI.
      Qed.

      Lemma additive_moebius1 mu :
        additive mu -> forall A, moebius mu A != 0%R -> #|A| = 1%N.
      Proof.
      move=>Hadd.
      apply: additiveUI_moebius1 ; last exact: additive0.
      exact: additive_additiveUI.
      Qed.


    End MoebiusTransform.


    Lemma pointed_moebius mu : pointed mu -> (moebius mu set0 == 0) && (\sum_(A : {set T}) moebius mu A == 1).
    Proof.
    move=>/andP [Hp0 HpT].
    rewrite moebius0 Hp0 andTb.
    by move: HpT ; rewrite moebiusE ; under eq_bigl do rewrite subsetT.
    Qed.

    Lemma pointed_moebius_card_le1 mu :
      pointed mu -> forall A : {set T}, (#|A| <= 1)%N -> moebius mu A = mu A.
    Proof.
    move=>Hpointed A Hle1.
    case (boolP (#|A|==0%N)).
    - rewrite cards_eq0=>/eqP-> ; exact: moebius0.
    - case (boolP (#|A|==1%N)).
      move=>/cards1P[t Ht] _.
      by rewrite Ht moebius1 pointed0// subr0.
    - move=>Hneq1 Hneq0.
      + have Hgt1: (#|A|>1)%N.
        induction #|A| ; first by rewrite eqxx in Hneq0.
        by induction n=>// ; by rewrite eqxx in Hneq1.
      + have := leq_ltn_trans Hle1 Hgt1 ; by rewrite ltnn.
    Qed.    


    Definition mpositive mu : Prop := forall A, moebius mu A >= 0.
    Definition mpositiveb mu : bool := [forall A : {set T}, moebius mu A >= 0].

    Definition mpositiveP mu : reflect (mpositive mu) (mpositiveb mu) := forallP.

    Lemma mpositive_monotonic mu :
      mpositive mu -> monotonic mu.
    Proof.
    move=>Hmpos A B.
    rewrite !moebiusE.
    rewrite [E in _<=E](bigID (fun C : {set T} => C \subset A))/=.
    rewrite [E in _<=E+_](eq_bigl (fun C : {set T} => C \subset A))=>/=[|C].
    - by rewrite lerDl sumr_ge0.
    - case (boolP (C \subset A))=>CsubA ; last by rewrite andbF.
      by rewrite subsetU // CsubA.
    Qed.

    Lemma mpositiveb_monotonicb mu :
      mpositiveb mu -> monotonicb mu.
    Proof.
    move=>/mpositiveP H ; apply/monotonicP ; exact: mpositive_monotonic.
    Qed.

    Lemma mpositive_2monotone mu :
      mpositive mu -> is_2monotone mu.
    Proof.
    move=>Hmpos A B.
    rewrite !moebiusE.
    rewrite [E in _<=E+_](bigID (fun C : {set T} => C \subset A))/=.
    rewrite [E in _<=E+_+_](eq_bigl (fun C : {set T} => C \subset A))=>/=[|C].
    rewrite -addrA.
    apply: lerD=>//.
    rewrite [E in _<=E+_](bigID (fun C : {set T} => C \subset B))/= addrC addrA.
    rewrite [E in _<=_+E+_](eq_bigl (fun C : {set T} => (C \subset B) && ~~(C \subset A)))=>[|C].
    under [E in _<=E+_+_]eq_bigl do rewrite setIC.
    by rewrite [E in _<=E+_]addrC big_subsetI lerDl sumr_ge0.
    - case (boolP (C \subset A))=>CsubA ; case (boolP (C \subset B))=>CsubB ; rewrite ?andbF ?andFb//.
      by rewrite subsetU // CsubB orbT.
    - case (boolP (C \subset A))=>CsubA ; last by rewrite andbF.
      by rewrite subsetU // CsubA.
    Qed.

    Lemma mpositiveb_2monotoneb mu :
      mpositiveb mu -> is_2monotoneb mu.
    Proof.
    move=>/mpositiveP H ; apply/is_2monotoneP ; exact: mpositive_2monotone.
    Qed.

    Lemma additiveUI_mpositive mu :
      additiveUI mu -> mu set0 = 0 -> monotonic mu -> mpositive mu.
    Proof.
    move=>Hadd H0 Hmon A.
    rewrite additiveUI_moebius// ffunE.
    case (#|A|==1)%N=>//.
    rewrite -H0.
    exact: monotonic0.
    Qed.


    
  End NumSetFunctions.


  Section RealSetFunctions.

    Variable R : realDomainType.

    Implicit Type mu : {ffun {set T} -> R}.

    Open Scope ring_scope.
    Import Order Order.POrderTheory Order.TotalTheory.
    
    Section QualitativeMoebiusTransform.

      Definition qmoebius mu : {ffun {set T} -> R} :=
        [ffun A : {set T} => if [forall t, (t \in A) ==> (mu A > mu (A :\ t))]
                            then mu A else mu set0].
      
      Lemma qmoebius_ge0 mu :
        monotonic mu -> forall A, qmoebius mu A >= mu set0.
      Proof.
      move=>Hmon ; apply: card_ind=>A IH.
      rewrite ffunE.
      case (boolP [forall t, (t \in A) ==> (mu (A :\ t) < mu A)])=>H//.
      by rewrite monotonic0.
      Qed.

      Lemma qmoebius_subset mu :
        monotonic mu -> forall A B, A \subset B -> qmoebius mu A <= mu B.
      Proof.
      move=>Hmon ; apply: card_ind=>A IH B HAB.
      rewrite ffunE.
      case (boolP [forall t, (t \in A) ==> (mu (A :\ t) < mu A)])=>H.
      - exact: monotonicS.
      - exact: monotonic0.
      Qed.

      Lemma qmoebiusE mu :
        monotonic mu ->
        forall A, mu A = \big[Num.max/mu set0]_(B : {set T} | B \subset A) qmoebius mu B.
      Proof.
      move=>Hmon ; apply: card_ind=>A IH.
      case (boolP [forall t, (t \in A) ==> (mu A > mu (A :\ t))])=>H.
      - have HqmA : mu A = qmoebius mu A by rewrite ffunE H.
        have Hle : \big[Num.max/mu set0]_(B : {set T} | B \subset A) qmoebius mu B >= mu A
          by rewrite HqmA ; exact: (TotalTheory.le_bigmax_cond (mu set0) (qmoebius mu)).
        have Hge : \big[Num.max/mu set0]_(B : {set T} | B \subset A) qmoebius mu B <= mu A.
        apply: bigmax_le=>[|/=B HBA] ; first exact: monotonic0.
        rewrite ffunE ; case [forall t, (t \in B) ==> (mu (B :\ t) < mu B)].
        * exact: monotonicS.
        * exact: monotonic0.
        by apply/eqP ; rewrite eq_le Hle Hge.
      - have [t Ht] := existsP H.
        rewrite negb_imply -leNgt in Ht.
        have [HtA Htmu] := andP Ht.
        have HAt : mu A = mu (A :\ t)
          by apply/eqP ; rewrite eq_le monotonicD// Htmu.
        rewrite HAt.
        have Hcard :  (#|A :\ t| < #|A|)%N  by rewrite [E in (_<E)%N](cardsD1 t) HtA.
        rewrite IH//.
        symmetry.
        rewrite (bigmaxID _ (fun B : {set T} => B \subset A :\ t))/=.
        rewrite (eq_bigl (fun B : {set T} => B \subset A :\ t))=>[/=|B].
        apply: max_l.
        rewrite -IH//-HAt.
        apply: bigmax_le=>//[|B/andP [HBA _]].
        - exact: monotonic0.
        - exact: qmoebius_subset.
        - case (boolP (B \subset A))=>HBA.
          + by rewrite andTb.
          + by rewrite subsetD1 (negbTE HBA) !andFb.
      Qed.

      Lemma qmoebius0 mu : qmoebius mu set0 = mu set0.
      Proof. by rewrite ffunE if_same. Qed.

      Lemma qmoebius1 mu t :
        monotonic mu -> qmoebius mu [set t] = mu [set t].
      Proof.
      rewrite ffunE=>Hmon.
      case (boolP [forall t0, (t0 \in [set t]) ==> (mu ([set t] :\ t0) < mu [set t])])=>///existsP [t'].
      rewrite negb_imply in_set1 -leNgt=>/andP[/eqP->].
      rewrite setDv=>Hle.
      apply/eqP ; by rewrite eq_le Hle monotonic0.
      Qed.


      Lemma qmoebius_maxSE_Some mu A :
        monotonic mu ->
        Some (mu A) = maxS (qmoebius mu) [set B : {set T} | B \subset A].
      Proof.
      move=>Hmon.
      have Hset0 : set0 \in [set B : {set T} | B \subset A]
        by rewrite !inE sub0set.
      rewrite (maxSE _ Hset0).
      congr (Some _).
      rewrite qmoebiusE// qmoebius0.
      by under [in RHS]eq_bigl do rewrite inE.
      Qed.

      Lemma qmoebius_maxSE mu :
        monotonic mu -> 
        mu = [ffun A : {set T} => match maxS (qmoebius mu)  [set B : {set T} | B \subset A] with
                            | Some x => x
                            | _ => mu set0
                                 end].
      Proof.
      move=>Hmon ; apply/ffunP=>/=A.
      by rewrite ffunE -qmoebius_maxSE_Some.
      Qed.

      Definition oqmoebius mu := [ffun A : {set T} => Some (qmoebius mu A)].

      Lemma is_massfun_oqmoebius mu :
        monotonic mu -> 
        is_massfun None (@omax _ R) [ffun A => Some (mu A)] (oqmoebius mu).
      Proof.
      move=>Hmon A/=.
      rewrite !ffunE qmoebius_maxSE_Some///maxS.
      by under eq_bigl do rewrite inE ; under [in RHS]eq_bigr do rewrite ffunE.
      Qed.

      Lemma is_massfun_qmoebius mu :
        monotonic mu ->
        is_massfun (mu set0) max mu (qmoebius mu).
      Proof.
      Check qmoebiusE.
      exact: qmoebiusE. Qed.       

    End QualitativeMoebiusTransform.

  End RealSetFunctions.
End SetFunctions.
