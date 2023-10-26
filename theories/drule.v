(* ************************************************************************************ *)
(* Decision rule

   Rules
     - Expected utility
     - Choquet utility
     - Jaffray utility
     - TBM utility (Smets)
     - Wald = min
     - Laplace
     - Hurwicz
     - Upess
     - Uopt

   Rule instances for XEU

 *)
(* ************************************************************************************ *)

From HB Require Import structures.
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)

Import Num Num.Theory.
Import GRing GRing.Theory.
Import Order Order.TotalTheory Order.POrderTheory.

(* Local libraries *)
From BelGames Require Import minmax fintype finset ssrnum setfun.
From BelGames Require Import massfun capacity.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




(*
Definition prefs d (R : porderType d) (T : finType) := {ffun T -> R}.
Definition kn d (R : porderType d) (T : finType) := {ffun {set T} -> R}.
 *)


Section DRule.
  Variable dU : Datatypes.unit.
  Variable U : porderType dU.
  Variable dV : Datatypes.unit.
  Variable V : porderType dV.

  Implicit Type X : Type.
  Implicit Type T : finType.

  Definition drule dispU (U : porderType dispU)
  dispV (V : porderType dispV)
  (knType : forall (T : finType), Type) :=
    forall X T, (X -> V) -> knType T -> (T -> X) -> U.
  
  Definition drule2 dispU (U : porderType dispU)
                    dispV (V : porderType dispV)
                    dispW (W : porderType dispW) :=
    forall X T, (X -> V) -> ({set T} -> W) -> (T -> X) -> U.

  Definition f_agg_type : Type := (forall (X : finType), (X -> V) -> {set X} -> V).

  Definition f_agg_axiom (f_agg : f_agg_type) : Prop :=
    forall (X Y : finType) (f : X -> Y) (g1 : X -> V) (g2 : Y -> V) (A : {set X}),
      (forall x, x \in A -> g1 x = g2 (f x)) ->
      #|[set f x | x in A]| == #|A| ->
      f_agg X g1 A = f_agg Y g2 [set f x | x in A].

  Structure zinst dW (W : porderType dW) := 
    { z_idw : W ;
      z_op_mfun : SemiGroup.com_law W ;
      z_idu : U ;
      z_oplus : SemiGroup.com_law U ;
      z_otimes : W -> V -> U ;
      z_f_agg : f_agg_type ;
      z_f_agg_ax : f_agg_axiom z_f_agg}.

  Definition XEU dW (W : porderType dW) (zi : zinst W) X T :
    (X -> V) -> {ffun {set T} -> W} -> (T -> X) -> U :=
    fun v m chi =>
      \big[z_oplus zi/z_idu zi]_(B : {set T}) z_otimes zi (m B) (z_f_agg zi (fun t => v (chi t)) B).

  (*
  Lemma XEU_eq dW (W : porderType dW) (zi : zinst W) (X : finType) T :
    forall v m chi,
      XEU zi v m (chi : T -> X)
      = \big[z_oplus zi/z_idu zi]_(B : {set T}) z_otimes zi (m B) (z_f_agg zi (v) [set chi t | t in B]).
  Proof.
  move=>v m chi.
  apply: eq_bigr=>/=A _.
  congr (z_otimes _ _).
  by rewrite z_f_agg_ax.
  Qed.
   *)

End DRule.

  



Section NumDRules.

  Variable R : realFieldType.
  Implicit Type X : Type.
  Implicit Type T : finType.

  Open Scope ring_scope.

  Section DRules.

    (** Expected utility *)
    Definition EU X T (v : X -> R) (p : prdist R T) chi := \sum_t v (chi t) * p t.
    Definition ExpectedUtility : drule R R (probability R) :=
      fun X T (v : X -> R) (w : probability R T) chi =>
        EU v (prdist_of_probability w) chi.
    
    Definition ExpectedUtility2 : drule2 R R R :=
      fun X T v w chi =>
        \sum_t w [set t] * v (chi t).



    
    (** Choquet *)
    Definition Choquet : drule R R (capacity R) :=
      fun X T v w chi =>
        \sum_(A : {set T}) moebius w A * minSb 0 (fun t => v (chi t)) A.
    Definition Choquet2 : drule2 R R R :=
      fun X T v w chi =>
        \sum_(A : {set T}) moebius w A * minSb 0 (fun t => v (chi t)) A.
    (*
        \sum_(A : {set T}) moebius w A * match minSb (fun t => v (chi t)) A with
                                         | Some x => x | None => 0
                                         end.
     *)

    (** Jaffray *)
    Definition Jaffray (alpha : R -> R -> R)  : drule R R (capacity R) :=
      fun X T v w chi =>
        \sum_(A : {set T})
        let vmin :=  minSb 0 (fun t => v (chi t)) A in
        let vmax :=  maxSb 0 (fun t => v (chi t)) A in
        moebius w A * ((alpha vmin vmax) * vmin + (1 - alpha vmin vmax) * vmax).
    
    Definition Jaffray2 (alpha : R -> R -> R)  : drule2 R R R :=
      fun X T v w chi =>
        \sum_(A : {set T})
        let vmin :=  minSb 0 (fun t => v (chi t)) A in
        let vmax :=  maxSb 0 (fun t => v (chi t)) A in
        moebius w A * ((alpha vmin vmax) * vmin + (1 - alpha vmin vmax) * vmax).


    (** TBM *)
    Definition BetP T (w : {ffun {set T} -> R}) : {ffun T -> R} :=
      [ffun t => \sum_(A : {set T} | t \in A) moebius w A / #|A|%:R].

    Lemma BetP_ge0 T (w : belief_function R T) : forall t, 0 <= BetP w t.
    Proof.
    move=>t.
    rewrite ffunE.
    apply: sumr_ge0=>/= A _.
    apply: divr_ge0.
    - exact: massfun_ge0.
    - exact: ler0n.
    Qed.

    Lemma BetP_sum1 T (w : capacity R T) : \sum_t BetP w t = 1.
    under eq_bigr do rewrite ffunE.
                     rewrite  sum_of_sumE.
                     under eq_bigr do rewrite -big_distrr /=.
                                      rewrite (bigD1 set0)//=.
                                      rewrite moebius0 pointed0 ?capa01// mul0r add0r.
                                      rewrite (eq_bigr (moebius w))=>[|A HA].
                                      - have [_ /eqP] := andP (pointed_moebius (capa01 (s:=w))).
                                        by rewrite (bigD1 set0)//= moebius0 pointed0 ?capa01// add0r.
                                      - rewrite sum_carddiv ; first by rewrite mulr1.
                                        by rewrite card_gt0.
    Qed.

    HB.instance Definition _ T (w : belief_function R T) :=
      PrDist_of_Ffun.Build R T _ (BetP_ge0 w) (BetP_sum1 w).

    Definition BetPr T (w : belief_function R T) :=
      probability_of_prdist (BetP w).

    Definition TBEU : drule R R (belief_function R) :=
      fun X T v w chi => ExpectedUtility v (BetPr w) chi.

    Definition TBEU2 : drule2 R R R :=
      fun X T v w chi => \sum_t (BetP [ffun A : {set T} => w A] t) * (v (chi t)).

    Definition Wald : drule R R (categorical_capacity R) :=
      fun X T v w chi => minSb 0 (fun t => v (chi t)) [set t | categorical_dist (s:=w) t].

    Definition Laplace : drule R R (categorical_capacity R) :=
      fun X T v w chi =>
        let worlds := [set t | categorical_dist (s:=w) t] in
        \sum_(t in worlds) v (chi t) / #|worlds|%:R.

    Definition Hurwicz (alpha : R) : drule R R (categorical_capacity R) :=
      fun X T v w chi =>
        let vmin := minSb 0 (fun t => v (chi t)) [set t | categorical_dist (s:=w) t] in
        let vmax := maxSb 0 (fun t => v (chi t)) [set t | categorical_dist (s:=w) t] in
        alpha * vmin + (1 - alpha) * vmax.

    (** Possibilistic utility *)
    
    Definition Uopt : drule2 R R R :=
      fun X T v w chi =>
        \big[max/0]_t min (qmoebius [ffun A : {set T} => w A] [set t]) (v (chi t)).

    Definition Upes : drule2 R R R :=
      fun X T v w chi =>
        \big[min/0]_t max (1 - qmoebius [ffun A : {set T} => w A] [set t]) (v (chi t)).
  
  End DRules.


  Section ZInstances.



    Definition minf : f_agg_type R := fun T (u : T -> R) B => minSb 0 u B.
    Lemma minf_correct : f_agg_axiom minf.
    Proof.
    move=>X Y f g1 g2 A Heq _.
    rewrite/minf.
    rewrite -minSb_imset.
    exact: minSb_eq=>x _.
    Qed.

    Definition minmaxf alpha : f_agg_type R :=
      fun T (u : T -> R) B => 
        let vmin := minSb 0 u B in
        let vmax := maxSb 0 u B in
        alpha vmin vmax * vmin + (1-alpha vmin vmax) * vmax.

    Lemma minmaxf_correct alpha : f_agg_axiom (minmaxf alpha).
    Proof.
    move=>X Y j g1 g2 A Heq _.
    rewrite/minmaxf.
    rewrite -minSb_imset -maxSb_imset.
    rewrite (minSb_eq 0 (F2:=g1)) ?(maxSb_eq 0 (F2:=g1))=>//t Ht ; by rewrite Heq.
    Qed.

    Definition moyf : f_agg_type R :=
      fun T (u : T -> R) B => \sum_(x in B) u x / #|B|%:R.

    Lemma moyf_correct : f_agg_axiom moyf.
    Proof.
    move=>X Y f g1 g2 A Heq Hcard.
    rewrite/moyf.
    rewrite big_imset=>/=[|x y Hx Hy Hxy].
    - apply: eq_bigr=>x Hx.
      by rewrite Heq// (eqP Hcard).
    - exact: imset_injP Hcard x y Hx Hy Hxy.
    Qed.

    Definition zJaffray (alpha : R -> R -> R) : zinst R R R :=
      {| z_idw := 0 ;
        z_op_mfun := +%R ;
        z_idu := 0 ;
        z_oplus := +%R ;
        z_otimes := *%R ;
        z_f_agg_ax := minmaxf_correct alpha |}.

    Definition zChoquet : zinst R R R :=
      {| z_idw := 0 ;
        z_op_mfun := +%R ;
        z_idu := 0 ;
        z_oplus := +%R ;
        z_otimes := *%R ;
        z_f_agg_ax := minf_correct |}.

    Definition zTBM : zinst R R R :=
      {| z_idw := 0 ;
        z_op_mfun := +%R ;
        z_idu := 0 ;
        z_oplus := +%R ;
        z_otimes := *%R ;
        z_f_agg_ax := moyf_correct |}.


    Definition zUopt : zinst R R R :=
      {| z_idw := 0 ;
        z_op_mfun := max ;
        z_idu := 0 ;
        z_oplus := max ;
        z_otimes := min ;
        z_f_agg_ax := minf_correct |}.

    Definition zUpes : zinst R R R :=
      {| z_idw := 0 ;
        z_op_mfun := max ;
        z_idu := 0 ;
        z_oplus := min ;
        z_otimes := fun w v => max (1-w) v ;
        z_f_agg_ax := minf_correct |}.


  End ZInstances.

  Section ZInstance_Correct.

    Variable X : Type.
    Variable T : finType.
    Implicit Type v : X -> R.
    Implicit Type w : capacity R T.
    Implicit Type m : rmassfun R T.
    Implicit Type chi : {ffun T -> X}.
    

    Lemma ExpectedUtilityE v (w : probability R T) chi :
      ExpectedUtility v w chi = \sum_t w [set t] * v (chi t).
    Proof.
    rewrite/ExpectedUtility/EU/prdist_of_probability/=.
    by under eq_bigr do rewrite ffunE mulrC.
    Qed.
    


    Lemma Jaffray_Choquet v (w : capacity R T) chi :
      Jaffray (fun _ _ => 1) v w chi = Choquet v w chi.
    Proof.
    apply: eq_bigr=>/=A _.
    by rewrite subrr mul0r mul1r addr0.
    Qed.

    Lemma Jaffray_EU alpha v (w : probability R T) chi :
      Jaffray alpha v w chi = ExpectedUtility v w chi.
    Proof.
    rewrite /Jaffray/ExpectedUtility/prdist_of_probability/=.
    under eq_bigr do rewrite pr_moebiusE ffunE (fun_if (fun x => x * _)) mul0r. 
                     rewrite -big_mkcond big_card1/=. 
                     apply: eq_bigr=>t _.
                     rewrite minSb1 maxSb1 mulrC ffunE.
                     congr (_ * _).
                     by rewrite mulrDl mul1r mulNr [E in _+E=_]addrC addrA subrr add0r.
    Qed.

    
    Lemma zJaffray_JEU alpha v w chi :
      Jaffray alpha v w chi = XEU (zJaffray alpha) v (moebius w) chi.
    Proof. by []. Qed.
    
    Lemma zJaffray_JEU2 alpha v w chi :
      Jaffray2 alpha v w chi = XEU (zJaffray alpha) v (moebius w) chi.
    Proof. by []. Qed.

    Lemma zJaffray_JEU' alpha v w m chi :
      is_massfun (z_idw (zJaffray alpha)) (z_op_mfun (zJaffray alpha)) w m ->
      Jaffray alpha v w chi = XEU (zJaffray alpha) v m chi.
    Proof.
    move=>Hm/=.
    rewrite (moebius_unique Hm).
    exact: zJaffray_JEU.
    Qed.
    
    Lemma Jaffray_Hurwicz alpha beta v (w : categorical_capacity R T) chi :
      (forall x y, alpha x y = beta) 
      -> Jaffray alpha v w chi = Hurwicz beta v w chi.
    Proof.
    rewrite /Jaffray/Hurwicz=>Hab/=.
    rewrite (bigD1 [set t | categorical_dist (s:=w) t])//= big1?addr0=>[|t].
    - by rewrite -( moebius_unique (categorical_massfunE w)) ffunE eqxx mul1r Hab.
    - rewrite -( moebius_unique (categorical_massfunE w)) ffunE=>H.
      by rewrite (negbTE H) mul0r.
    Qed.

    Lemma zJaffray_Hurwicz alpha beta v (w : categorical_capacity R T) chi :
      (forall x y, alpha x y = beta) 
      -> Hurwicz beta v w chi = XEU (zJaffray alpha) v (moebius w) chi.
    Proof.
    move=>Hab.
    rewrite -(Jaffray_Hurwicz v w chi Hab).
    exact: zJaffray_JEU.
    Qed.

    Lemma zJaffray_Hurwicz' alpha beta v (w : categorical_capacity R T) m chi :
      (forall x y, alpha x y = beta) 
      -> is_massfun (z_idw (zJaffray alpha)) (z_op_mfun (zJaffray alpha)) w m ->
      Hurwicz beta v w chi = XEU (zJaffray alpha) v m chi.
    Proof.
    move=>Hab Hm ; rewrite (moebius_unique Hm).
    exact: zJaffray_Hurwicz.
    Qed.

    
    Lemma zChoquet_CEU v w chi :
      Choquet v w chi = XEU zChoquet v (moebius w) chi.
    Proof.
    by [].
    Qed.

    Lemma zChoquet_CEU' v w m chi :
      is_massfun (z_idw zChoquet) (z_op_mfun zChoquet) w m
      -> Choquet v w chi = XEU zChoquet v m chi.
    Proof.
    move=>Hm ; rewrite (moebius_unique Hm).
    exact: zChoquet_CEU.
    Qed.

    Lemma zJaffray_zChoquet v w m chi :
      XEU (zJaffray (fun _ _ => 1)) v (moebius w) chi = XEU zChoquet v (moebius w) chi.
    Proof.
    rewrite -zJaffray_JEU -zChoquet_CEU.
    exact: Jaffray_Choquet.
    Qed.

    Lemma Choquet_EU v (w : probability R T) chi :
      Choquet v w chi = ExpectedUtility v w chi.
    Proof.
    rewrite -Jaffray_Choquet.
    exact: Jaffray_EU.
    Qed.

    Lemma zChoquet_EU v (w : probability R T) chi :
      ExpectedUtility v w chi = XEU zChoquet v (moebius w) chi.
    Proof.
    rewrite -Choquet_EU.
    exact: zChoquet_CEU.
    Qed.
    
    Lemma zChoquet_EU' v (w : probability R T) m chi :
      is_massfun (z_idw zChoquet) (z_op_mfun zChoquet) w m
      -> ExpectedUtility v w chi = XEU zChoquet v m chi.
    Proof.
    move=>Hm ; rewrite (moebius_unique Hm).
    exact: zChoquet_EU.
    Qed.

    Lemma Choquet_Wald v (w : categorical_capacity R T) chi :
      Choquet v w chi = Wald v w chi.
    Proof.
    rewrite/Choquet/Wald.
    rewrite (bigD1 [set t | categorical_dist (s:=w) t])//= big1?addr0=>[|t].
    - by rewrite -( moebius_unique (categorical_massfunE w)) ffunE eqxx mul1r.
    - rewrite -( moebius_unique (categorical_massfunE w)) ffunE=>H.
      by rewrite (negbTE H) mul0r.
    Qed.

    Lemma zChoquet_Wald v (w : categorical_capacity R T) chi :
      Wald v w chi = XEU zChoquet v (moebius w) chi.
    Proof.
    rewrite -Choquet_Wald.
    exact: zChoquet_CEU.
    Qed.

    Lemma zChoquet_Wald' v (w : categorical_capacity R T) m chi :
      is_massfun (z_idw zChoquet) (z_op_mfun zChoquet) w m
      -> Wald v w chi = XEU zChoquet v  m chi.
    Proof.
    move=>Hm ; rewrite (moebius_unique Hm).
    exact: zChoquet_Wald.
    Qed.
    
    Lemma zJaffray_CEU' v (w : capacity R T) m chi :
      is_massfun (z_idw (zJaffray (fun _ _ =>1))) (z_op_mfun (zJaffray (fun _ _ =>1))) w m
      -> Choquet v w chi = XEU (zJaffray (fun _ _=>1)) v m chi.
    Proof.
    move=>Hm.
    rewrite (moebius_unique Hm).
    rewrite (zJaffray_zChoquet v w m).
    exact: zChoquet_CEU.
    Qed.

    Lemma zJaffray_EU' alpha v (w : probability R T) m chi :
      is_massfun (z_idw (zJaffray alpha)) (z_op_mfun (zJaffray alpha)) w m
      -> ExpectedUtility v w chi = XEU (zJaffray alpha) v m chi.
    Proof.
    move=>Hm.
    by rewrite (moebius_unique Hm) -zJaffray_JEU Jaffray_EU.
    Qed.



    

    Lemma TBEUE v (w : belief_function R T) chi :
      TBEU v w chi = \sum_(A : {set T}) moebius w A * \sum_(t in A) v (chi t) / #|A|%:R.
    Proof.
    rewrite/TBEU/ExpectedUtility/EU/BetPr/=.
    under eq_bigr do rewrite !ffunE big_set1 ffunE.
                     have Hl B : moebius w B * (\sum_(t in B) v (chi t) / #|B|%:R) = (\sum_(t in B) moebius w B * v (chi t) / #|B|%:R)
                       by rewrite big_distrr /= ; under eq_bigr do rewrite mulrA.
                                                                   have Hr t : (\sum_(B : {set T} | t \in B) moebius w B / #|B|%:R) * v (chi t) = (\sum_(B : {set T} | t \in B) moebius w B * v (chi t) / #|B|%:R)
                                                                     by rewrite big_distrl /= ; under eq_bigr do rewrite mulrC mulrA (mulrC (v _)).
                                                                                                                 under [RHS]eq_bigr do rewrite Hl.
                                                                                                                                       under [LHS]eq_bigr do rewrite mulrC Hr.
                                                                                                                                                             by symmetry ; exact: big_partitionS.
    Qed.

    
    Lemma TBEU_EU v (w : probability R T) chi :
      TBEU v w chi = ExpectedUtility v w chi.
    Proof.
    rewrite /TBEU/ExpectedUtility/prdist_of_probability/EU/=.
    under eq_bigr do rewrite/BetP pr_moebiusE ffunE.
    apply: eq_bigr=>t _.
    congr (_ * _).
    rewrite !ffunE big_set1 ffunE.
    rewrite (bigD1 [set t])/= ; last by rewrite in_set1.
    rewrite ffunE big1 ?cards1 ?eqxx ?addr0 ?divr1=>//A.
    move=>/andP [Ht HA].
    have Hcard : #|A| != 1%N
      by apply/negP=>/cards1P [x Hx] ; rewrite Hx in_set1 in Ht ;
                      rewrite (eqP Ht) Hx eqxx in HA.
    by rewrite ffunE (negbTE Hcard) mul0r.
    Qed.

    

    Lemma zTBM_TBEU v (w : belief_function R T) chi :
      TBEU v w chi = XEU zTBM v (moebius w) chi.
    Proof.
    by rewrite TBEUE.
    Qed.

    Lemma zTBM_TBEU' v (w : belief_function R T) m chi :
      is_massfun (z_idw zTBM) (z_op_mfun zTBM) w m
      -> TBEU v w chi = XEU zTBM v m chi.
    Proof.
    move=>Hm.
    rewrite (moebius_unique Hm).
    exact: zTBM_TBEU.
    Qed.

    Lemma zTBM_EU v (w : probability R T) m chi :
      is_massfun (z_idw zTBM) (z_op_mfun zTBM) w m
      -> ExpectedUtility v w chi = XEU zTBM v m chi.
    Proof.
    move=>Hm.
    rewrite -(zTBM_TBEU' _ _ Hm).
    by symmetry ; exact: TBEU_EU.
    Qed.


    Lemma TBEU_Laplace v (w : categorical_capacity R T) chi :
      TBEU v w chi = Laplace v w chi.
    Proof.
    rewrite /TBEU/ExpectedUtility/prdist_of_probability/EU/Laplace/=.
    rewrite [in RHS]big_mkcond.
    apply: eq_big=>//= t _.
    rewrite !ffunE.
    - case (boolP (t \in [set t0 | categorical_dist (s:=w) t0]))=>H.
      rewrite big_set1 ffunE.
      rewrite -(moebius_unique (categorical_massfunE w)).
      congr (_ * _).
      rewrite (bigD1 [set t0 | categorical_dist (s:=w) t0])//= ffunE eqxx div1r big1 ?addr0=>//= A/andP [_ HA].
      by rewrite ffunE (negbTE HA) mul0r.
    - rewrite big_set1 ffunE big1 ?mulr0=>//=A HA.
      rewrite -(moebius_unique (categorical_massfunE w)) ffunE.
      case (boolP (A == [set t0 | categorical_dist (s:=w) t0] ))=>/= [Hcontra|H'] ; 
        last by rewrite (negbTE H') mul0r.
      by rewrite -(eqP Hcontra) HA in H.
    Qed.

    Lemma zTBM_Laplace v (w : categorical_capacity R T) m chi :
      is_massfun (z_idw zTBM) (z_op_mfun zTBM) w m
      -> Laplace v w chi = XEU zTBM v m chi.
    Proof.
    move=>Hm.
    rewrite -TBEU_Laplace.
    exact: zTBM_TBEU'.
    Qed.

    (*
    Lemma zUopt_Uopt v (w : possibility R T) m chi :
      is_massfun (z_idw zUpes) (z_op_mfun zUopt) w m
      -> Uopt v w chi = XEU zUopt v m chi.
    Proof.
    move=>Hm.
    rewrite/Uopt/XEU/=.

    Lemma zUpes_Wald v (w : categorical_capacity R T) m chi :
      is_massfun (z_idw zUpes) (z_op_mfun zUpes) w m
      -> Wald v w chi = XEU zUpes v m chi.
    Proof.
    move=>Hm.
    rewrite/Wald/XEU/=.
     *)
    
  End ZInstance_Correct.
  
End NumDRules.

Section XEUMassFunction.

  Section XEUmDef.
    Variable R : eqType.
    Variable T : finType.
    Variable idx : R.
    Variable op : SemiGroup.com_law R.

    Definition XEUm idz oplus (otimes : R -> R -> R) T (m : massfun T idx op) (phi_u_chi : {set T} -> R) :=
      \big[oplus/idz]_(A : {set T}) otimes (m A) (phi_u_chi A).

  End XEUmDef.


  Section XEUmZInstance.

    
    Variable R : numDomainType.
    Variable zi : zinst R R R.
    
    Lemma XEU_XEUm (X T : finType) (v : X -> R) (m : massfun T (z_idw zi) (z_op_mfun zi)) chi :
      XEU zi v m chi = XEUm (z_idu zi) (z_oplus zi) (z_otimes zi) m (z_f_agg zi (fun t => v (chi t))).
    Proof. exact: eq_bigr. Qed.

  End XEUmZInstance.

End XEUMassFunction.
