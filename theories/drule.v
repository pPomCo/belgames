From HB Require Import structures.
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)

Import Num Num.Theory.
Import GRing GRing.Theory.
Import Order Order.TotalTheory Order.POrderTheory.

(* Local libraries *)
From decision Require Import minmax fintype finset ssrnum setfun.
From decision Require Import massfun capacity.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.





Definition prefs d (R : porderType d) (T : finType) := {ffun T -> R}.
Definition kn d (R : porderType d) (T : finType) := {ffun {set T} -> R}.


Section DRule.
  Variable dU : Datatypes.unit.
  Variable U : porderType dU.
  Variable dV : Datatypes.unit.
  Variable V : porderType dV.

  Definition drule dispU (U : porderType dispU)
  dispV (V : porderType dispV)
  (knType : forall (T : finType), Type) :=
    forall X T, prefs V X -> knType T -> (T -> X) -> U.


  Structure zinst dW (W : porderType dW) := 
    { z_idw : W ;
      z_op_mfun : Monoid.com_law z_idw ;
      z_idu : U ;
      z_oplus : Monoid.com_law z_idu ;
      z_otimes : W -> V -> U ;
      z_f_agg : forall (X : finType), (X -> V) -> {set X} -> V }.

  (*
  Definition is_repr dW (W : porderType dW) (T : finType) : {ffun {set T} -> W} -> {ffun {set T} -> W} -> forall idx : W, Monoid.com_law idx -> bool.
  Admitted.
   *)

  Definition XEU dW (W : porderType dW) (zi : zinst W) (X T : finType) :
    prefs V X -> kn W T -> (T -> X) -> U :=
    fun v m chi =>
      \big[z_oplus zi/z_idu zi]_(B : {set T}) z_otimes zi (m B) (z_f_agg zi (fun t => v (chi t)) B).

End DRule.


Section NumDRules.

  Variable R : realFieldType.
  Implicit Type X T : finType.

  Open Scope ring_scope.

  Section DRules.

    (** Expected utility *)
    Definition EU X T (v : prefs R X) (p : prdist R T) chi := \sum_t v (chi t) * p t.
    Definition ExpectedUtility : drule R R (probability R) :=
      fun X T (v : prefs R X) (w : probability R T) chi =>
        EU v (prdist_of_probability w) chi.


    (** Choquet *)
    Definition Choquet : drule R R (capacity R) :=
      fun X T v w chi =>
        \sum_(A : {set T}) moebius w A * match minS (fun t => v (chi t)) A with
                                         | Some x => x | None => 0
                                         end.

    (** Jaffray *)
    Definition Jaffray (alpha : R -> R -> R)  : drule R R (capacity R) :=
      fun X T v w chi =>
        \sum_(A : {set T})
        let vmin :=  match minS (fun t => v (chi t)) A with Some x => x | None => 0%R end in
        let vmax :=  match maxS (fun t => v (chi t)) A with Some x => x | None => 0%R end in
        moebius w A * ((alpha vmin vmax) * vmin + (1 - alpha vmin vmax) * vmax).


    (** TBM *)
    Definition BetP T (w : capacity R T) : {ffun T -> R} :=
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

    Definition Wald : drule R R (categorical_capacity R) :=
      fun X T v w chi => match minS (fun t => v (chi t)) [set t | categorical_dist (s:=w) t] with
                       | Some x => x | None => 0 end.

    Definition Laplace : drule R R (categorical_capacity R) :=
      fun X T v w chi =>
        let worlds := [set t | categorical_dist (s:=w) t] in
        \sum_(t in worlds) v (chi t) / #|worlds|%:R.

    Definition Hurwicz (alpha : R) : drule R R (categorical_capacity R) :=
      fun X T v w chi =>
        let vmin := match minS (fun t => v (chi t)) [set t | categorical_dist (s:=w) t] with
                       | Some x => x | None => 0 end in
        let vmax := match maxS (fun t => v (chi t)) [set t | categorical_dist (s:=w) t] with
                    | Some x => x | None => 0 end in
        alpha * vmin + (1 - alpha) * vmax.

    (** Possibilistic utility *)
  (*
  Definition Uopt v (p : pidist R T) chi :=
    \big[max/0]_t min (v (chi t)) (p t).
  
  Definition Upess v (p : pidist R T) chi :=
    \big[max/0]_t min (v (chi t)) (p t).
   *)
  End DRules.


  Section ZInstances.

    Definition zJaffray (alpha : R -> R -> R) : zinst R R R :=
      {| z_op_mfun := +%R ;
        z_oplus := +%R ;
        z_otimes := *%R ;
        z_f_agg := fun X u B =>
                     let vmin := match minS u B with Some x => x | None => 0 end in 
                     let vmax := match maxS u B with Some x => x | None => 0 end in
                     alpha vmin vmax * vmin + (1-alpha vmin vmax) * vmax |}.

    Definition zChoquet : zinst R R R :=
    {| z_op_mfun := +%R ;
      z_oplus := +%R ;
      z_otimes := *%R ;
      z_f_agg := fun X u B => match minS u B with Some x => x | None => 0 end |}.

    Definition zTBM : zinst R R R :=
      {| z_op_mfun := +%R ;
        z_oplus := +%R ;
        z_otimes := *%R ;
        z_f_agg := fun X u B => \sum_(x in B) u x / #|B|%:R |}.


  End ZInstances.

  Section ZInstance_Correct.

    Variable X T : finType.
    Implicit Type v : prefs R X.
    Implicit Type w : capacity R T.
    Implicit Type m : {ffun {set T} -> R}.
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
                     rewrite minS1 maxS1 mulrC ffunE.
                     congr (_ * _).
                     by rewrite mulrDl mul1r mulNr [E in _+E=_]addrC addrA subrr add0r.
    Qed.

    

    Lemma zJaffray_JEU alpha v w chi :
      Jaffray alpha v w chi = XEU (zJaffray alpha) v (moebius w) chi.
    Proof. by []. Qed.

    Lemma zJaffray_JEU' alpha v w m chi :
      is_mass_function (z_op_mfun (zJaffray alpha)) w m ->
      Jaffray alpha v w chi = XEU (zJaffray alpha) v m chi.
    Proof.
    move=>Hm ; rewrite (moebius_unique Hm).
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
      -> is_mass_function (z_op_mfun (zJaffray alpha)) w m ->
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
      is_mass_function (z_op_mfun zChoquet) w m
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
      is_mass_function (z_op_mfun zChoquet) w m
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
      is_mass_function (z_op_mfun zChoquet) w m
      -> Wald v w chi = XEU zChoquet v  m chi.
    Proof.
    move=>Hm ; rewrite (moebius_unique Hm).
    exact: zChoquet_Wald.
    Qed.
    
    Lemma zJaffray_CEU' v (w : capacity R T) m chi :
      is_mass_function (z_op_mfun (zJaffray (fun _ _ =>1))) w m
      -> Choquet v w chi = XEU (zJaffray (fun _ _=>1)) v m chi.
    Proof.
    move=>Hm.
    rewrite (moebius_unique Hm).
    rewrite (zJaffray_zChoquet v w m).
    exact: zChoquet_CEU.
    Qed.

    Lemma zJaffray_EU' alpha v (w : probability R T) m chi :
      is_mass_function (z_op_mfun (zJaffray alpha)) w m
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
      is_mass_function (z_op_mfun zTBM) w m
      -> TBEU v w chi = XEU zTBM v m chi.
    Proof.
    move=>Hm.
    rewrite (moebius_unique Hm).
    exact: zTBM_TBEU.
    Qed.

    Lemma zTBM_EU v (w : probability R T) m chi :
      is_mass_function (z_op_mfun zTBM) w m
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
      case (boolP (A == [set t0 | categorical_dist (s:=w) t0] ))=>/= Hcontra ;
        last by rewrite mul0r.
      by rewrite -(eqP Hcontra) HA in H.
    Qed.

    Lemma zTBM_Laplace v (w : categorical_capacity R T) m chi :
      is_mass_function (z_op_mfun zTBM) w m
      -> Laplace v w chi = XEU zTBM v m chi.
    Proof.
    move=>Hm.
    rewrite -TBEU_Laplace.
    exact: zTBM_TBEU'.
    Qed.

    
    
  End ZInstance_Correct.

End NumDRules.
