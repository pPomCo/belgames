(******************************************************************************)
(** This file provide a theory for simultaneous games

   1. Profiles
   A profile assign a strategy (ai : A i) to each player (i : I)
   We distinguish:
   - Profiles for complete games : forall i, A i
   - Profiles for incomplete games : forall i, T i -> A i
   - Local profiles for HG games: forall i, P i -> A i

   cprofile A          == {dffun forall i : I, A i}
   iprofile A T        == cprofile (fun i => {ffun T i -> A i})
   local_cprofile P A  == {ffun forall (s : {i : I | P i}), A (val s)}

   We then define:
   change_strategy A p i ai       == the cprofile p where (p i) has changed to ai
   change_istrategy T A p i ti ai == the iprofile p where (p i ti) has changed to ai,
   And prove:
   change_strategy_id A p i :       p = change_strategy p (p i).
   change_istrategy_id T A p i ti : p = change_istrategy p ti (p i ti).

   Finally, we cast/project profiles with:
   iprofile_flatten T A p          == flatten (p : iprofile T A) to a cprofile
                                      {dffun forall s : {i : I & T i}, A i}
   proj_iprofile T A p t :         == project (p : iprofile T A) according to (t : cprofile T)
                                      i.e. proj_iprofile T A p t i = p (t i) i
   proj_flatprofile T A p :        == project the flat profile p according to (t : cprofile T)
                                      i.e. proj_flatprofile T A p t i = p (existT T i (t i))
   proj_flatlocalprofile T A P f p == project the flat local profile p according to f
                                      i.e. proj_flatlocalprofile T A P f p i = p (f i)

   And we prove:
   proj_iprof_flatprof T Y p t :
     proj_iprofile p t = proj_flatprofile (iprofile_flatten p) t.
   change_strat_istrat T A p i_ti ai :
     change_strategy (iprofile_flatten p) ai = iprofile_flatten (change_istrategy p (projT2 i_ti) ai).

   2. Games
   2.1. Complete games -- they are fully specified by their utility functions
   cgame R A                       == cprofile A -> I -> R (the type of complete games)
   Nash_equilibrium_bool G p       == true iff there is no (i : I) such as there is no (ai : A i)
                                      such that (G p i) < (G p (change_strategy p i ai))
   Nash_equilibrium G p            == True iff there is no (i : I) such as there is no (ai : A i)
                                      such that (G p i) < (G p (change_strategy p i ai))
   Nash_equilibriumP G p           == reflect (Nash_equilibrium G p) (Nash_equilibrium_bool G p)

   2.2. Hypergraphical games -- Particular sort of complete game where utility functions are
        decomposed into several local games. We index local games with (local_game : finType)
        and check whether (i : I) plays in (lg : local_game) using (plays_in : lg -> pred I).
        let localprof := (fun lg : localgame => local_cprofile action (plays_in lg))
        and localagent := (fun lg => {i | plays_in lg i}) in

   hg_game (u : forall lg, localprof lg -> localagent lg -> R)
      == fun a i => \sum_(s : {lg : localgame | plays_in lg i})
                      u (tag s) [ffun i => a (val i)] (exist _ i (tagged s)).
      == the complete game where utility functions are defined locally according to u

   Then we prove:
   hg_gameE u a i == \sum_(lg | plays_in lg i)
                         match boolP (plays_in lg i) with
                         | AltTrue h => u lg [ffun j => a (val j)] (exist (plays_in lg) i h)
                         | AltFalse _ => 0
                         end.

   3. BelGames -- Incomplete games where the knowledge is captured by a belief function.
   belgame R T                == ((bpa R (cprofile T)) * (profile -> (cprofile T) -> i -> R))
   proper_belgame G cond      == One can condition given (ti : T i) for all agent (i : I)
                                 according to (cond : conditioning (cprofile T))
   belgame_utility G cond xeu H p i == utility of p for i, according to the scoring function xeu,
                                 given that (H : proper_belgame G cond)
   BelG_Nash_equilibrium_bool G cond xeu H p
                              == true iff p is a Nash equilibrium according to (belgame_utility G cond xeu H p)
                                 i.e. there is no (i : I) such that there is no (ti : T i) such
                                 that there is no (ai : A i) such that (belgame_utility G cond xeu H p i)
                                 < (belgame_utility G cond xeu H (change_istrategy T A p i ti ai) i)
  BelG_Nash_equilibrium G cond xeu H p
  BelG_Nash_equilibriumP G cond xeu H p

  4. Mixed strategy profiles
  We show that they are descriptible by their mixed-extension
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


From decision Require Import fintype finset ssrnum.
From decision Require Import setfun massfun capacity conditioning drule.

Local Open Scope order_scope.

Section Profile.

  Implicit Types I : finType.

  Definition cprofile I (A : I -> eqType)
    := {dffun forall i : I, A i}.

  Definition iprofile I (A : I -> eqType) (T : I -> finType)
    := cprofile (fun i => {ffun T i -> A i}).

  Definition change_strategy I A (p : cprofile A) (i : I) (a'_i : A i) : cprofile A
    := [ffun j => match boolP (i == j) with
                  | AltTrue h => eq_rect _ A a'_i _ (eqP h)
                  | AltFalse _ => p j
                  end].

  Lemma change_strategy_id I A (p : cprofile A) (i : I) :
    p = change_strategy p (p i).
  Proof.
  apply ffunP => j ; rewrite ffunE.
  case (boolP (i == j)) => // H.
  by rewrite f_equal_dep.
  Qed.

  Definition local_cprofile I (A : I -> eqType) (P : pred I) :=
    {ffun forall (s : {x : I | P x}), A (val s)}.

  Definition localize I (A : I -> eqType) (P : pred I) (a : cprofile A) : local_cprofile A P :=
    [ffun s : {i : I | P i} => a (tag s)].

  (*| Transform an iprofile to a profile such as support is the set of dependent pairs (i,t_i) |*)
  Definition iprofile_flatten I (T : I -> finType) A (p : iprofile A T)
    : cprofile (fun i_ti => A (projT1 i_ti)) :=
    [ffun i_ti => p (projT1 i_ti) (projT2 i_ti)].

  (*| Profile that will be played if player's types are known |*)
  Definition proj_iprofile I (T : I -> finType) A (p : iprofile A T)
    : cprofile T -> cprofile A :=
    fun theta => [ffun i => p i (theta i)].

  Definition proj_flatprofile I (T : I -> finType) A
             (p : cprofile (fun i_ti => A (projT1 i_ti)))
    : cprofile T -> cprofile A :=
    fun theta => [ffun i => p (existT _ i (theta i))].

  Definition proj_flatlocalprofile
             I (T : I -> finType) (A : I -> eqType) (P : pred {i : I & T i})
             (HP : forall i : I, {ti : T i | P (existT _ i ti)})
             (p : local_cprofile (fun i_ti => A (projT1 i_ti)) P) : cprofile A
    := [ffun i : I =>
        let (ti, Hi_ti) := HP i in
        let x := (exist P (existT T i ti) Hi_ti) in
        let ai : A i := p x in
        ai
       ].

  Lemma proj_iprof_flatprof I (T : I -> finType) A (p : iprofile A T) theta :
    (proj_iprofile p theta) = (proj_flatprofile (iprofile_flatten p) theta).
  Proof.
    by apply: eq_dffun => i; rewrite ffunE.
  Qed.

  Definition change_istrategy I T A (p : iprofile A T) (i : I) ti ai
    : iprofile A T :=
    [ffun j => [ffun tj => match boolP (i == j) with
                         | AltTrue h =>
                           let ti' := eq_rect _ T ti _ (eqP h) in
                           if ti' == tj
                           then eq_rect i A ai j (eqP h)
                           else p j tj
                         | AltFalse _ => p j tj
                         end]].


  Lemma change_istrategy_id I T A (p : iprofile A T) (i : I) (ti : T i) :
    p = change_istrategy p ti (p i ti).
  Proof.
  apply ffunP => j ; rewrite ffunE.
  apply ffunP => tj ; rewrite ffunE.
  case (boolP (i == j)) => Hj //=.
  case (boolP (eq_rect i _ ti j (eqP Hj) == tj)) => //= Htj.
  by rewrite (map_subst (fun j tj => p j tj)) (eqP Htj).
  Qed.

  Lemma change_strat_istrat I T A (p : iprofile A T) (i_ti : {i : I & T i})
        (ai : A (projT1 i_ti)) :
    (change_strategy (iprofile_flatten p) ai)
    = (iprofile_flatten (change_istrategy p (projT2 i_ti) ai)).
  Proof.
  apply eq_dffun => j_tj //=.
  rewrite !ffunE.
  case (boolP (@eq_op (fintype_Finite__to__eqtype_Equality (@Specif_sigT__canonical__fintype_Finite I T)) i_ti j_tj)) =>H1 ; case (boolP (projT1 i_ti == projT1 j_tj)) => H2 //=.
  - case (boolP ((eq_rect _ _ (projT2 i_ti) (projT1 j_tj)  (@elimT
      (@eq (Finite.sort I) _ _) _ eqP H2)) == (projT2 j_tj))) => H3.
    + rewrite (rew_map A _ (eqP H1) ai).
      by rewrite (eq_irrelevance (f_equal (projT1 (P:=fun i : I => T i)) (eqP H1)) (eqP _)).
    + move/eqP in H3.
      have Hcontra := projT2_eq (eqP H1).
      by rewrite (eq_irrelevance (projT1_eq (eqP H1)) (eqP H2)) in Hcontra.
  - move/eqP in H2.
    by rewrite (eqP H1) in H2.
  - case (boolP ((eq_rect _ _ (projT2 i_ti) (projT1 j_tj)  (@elimT
        (@eq (Finite.sort I) _ _) _ eqP H2)) == (projT2 j_tj))) => H3 //.
    have Hcontra := eq_sigT i_ti j_tj (eqP H2) (eqP H3).
    by move/eqP in H1.
  Qed.


End Profile.


Section Games.
  Open Scope order_scope.

  Section CGameDefs.

    Definition cgame_situation (I : finType) (A : I -> eqType) (X : eqType) :=
      cprofile A -> X.

    Variable I : finType.
    Variable A : I -> eqType.
    Variable X : eqType.
    Implicit Type CGS : cgame_situation A X.

    Definition cgame CGS (disp : I -> Datatypes.unit) (V : forall i, porderType (disp i)) :=
      forall (i : I), X -> V i.

    Variable disp : I -> Datatypes.unit.
    Variable V : forall i, porderType (disp i).
    
    Definition best_response CGS (CG : cgame CGS V) (a : cprofile A) (i : I) : Prop
      := forall ai : A i, ~ (CG i (CGS a) < CG i (CGS (change_strategy a ai))).

    (*
  Lemma best_responseP fA (G : cgame fA) a i :
    reflect (best_response G a i) (best_response_bool G a i).
  Proof.
  case (boolP (best_response_bool G a i)) => H ; constructor.
  - move=> ai.
    move/forallP in H.
    exact: negP (H ai).
  - move=> Hcontra ; move: H.
    rewrite negb_forall => /existsP H.
    destruct H as [h Hx].
    move => /negPn in Hx.
    contradiction (Hcontra h).
  Qed.
    
  Definition Nash_equilibrium_bool fA (G : cgame fA) (a : cprofile fA) : bool :=
    [forall i : I,
      [forall ai : fA i,
        ~~ (G a i < G (change_strategy a ai) i)]].
     *)

    Definition Nash_equilibrium CGS (CG : cgame CGS V) (a : cprofile A) : Prop :=
      forall i : I, forall ai : A i, ~ (CG i (CGS a) < CG i (CGS (change_strategy a ai))).

    (*
  Lemma Nash_equilibriumP fA G (a : cprofile fA) :
    reflect (Nash_equilibrium G a) (Nash_equilibrium_bool G a).
  Proof.
  case (boolP (Nash_equilibrium_bool G a)) => H ; constructor.
  - move => i ai.
    exact: negP (forallP (forallP H i) ai).
  - rewrite /Nash_equilibrium => Hcontra.
    destruct (forallPn H) as [i Hi].
    destruct (forallPn Hi) as [ai Hai].
    move /negPn in Hai.
    have Hcontra' := Hcontra i ai ; contradiction.
  Qed.
     *)
    
    Lemma Nash_equilibrium_best_response CGS (CG : cgame CGS V) (a : cprofile A) :
      Nash_equilibrium CG a <-> forall i, best_response CG a i.
    Proof. by []. Qed.

    (*
  Lemma Nash_equilibrium_best_response_bool fA G (a : cprofile fA) :
    Nash_equilibrium_bool G a = [forall i, best_response_bool G a i].
  Proof. by []. Qed.
     *)

  End CGameDefs.


  Section HGGamesDefs.

    Variable I : finType.
    Variable A : I -> eqType.
    Variable E : finType.
    Variable plays_in : E -> pred I.
    Variable X : E -> eqType.

    Definition hggame_situation :=
      forall e : E, local_cprofile A (plays_in e) -> X e.

    Notation XX := {dffun forall e, X e}.

    Definition global_conseq (HGS : hggame_situation) (a : cprofile A) : XX :=
      [ffun e : E => HGS e (localize (plays_in e) a)].

    Definition hggame_csituation (HGS : hggame_situation) : cgame_situation A XX :=
      global_conseq HGS.
      
    Definition hggame (HGS : hggame_situation) (disp : I -> Datatypes.unit) (V : forall i, porderType (disp i)) :=
      cgame (hggame_csituation HGS) V.

    Section DecomposableHGGames.

      Variable HGS : hggame_situation.
      Variable disp : I -> Datatypes.unit.
      Variable V : forall i, porderType (disp i).

      Variable idx : forall i, V i.
      Variable op : forall i, SemiGroup.com_law (V i).
      Definition hggame_decomp (HG : hggame HGS V) (v : forall i e, X e -> V i) : Prop :=
        forall (i : I) (x : XX), HG i x = \big[@op i/idx i]_(e : E) v i e (x e).
      Definition hggame_gdecomp (HG : hggame HGS V) (v : forall i e, X e -> V i) : Prop :=
        forall (i : I) (x : XX), HG i x = \big[@op i/idx i]_(e : E | plays_in e i) v i e (x e).

      Definition mkhggame (v : forall i e, X e -> V i) : hggame HGS V :=
        fun i x => \big[@op i/idx i]_(e : E) v i e (x e).

      Lemma mkhggame_decomp (v : forall i e, X e -> V i) :
        hggame_decomp (mkhggame v) v.
      Proof. by []. Qed.

    End DecomposableHGGames.

  End HGGamesDefs.



  
  Section IGameDefs.

    Definition igame_situation (I FoD : finType) (A : I -> eqType) (T : I -> finType) (signal : forall i, FoD -> T i) X :=
      cprofile A -> FoD -> X.

    Variable I FoD : finType.
    Variable A : I -> eqType.
    Variable T : I -> finType.
    Variable signal : forall i, FoD -> T i.
    Variable X : eqType.


    Implicit Type IGS : igame_situation A signal X.

    Definition act_of_iprofile IGS (s : iprofile A T) : {ffun FoD -> X} :=
      [ffun t => IGS (proj_iprofile s [ffun i => signal i t]) t].

    Definition igame IGS
    (dispU : forall i, T i -> Datatypes.unit) (U : forall i, forall ti : T i, porderType (dispU i ti))
    (dispV : forall i, T i -> Datatypes.unit) (V : forall i, forall ti : T i, porderType (dispV i ti))
    (dispW : forall i, T i -> Datatypes.unit) (W : forall i, forall ti : T i, porderType (dispW i ti)) :=
      forall i (ti : T i), ((drule2 (U i ti) (V i ti) (W i ti)) * (X -> V i ti) * ({set FoD} -> W i ti))%type.

    Definition iutility IGS
    (dispU : forall i, T i -> Datatypes.unit) (U : forall i, forall ti : T i, porderType (dispU i ti))
    (dispV : forall i, T i -> Datatypes.unit) (V : forall i, forall ti : T i, porderType (dispV i ti))
    (dispW : forall i, T i -> Datatypes.unit) (W : forall i, forall ti : T i, porderType (dispW i ti))
    (IG : igame IGS U V W) (s : iprofile A T) i (ti : T i) :=
      let u := (IG i ti).1.1 in
      let v := (IG i ti).1.2 in
      let w := (IG i ti).2 in
      u X FoD v w (act_of_iprofile IGS s).

    
  End IGameDefs.
    
End Games.


Module Classical.

  Open Scope ring_scope.
  Implicit Type R : numDomainType.
  Implicit Type I : finType.

  Definition cgame R I (A : I -> eqType) := I -> cprofile A -> R.

  Definition of_cgame R I (A : I -> eqType) X (CGS : cgame_situation A X) (CG : games2.cgame CGS (fun=>R)) : Classical.cgame R A :=
    (fun i a => CG i (CGS a)).

  Lemma of_cgameE R I (A : I -> eqType) X (CGS : cgame_situation A X) (CG : games2.cgame CGS (fun=>R)) :
    forall (i : I) (a : cprofile A), CG i (CGS a) = of_cgame CG i a.
  Proof. by []. Qed.

  Definition hggame R I (A : I -> eqType) (E : finType) (plays_in : E -> pred I)
  (u : forall (i : I) (e : E), plays_in e i -> local_cprofile A (plays_in e) -> R) : cgame R A :=
    fun i a => \sum_(s : {e : E | plays_in e i}) u i (tag s) (tagged s) (localize (plays_in (tag s)) a).
  
End Classical.








Section SeltenHowsonRosenthal.

  

  Check igame.

  Variable I FoD : finType.
  Variable A : I -> finType.
  Variable T : I -> finType.
  Variable signal : forall i, FoD -> T i.
  Variable X : finType.
  Variable IGS : igame_situation A signal X.

  Variable dispU : forall i, T i -> Datatypes.unit.
  Variable U : forall i, forall ti : T i, porderType (dispU ti).
  Variable dispV : forall i, T i -> Datatypes.unit.
  Variable V : forall i, forall ti : T i, porderType (dispV ti).
  Variable dispW : forall i, T i -> Datatypes.unit.
  Variable W : forall i, forall ti : T i, porderType (dispW ti).

  Check igame IGS U V W.

  Notation HR_I := ({i : I & T i}).
  Notation HR_A := (fun i_ti : HR_I => A (tag i_ti)).
  Notation HR_V := (fun i_ti : HR_I => U (tagged i_ti)).

  Check cgame_situation HR_A _.

  Variable IG : igame IGS U V W.

  Definition HRequiv X' (CGS : cgame_situation HR_A X') (CG : cgame CGS HR_V) :=
    forall i (ti : T i) (s : iprofile A T), iutility IG s ti = CG (existT T i ti) (CGS (iprofile_flatten s)).



  Notation projprofile := (fun (a : cprofile HR_A) (t : FoD) => proj_flatprofile a [ffun i => signal i t]).


  Section SeltenTransform.

    Notation HR_X := {ffun FoD -> X}.

    Definition Selten_cgame_situation : cgame_situation HR_A HR_X :=
      fun a : cprofile HR_A => [ffun t => IGS (projprofile a t) t].

    Definition Selten_cgame : cgame Selten_cgame_situation HR_V :=
      fun (i_ti : HR_I) (x : HR_X) =>
        let (uv, w) := (IG (tagged i_ti)) in
        let (u,v) := uv in 
        u X FoD v w x.

    Lemma Selten_correct :
      HRequiv Selten_cgame.
    Proof.
    move=>i ti s.
    rewrite /Selten_cgame/iutility/=.
    case IG ; case=>u v w.
    congr (u X FoD v w _)=>//=.
    rewrite /act_of_iprofile/Selten_cgame_situation/=.
    rewrite (eq_ffun (fun t => IGS (proj_flatprofile (iprofile_flatten s) [ ffun i0 : I => signal i0 t]) t))=>//=t.
    congr (IGS _).
    exact: proj_iprof_flatprof.
    Qed.

  End SeltenTransform.

  Section HRTransforms.
    Section HRGeneral.

      Variable x0 : X.
      Variable zi : forall i (ti : T i), zinst (U ti) (V ti) (W ti).
      Variable m : forall i (ti : T i), {ffun {set FoD} -> W ti}.
      (* Variable m_repr : forall i (ti : T i),
          is_massfun (z_idw (zi ti)) (z_op_mfun (zi ti)) (IG ti).2 (m ti).
       *)

      Notation HR_E := {set FoD}.

      Notation HR_plays_in := (fun (e : HR_E) (i_ti : HR_I) =>
                                 [exists t, (t \in e) && (tagged i_ti == signal (tag i_ti) t)]).

      Notation HR_X := (fun e : HR_E => {set X}).

      (* For all t in lg, return the corresponding cprofile *)
      Definition proj_flatlocprofile (e : HR_E) (ae : local_cprofile HR_A (HR_plays_in e)) (t : FoD) (Ht : t \in e) : cprofile A.
      apply: finfun=>i.
      have Hi : HR_plays_in e (existT T i (signal i t))
        by apply/existsP ; exists t ; rewrite Ht /= eqxx.
      exact:  ae (exist (HR_plays_in e) _ Hi).
      Defined.

      Definition HRG_local_conseq (e : HR_E) (ae : local_cprofile HR_A (HR_plays_in e)) : HR_X e :=
        (* let f t :=  match (boolP (t \in e)) with
                    | AltTrue H => Some (IGS (proj_flatlocprofile ae H) t)
                    | AltFalse _ => None end in *)
        let f t :=  match (boolP (t \in e)) with
                    | AltTrue H => IGS (proj_flatlocprofile ae H) t
                    | AltFalse _ => x0 end in
        [set f t | t in e].
        (* [set:: pmap f (index_enum FoD)]. *)

      Definition HRG_hggame_situation : hggame_situation HR_A HR_plays_in HR_X :=
        fun (e : HR_E) (ae : local_cprofile HR_A (HR_plays_in e)) =>
          HRG_local_conseq ae.

      Definition HRG_local_u (i_ti : HR_I) (e : HR_E)  : HR_X e -> HR_V i_ti :=
        let v := (IG (tagged i_ti)).1.2 in
        fun A => z_otimes (zi (tagged i_ti))
              (m (tagged i_ti) e)
              (z_f_agg (zi (tagged i_ti)) v A).

      Definition HRG_hggame : hggame HRG_hggame_situation HR_V :=
        mkhggame
        HRG_hggame_situation
        (fun i_ti : HR_I => z_idu (zi (tagged i_ti))) 
        (fun i_ti : HR_I => z_oplus (zi (tagged i_ti)))
        HRG_local_u.

      Lemma HRGeneral_correct :
        (forall i (ti : T i),
            let u := (IG ti).1.1 in
            let v := (IG ti).1.2 in
            let w := (IG ti).2 in
            forall chi, u _ _ v w chi = XEU (zi ti) v (m ti) chi)
        -> HRequiv (CGS:=hggame_csituation HRG_hggame_situation) HRG_hggame.
      Proof.
      move=>Hzi i ti s.
      rewrite /HRG_hggame/iutility/mkhggame/=.
      have := Hzi i ti.
      set u := (IG ti).1.1=>/=.
      set v := (IG ti).1.2=>/=.
      set w := (IG ti).2=>/=->.
      apply: eq_bigr=>/=B _.
      congr (z_otimes _ _ _)=>//=.
      rewrite z_f_agg_ax/=.
      rewrite /v.
      congr (z_f_agg _ _ _).
      rewrite ffunE /HRG_hggame_situation/HRG_local_conseq.
      apply eq_in_imset=>t Ht.
      case (boolP (t \in B))=>// Ht_dep ; last by rewrite Ht in Ht_dep.
      rewrite ffunE.
      congr (IGS _ _).
      apply/ffunP=>j.
      by rewrite !ffunE=>/=.
      Qed.
    End HRGeneral.

  End HRTransforms.

End SeltenHowsonRosenthal.
