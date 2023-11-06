(* ************************************************************************************ *)
(* Game theory (generalized algebraic games)

   Similar to modules 'games' and 'HRtransform' but for the algebraic game model

   profiles
   cgame         == game of complete information
   hggame        == hypergraphical game (of complete information)
   igame         == game of incomplete information 

   Selten transform
   Algebraic Howson and Rosenthal transform
 *)
(* ************************************************************************************ *)
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing GRing.Theory.
Import Num.Theory.

From BelGames Require Import drule.



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

    Definition Nash_equilibrium CGS (CG : cgame CGS V) (a : cprofile A) : Prop :=
      forall i : I, forall ai : A i, ~ (CG i (CGS a) < CG i (CGS (change_strategy a ai))).
    
    Lemma Nash_equilibrium_best_response CGS (CG : cgame CGS V) (a : cprofile A) :
      Nash_equilibrium CG a <-> forall i, best_response CG a i.
    Proof. by []. Qed.

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


  Notation HR_I := ({i : I & T i}).
  Notation HR_A := (fun i_ti : HR_I => A (tag i_ti)).
  Notation HR_V := (fun i_ti : HR_I => U (tagged i_ti)).


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

      Variable x0 : FoD * cprofile A.
      Variable zi : forall i (ti : T i), zinst (U ti) (V ti) (W ti).
      Variable m : forall i (ti : T i), {ffun {set FoD} -> W ti}.
      
      Notation HR_E := {set FoD}.

      Notation HR_plays_in := (fun (e : HR_E) (i_ti : HR_I) =>
                                 [exists t, (t \in e) && (tagged i_ti == signal (tag i_ti) t)]).

      Notation HR_X := (fun e : HR_E => {set FoD * cprofile A}). (*   {set FoD * cprofile a} *)

      (* For all t in lg, return the corresponding cprofile *)
      Definition proj_flatlocprofile (e : HR_E) (ae : local_cprofile HR_A (HR_plays_in e)) (t : FoD) (Ht : t \in e) : cprofile A.
      apply: finfun=>i.
      have Hi : HR_plays_in e (existT T i (signal i t))
        by apply/existsP ; exists t ; rewrite Ht /= eqxx.
      exact:  ae (exist (HR_plays_in e) _ Hi).
      Defined.

      (** ** **
          ============================
          z_f_agg (zi ti) (fun t : FoD => v (act_of_iprofile IGS s t)) B =
          z_f_agg (zi ti) (IG ti).1.2 (hggame_csituation HRG_hggame_situation (iprofile_flatten s) B)
          ** ** **)

      Definition HRG_local_conseq (e : HR_E) (ae : local_cprofile HR_A (HR_plays_in e)) : HR_X e :=
        (* let f t :=  match (boolP (t \in e)) with
                    | AltTrue H => Some (IGS (proj_flatlocprofile ae H) t)
                    | AltFalse _ => None end in *)
        let f t :=  match (boolP (t \in e)) with
                    | AltTrue H => (t, (proj_flatlocprofile ae H))
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
              (z_f_agg (zi (tagged i_ti)) (fun x => v (IGS x.2 x.1)) A).

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
      rewrite ffunE. (* /HRG_hggame_situation/HRG_local_conseq *)
      apply: z_f_agg_ax.
      - move=>t Ht.
        congr (v _).
        rewrite ffunE.
        congr (IGS _ _).
        + case (boolP (t \in B))=>//=H ; last by rewrite Ht in H.
          by apply/ffunP=>j ; rewrite !ffunE.
        + by case (boolP (t \in B))=>//=H ; last rewrite Ht in H.
      - apply/imset_injP=>t1 t2 Ht1 Ht2.
        case (boolP (t1 \in B))=>//=Ht1' ; last by rewrite Ht1 in Ht1'.
        case (boolP (t2 \in B))=>//=Ht2' ; last by rewrite Ht2 in Ht2'.
        by case.
      Qed.
    End HRGeneral.

  End HRTransforms.

End SeltenHowsonRosenthal.
