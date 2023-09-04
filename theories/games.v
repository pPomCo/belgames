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


Require Import general_lemmas capacity.

Local Open Scope ring_scope.

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

  Variable R : realFieldType.
  Variable I : finType. (* agents *)
  Implicit Type A : forall i : I, eqType.
  Implicit Type fA T : forall i : I, finType.

  Definition cgame A := cprofile A -> I -> R.

  Definition best_response_bool fA (G : cgame fA) (a : cprofile fA) (i : I) : bool
    := [forall ai : fA i, ~~ (G a i < G (change_strategy a ai) i)].

  Definition best_response A (G : cgame A) (a : cprofile A) (i : I) : Prop
    := forall ai : A i, ~ (G a i < G (change_strategy a ai) i).

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


  Definition Nash_equilibrium A (G : cgame A) (a : cprofile A) : Prop :=
    forall i : I, forall ai : A i, ~ (G a i < G (change_strategy a ai) i).

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

  Lemma Nash_equilibrium_best_response A G (a : cprofile A) :
    Nash_equilibrium G a <-> forall i, best_response G a i.
  Proof.
  by rewrite /Nash_equilibrium /best_response.
  Qed.

  Lemma Nash_equilibrium_best_response_bool fA G (a : cprofile fA) :
    Nash_equilibrium_bool G a = [forall i, best_response_bool G a i].
  Proof. by []. Qed.


  Section HypergraphicalGame.

    Variable A : I -> eqType.
    Variable localgame : finType.
    Variable plays_in : localgame -> pred I.
    Notation localprof := (fun lg : localgame => local_cprofile A (plays_in lg)).
    Notation localagent := (fun lg => {i | plays_in lg i}).

    Definition hg_game (u : forall lg, localprof lg -> localagent lg -> R) : cgame A
      := fun a i => \sum_(s : {lg : localgame | plays_in lg i}) u (tag s) [ffun i => a (val i)] (exist _ i (tagged s)).

    Lemma hg_gameE u a i :
      hg_game u a i = \sum_(lg : localgame | plays_in lg i)
                        match boolP (plays_in lg i) with
                        | AltTrue h => u lg [ffun i => a (val i)] (exist _ i h)
                        | AltFalse _ => 0
                        end.
    Proof.
    by rewrite /hg_game (sig_big_dep2 (fun t Ht => u t [ffun j => a (val j)] (exist _ i Ht))).
    Qed.

  End HypergraphicalGame.


  Section Igame.

    Variable A : forall i : I, eqType.
    Variable T : forall i : I, finType.

    Notation Tn := {dffun forall i : I, T i}.

    Notation xeu_function W := ({ffun W -> R} -> {ffun {set W} -> R}) (only parsing).

    Definition igame :=
      (massfun R Tn * (cprofile A -> Tn -> I -> R))%type.

    Definition proper_igame (G : igame) (cond : conditioning R Tn) : bool :=
      [forall i : I, [forall ti : T i, revisable cond G.1 (event_ti ti)]].

    Definition is_revisable (G : igame) (cond : conditioning R Tn) (HG : proper_igame G cond) i (ti : T i) :
      revisable cond G.1 (event_ti ti)
      := (forallP ((forallP HG) i)) ti.

    Definition igame_utility (G : igame) (cond : conditioning R Tn) (fXEU : xeu_function _) (HG : proper_igame G cond) (p : iprofile A T) (i : I) (ti : T i) : R :=
        let kn := cond G.1 (event_ti ti) (is_revisable HG ti) in
        XEU kn (fXEU [ffun t => G.2 (proj_iprofile p t) t i]).

    Definition Igame_Nash_equilibrium (G : igame) (cond : conditioning R Tn) fXEU (HG : proper_igame G cond) (p : iprofile A T) : Prop :=
      forall i : I,
      forall ti : T i,
      forall ai : A i,
        ~ (igame_utility fXEU HG p ti < igame_utility fXEU HG (change_istrategy p ti ai) ti).

  End Igame.

  Section FiniteIGame. (* assuming finite sets of actions *)

    Variable fA : forall i : I, finType.
    Variable T : forall i : I, finType.

    Notation Tn := {dffun forall i : I, T i}.

    Definition Igame_Nash_equilibrium_bool (G : igame fA T) (cond : conditioning R Tn) fXEU (HG : proper_igame G cond) (p : iprofile fA T) : bool :=
      [forall i : I,
        [forall ti : T i,
          [forall ai : fA i,
            ~~ (igame_utility fXEU HG p ti < igame_utility fXEU HG (change_istrategy p ti ai) ti)]]].

    Lemma Igame_Nash_equilibriumP (G : igame fA T) cond fXEU (HG : proper_igame G cond) p :
      reflect (Igame_Nash_equilibrium fXEU HG p) (Igame_Nash_equilibrium_bool fXEU HG p).
    Proof.
      case (boolP (Igame_Nash_equilibrium_bool fXEU HG p)) => H ; constructor.
      - move => i ti ai.
        exact: negP (forallP (forallP (forallP H i) ti) ai).
      - rewrite /Igame_Nash_equilibrium => Hcontra.
        destruct (forallPn H) as [i Hi].
        destruct (forallPn Hi) as [ti Hti].
        destruct (forallPn Hti) as [ai Hai].
        move /negPn in Hai.
        have Hcontra' := Hcontra i ti ai ; contradiction.
    Qed.

  End FiniteIGame.

  Section BGame.

    Notation Tconfig := (fun T => {ffun forall i : I, T i}).

    Variable A : forall i : I, eqType.
    Variable T : forall i : I, finType.

    Notation Tn := {dffun forall i : I, T i}.

    Definition bgame :=
      (proba R Tn * (cprofile A -> Tn -> I -> R))%type.

    Definition proper_bgame (G : bgame) : bool :=
      [forall i : I, [forall ti : T i, Pr_revisable G.1 (event_ti ti)]].

    Definition is_Pr_revisable (G : bgame) (HG : proper_bgame G) i (ti : T i) :
      Pr_revisable G.1 (event_ti ti)
      := (forallP ((forallP HG) i)) ti.

    Definition igame_of_bgame_ax (G : bgame)
      : [forall B : {set Tn}, (G.1 : massfun R Tn) B >= 0] && (1%N.-additive (G.1 : massfun R Tn)).
    exact: (introTF (c:=true) andP (conj (bpa_ax G.1) (proba_ax G.1))).
    Defined.
    
    Definition igame_of_bgame (G : bgame)
      : {G' : igame A T | [forall B : {set Tn}, G'.1 B >= 0] && (1%N.-additive G'.1)} :=
      exist _ (G.1 : massfun R Tn, G.2) (igame_of_bgame_ax G).

    Definition bgame_of_igame_bpa_ax (sG : {G : igame A T | [forall B : {set Tn}, G.1 B >= 0] && (1%N.-additive G.1)}) : bpa_axiom ((tag sG).1 : massfun R Tn).
    exact: match elimTF andP (tagged sG) with conj Hge0 H1add => Hge0 end.
    Defined.

    Definition bgame_of_igame_proba_ax (sG : {G : igame A T | [forall B : {set Tn}, G.1 B >= 0] && (1%N.-additive G.1)}) : proba_axiom ((tag sG).1 : massfun R Tn).
    exact: match elimTF andP (tagged sG) with conj Hge0 H1add => H1add end.
    Defined.

    Definition bgame_of_igame (sG : {G : igame A T | [forall B : {set Tn}, G.1 B >= 0] && (1%N.-additive G.1)}) : bgame :=
      ({| proba_val := {| bpa_ax := bgame_of_igame_bpa_ax sG |} ; proba_ax := bgame_of_igame_proba_ax sG |}, (tag sG).2).

    Lemma bgame_of_igame_cancel :
      cancel bgame_of_igame igame_of_bgame.
    Proof.
    case ; case=> p u HG.
    rewrite /igame_of_bgame/=.
    rewrite (eq_irrelevance (igame_of_bgame_ax
                             (bgame_of_igame (exist (fun G0 : igame A T => [forall B, 0 <= G0.1 B] && ( 1%N.-additive G0.1 )) _ HG))) HG).
    exact: eq_exist_curried=>//=.
    Qed.
    
    Lemma igame_of_bgame_cancel :
      cancel igame_of_bgame bgame_of_igame.
    Proof.
    case=>p u.
    congr (_,u).
    apply: proba_eqE=>/=.
    by apply: bpa_eqE=>/=.
    Qed.
    
    Definition bgame_utility (G : bgame) (HG : proper_bgame G) (p : iprofile A T) (i : I) (ti : T i) : R
      :=
      let kn := Pr_conditioning (is_Pr_revisable HG ti) in
      [EU of [ffun t => G.2 (proj_iprofile p t) t i] wrt kn].

  End BGame.
End Games.


Section MixedStrategies.

  Variable R : realFieldType.
  Variable I : finType.
  Variable A : I -> finType.

  Variable witnessI : I.

  Definition mixed_cprofile := cprofile (fun i => [eqType of proba R (A i)]).

  Definition ms_util (G : cgame R A) (mp : mixed_cprofile) (i : I) : R :=
    let pr := prod_proba mp witnessI in
    [EU of [ffun p => G p i] wrt pr].

  Definition ms_Nash_equilibrium (G : cgame R A) (mp : mixed_cprofile) : Prop :=
    forall i (si : proba R (A i)),
      ~ ms_util G mp i < ms_util G (change_strategy mp si) i.

  Definition mixed_cgame (G : cgame R A) : cgame R (fun i => [eqType of proba R (A i)])
    := fun mp i => ms_util G mp i.

  Lemma mixed_cgameE G mp i : ms_util G mp i = (mixed_cgame G) mp i.
  Proof. by []. Qed.

  Lemma ms_NashE (G : cgame R A) (mp : mixed_cprofile) :
    ms_Nash_equilibrium G mp <-> Nash_equilibrium (mixed_cgame G) mp.
  Proof.
  split => H i si.
  - by rewrite -!mixed_cgameE.
  - by rewrite mixed_cgameE.
  Qed.

End MixedStrategies.
