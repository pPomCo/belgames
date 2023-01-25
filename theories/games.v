(******************************************************************************)
(** This file provide a theory for simultaneous games

   1. Profiles
   A profile assign a strategy (ai : A i) to each player (i : X)
   We distinguish:
   - Profiles for complete games : forall i, A i
   - Profiles for incomplete games : forall i, T i -> A i
   - Local profiles for HG games: forall i, P i -> A i

   cprofile A          == {dffun forall i : X, A i}
   iprofile T A        == cprofile (fun i => {ffun T i -> A i})
   local_cprofile P A  == {ffun forall (s : {i : X | P i}), A (val s)}

   We then define:
   change_strategy A p i ai       == the cprofile p where (p i) has changed to ai
   change_istrategy T A p i ti ai == the iprofile p where (p i ti) has changed to ai,
   And prove:
   change_strategy_id A p i :       p = change_strategy p (p i).
   change_istrategy_id T A p i ti : p = change_istrategy p ti (p i ti).

   Finally, we cast/project profiles with:
   iprofile_flatten T A p          == flatten (p : iprofile T A) to a cprofile
                                      {dffun forall s : {i : X & T i}, A i}
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
   cgame R A                       == cprofile A -> X -> R (the type of complete games)
   Nash_equilibrium G p            == true iff there is no (i : X) such as there is no (ai : A i)
                                      such that (G p i) < (G p (change_strategy p i ai))
   Nash_equilibrium_prop G p       == True iff there is no (i : X) such as there is no (ai : A i)
                                      such that (G p i) < (G p (change_strategy p i ai))
   Nash_equilibriumP G p           == reflect (Nash_equilibrium_prop G p) (Nash_equilibrium G p)

   2.2. Hypergraphical games -- Particular sort of complete game where utility functions are
        decomposed into several local games. We index local games with (local_game : finType)
        and check whether (i : X) plays in (lg : local_game) using (plays_in : lg -> pred X).
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
   proper_belgame G cond      == One can condition given (ti : T i) for all agent (i : X)
                                 according to (cond : conditioning (cprofile T))
   belgame_utility G cond xeu H p i == utility of p for i, according to the scoring function xeu,
                                 given that (H : proper_belgame G cond)
   BelG_Nash_equilibrium G cond xeu H p
                              == true iff p is a Nash equilibrium according to (belgame_utility G cond xeu H p)
                                 i.e. there is no (i : X) such that there is no (ti : T i) such
                                 that there is no (ai : A i) such that (belgame_utility G cond xeu H p i)
                                 < (belgame_utility G cond xeu H (change_istrategy T A p i ti ai) i)
  BelG_Nash_equilibrium_prop G cond xeu H p
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


Require Import general_lemmas bel.

Open Scope ring_scope.


Section Profile.

  Implicit Type X : finType.

  Definition cprofile X (A : X -> eqType)
    := {dffun forall i : X, A i}.
  (*
  Definition iprofile X (T : X -> finType) (A : X -> eqType)
    := {dffun forall i : X, {ffun T i -> A i}}.
   *)
  Definition iprofile X (T : X -> finType) (A : X -> eqType)
    := cprofile (fun i => [eqType of {ffun T i -> A i}]).

  Definition change_strategy X A (p : cprofile A) (i : X) (ai : A i) : cprofile A
    := [ffun j => match boolP (i == j) with
                  | AltTrue h => eq_rect _ A ai _ (eqP h)
                  | AltFalse _ => p j
                  end].

  Lemma change_strategy_id X A (p : cprofile A) (i : X) :
    p = change_strategy p (p i).
  Proof.
  apply ffunP => j ; rewrite ffunE.
  case (boolP (i == j)) => // H.
  by rewrite f_equal_dep.
  Qed.

  Definition local_cprofile X (A : X -> eqType) (P : pred X) :=
    {ffun forall (s : {x : X | P x}), A (val s)}.

  (*| Transform an iprofile to a profile such as support is the set of dependent pairs (i,t_i) |*)
  Definition iprofile_flatten X (T : X -> finType) A (p : iprofile T A)
    : cprofile (fun i_ti => A (projT1 i_ti)) :=
    [ffun i_ti => p (projT1 i_ti) (projT2 i_ti)].

  (*| Profile that will be played if player's types are known |*)
  Definition proj_iprofile X (T : X -> finType) A (p : iprofile T A)
    : cprofile T -> cprofile A :=
    fun theta => [ffun i => p i (theta i)].

  Definition proj_flatprofile X (T : X -> finType) A
             (p : cprofile (fun i_ti => A (projT1 i_ti)))
    : cprofile T -> cprofile A :=
    fun theta => [ffun i => p (existT _ i (theta i))].

  Definition proj_flatlocalprofile
             X (T : X -> finType) (A : X -> eqType) (P : pred {i : X & T i})
             (HP : forall i : X, {ti : T i | P (existT _ i ti)})
             (p : local_cprofile (fun i_ti => A (projT1 i_ti)) P) : cprofile A
    := [ffun i : X =>
        let (ti, Hi_ti) := HP i in
        let x : sig_finType P := (exist P (existT T i ti) Hi_ti) in
        let ai : A i := p x in
        ai
       ].

  Lemma proj_iprof_flatprof X (T : X -> finType) A (p : iprofile T A) theta :
    (proj_iprofile p theta) = (proj_flatprofile (iprofile_flatten p) theta).
  Proof.
    by apply: eq_dffun => i; rewrite ffunE.
  Qed.

  Definition change_istrategy X T A (p : iprofile T A) (i : X) ti ai
    : iprofile T A :=
    [ffun j => [ffun tj => match boolP (i == j) with
                         | AltTrue h =>
                           let ti' := eq_rect _ T ti _ (eqP h) in
                           if ti' == tj
                           then eq_rect i A ai j (eqP h)
                           else p j tj
                         | AltFalse _ => p j tj
                         end]].


  Lemma change_istrategy_id X T A (p : iprofile T A) (i : X) (ti : T i) :
    p = change_istrategy p ti (p i ti).
  Proof.
  apply ffunP => j ; rewrite ffunE.
  apply ffunP => tj ; rewrite ffunE.
  case (boolP (i == j)) => Hj //=.
  case (boolP (eq_rect i _ ti j (eqP Hj) == tj)) => //= Htj.
  by rewrite (map_subst (fun j tj => p j tj)) (eqP Htj).
  Qed.

  Lemma change_strat_istrat X T A (p : iprofile T A) (i_ti : {i : X & T i})
        (ai : A (projT1 i_ti)) :
    (change_strategy (iprofile_flatten p) ai)
    = (iprofile_flatten (change_istrategy p (projT2 i_ti) ai)).
  Proof.
  apply eq_dffun => j_tj //=.
  rewrite !ffunE.
  case (boolP (@eq_op (Finite.eqType (tag_finType T)) i_ti j_tj)) => H1;
                   case (boolP (projT1 i_ti == projT1 j_tj)) => H2 //=.
  - case (boolP ((eq_rect _ _ (projT2 i_ti) (projT1 j_tj)  (@elimT
      (@eq (Finite.sort X) _ _) _ eqP H2)) == (projT2 j_tj))) => H3.
    + rewrite (rew_map A _ (eqP H1) ai).
      by rewrite (Eqdep_dec.eq_proofs_unicity
                    (@eqType_dec_prop X) (f_equal _ (eqP H1))(eqP H2)).
    + move/eqP in H3.
      have Hcontra := projT2_eq (eqP H1).
      by rewrite (Eqdep_dec.eq_proofs_unicity (@eqType_dec_prop X)
           (projT1_eq (eqP H1)) (eqP H2)) in Hcontra.
  - move/eqP in H2.
    by rewrite (eqP H1) in H2.
  - case (boolP ((eq_rect _ _ (projT2 i_ti) (projT1 j_tj)  (@elimT
        (@eq (Finite.sort X) _ _) _ eqP H2)) == (projT2 j_tj))) => H3 //.
    have Hcontra := eq_sigT i_ti j_tj (eqP H2) (eqP H3).
    by move/eqP in H1.
  Qed.


End Profile.


Section Games.

  Variable R : realFieldType.
  Variable agent : finType.
  Implicit Type A : forall i : agent, eqType.
  Implicit Type fA T : forall i : agent, finType.

  Definition cgame A := cprofile A -> agent -> R.

  Definition best_response fA (G : cgame fA) (a : cprofile fA) (i : agent) : bool
    := [forall ai : fA i, ~~ (G a i < G (change_strategy a ai) i)].

  Definition best_response_prop A (G : cgame A) (a : cprofile A) (i : agent) : Prop
    := forall ai : A i, ~ (G a i < G (change_strategy a ai) i).

  Lemma best_responseP fA (G : cgame fA) a i :
    reflect (best_response_prop G a i) (best_response G a i).
  Proof.
  case (boolP (best_response G a i)) => H ; constructor.
  - move=> ai.
    move/forallP in H.
    exact: negP (H ai).
  - move=> Hcontra ; move: H.
    rewrite negb_forall => /existsP H.
    destruct H as [h Hx].
    move => /negPn in Hx.
    contradiction (Hcontra h).
  Qed.

  Definition Nash_equilibrium fA (G : cgame fA) (a : cprofile fA) : bool :=
    [forall i : agent,
      [forall ai : fA i,
        ~~ (G a i < G (change_strategy a ai) i)]].


  Definition Nash_equilibrium_prop A (G : cgame A) (a : cprofile A) : Prop :=
    forall i : agent, forall ai : A i, ~ (G a i < G (change_strategy a ai) i).

  Lemma Nash_equilibriumP fA G (a : cprofile fA) :
    reflect (Nash_equilibrium_prop G a) (Nash_equilibrium G a).
  Proof.
  case (boolP (Nash_equilibrium G a)) => H ; constructor.
  - move => i ai.
    exact: negP (forallP (forallP H i) ai).
  - rewrite /Nash_equilibrium_prop => Hcontra.
    destruct (forallPn H) as [i Hi].
    destruct (forallPn Hi) as [ai Hai].
    move /negPn in Hai.
    have Hcontra' := Hcontra i ai ; contradiction.
  Qed.

  Lemma Nash_equilibrium_best_response_prop A G (a : cprofile A) :
    Nash_equilibrium_prop G a <-> forall i, best_response_prop G a i.
  Proof.
  by rewrite /Nash_equilibrium_prop /best_response.
  Qed.

  Lemma Nash_equilibrium_best_response fA G (a : cprofile fA) :
    Nash_equilibrium G a = [forall i, best_response G a i].
  Proof.
  by [].
  Qed.


  Section HypergraphicalGame.

    Variable A : agent -> eqType.
    Variable localgame : finType.
    Variable plays_in : localgame -> pred agent.
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


  Section BelGame.


    Notation Tconfig := (fun T => [finType of {dffun forall i : agent, T i}]).

    Notation "'xeu_function' T" := ({ffun T -> R} -> {ffun {set T} -> R}) (at level 80).

    Definition belgame A T :=
      (bpa R (Tconfig T) * (cprofile A -> Tconfig T -> agent -> R))%type.

    Definition proper_belgame A T (G : belgame A T) (cond : conditioning R (Tconfig T)) : bool :=
      [forall i : agent, [forall ti : T i, revisable cond G.1 (event_ti ti)]].

    Definition is_revisable A T (G : belgame A T) (cond : conditioning R (Tconfig T)) (HG : proper_belgame G cond) i (ti : T i) :
      revisable cond G.1 (event_ti ti)
      := (forallP ((forallP HG) i)) ti.

    Definition belgame_utility A T (G : belgame A T) (cond : conditioning R (Tconfig T)) (xeu : xeu_function _) (HG : proper_belgame G cond) (p : iprofile T A) (i : agent) (ti : T i) : R
      :=
        let kn := cond G.1 (event_ti ti) (is_revisable HG ti) in
        XEU kn (xeu [ffun t => G.2 (proj_iprofile p t) t i]).

    Definition BelG_Nash_equilibrium fA T (G : belgame fA T) (cond : conditioning R (Tconfig T)) (xeu : xeu_function _) (HG : proper_belgame G cond) (p : iprofile T fA) : bool :=
      [forall i : agent,
        [forall ti : T i,
          [forall ai : fA i,
            ~~ (belgame_utility xeu HG p ti < belgame_utility xeu HG (change_istrategy p ti ai) ti)]]].

    Definition BelG_Nash_equilibrium_prop A T (G : belgame A T) (cond : conditioning R (Tconfig T)) (xeu : xeu_function _) (HG : proper_belgame G cond) (p : iprofile T A) : Prop :=
      forall i : agent,
      forall ti : T i,
      forall ai : A i, ~ (belgame_utility xeu HG p ti < belgame_utility xeu HG (change_istrategy p ti ai) ti).

    Lemma BelG_Nash_equilibriumP fA T (G : belgame fA T) cond xeu (HG : proper_belgame G cond) p :
      reflect (BelG_Nash_equilibrium_prop xeu HG p)  (BelG_Nash_equilibrium xeu HG p).
    Proof.
    case (boolP (BelG_Nash_equilibrium xeu HG p)) => H ; constructor.
    - move => i ti ai.
      exact: negP (forallP (forallP (forallP H i) ti) ai).
    - rewrite /BelG_Nash_equilibrium_prop => Hcontra.
      destruct (forallPn H) as [i Hi].
      destruct (forallPn Hi) as [ti Hti].
      destruct (forallPn Hti) as [ai Hai].
      move /negPn in Hai.
      have Hcontra' := Hcontra i ti ai ; contradiction.
    Qed.


  End BelGame.

  Section BGame.

    Notation Tconfig := (fun T => [finType of {dffun forall i : agent, T i}]).

    Definition bgame A T :=
      (proba R (Tconfig T) * (cprofile A -> Tconfig T -> agent -> R))%type.

    Definition proper_bgame A T (G : bgame A T) : bool :=
      [forall i : agent, [forall ti : T i, Pr_revisable G.1 (event_ti ti)]].

    Definition is_Pr_revisable A T (G : bgame A T) (HG : proper_bgame G) i (ti : T i) :
      Pr_revisable G.1 (event_ti ti)
      := (forallP ((forallP HG) i)) ti.

    Definition belgame_of_bgame A T (G : bgame A T) : {G' : belgame A T | 1%N.-additive G'.1}
      := let (p,u) := G in match p with {| proba_val := m ; proba_ax := H|} => exist _ (m,u) H end.

    Definition bgame_of_belgame A T (sG : {G : belgame A T | 1%N.-additive G.1}) : bgame A T
      := let (G,H) := sG in let (m,u) := G in ({|proba_ax:=H|}, u).

    Lemma bgame_of_belgame_cancel A T :
      cancel (@bgame_of_belgame A T) (@belgame_of_bgame A T).
    Proof. by do 2 case. Qed.

    Lemma belgame_of_bgame_cancel A T :
      cancel (@belgame_of_bgame A T) (@bgame_of_belgame A T).
    Proof. by do 2 case. Qed.

    Definition bgame_utility A T (G : bgame A T) (HG : proper_bgame G) (p : iprofile T A) (i : agent) (ti : T i) : R
      :=
        let kn := Pr_conditioning (is_Pr_revisable HG ti) in
        \sum_t dist kn t * G.2 (proj_iprofile p t) t i.

  End BGame.
End Games.


Section MixedStrategies.

  Variable R : realFieldType.
  Variable X : finType.
  Variable A : X -> finType.

  Variable witnessX : X.


  Definition mixed_cprofile := cprofile (fun i => proba_eqType R (A i)).

  Definition ms_utility (G : cgame R A) (mp : mixed_cprofile) (i : X) : R
    := let pr := prod_proba mp witnessX in
       \sum_(p : cprofile A) (dist pr p) * (G p i).

  Definition ms_Nash_equilibrium (G : cgame R A) (mp : mixed_cprofile) : Prop
    := forall i : X,
      forall si : proba R (A i),
      ~ ms_utility G mp i < ms_utility G (change_strategy mp si) i.

  Definition mixed_cgame (G : cgame R A) : cgame R (fun i => proba_eqType R (A i))
    := fun mp i => ms_utility G mp i.

  Lemma mixed_cgameE (G : cgame R A) (mp : mixed_cprofile) (i : X) :
    ms_utility G mp i = (mixed_cgame G) mp i.
  Proof. by []. Qed.

  Lemma ms_NashE (G : cgame R A) (mp : mixed_cprofile) :
    ms_Nash_equilibrium G mp <-> Nash_equilibrium_prop (mixed_cgame G) mp.
  Proof.
  split => H i si.
  - by rewrite -!mixed_cgameE.
  - by rewrite mixed_cgameE.
  Qed.

End MixedStrategies.


Close Scope ring_scope.
