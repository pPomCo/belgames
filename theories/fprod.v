From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg finset ssrint matrix ssrnum.

(** * Formalization of the dependent product of [finType]s *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Misc.

Lemma Tagged_eta A (P : A -> Type) (s : {x : A & P x}) :
  s = @Tagged _ (tag s) _ (tagged s).
Proof. by move: s => [x Q]. Qed.

(** Tip to leverage a Boolean condition *)
Definition sumb (b : bool) : {b = true} + {b = false} :=
  if b is true then left erefl else right erefl.

End Misc.


Section Finite_product_structure.

Variables (I : finType) (T_ : I -> finType).

Definition tagged' i (u : {i : I & T_ i}) (p : tag u == i) : T_ i.
rewrite -(eqP p).
exact (tagged u).
Defined.

Lemma TaggedE i P1 P2 : @Tagged I i T_ P1  = Tagged T_ P2 -> P1 = P2.
move=> H.
have H' := (EqdepFacts.eq_sigT_eq_dep _ _ _ _ _ _ H).
have H'' := (EqdepFacts.eq_dep_dep1 _ _ _ _ _ _ H').
case: H'' => h.
by rewrite [h]eq_axiomK /=.
Qed.

Notation fprod_type := (forall i : I, T_ i) (only parsing).

(** Definition and cardinal of [fprod] := dependent product of finTypes *)

Definition fprod : predArgType :=
  {fprod_fun : {ffun I -> {i : I & T_ i}} | [forall i : I, tag (fprod_fun i) == i] }.

Program Definition fprod_type_of_fprod (f : fprod) : fprod_type :=
  fun i => ecast j (T_ j) _ (tagged (val f i)).
Next Obligation.
case => f p i /= ; apply/eqP.
by move/forallP in p.
Defined.

Lemma fprod_of_fprod_type_ax (f : fprod_type) :
  [forall i : I, tag ([ffun i => existT T_ i (f i)] i) == i].
Proof.
by apply/forallP =>i ; rewrite ffunE.
Qed.
  
Definition fprod_of_fprod_type (f : fprod_type) : fprod :=
  exist _ [ffun i => existT _ i (f i)] (fprod_of_fprod_type_ax f). 

Coercion fprod_type_of_fprod : fprod >-> Funclass.

(* Canonical fprod_fun_finType := [finType of {ffun I -> {i : I & T_ i}}]. *)
(** TODO: fix canonical projections **)


Lemma fprodK : cancel fprod_type_of_fprod fprod_of_fprod_type.
Proof.
move => x.
rewrite /fprod_type_of_fprod /fprod_of_fprod_type.
apply: val_inj =>/=.
apply/ffunP => i; rewrite !ffunE.
case: x => f p /=.
rewrite [RHS]Tagged_eta.
set Ei := eqP (elimTF forallP p i).
apply EqdepFacts.eq_dep_eq_sigT.
apply EqdepFacts.eq_dep1_dep.
exact: EqdepFacts.eq_dep1_intro.
Qed.

Lemma fprodE g : forall x, (fprod_of_fprod_type g) x = g x.
Proof.
move=> i.
rewrite /fprod_of_fprod_type /fprod_type_of_fprod /=.
rewrite -/(eq_rect _ _ _ _ _).
set Ej := (eqP (elimTF forallP (fprod_of_fprod_type_ax g) i)).
rewrite -[g i](rew_opp_r T_ Ej).
f_equal.
apply: TaggedE.
rewrite -!Tagged_eta {1}ffunE /Tagged.
apply EqdepFacts.eq_dep_eq_sigT.
apply EqdepFacts.eq_dep1_dep.
apply: EqdepFacts.eq_dep1_intro.
by rewrite rew_opp_r.
Qed.

Lemma fprodP f1 f2 :
  (forall x, fprod_type_of_fprod f1 x = fprod_type_of_fprod f2 x) <-> f1 = f2.
Proof.
split=> [eq_f12 | -> //].
rewrite -[f1]fprodK -[f2]fprodK.
apply: val_inj =>/=.
apply/ffunP => x; rewrite !ffunE.
by rewrite eq_f12.
Qed.

Definition otagged
  (R : Type) (i : I) (F : T_ i -> R) (idx : R) (x : {i : I & T_ i}) :=
  match sumb (tag x == i) with
  | left prf => F (tagged' prf)
  | right _ => idx
  end.

Lemma card_fprod :
  #|fprod| = \big[muln/1%N]_(i : I) #|T_ i|.
Proof.
rewrite card_sub.
rewrite -[LHS]/#|family (fun i : I => [pred j : {i : I & T_ i} | tag j == i])|.
rewrite card_family.
set lhs := LHS; suff->: lhs = foldr muln 1%N [seq #|T_ i| | i : I]; rewrite {}/lhs.
Search "bigop".
Search reducebig.
by rewrite /image_mem foldr_map bigop.unlock /reducebig; f_equal; rewrite enumT.
f_equal; apply eq_map => i.
rewrite -sum1_card ; (under eq_bigr => i0 do rewrite inE).
rewrite -sum1_card.
(* pose IT := tag_finType T_. *)
pose h : T_ i -> _ := @Tagged I i T_.
pose h'0 := @tagged' i.
case Ecard: #|T_ i|.
{ rewrite !big_pred0 // => x.
  by rewrite inE -(ltnn 0); symmetry; rewrite -{2}Ecard; apply/card_gt0P; exists x.
  move/eqP: Ecard; apply: contraTF; rewrite -leqn0 -ltnNge => Hi.
  apply/card_gt0P.
  by exists (tagged' Hi). }
have {Ecard} /card_gt0P [it0 _] : (0 < #|T_ i|)%N by rewrite Ecard.
pose h' := otagged id it0.
rewrite (reindex h); last first.
{ exists h'.
  move => it; rewrite inE => Hx.
  { rewrite /= /h' /h /otagged.
    case: sumb => prf; first by rewrite /tagged' (eq_axiomK (eqP prf)).
    exfalso.
    by rewrite eqxx in prf. }
  move=> x Hx.
  rewrite /h' /h /otagged.
  case: sumb => prf.
  { rewrite /= [x in RHS]Tagged_eta /=.
    (* and then *)
    apply EqdepFacts.eq_dep_eq_sigT.
    apply EqdepFacts.eq_dep1_dep.
    apply: EqdepFacts.eq_dep1_intro; first exact/eqP.
    move=> H0; rewrite /tagged'.
    by rewrite [eqP prf]eq_irrelevance. }
  exfalso; move/negbT/negP: prf; apply.
  by rewrite inE in Hx. }
apply: eq_bigl => j; by rewrite inE /= eqxx.
Qed.

Lemma gt0_prodn_cond (P : pred I) F :
  (0 < \prod_(i | P i) F i -> forall i, P i -> 0 < F i)%N.
Proof.
move=> Hpos i; apply/implyP; move: i; apply/forallP; move: Hpos.
apply: contraTT.
rewrite negb_forall; case/existsP => x.
rewrite negb_imply; case/andP => h1.
rewrite -!eqn0Ngt; move/eqP => h2.
apply/eqP.
by rewrite (bigD1 x h1) h2 /= mul0n.
Qed.

Lemma gt0_prodn (F : I -> nat) :
  (0 < \prod_i F i -> forall i, 0 < F i)%N.
Proof. by move=> Hpos i; apply: (@gt0_prodn_cond predT). Qed.

Definition pick_notemp :
  (0 < #|fprod|)%N -> forall i : I, T_ i.
Proof.
rewrite /= card_fprod.
move/gt0_prodn => top i; move/(_ i) in top.
pose x := pick (T_ i).
case: pickP @x; first done.
by move/eq_card0 => H0; rewrite H0 in top.
Qed.

Lemma tagged'E (a : fprod) (i : I) (E : tag ((val a) i) == i) :
  tagged' E = a i.
Proof.
rewrite /tagged'.
rewrite /eq_rect -/(ecast y (T_ y) (eqP E) (tagged ((val a) i))).
case: a E => f p /= E.
rewrite /fprod_type_of_fprod /=.
rewrite [eqP E]eq_irrelevance; first exact/eqP.
move=> H; rewrite [eqP (elimTF forallP p i)]eq_irrelevance ; first exact/eqP.
Qed.

Definition ftagged (H : (0 < #|fprod|)%N) (f : {ffun I -> {i : I & T_ i}}) (i : I) :=
  @otagged (T_ i) i id (pick_notemp H i) (f i).

Lemma ftaggedE (t : fprod) H i : ftagged H (val t) i = t i.
Proof.
rewrite /ftagged /otagged.
case: sumb.
{ by move=> E; rewrite tagged'E. }
move=> /negbT /negP K; exfalso; apply: K.
move: i; apply/forallP/(tagged t). (* might be refactor(iz)ed *)
Qed.

Definition dffun_of_fprod (f : fprod) : {dffun forall i : I, T_ i} :=
  [ffun x => f x].

Lemma fprod_of_dffun_ax (f : {dffun forall i : I, T_ i}) : 
  [forall i : I, tag ([ffun i => existT T_ i (f i)] i) == i].
Proof.
by apply/forallP=>i ; rewrite ffunE.
Qed.

Definition fprod_of_dffun (f : {dffun forall i : I, T_ i}) : fprod :=
  exist _ [ffun i => existT _ i (f i)] (fprod_of_dffun_ax _).

Lemma dffun_of_fprodK : cancel dffun_of_fprod fprod_of_dffun.
Proof.
move=> x.
apply: val_inj =>/=.
apply/ffunP => i; rewrite !ffunE.
case: x => f p /=.
rewrite [RHS]Tagged_eta.
set Ei := eqP (elimTF forallP p i).
apply EqdepFacts.eq_dep_eq_sigT.
apply EqdepFacts.eq_dep1_dep.
exact: EqdepFacts.eq_dep1_intro.
Qed.

Lemma fprod_of_dffunK : cancel fprod_of_dffun dffun_of_fprod.
Proof.
move=> x.
apply/ffunP => i ; rewrite !ffunE.
rewrite /fprod_of_dffun/=.
(* by rewrite fprodE.
Qed. *)
Admitted.

End Finite_product_structure.

Notation "[ 'fprod' i : I => F ]" := (fprod_of_fprod_type (fun i : I => F))
  (at level 0, i ident, only parsing) : fun_scope.

Notation "[ 'fprod' : I => F ]" := (fprod_of_fprod_type (fun _ : I => F))
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fprod' i => F ]" := [fprod i : _ => F]
  (at level 0, i ident, format "[ 'fprod'  i  =>  F ]") : fun_scope.

Notation "[ 'fprod' => F ]" := [fprod : _ => F]
  (at level 0, format "[ 'fprod' =>  F ]") : fun_scope.

Lemma big_tag_cond (R : Type) (idx : R) (op : Monoid.com_law idx)
  (I : finType) (T_ : I -> finType) (Q_ : forall i, {set T_ i})
  (P_ : forall i : I, T_ i -> R) (i : I) (E : (0 < #|fprod T_|)%N) :
  \big[op/idx]_(j in [finType of {i0 : I & T_ i0}] | (tag j == i) && (otagged id (pick_notemp E i) j \in Q_ i)) otagged (P_ i) idx j =
  \big[op/idx]_(j in Q_ i) P_ i j.
Proof.
(* pose IT := tag_finType T_. *)
pose h : T_ i -> _ := @Tagged I i T_.
pose h'0 := @tagged' _ _ i.
case Ecard: #|T_ i|.
{ rewrite !big_pred0 // => x.
  move/eqP: Ecard; apply: contraTF; rewrite -leqn0 -ltnNge => Hi.
  by apply/card_gt0P; exists x.
  move/eqP: Ecard; apply: contraTF; rewrite -leqn0 -ltnNge => Hi.
  apply/card_gt0P.
  (* case/and3P in Hi.
   (* Error: tampering with discharged assumptions of "in" tactical *) *)
  case/and3P: Hi =>/= t H1 H2.
  by exists (otagged id (pick_notemp E i) x). }
have {Ecard} /card_gt0P [it0 _] : (0 < #|T_ i|)%N by rewrite Ecard.
pose h' := otagged id it0.
rewrite (reindex h); last first.
{ exists h'.
  move => it; rewrite inE => Hx.
  { rewrite /= /h' /h /otagged.
    case: sumb => prf; first by rewrite /tagged' (eq_axiomK (eqP prf)).
    exfalso.
    by rewrite eqxx in prf. }
  move=> x Hx.
  rewrite /h' /h /otagged.
  case: sumb => prf.
  { rewrite /= [x in RHS]Tagged_eta /=.
    (* and then *)
    apply EqdepFacts.eq_dep_eq_sigT.
    apply EqdepFacts.eq_dep1_dep.
    apply: EqdepFacts.eq_dep1_intro; first exact/eqP.
    move=> H0; rewrite /tagged'.
    by rewrite [eqP prf]eq_irrelevance. }
  exfalso; move/negbT/negP: prf; apply.
  rewrite inE in Hx.
  by case/and3P: Hx. }
rewrite /= eqxx /=.
apply: eq_big => j.
{ congr in_mem. (* TODO: simplify *)
  rewrite /otagged /tagged' /=.
  case: sumb; last by rewrite eqxx.
  by move=> E'; f_equal; rewrite [eqP E']eq_irrelevance. }
move=> H; rewrite /otagged /tagged' /=.
case: sumb; last by rewrite eqxx.
by move=> E'; f_equal; rewrite [eqP E']eq_irrelevance.
Qed.

Arguments big_tag_cond [R idx op I T_] _ _ _ _.

(* big_tag might be deduced from big_tag_cond *)
Lemma big_tag (R : Type) (idx : R) (op : Monoid.com_law idx)
  (I : finType) (T_ : I -> finType)
  (P_ : forall i : I, T_ i -> R) (i : I) :
  \big[op/idx]_(j in [finType of {i0 : I & T_ i0}] | tag j == i) otagged (P_ i) idx j =
  \big[op/idx]_(j in T_ i) P_ i j.
Proof.
(* pose IT := tag_finType T_. *)
pose h : T_ i -> _ := @Tagged I i T_.
pose h'0 := @tagged' _ _ i.
case Ecard: #|T_ i|.
{ rewrite !big_pred0 // => x.
  move/eqP: Ecard; apply: contraTF; rewrite -leqn0 -ltnNge => Hi.
  by apply/card_gt0P; exists x.
  move/eqP: Ecard; apply: contraTF; rewrite -leqn0 -ltnNge => Hi.
  by apply/card_gt0P; exists (tagged' (proj2 (andP Hi))). }
have {Ecard} /card_gt0P [it0 _] : (0 < #|T_ i|)%N by rewrite Ecard.
pose h' := otagged id it0.
rewrite (reindex h); last first.
{ exists h'.
  move => it; rewrite inE => Hx.
  { rewrite /= /h' /h /otagged.
    case: sumb => prf; first by rewrite /tagged' (eq_axiomK (eqP prf)).
    exfalso.
    by rewrite eqxx in prf. }
  move=> x Hx.
  rewrite /h' /h /otagged.
  case: sumb => prf.
  { rewrite /= [x in RHS]Tagged_eta /=.
    (* and then *)
    apply EqdepFacts.eq_dep_eq_sigT.
    apply EqdepFacts.eq_dep1_dep.
    apply: EqdepFacts.eq_dep1_intro; first exact/eqP.
    move=> H0; rewrite /tagged'.
    by rewrite [eqP prf]eq_irrelevance. }
  exfalso; move/negbT/negP: prf; apply.
  by rewrite inE in Hx. }
rewrite /otagged.
apply: eq_big => j; first by rewrite /otagged /= eqxx /=.
move=> H; rewrite /otagged /tagged' /=.
case: sumb; last by rewrite eqxx.
by move=> E; f_equal; rewrite [eqP E]eq_irrelevance.
Qed.

Arguments big_tag [R idx op I T_] _ _.

Section big_fprod.
  Variable R : realFieldType.
  Variable I : finType.
  Variable T_ : forall i : I, finType.
  Variable P_ : forall i : I, {ffun T_ i -> R}.
  Let T := fprod T_.

  Print fprod.
  Definition ofprod (idx : fprod T_) (f : {ffun I -> {i : I & T_ i}}) : fprod T_.
    (*
:=
    match sumb ([forall i : I, tag (f i) == i]) with
    | left prf => (* @Build_fprod I T_ f prf *) exist _ [ffun i => f i] (_)
    | right _ => idx
    end.
     *)
  Admitted.

  Local Open Scope ring_scope.

  Lemma big_fprod_dep (Q : pred {ffun I -> {i : I &  (T_ i)}}) :
      \big[+%R/0]_(t : fprod _ | Q (val t)) \big[*%R/1%R]_(i in I) P_ i (t i) =
        \big[+%R/0%R]_(g in family (fun i : I => [pred j : {i : I &  (T_ i)} | tag j == i]) | g \in Q)
         \big[*%R/1%R]_(i : I) (otagged (P_ i) 0%R (g i)).
    Proof.
      case Ecard: #|T|.
      { rewrite !big_pred0 // => x.
        move/eqP: Ecard; apply: contraTF; rewrite -leqn0 -ltnNge => H.
        by apply/card_gt0P; exists x.
        move/eqP: Ecard; apply: contraTF; rewrite -leqn0 -ltnNge => H.
        apply/card_gt0P.
        have /andP [H1 H2] := H.
        by exists (exist (fun x => x \in family (fun i : I => [pred j | tag j == i])) x H1). }
      have {Ecard} /card_gt0P [it0 _] : (0 < #|T|)%N by rewrite Ecard.
      pose h := @fprod_fun I T_.
      pose h' := ofprod it0.
      rewrite (reindex h); last first.
      { exists h'.
        move => it; rewrite inE => Hx.
        { rewrite /= /h' /h /ofprod.
          case: sumb => prf; case: it prf Hx =>//= f p p'.
          by rewrite [p]eq_irrelevance.
          by rewrite p in p'. }
        move=> x Hx.
        rewrite /h' /h /ofprod.
        case: sumb => prf; case: x prf Hx => //= f p p'.
        by rewrite !inE /= p in p'. }
      apply: eq_big => a.
      { case: a => /= a Ha; rewrite inE.
        apply: (_ : ?[n] = true -> Q a = ?n && (a \in Q)) =>//.
        move=>->//. }
      move=> _; apply: eq_bigr => i Hi.
      rewrite /otagged /tagged' /=.
      case: sumb =>//= H.
      { f_equal; symmetry; clear Hi.
        rewrite -/(tagged' _).
        apply: tagged'E. }
      case: a H => f p /= H.
      by rewrite (forallP p i) in H.
    Qed.

    Lemma big_fprod :
      \big[+%R/0%R]_(t : T) \big[*%R/1%R]_(i in I) P_ i (t i) =
        \big[+%R/0%R]_(g in family (fun i : I => [pred j : {i : I & (T_ i)} | tag j == i]))
         \big[*%R/1%R]_(i : I) (otagged (P_ i) 0%R (g i)).
    Proof.
      rewrite (big_fprod_dep predT).
      by apply: eq_bigl => g; rewrite inE andbC.
    Qed.

End big_fprod.
