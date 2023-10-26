From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.





(******************************************************************************)
(** 
    General lemmas which are useful but which are not specially about BelGames
    and HRtransforms

    DECIDABILITY OF EQTYPES:

     Lemma eqType_dec_prop :
       forall (T : eqType) (t1 t2 : T), t1 = t2 \/ t1 <> t2.
     Lemma eqType_dec :
       forall (T : eqType) (t1 t2 : T), {t1 = t2} + {t1 <> t2}.

    PICK:

     Definition pick_nonemptyset :
       forall (X : finType) (B : {set X}), B != set0 -> X.
     Definition pick_nonemptyset_sig :
       forall (X : finType) (B : {set X}),
       B != set0 -> {x : X | x \in B}.

    SUBSET LEMMAS:

     Lemma subset_set0 :
       forall (T : finType) (A B : {set T}),
       (A \subset B) && (A \subset ~: B) = (A == set0).
     Lemma subsetF :
       forall (T : finType) (A B : {set T}),
       A \subset B ->
       A \subset ~: B -> forall t : T, t \in A -> Logic.False.
     Lemma subset_disjoint :
       forall (T : finType) (A B : {set T}),
       [disjoint A & B] ->
       forall B0 : {set T},
       B0 != set0 -> B0 \subset A -> ~~ (B0 \subset B).

    EXISTS LEMMAS:

     Lemma exists_l :
       forall (T : Type) (P Q : T -> Prop),
       (exists x : T, P x /\ Q x) -> exists x : T, P x.
     Lemma exists_r :
       forall (T : Type) (P Q : T -> Prop),
       (exists x : T, P x /\ Q x) -> exists x : T, Q x.
     Lemma existsb_l :
       forall (T : finType) (P Q : pred T),
       [exists x, P x && Q x] -> [exists x, P x].
     Lemma existsb_r :
       forall (T : finType) (P Q : pred T),
       [exists x, P x && Q x] -> [exists x, Q x].
     Lemma set0_existsF :
       forall (X : finType) (B : {set X}),
       (B == set0) = ~~ [exists x, x \in B].

    SIG_BIG_DEP ON SIGS (NOT ON SIGTS):

     Definition osig :
       forall (X : finType) (P : pred X), X -> {? x | P x}.
     Lemma osig_bij :
       forall (X : finType) (P : pred X) (x : X),
       P x -> omap ((@sval) X (fun x0 : X => P x0)) (osig P x) = Some x.
     Lemma sig_big_dep2 :
       forall (R : Type) (idx : R) (op : Monoid.com_law idx)
         (X : finType) (P : pred X) (f : forall x : X, P x -> R),
       \big[op/idx]_s f (tag s) (tagged s) =
       \big[op/idx]_(x | P x)
          match boolP (P x) with
          | @AltTrue _ _ h => f x h
          | @AltFalse _ _ _ => idx
          end.
     Lemma sig_big :
       forall (R : Type) (idx : R) (op : Monoid.com_law idx)
         (X : finType) (P : pred X) (f : X -> R),
       \big[op/idx]_s f (tag s) = \big[op/idx]_(x | P x) f x.
     Definition set1_oinv : forall X : finType, {set X} -> option X.

    BIG LEMMAS:

     Lemma big_card1 :
       forall (R : Type) (idx : R) (op : Monoid.com_law idx)
         (X : finType) (f : {set X} -> R),
       \big[op/idx]_(A | #|A| == 1) f A = \big[op/idx]_x f [set x].
     Lemma big_setI_distrl :
       forall (R : Type) (zero : R) (times : Monoid.mul_law zero)
         (plus : Monoid.add_law zero times) (T : finType)
         (P : pred {set T}) (h : {set T} -> {set T})
         (f g : {set T} -> R),
       \big[plus/zero]_(A | P (h A)) times (g A) (f (h A)) =
       \big[plus/zero]_(B | P B)
          times (\big[plus/zero]_(A | h A == B) g A) (f B).

    NUM LEMMAS:

     Context {R : numFieldType}.
     Lemma mulr_ll :
       forall x y z : R, y = z -> x * y = x * z.
     Lemma mulr_rr :
       forall x y z : R, y = z -> y * x = z * x.
     Lemma neq01 : (0 : R) != 1.
     Lemma addr_gte0 :
       forall x y : R, 0 < x -> 0 <= y -> 0 < x + y.
     Lemma sum_ge0 :
       forall (X : finType) (P : pred X) (f : X -> R),
       (forall x : X, P x -> 0 <= f x) -> 0 <= \sum_(x | P x) f x.
     Lemma sum_ge0_eq0E :
       forall (X : finType) (P : pred X) (f : X -> R),
       (forall x : X, P x -> 0 <= f x) ->
       \sum_(x | P x) f x = 0 <-> (forall x : X, P x -> f x = 0).
     Lemma sum_ge0_neq0E :
       forall (X : finType) (P : pred X) (f : X -> R),
       (forall x : X, P x -> 0 <= f x) ->
       \sum_(x | P x) f x != 0 -> exists x : X, P x && (0 < f x).
     Lemma sum_div :
       forall (X : finType) (P : pred X) (cst : R)
         (f : X -> R),
       \sum_(x | P x) f x / cst = (\sum_(x | P x) f x) / cst.
     Lemma sum_div_eq1 :
       forall (X : finType) (P : pred X) (cst : R),
       cst != 0 ->
       forall f : X -> R,
       (\sum_(x | P x) f x / cst == 1) = (\sum_(x | P x) f x == cst).
   End

 *)
(******************************************************************************)
Section SomeLemmas.


  (* Not used *)
  Lemma nat_split012 (n : nat) :
    (n == 0)%N || (n == 1)%N || (n > 1)%N.
  Proof. by case n => // ; case => //. Qed.





  (** Decidability of eqTypes **)
  Lemma eqType_dec_prop (T : eqType) (t1 t2 : T) :
    t1 = t2 \/ t1 <> t2.
  Proof.
  case (boolP (t1 == t2)) => /eqP H.
  - exact: or_introl.
  - exact: or_intror.
  Qed.

  Lemma eqType_dec (T : eqType) (t1 t2 : T) :
    {t1 = t2} + {t1 <> t2}.
  Proof.
  case (boolP (t1 == t2)) => /eqP Ht.
  - by left.
  - by right.
  Qed.


  Lemma pick_set1E (T : finType) (x0 : T) : [pick x in [set x0]] = Some x0.
  Proof.
    case: pickP.
    - by move=> x; rewrite inE; move/eqP=>->.
    - by move/(_ x0); rewrite inE eqxx.
  Qed.


  Definition pick_nonemptyset {X : finType} (B : {set X}) (HB : B != set0) : X.
  case (pickP [pred x in B]) => [x _ | H0].
  - exact: x.
  - by rewrite (cards0_eq (eq_card0 H0)) eqxx in HB.
  Defined.

  Definition pick_nonemptyset_sig {X : finType} (B : {set X}) (HB : B != set0) : {x : X | x \in B}.
  exists (pick_nonemptyset HB).
  rewrite /pick_nonemptyset => //=.
  case (pickP [pred x in B]) => //= H0.
  have HB' := HB.
  by rewrite (cards0_eq (eq_card0 H0)) eqxx in HB'.
  Defined.

  Lemma pick_set1 {X : finType} (x : X) A (HA : A = [set x]) (Hx : A != set0) :
    pick_nonemptyset Hx = x.
  Proof.
  rewrite /pick_nonemptyset.
  case pickP => /= [y|H].
  - by rewrite HA in_set1 => /eqP ->.
  - have := H x => /= ; by rewrite {1}HA in_set1 eqxx.
  Qed.

  (** The only subset of B and B^c is set0 **)
  Lemma subset_set0 {T : finType} (A B : {set T}) :
    (A \subset B) && (A \subset ~:B) = (A == set0).
  Proof.
  case (boolP (A == set0)) => [/eqP -> | /set0Pn [x Hx]].
  - by rewrite !sub0set.
  - case (boolP (A \subset B)) ; case (boolP (A \subset ~:B)) => //.
    rewrite !subsetE => /pred0P H1 /pred0P H2.
    have := H2 x.
    have := H1 x.
    rewrite /= Hx !andbT.
    move => Hx1 /negP/negP Hx2.
    by rewrite -in_setC setCK Hx2 in Hx1.
  Qed.


  Lemma subsetF {T : finType} (A B : {set T}) :
    A \subset B -> A \subset ~:B -> forall t, t \in A -> Logic.False.
  Proof.
  move => H1 H2 t Ht.
  have HA : A = set0. by apply/eqP ; rewrite -(subset_set0 _ B) H1 H2.
  by rewrite HA in_set0 in Ht.
  Qed.

  Lemma subset_disjoint {T : finType} (A B : {set T}) :
    [disjoint A & B] ->
    forall B0 : {set T},
    B0 != set0 ->
    B0 \subset A -> ~~ (B0 \subset B).
  Proof.
  move => HAB B0 Hb0 /subsetP /= H.
  apply /subsetPn.
  have [x Hx] := pick_nonemptyset_sig Hb0.
  exists x => //.
  by rewrite (disjointFr HAB (H x Hx)).
  Qed.
  
  (** Split 'exists' predicates **)
  Lemma exists_l (T : Type) (P Q : T -> Prop) :
    (exists x, P x /\ Q x) -> (exists x, P x).
  Proof.
  case => x [H _] ; by exists x.
  Qed.

  Lemma exists_r (T : Type) (P Q : T -> Prop) :
    (exists x, P x /\ Q x) -> (exists x, Q x).
  Proof.
  case => x [_ H] ; by exists x.
  Qed.

  (* The only one used *)
  Lemma existsb_l (T : finType) (P Q : pred T) :
    [exists x, P x && Q x] -> [exists x, P x].
  Proof.
  move => /existsP ; case => x /andP [H _].
  apply/existsP ; by exists x.
  Qed.

  Lemma existsb_r (T : finType) (P Q : pred T) :
    [exists x, P x && Q x] -> [exists x, Q x].
  Proof.
  move => /existsP ; case => x /andP [_ H].
  apply/existsP ; by exists x.
  Qed.


  Lemma set0_existsF (X : finType) (B : {set X}) :
    (B == set0) = (~~ [exists x, x \in B]).
  Proof.
  case (boolP [exists x, x \in B]) => /existsP/set0Pn => [H|-> //].
  by rewrite (negbTE H).
  Qed.



  Section SigBigDep2.
    (** Proof of a version of sig_big_dep about 'sig' (but not about 'sigT') **)


    (* Projection from 'X' into 'option {x : X | P x}' -- needed for sig_big_dep2 *)
    Definition osig (X : finType) (P : pred X) : X -> option {x : X | P x}
      := (fun x => match boolP (P x) with AltTrue h => Some (exist P x h) | _ => None end).

    Lemma osig_bij (X : finType) (P : pred X) : forall x : X, P x -> omap sval (osig P x) = Some x.
    move => x Hx.
    rewrite/omap/obind/oapp/osig => //=.
    case (boolP (P x)) => [Hx' //|] ; by rewrite Hx.
    Qed.

    Lemma sig_big_dep2 {R} {idx : R} {op : Monoid.com_law idx} {X : finType} (P : pred X) f :
      \big[op/idx]_(s : {x : X | P x}) f (tag s) (tagged s) = \big[op/idx]_(x : X | P x) match boolP (P x) with AltTrue h => f x h | _ => idx end.
    Proof.
    rewrite (reindex_omap (op:=op) (sval) (osig P) (@osig_bij _ P)).
    apply eq_big => [[x Hx]|[x Hx] _] /=.
    - rewrite /osig ; case (boolP (P x)) => [Hx'|] ; last by rewrite Hx.
        by rewrite (Eqdep_dec.eq_proofs_unicity (@eqType_dec_prop _ ) Hx Hx') eqxx.
    - case (boolP (P x)) => [Hx'|] ; last by rewrite Hx.
        by rewrite (Eqdep_dec.eq_proofs_unicity
                    (@eqType_dec_prop _ ) ((ssrfun.svalP (exist (fun x0 : X => P x0) x Hx)))).
    Qed.

    (* Not used *)
    Lemma sig_big R (idx : R) (op : Monoid.com_law idx) (X : finType) (P : pred X) f :
      \big[op/idx]_(s : {x : X | P x}) f (tag s) = \big[op/idx]_(x : X | P x) f x.
    Proof.
    rewrite (sig_big_dep2 (fun x _ => f x)).
    apply eq_bigr => x Hx.
    case (boolP (P x)) => [//|] ; by rewrite Hx.
    Qed.

  End SigBigDep2.




  Section Set1_inverse.
    (** option-inverse of (set1 : X -> {set X}) **)
    (* not used *)
    
    (* Projection from '{set X}' into 'option X' -- o-inverse of set1 -- neede for big_card1 *)
    Definition set1_oinv {X : finType} : {set X} -> option X
      := fun A => match boolP (#|A| > 0)%N with
                  | AltTrue h => if (#|A| == 1)%N
                                 then let (x,_,_) := eq_bigmax_cond (fun=>0%N) h in Some x
                                 else None
                  | _ => None
                  end.

    Lemma set1_ocancel {X : finType} :
      ocancel (@set1_oinv X) set1.
    Proof.
    move => A.
    rewrite /oapp /set1_oinv.
    case (boolP (#|A| > 0)%N) => H //.
    destruct (eq_bigmax_cond (fun=>0%N) H) as [x Hx _].
    case (boolP (#|A| == 1)%N) => // /cards1P [y Hy].
    rewrite Hy in_set1 in Hx.
    by rewrite Hy (eqP Hx).
    Qed.

    Lemma set1_oinv_pcancel {X : finType} :
      pcancel (@set1 X) set1_oinv.
    Proof.
    move => x.
    rewrite /set1_oinv.
    case (boolP (#|[set x]| > 0)%N) => [Hx|] ; last by rewrite cards1.
    rewrite cards1 eqxx //.
    destruct (eq_bigmax_cond (fun=>0%N) Hx) as [y Hy _].
    rewrite in_set1 in Hy.
    by rewrite (eqP Hy).
    Qed.

    Lemma set1_oinv_omap {X : finType} (A : {set X}) (HA : #|A| == 1%N):
      omap set1 (set1_oinv A) = Some A.
    Proof.
    rewrite /omap/obind/oapp/set1_oinv.
    case (boolP (0 < #|A|)%N) => H0 ; case (boolP (#|A| == 1)%N) => H1.
    - destruct (eq_bigmax_cond (fun=>0%N) H0) as [w Hw _].
      destruct (cards1P H1) as [w' Hw'].
      rewrite Hw' in_set1 in Hw.
      by rewrite Hw' (eqP Hw).
    - by rewrite (eqP HA) in H1.
    - by rewrite -eqn0Ngt (eqP H1) in H0.
    - by rewrite (eqP HA) in H1.
    Qed.

  (* Bigop on singletons *)
  Lemma big_card1 R (idx : R) (op : Monoid.com_law idx) (X : finType) (f : {set X} -> R) :
    \big[op/idx]_(A : {set X} | #|A| == 1%N) f A = \big[op/idx]_(x : X) f [set x].
  Proof.
  rewrite (reindex_omap set1 set1_oinv) => [|A HA].
  - apply: eq_bigl => x.
    by rewrite set1_oinv_pcancel cards1 !eqxx.
  - rewrite /omap /obind /oapp /set1_oinv.
    case (boolP (0 < #|A|)%N) => [Hcard|] ; last by rewrite (eqP HA).
    rewrite HA.
    destruct (eq_bigmax_cond (fun=>0%N) Hcard) as [x Hx _].
    move: HA => /cards1P [y Hy].
    rewrite Hy in_set1 in Hx.
    by rewrite Hy (eqP Hx).
  Qed.

  End Set1_inverse.




  (** Similar to partition_big + big_distrl **)
  Lemma big_setI_distrl {R} {zero : R} {times : Monoid.mul_law zero} {plus : Monoid.add_law zero times} {T : finType} (P : pred {set T}) (h : {set T} -> {set T}) (f g : {set T} -> R) :
    \big[plus/zero]_(A : {set T} | P (h A)) times (g A) (f (h A))
    =
    \big[plus/zero]_(B : {set T} | P B) times (\big[plus/zero]_(A : {set T} | h A == B) g A) (f B).
  Proof.
  under [RHS]eq_bigr do rewrite big_distrl /=.
  rewrite [LHS](partition_big h P) => //.
  apply: eq_bigr => B HB ; apply: eq_big => [A | A /andP [_ HA2]].
  - case (boolP (h A == B)) => H ; last by rewrite (negbTE H) andbF.
    by rewrite H (eqP H) HB. 
  - by rewrite (eqP HA2).
  Qed.


  (** Split a commutative bigop according to a predicate P **)
  (* From theories.common *)
  Lemma split_big {R} {idx : R} {op : Monoid.com_law idx} {I} [r : seq I] P Q f :
    \big[op/idx]_(i <- r | P i) f i =
    op (\big[op/idx]_(i <- r | P i && Q i) f i)
       (\big[op/idx]_(i <- r | P i && ~~ Q i) f i).
  Proof.
  exact: bigID.
  Qed.

End SomeLemmas.

Section NumLemmas.

  Context {R : numFieldType}.
  Implicit Type X : finType.

  Lemma mulr_ll (x y z : R) :
    y = z -> x * y = x * z.
  Proof. by move => ->. Qed.

  Lemma mulr_rr (x y z : R) :
    y = z -> y * x = z * x.
  Proof. by move => ->. Qed.



  

  Lemma neq01 : ((0:R) != 1).
  Proof.
  have := ltr01 (R:=R) ; by rewrite lt0r eq_sym => /andP [H _].
  Qed.

  Lemma addr_gte0 [x y : R] : 0 < x -> 0 <= y -> 0 < x + y.
  Proof.
  rewrite le0r => Hx /orP ; case => [/eqP ->| Hy].
  - by rewrite addr0.
  - exact: addr_gt0.
  Qed.

  Lemma sum_ge0 {X} (P : pred X) (f : X -> R) :
    (forall x, P x -> f x >= 0) -> \sum_(x | P x) f x >= 0.
  Proof.
  move => H ; apply big_ind => // ; exact: addr_ge0.
  Qed.
  
  Lemma prod_ge0 {X} (P : pred X) (f : X -> R) :
    (forall x, P x -> f x >= 0) -> \prod_(x | P x) f x >= 0.
  Proof.
  move => H ; apply big_ind ; rewrite ?ler01//.
  exact: mulr_ge0.
  Qed.

  Lemma sum_ge0_eq0E {X} (P : pred X) (f : X -> R) :
    (forall x, P x -> f x >= 0) -> \sum_(x | P x) f x = 0 <-> forall x, P x -> f x = 0.
  Proof.
  move => Hge0 ; split => [Hsum x Hx | Heq0].
  - apply/eqP/negP => /negP Hcontra.
    rewrite (bigD1 x) //= in Hsum.
    have Hge0' : forall y, P y && (y != x) -> 0 <= f y. move => y /andP [Hy _] ; exact: Hge0.
    have Hgt0 : f x > 0. by rewrite lt0r Hge0 // Hcontra.
    have := addr_gte0 Hgt0 (sum_ge0 Hge0').
    by rewrite Hsum lt0r eqxx andFb.
  - by rewrite (eq_bigr (fun=>0)) // big1.
  Qed.


  Lemma sum_ge0_neq0E {X} (P : pred X) (f : X -> R) :
    (forall x, P x -> f x >= 0) -> \sum_(x | P x) f x != 0 -> exists x : X, P x && (f x > 0).
  Proof.
  move => Hge0 Hsum.
  have Hsum2 : \sum_(x | P x) f x > 0. by rewrite lt0r Hsum sum_ge0 //.
  have Hex : exists x : X, ~~ ~~ (P x && (f x != 0)).
  apply/forallPn/negP => /forallP Hcontra.
  have Hcontra2 : \sum_(x | P x) f x = 0. apply sum_ge0_eq0E => // x Hx.
  move: (Hcontra x) ; by rewrite Hx andTb Bool.negb_involutive => /eqP ->.
  move: Hsum2 ; by rewrite Hcontra2 lt0r eqxx andFb.
  destruct Hex as [x Hx].
  exists x.
  have [Hx1 Hx2] := andP (negPn Hx).
  by rewrite lt0r Hx1 Hx2 Hge0.
  Qed.

  Lemma sum_div {X} (P : pred X) (cst : R) (f : X -> R) :
    \sum_(x : X | P x) f x / cst = (\sum_(x : X | P x) f x) / cst.
  Proof. by rewrite big_distrl.
  Qed.

  Lemma sum_div_eq1 {X} (P : pred X) (cst : R) (Hcst : cst != 0) (f : X -> R) :
    (\sum_(x : X | P x) f x / cst == 1) = (\sum_(x : X | P x) f x == cst).
  Proof.
  rewrite -(divr1 1) sum_div eqr_div //.
  - by rewrite mulr1 mul1r.
  - by rewrite eq_sym neq01.
  Qed.



  (* Lemma big_partitionS {X} (f : {set X} -> X -> R) : *)
  Lemma big_partitionS [Y] (idx : Y) (op : Monoid.com_law idx) [X] (f : {set X} -> X -> Y) :
    \big[op/idx]_(A : {set X}) (\big[op/idx]_(x in A) f A x) = \big[op/idx]_(x : X) \big[op/idx]_(A : {set X} | x \in A) f A x.
  Proof.
  set pair_sig : finType := [finType of {p : {set X} * X | p.2 \in p.1}].
  set f1 : pair_sig -> {set X} := fun s => (val s).1.
  set f2 : pair_sig -> X := fun s => (val s).2.
  - have proof1 :
      \big[op/idx]_x \big[op/idx]_(A : {set X} | x \in A) f A x =
      \big[op/idx]_x \big[op/idx]_(s : pair_sig | (f2 s) == x) f (f1 s) (f2 s).
    apply eq_bigr => x _.
    set f1inv : {set X} -> option pair_sig := fun A => match (boolP (x \in A)) with AltTrue h => Some (exist _ (A,x) h) | _ => None end.
    rewrite (reindex_omap f1 f1inv) => /=.
    + apply eq_big => /= s ;  destruct s as [[A y] Hy] ; simpl in Hy.
      * rewrite /f1/f1inv/f2 => /=.
        case (boolP (x \in A)) => Hx /=.
        - case (boolP (y == x)) => H0 //=.
          + apply/eqP ; apply f_equal.
            have H :  (@sval) ({set X} * X) (fun a : {set X} * X => a.2 \in a.1) (exist (fun x0 : {set X} * X => x0.2 \in x0.1) (A, x) Hx) =
                      (@sval) ({set X} * X) (fun a : {set X} * X => a.2 \in a.1) (exist (fun p : {set X} * X => p.2 \in p.1) (A, y) Hy).
            by simpl ; rewrite (eqP H0).
            apply (eq_sig _ _ H) => //=.
            exact: (Eqdep_dec.eq_proofs_unicity (@eqType_dec_prop bool_eqType)).
          + by apply/eqP ; case => /eqP ; rewrite eq_sym (negbTE H0).
        - symmetry ; apply/eqP => Hcontra.
          by rewrite -Hcontra Hy in Hx.
      * rewrite /f1/f2 => /= /andP [Hx Hinv].
        move: Hinv ; rewrite /f1inv.
        case (boolP (x\in A)) => H ; last by rewrite Hx in H.
        by move/eqP ; case => ->.
    + rewrite /omap/obind/oapp/f1inv => A Hx.
      by case (boolP (x \in A)) => // ; rewrite Hx.
  - have proof2 :
      \big[op/idx]_(A : {set X}) (\big[op/idx]_(x in A) f A x) =
      \big[op/idx]_(A : {set X}) (\big[op/idx]_(s : pair_sig | f1 s == A) f (f1 s) (f2 s)).
    apply eq_bigr => A _.
    set f2inv : X -> option pair_sig := fun x => match (boolP (x \in A)) with AltTrue h => Some (exist _ (A,x) h) | _ => None end.
    rewrite (reindex_omap f2 f2inv) => /=.
    + apply eq_big => /= s ;  destruct s as [[B x] HB] ; simpl in HB.
      * rewrite /f1/f2inv/f2 => /=.
        case (boolP (x \in A)) => HA /=.
        - case (boolP (B == A)) => H0 //=.
          + apply/eqP ; apply f_equal.
            have H :  (@sval) ({set X} * X) (fun a : {set X} * X => a.2 \in a.1) (exist (fun x0 : {set X} * X => x0.2 \in x0.1) (A, x) HA) =
                      (@sval) ({set X} * X) (fun a : {set X} * X => a.2 \in a.1) (exist (fun p : {set X} * X => p.2 \in p.1) (B, x) HB).
            by simpl ; rewrite (eqP H0).
            apply (eq_sig _ _ H) => //=.
            exact: (Eqdep_dec.eq_proofs_unicity (@eqType_dec_prop bool_eqType)).
          + by apply/eqP ; case => /eqP ; rewrite eq_sym (negbTE H0).
        - symmetry ; apply/eqP => Hcontra.
          by rewrite -Hcontra HB in HA.
      * rewrite /f1/f2 => /= /andP [Hx Hinv].
        move: Hinv ; rewrite /f2inv.
        case (boolP (x\in A)) => H ; last by rewrite Hx in H.
        by move/eqP ; case => ->.
    + rewrite /omap/obind/oapp/f2inv => x Hx.
      by case (boolP (x \in A)) => // ; rewrite Hx.
  - rewrite proof2 proof1.
    rewrite -[LHS](partition_big f1 (P:=predT) predT) => //.
    rewrite -[RHS](partition_big f2 (P:=predT) predT) => //.  
  Qed.


  Lemma sum_of_sumE {X : finType} (f : {set X} -> R) (P : pred {set X}):
    \sum_(x : X) \sum_(A : {set X} | P A && (x \in A)) f A = \sum_(A | P A) \sum_(w in A) f A.
  Proof.
  rewrite !pair_big_dep /=.
  rewrite (reindex (fun p => (p.2,p.1))) //=.
  exists (fun p => (p.2,p.1)) ; by case.
  Qed.

  Lemma sum_cardiv {X : finType} (A : {set X}) (H : (#|A| > 0)%N):
    \sum_(w in A) #|A|%:R^-1 = (1 : R).
  Proof.
  rewrite big_const iter_addr addr0 /=.
  rewrite -(mulr_natl #|A|%:R^-1 #|A|) divff //=.
  by rewrite pnatr_eq0 -lt0n.
  Qed.



End NumLemmas.
