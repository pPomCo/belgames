(* ************************************************************************************ *)
(* Numerical lemmas

   Section NumLemmas:                                                   (to be integrated)
     Lemmas on numDomainTypes (mostly about \sum)

   Section NumFieldLemmas:                                              (to be integrated)
     Lemmas on numFieldTypes

 *)
(* ************************************************************************************ *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import ssrAC div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly.

From mathcomp Require Import ssrnum.
Import Num.Theory.
Import GRing GRing.Theory.
     
Section NumLemmas.

  Local Open Scope ring_scope.
  Implicit Type T : finType.

  Context {R : numDomainType}.
  Implicit Type x y z : R.

  Lemma mulr_ll x y z :
    y = z -> x * y = x * z.
  Proof. by move=>->. Qed.

  Lemma mulr_rr x y z :
    y = z -> y * x = z * x.
  Proof. by move=>->. Qed.



  Lemma neq01 : ((0:R) != 1).
  Proof.
  have := ltr01 (R:=R) ; by rewrite lt0r eq_sym=>/andP [H _].
  Qed.

  Lemma addr_gte0 [x y : R] : 0 < x -> 0 <= y -> 0 < x + y.
  Proof.
  rewrite le0r=>Hx /orP ; case=>[/eqP ->| Hy].
  - by rewrite addr0.
  - exact: addr_gt0.
  Qed.


  Lemma deprecated_sum_ge0 {T} (P : pred T) (f : T -> R) :
    (forall t, P t -> f t >= 0) -> \sum_(t | P t) f t >= 0.
  Proof.
  move=>H ; apply big_ind=>// ; exact: addr_ge0.
  Qed.

  #[deprecated(since="decision.2.0", note="Use Num.Theory.sumr_ge0")]
  Notation sum_ge0 := deprecated_sum_ge0.

  Lemma sumr_le [I : Type] (r : seq I) (P : pred I) (F G : I -> R) :
    (forall i, P i -> F i <= G i) -> \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
  Proof.
  move=>H.
  rewrite -subr_ge0 -mulrN1 big_distrl -big_split /=.
  apply big_ind=>//[x y Hx Hy|i Hi].
  - by apply: addr_ge0.
  - rewrite mulrN1 subr_ge0 ; exact: H.
  Qed.
  
  Lemma prod_ge0 {T} (P : pred T) (f : T -> R) :
    (forall t, P t -> f t >= 0) -> \prod_(t | P t) f t >= 0.
  Proof.
  move=>H ; apply big_ind=>//=.
  exact: mulr_ge0.
  Qed.

  Lemma sum_ge0_eq0E {T} (P : pred T) (f : T -> R) :
    (forall t, P t -> f t >= 0) -> \sum_(t | P t) f t = 0 <-> forall t, P t -> f t = 0.
  Proof.
  move=>Hge0 ; split=>[Hsum t Ht | Heq0].
  - apply/eqP/negP=>/negP Hcontra.
    rewrite (bigD1 t) //= in Hsum.
    have Hge0' t' : P t' && (t' != t) -> 0 <= f t' by move=>/andP [Ht' _] ; exact: Hge0.
    have Hgt0 : f t > 0 by rewrite lt0r Hge0 // Hcontra.
    have := addr_gte0 Hgt0 (sum_ge0 _ _ Hge0').
    by rewrite Hsum lt0r eqxx andFb.
  - by rewrite (eq_bigr (fun=>0)) // big1.
  Qed.


  Lemma sum_ge0_neq0E {T} (P : pred T) (f : T -> R) :
    (forall t, P t -> f t >= 0) -> \sum_(t | P t) f t != 0 -> exists t : T, P t && (f t > 0).
  Proof.
  move=>Hge0 Hsum.
  have Hsum2 : \sum_(t | P t) f t > 0. by rewrite lt0r Hsum sum_ge0 //.
  have Hex : exists t : T, ~~ ~~ (P t && (f t != 0)).
  apply/forallPn/negP=>/forallP Hcontra.
  have Hcontra2 : \sum_(t | P t) f t = 0. apply sum_ge0_eq0E=>// t Ht.
  move: (Hcontra t) ; by rewrite Ht andTb Bool.negb_involutive=>/eqP ->.
  move: Hsum2 ; by rewrite Hcontra2 lt0r eqxx andFb.
  destruct Hex as [t Ht].
  exists t.
  have [Ht1 Ht2] := andP (negPn Ht).
  by rewrite lt0r Ht1 Ht2 Hge0.
  Qed.

  Lemma sum_div {T} (P : pred T) (cst : R) (f : T -> R) :
    \sum_(t : T | P t) f t / cst = (\sum_(t : T | P t) f t) / cst.
  Proof. by rewrite big_distrl.
  Qed.

  (*
  Lemma sum_div_eq1 {T} (P : pred T) (cst : R) (Hcst : cst != 0) (f : T -> R) :
    (\sum_(t : T | P t) f t / cst == 1) = (\sum_(t : T | P t) f t == cst).
  Proof.
  rewrite -(divr1 1) sum_div eqr_div //.
  - by rewrite mulr1 mul1r.
  - by rewrite eq_sym neq01.
  Qed.
   *)


  Lemma sum_of_sumE_cond {T : finType} (f : {set T} -> R) (P : pred {set T}):
    \sum_(t : T) \sum_(A : {set T} | P A && (t \in A)) f A = \sum_(A | P A) \sum_(w in A) f A.
  Proof.
  rewrite !pair_big_dep /=.
  rewrite (reindex (fun p=>(p.2,p.1))) //=.
  exists (fun p=>(p.2,p.1)) ; by case.
  Qed.

  Lemma sum_of_sumE {T : finType} (f : {set T} -> R) :
    \sum_(t : T) \sum_(A : {set T} | t \in A) f A = \sum_(A : {set T}) \sum_(w in A) f A.
  Proof.
  rewrite !pair_big_dep /=.
  rewrite (reindex (fun p=>(p.2,p.1))) //=.
  exists (fun p=>(p.2,p.1)) ; by case.
  Qed.

  (*
  Lemma sum_carddiv {T : finType} (A : {set T}) (H : (#|A| > 0)%N):
    \sum_(t in A) #|A|%:R^-1 = (1 : R).
  Proof.
  rewrite big_const iter_addr addr0 /=.
  rewrite -(mulr_natl #|A|%:R^-1 #|A|) divff //=.
  by rewrite pnatr_eq0 -lt0n.
  Qed.
   *)


End NumLemmas.

Section NumFieldLemmas.
  
  Local Open Scope ring_scope.
  Implicit Type T : finType.

  Context {R : numFieldType}.
  Implicit Type x y z : R.
  
  Lemma sum_div_eq1 {T} (P : pred T) (cst : R) (Hcst : cst != 0) (f : T -> R) :
    (\sum_(t : T | P t) f t / cst == 1) = (\sum_(t : T | P t) f t == cst).
  Proof.
  rewrite -(divr1 1) sum_div eqr_div //.
  - by rewrite mulr1 mul1r.
  - by rewrite eq_sym neq01.
  Qed.

  Lemma sum_carddiv {T : finType} (A : {set T}) (H : (#|A| > 0)%N):
    \sum_(t in A) #|A|%:R^-1 = (1 : R).
  Proof.
  rewrite big_const iter_addr addr0 /=.
  rewrite -(mulr_natl #|A|%:R^-1 #|A|) divff //=.
  by rewrite pnatr_eq0 -lt0n.
  Qed.

End NumFieldLemmas.
