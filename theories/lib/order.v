(* ************************************************************************************ *)
(* order: min and max
   
   Lemmas about min, max, bigmin and bigmax                             (to be integrated)
 *)
(* ************************************************************************************ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import path fintype tuple bigop finset div prime finfun.
From mathcomp Require Import finset order.

Open Scope order_scope.
Import Order Order.POrderTheory Order.TotalTheory.

From BelGames Require Import finset.



Lemma maxx_ge {disp : unit} {T : orderType disp} (x y z : T) :
  max x y <= z = (x <= z) && (y <= z).
Proof.
rewrite maxEge.
case (boolP (y <= x)) => /=Hxy.
- case (boolP (x <= z)) => // Hxz ; by rewrite (POrderTheory.le_trans Hxy Hxz).
- case (boolP (y <= z)) => //= Hyz ; last by rewrite andbF.
  rewrite -ltNge in Hxy.
  have := lt_le_trans Hxy Hyz.
  by rewrite lt_leAnge=>/andP [-> _].
Qed.

Lemma minx_le {disp : unit} {T : orderType disp} (x y z : T) :
  min x y >= z = (x >= z) && (y >= z).
Proof.
rewrite minEle.
case (boolP (x <= y)) => /=Hxy.
- case (boolP (z <= x)) => // Hxz ; by rewrite (POrderTheory.le_trans Hxz Hxy).
- case (boolP (z <= y)) => //= Hyz ; last by rewrite andbF.
  rewrite -ltNge in Hxy.
  have := le_lt_trans Hyz Hxy.
  by rewrite lt_leAnge=>/andP [-> _].
Qed.



Lemma bigmaxUl {disp : Datatypes.unit} {TT : orderType disp} [I : finType]
(x : TT) (A B : {set I}) (F : I -> TT) :
  (\big[max/x]_(i in A) F i <= \big[max/x]_(i in A :|: B) F i)%O.
Proof. by apply: sub_bigmax=>t ; rewrite in_setU=>->. Qed.

Lemma bigmaxUr {disp : Datatypes.unit} {TT : orderType disp} [I : finType]
(x : TT) (A B : {set I}) (F : I -> TT) :
  (\big[max/x]_(i in B) F i <= \big[max/x]_(i in A :|: B) F i)%O.
Proof. under [E in (_<=E)%O]eq_bigl do rewrite setUC ; exact: bigmaxUl. Qed.

Lemma bigmaxIl {disp : Datatypes.unit} {TT : orderType disp} [I : finType]
(x : TT) (A B : {set I}) (F : I -> TT) :
  (\big[max/x]_(i in A) F i >= \big[max/x]_(i in A :&: B) F i)%O.
Proof. by apply: sub_bigmax=>t ; rewrite in_setI=>/andP[->_]. Qed.

Lemma bigmaxIr {disp : Datatypes.unit} {TT : orderType disp} [I : finType]
(x : TT) (A B : {set I}) (F : I -> TT) :
  (\big[max/x]_(i in B) F i >= \big[max/x]_(i in A :&: B) F i)%O.
Proof. under eq_bigl do rewrite setIC ; exact: bigmaxIl. Qed.

Lemma bigmaxD {disp : Datatypes.unit} {TT : orderType disp} [I : finType]
(x : TT) (A B : {set I}) (F : I -> TT) :
  (\big[max/x]_(i in B) F i >= \big[max/x]_(i in B :\: A) F i)%O.
Proof. by apply: sub_bigmax=>t ; rewrite in_setD=>/andP[_->]. Qed.

Lemma bigmaxU {disp : Datatypes.unit} {TT : orderType disp} [I : finType]
(x : TT) (A B : {set I}) (F : I -> TT) :
  \big[max/x]_(i in A :|: B) F i = max (\big[max/x]_(i in A) F i) (\big[max/x]_(i in B) F i).
case (boolP (A == set0))=>[/eqP->|HA].
- rewrite big_set0.
  under eq_bigl do rewrite set0U.
  exact: bigmax_idl.
- rewrite (bigmaxID x [in A]).
  rewrite (eq_bigl [in A])=>[|t] ;
    last by rewrite !inE ; case (t \in A) ; case (t \in B).
  rewrite [E in max _ E = _](eq_bigl [in B :\: A])=>[|t] ;
    last by rewrite !inE ; case (t \in A) ; case (t \in B).
  rewrite (bigmaxID x [in A :&: B]).
  rewrite [E in max (max E _) _](eq_bigl [in A :&: B])=>[|t] ;
    last by rewrite !inE ; case (t \in A) ; case (t \in B).
  rewrite [E in _=max (max E _) _](eq_bigl [in A :&: B])=>[|t] ;
    last by rewrite !inE ; case (t \in A) ; case (t \in B).
  rewrite [E in max (max _ E) _](eq_bigl [in A :\: B])=>[|t] ;
    last by rewrite !inE ; case (t \in A) ; case (t \in B).
  rewrite [E in _=max (max _ E) _](eq_bigl [in A :\: B])=>[|t] ;
    last by rewrite !inE ; case (t \in A) ; case (t \in B).
  rewrite [E in _=max _ E](bigmaxID x [in B :\: A]).
  rewrite [E in _=max _ (max E _)](eq_bigl [in B :\: A])=>[|t] ;
    last by rewrite !inE ; case (t \in A) ; case (t \in B).
  rewrite [E in _=max _ (max _ E)](eq_bigl [in A :&: B])=>[|t] ;
    last by rewrite !inE ; case (t \in A) ; case (t \in B).
  by rewrite !maxA [E in _=E]maxC !maxA maxxx.
Qed.
  


Lemma bigmin_idx {disp : Datatypes.unit} {T : orderType disp} [I : eqType] (r : seq I) (x : T) (P : pred I) (F : I -> T) :
  \big[min/x]_(i <- r | P i) F i <= x.
Proof.
induction r.
- by rewrite bigop.unlock.
- apply: (le_trans _ IHr).
  apply: sub_bigmin_cond=>i.
  rewrite !/(_\in_)/mem//=.
  by case (P a)=>//=-> ; rewrite orbT.
Qed.

Lemma bigmax_idx {disp : Datatypes.unit} {T : orderType disp} [I : eqType] (r : seq I) (x : T) (P : pred I) (F : I -> T) :
  \big[max/x]_(i <- r | P i) F i >= x.
Proof.
induction r.
- by rewrite bigop.unlock.
- apply: (le_trans IHr).
  apply: sub_bigmax_cond=>i.
  rewrite !/(_\in_)/mem//=.
  by case (P a)=>//=-> ; rewrite orbT.
Qed.

Lemma bigmin_idx2 {disp : Datatypes.unit} {T : orderType disp} [I : finType] (x : T) (P : pred I) (F : I -> T) :
  (forall i, P i -> x <= F i)
  -> \big[min/x]_(i | P i) F i = x.
Proof.
move=>H.
rewrite bigop.unlock.
induction (index_enum I)=>//=.
case (boolP (P a))=>//= Ha.
by rewrite IHl minElt ltNge H.
Qed.

Lemma bigmax_idx2 {disp : Datatypes.unit} {T : porderType disp} [I : finType] (x : T) (P : pred I) (F : I -> T) :
  (forall i, P i -> x >= F i)
  -> \big[max/x]_(i | P i) F i = x.
Proof.
move=>H.
rewrite bigop.unlock.
induction (index_enum I)=>//=.
case (boolP (P a))=>//= Ha.
by rewrite IHl maxEle H.
Qed.

Lemma bigmin_set1 {disp : Datatypes.unit} {T : orderType disp} [I : finType] (x : T) (j : I) (F : I -> T) :
  \big[min/x]_(i in [set j]) F i = min x (F j).
Proof.
rewrite minEle.
case (boolP (x <= F j))=>H ; first by apply: bigmin_idx2=>i /set1P->.
apply/eqP ; rewrite eq_le ; apply/andP ; split.
- apply: bigmin_le_cond ; by rewrite in_set1.
- apply: le_bigmin=>[|i /set1P->//].
  by rewrite leNgt lt_leAnge (negbTE H) andFb.
Qed.

Lemma bigmax_set1 {disp : Datatypes.unit} {T : orderType disp} [I : finType] (x : T) (j : I) (F : I -> T) :
  \big[max/x]_(i in [set j]) F i = max x (F j).
Proof.
rewrite maxEle.
case (boolP (x <= F j))=>H.
- apply/eqP ; rewrite eq_le ; apply/andP ; split.
  + by apply: bigmax_le=>//i /set1P->.
  + by apply: le_bigmax_cond ; rewrite in_set1.
- apply: bigmax_idx2=>i /set1P->.
  by rewrite leNgt lt_leAnge (negbTE H) andFb.
Qed.

Lemma bigmax_imset {disp : unit} {T : orderType disp} [I J : finType] (x : T) [h : I -> J] [A : {set I}] (F : J -> T) :
  \big[max/x]_(j in [set h x | x in A]) F j = \big[max/x]_(i in A) F (h i).
Proof.
case (boolP (A == set0))=>[/eqP->|HA0] ;
                         first by rewrite imset0 !big_set0.
have [t Ht] := pick_nonemptyset_sig HA0.
symmetry.
apply/eqP ; rewrite eq_le ; apply/andP ; split.
- rewrite bigmax_mkcond.
  apply: bigmax_le=>[|j _].
  + by rewrite bigmax_idl le_maxr lexx orTb.
  + case (boolP (j \in A))=>H ;
                           last by rewrite bigmax_idl le_maxr lexx orTb.
    by apply: le_bigmax_cond ; first exact: imset_f.
- rewrite bigmax_mkcond.
  apply: bigmax_le=>[|j _].
  + by rewrite bigmax_idl le_maxr lexx orTb.
  + case (boolP (j \in [set h x0 | x0 in A]))=>H ;
                                              last by rewrite bigmax_idl le_maxr lexx orTb.
    have [i Hi ->] := imsetP H.
    exact: le_bigmax_cond.
Qed.

Lemma bigmin_imset {disp : unit} {T : orderType disp} [I J : finType] (x : T) [h : I -> J] [A : {set I}] (F : J -> T) :
  \big[min/x]_(j in [set h x | x in A]) F j = \big[min/x]_(i in A) F (h i).
Proof.
case (boolP (A == set0))=>[/eqP->|HA0] ;
  first by rewrite imset0 !big_set0.
symmetry.
apply/eqP ; rewrite eq_le ; apply/andP ; split.
- rewrite [E in _<=E]bigmin_mkcond.
  apply: le_bigmin=>[|j _].
  + by rewrite bigmin_idl le_minl lexx orTb.
  + case (boolP (j \in [set h x0 | x0 in A]))=>H ;
      last by rewrite bigmin_idl le_minl lexx orTb.
    have [i Hi ->] := imsetP H.
    exact: bigmin_le_cond.
- rewrite [E in _<=E]bigmin_mkcond.
  apply: le_bigmin=>[|j _].
  + by rewrite bigmin_idl le_minl lexx orTb.
  + case (boolP (j \in A))=>H ;
      last by rewrite bigmin_idl le_minl lexx orTb.
    by apply: bigmin_le_cond ; first exact: imset_f.
Qed.

