From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import path fintype tuple bigop finset div prime finfun.
From mathcomp Require Import finset order.

Open Scope order_scope.
Import Order Order.POrderTheory Order.TotalTheory.

From decision Require Import fintype finset.



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
