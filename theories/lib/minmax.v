(* ************************************************************************************ *)
(* Minimum/maximum

   Section MinMax:      
     bigmin/bigmax with default value (minSb and maxSb functions)

   Section OMinMax:
     option-bigmin/bigmax (None for empty sets, Some x otherwise)
     omin / omax are commutative monoids 

 *)
(* ************************************************************************************ *)

From HB Require Import structures.
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From BelGames Require Import finset order.



Section MinMax.
  Import Order Order.POrderTheory Order.TotalTheory.
  Open Scope order_scope.
  

  Definition minSb {disp : Datatypes.unit} {T : orderType disp} [I : finType] (t0 : T) (F : I -> T) (A : {set I}) :=
    match [pick t in A] with
    | Some x => \big[min/F x]_(i in A) F i
    | None => t0
    end.

  Lemma minSb1 {disp : Datatypes.unit} {T : orderType disp} [I : finType] (t0 : T) (F : I -> T) (i : I) :
    minSb t0 F [set i] = F i.
  Proof. by rewrite /minSb pick_set1E bigmin_set1 minxx. Qed.
  
  Lemma minSb_eq {disp : Datatypes.unit} {T : orderType disp} [I : finType] (t0 : T) (F1 F2 : I -> T) (A : {set I}) :
    {in A, F1 =1 F2} ->
    minSb t0 F1 A = minSb t0 F2 A.
  Proof.
  move=>HF.
  rewrite/minSb.
  case: pickP=>[x Hx|//].
  rewrite (HF x Hx).
  apply: eq_bigr=>y Hy.
  exact: HF=>/=.
  Qed.
  
  Definition maxSb {disp : Datatypes.unit} {T : orderType disp} [I : finType] (t0 : T) (F : I -> T) (A : {set I}) :=
    match [pick t in A] with
    | Some x => \big[max/F x]_(i in A) F i
    | None => t0
    end.

  Lemma maxSb1 {disp : Datatypes.unit} {T : orderType disp} [I : finType] (t0 : T) (F : I -> T) (i : I) :
    maxSb t0 F [set i] = F i.
  Proof. by rewrite /maxSb pick_set1E bigmax_set1 maxxx. Qed.

  Lemma maxSb_eq {disp : Datatypes.unit} {T : orderType disp} [I : finType] (t0 : T) (F1 F2 : I -> T) (A : {set I}) :
    {in A, F1 =1 F2} ->
    maxSb t0 F1 A = maxSb t0 F2 A.
  Proof.
  move=>HF.
  rewrite/maxSb.
  case: pickP=>[x Hx|//].
  rewrite (HF x Hx).
  apply: eq_bigr=>y Hy.
  exact: HF=>/=.
  Qed.


  Lemma minSb_imset {disp : Datatypes.unit} {T : orderType disp} [X Y : finType] (t0 : T) (f1 : X -> Y) (f2 : Y -> T) A :
    (minSb t0 (fun x : X => f2 (f1 x)) A) = (minSb t0 f2 [set f1 x | x in A]).
  Proof.
  rewrite/minSb.
  case: pickP=>[x Hx|].
  - case pickP=>[y Hy|].
    + rewrite bigmin_imset.
      apply/eqP ; rewrite eq_le ; apply/andP ; split=>/= ;
        apply: le_bigmin=>[|x2 Hx2] ; first by case (imsetP Hy)=>x2 Hx2 -> ; exact: bigmin_le_cond.
      exact: bigmin_le_cond.
      exact: bigmin_le_cond.
      exact: bigmin_le_cond.
    + move=>H ; apply/eqP/negP=>Hcontra.
      have :=  eq_card0 H.
      have : exists y, y \in [set f1 x | x in A] by exists (f1 x) ; exact: imset_f.
      move/card_gt0P.
      rewrite lt0n=>Hcontra2/eqP.
      by rewrite (negbTE Hcontra2).
  - move=>H0.
    have HA := eq_card0 H0.
    case (pickP)=>[x Hx|//].
    by rewrite (cards0_eq HA) imset0 in_set0 in Hx.
  Qed.

  Lemma maxSb_imset {disp : Datatypes.unit} {T : orderType disp} [X Y : finType] (t0 : T) (f1 : X -> Y) (f2 : Y -> T) A :
    (maxSb t0 (fun x : X => f2 (f1 x)) A) = (maxSb t0 f2 [set f1 x | x in A]).
  Proof.
  rewrite/maxSb.
  case: pickP=>[x Hx|].
  - case pickP=>[y Hy|].
    + rewrite bigmax_imset.
      apply/eqP ; rewrite eq_le ; apply/andP ; split=>/= ;
        apply: bigmax_le=>[|x2 Hx2] ; first by case (imsetP Hy)=>x2 Hx2 -> ; exact: le_bigmax_cond.
      exact: le_bigmax_cond.
      case (imsetP Hy)=>x2 Hx2 -> ; exact: le_bigmax_cond.
      exact: le_bigmax_cond.
    + move=>H ; apply/eqP/negP=>Hcontra.
      have :=  eq_card0 H.
      have : exists y, y \in [set f1 x | x in A] by exists (f1 x) ; exact: imset_f.
      move/card_gt0P.
      rewrite lt0n=>Hcontra2/eqP.
      by rewrite (negbTE Hcontra2).
  - move=>H0.
    have HA := eq_card0 H0.
    case (pickP)=>[x Hx|//].
    by rewrite (cards0_eq HA) imset0 in_set0 in Hx.
  Qed.
  
End MinMax.


Section OMinMax.

  Import Order Order.TotalTheory.

  Variable disp : Datatypes.unit.
  Variable R : orderType disp.


  Definition omin : option R -> option R -> option R
    := fun or1 or2 => match or1,or2 with
                   | Some r1, Some r2 => Some (Order.min r1 r2)
                   | Some r, None | None, Some r => Some r
                   | _, _ => None
                   end.

  Lemma ominA : associative omin.
  Proof. move=>[x|] [y|] [z|] // ; by rewrite /omin minA. Qed.

  Lemma ominC : commutative omin.
  Proof. move=>[x|][y|]// ; by rewrite /omin minC. Qed.

  Lemma omin1m : left_id None omin.
  Proof. by case. Qed.

  HB.instance Definition _ : Monoid.isComLaw (option R) None omin
    := Monoid.isComLaw.Build _ _ _ ominA ominC omin1m.

  Section OMinTheory.

    Definition minS (T : finType) (u : T -> R) (B : {set T}) : option R
      := \big[omin/None]_(w in B) Some (u w).
    
    Lemma minS_eq {T : finType} (u1 u2 : T -> R) (B : {set T}) :
      {in B, u1 =1 u2} -> minS u1 B = minS u2 B.
    Proof.
    rewrite /minS => Hu.
    apply eq_bigr => w Hw ; apply f_equal.
    by rewrite Hu.
    Qed.

    Lemma minS0 {T : finType} (u : T -> R) :
      minS u (set0) = None.
    Proof.
    by rewrite/minS big1=>//t ; rewrite in_set0.
    Qed.

    Lemma minS0E {T : finType} (u : T -> R) (A : {set T}) :
      (minS u A == None) = (A == set0).
    Proof.
    case (boolP (A == set0))=>H ; first by rewrite (eqP H) minS0 eqxx.
    rewrite /minS.
    have [t Ht] := pick_nonemptyset_sig H.
    rewrite (bigD1 t)=>//=.
    by case (\big[omin/None]_(i in A | i != t) Some (u i)).
    Qed.

 

    Lemma argminS0F_sig {T : finType} (u : T -> R) (A : {set T}) :
      0 < #|A| -> {t : T | minS u A = Some (u t)}.
    Proof.
    rewrite /minS -big_enum -(eqP (enum_tupleP A))=>/=.
    elim: (fintype.enum A)=>//= t r H Hr1.
    case (boolP (size r == 0))=>[/eqP Hr|Hr].
    - exists t.
      by rewrite (size0nil Hr) bigop.unlock.
    - rewrite -lt0n in Hr.
      have [t0 Ht0] := H Hr.
      rewrite big_cons Ht0 /omin minEgt.
      case (boolP (u t0 < u t)%O)=>Hlt.
      + by exists t0.
      - by exists t.
    Qed.

    Lemma argminS0F {T : finType} (u : T -> R) (A : {set T}) :
      0 < #|A| -> exists t, minS u A = Some (u t).
    Proof.
    move=>HcardA.
    have [t Ht] := argminS0F_sig u HcardA.
    by exists t.
    Qed.

    Lemma minS0F_sig {T : finType} (u : T -> R) (A : {set T}) :
      0 < #|A| -> {r : R | minS u A = Some r}.
    Proof.
    move=>HcardA.
    have [t Ht] := argminS0F_sig u HcardA.
    by exists (u t).
    Qed.

    Lemma minS0F {T : finType} (u : T -> R) (A : {set T}) :
      0 < #|A| -> exists r, minS u A = Some r.
    Proof.
    move=>HcardA.
    have [t Ht] := argminS0F_sig u HcardA.
    by exists (u t).
    Qed.
    
    Lemma minS1 {T : finType} (u : T -> R) (t : T) :
      minS u [set t] = Some (u t).
    Proof.
    rewrite /minS (big_pred1 t) => // x.
    by rewrite in_set1.
    Qed.

    Lemma minSE {T : finType} (u : T -> R) (B : {set T}) (t0 : T) :
      t0 \in B -> minS u B = Some (\big[min/u t0]_(t in B) u t).
    Proof.
    move: B ; apply: card_ind=>A IH.
    case (boolP (A == set0))=>[/eqP->|HA0 Ht0] ;
      first by rewrite in_set0.
    case (boolP (A == [set t0]))=>[/eqP->|HA].
    - rewrite minS1 (bigminD1 t0) ; last by rewrite in_set1.
      rewrite big_pred0 ?POrderTheory.minxx=>//t.
      by rewrite in_set1 ; case (t == t0).
    - have HAt0 : A :\ t0 != set0
        by apply/negP ; rewrite setD_eq0 subset1 (negbTE HA0) (negbTE HA).
      have [t1 Ht10] := pick_nonemptyset_sig HAt0.
      have Ht1 : t1 \in A
        by move: Ht10 ; rewrite in_setD=>/andP[_->].
      rewrite /minS (bigD1 t1)//= [in RHS](bigD1 t1)//=.
      under eq_bigl do rewrite andbC -in_setD1.
      under [in RHS]eq_bigl do rewrite andbC -in_setD1.
      have :=  IH (A :\ t1) ; rewrite/minS=>->//.
      + by rewrite [E in (_<E)%N](cardsD1 t1) Ht1.
      + rewrite in_setD1 Ht0 andbT eq_sym.
        by move: Ht10 ; rewrite in_setD1=>/andP[->_].
    Qed.

    Lemma minS_imset {T1 T2 : finType} (f : T1 -> T2) (u : T2 -> R) (B : {set T1}) :
      minS u [set f t | t in B] = minS (fun t => u (f t)) B.
    Proof.
    case (boolP (B == set0))=>[/eqP->|HB] ;
      first by rewrite imset0 !minS0.
    have [t Ht] := pick_nonemptyset_sig HB.
    rewrite (minSE _ Ht).
    rewrite (minSE _ (imset_f f Ht)).
    congr (Some _).
    exact: bigmin_imset.
    Qed.

    
  End OMinTheory.

  Definition omax : option R -> option R -> option R
    := fun or1 or2 => match or1,or2 with
                   | Some r1, Some r2 => Some (max r1 r2)
                   | Some r, None | None, Some r => Some r
                   | _, _ => None
                   end.

  Definition omaxA : associative omax.
  Proof. move=>[x|] [y|] [z|] // ; by rewrite /omax maxA. Qed.

  Lemma omaxC : commutative omax.
  Proof. move=>[x|][y|]// ; by rewrite /omax maxC. Qed.

  Lemma omax1m : left_id None omax.
  Proof. by case. Qed.

  HB.instance Definition _ : Monoid.isComLaw (option R) None omax
    := Monoid.isComLaw.Build _ _ _ omaxA omaxC omax1m.

  Section OMaxTheory.

    Definition maxS (T : finType) (u : T -> R) (B : {set T}) : option R
      := \big[omax/None]_(w in B) Some (u w).
    
    Lemma maxS_eq {T : finType} (u1 u2 : T -> R) (B : {set T}) :
      {in B, u1 =1 u2} -> maxS u1 B = maxS u2 B.
    Proof.
    rewrite /maxS => Hu.
    apply eq_bigr => w Hw ; apply f_equal.
    by rewrite Hu.
    Qed.
    
    Lemma maxS0 {T : finType} (u : T -> R) :
      maxS u (set0) = None.
    Proof.
    by rewrite/maxS big1=>//t ; rewrite in_set0.
    Qed.

    Lemma maxS0E {T : finType} (u : T -> R) (A : {set T}) :
      (maxS u A == None) = (A == set0).
    Proof.
    case (boolP (A == set0))=>H ; first by rewrite (eqP H) maxS0 eqxx.
    rewrite /maxS.
    have [t Ht] := pick_nonemptyset_sig H.
    rewrite (bigD1 t)=>//=.
    by case (\big[omax/None]_(i in A | i != t) Some (u i)).
    Qed.

    Lemma argmaxS0F_sig {T : finType} (u : T -> R) (A : {set T}) :
      0 < #|A| -> {t : T | maxS u A = Some (u t)}.
    Proof.
    rewrite /maxS -big_enum -(eqP (enum_tupleP A))=>/=.
    elim: (fintype.enum A)=>//= t r H Hr1.
    case (boolP (size r == 0))=>[/eqP Hr|Hr].
    - exists t.
      by rewrite (size0nil Hr) bigop.unlock.
    - rewrite -lt0n in Hr.
      have [t0 Ht0] := H Hr.
      rewrite big_cons Ht0 /omax maxEgt.
      case (boolP (u t0 < u t)%O)=>Hlt.
      + by exists t.
      - by exists t0.
    Qed.

    Lemma argmaxS0F {T : finType} (u : T -> R) (A : {set T}) :
      0 < #|A| -> exists t, maxS u A = Some (u t).
    Proof.
    move=>HcardA.
    have [t Ht] := argmaxS0F_sig u HcardA.
    by exists t.
    Qed.

    Lemma maxS0F_sig {T : finType} (u : T -> R) (A : {set T}) :
      0 < #|A| -> {r : R | maxS u A = Some r}.
    Proof.
    move=>HcardA.
    have [t Ht] := argmaxS0F_sig u HcardA.
    by exists (u t).
    Qed.

    Lemma maxS0F {T : finType} (u : T -> R) (A : {set T}) :
      0 < #|A| -> exists r, maxS u A = Some r.
    Proof.
    move=>HcardA.
    have [t Ht] := argmaxS0F_sig u HcardA.
    by exists (u t).
    Qed.
    
    Lemma maxS1 {T : finType} (u : T -> R) (t : T) :
      maxS u [set t] = Some (u t).
    Proof.
    rewrite /maxS (big_pred1 t) => // x.
    by rewrite in_set1.
    Qed.




    Lemma maxSE {T : finType} (u : T -> R) (B : {set T}) (t0 : T) :
      t0 \in B -> maxS u B = Some (\big[max/u t0]_(t in B) u t).
    Proof.
    move: B ; apply: card_ind=>A IH.
    case (boolP (A == set0))=>[/eqP->|HA0 Ht0] ;
      first by rewrite in_set0.
    case (boolP (A == [set t0]))=>[/eqP->|HA].
    - rewrite maxS1 (bigmaxD1 t0) ; last by rewrite in_set1.
      rewrite big_pred0 ?POrderTheory.maxxx=>//t.
      by rewrite in_set1 ; case (t == t0).
    - have HAt0 : A :\ t0 != set0
        by apply/negP ; rewrite setD_eq0 subset1 (negbTE HA0) (negbTE HA).
      have [t1 Ht10] := pick_nonemptyset_sig HAt0.
      have Ht1 : t1 \in A
        by move: Ht10 ; rewrite in_setD=>/andP[_->].
      rewrite /maxS (bigD1 t1)//= [in RHS](bigD1 t1)//=.
      under eq_bigl do rewrite andbC -in_setD1.
      under [in RHS]eq_bigl do rewrite andbC -in_setD1.
      have :=  IH (A :\ t1) ; rewrite/maxS=>->//.
      + by rewrite [E in (_<E)%N](cardsD1 t1) Ht1.
      + rewrite in_setD1 Ht0 andbT eq_sym.
        by move: Ht10 ; rewrite in_setD1=>/andP[->_].
    Qed.
    
    Lemma maxS_imset {T1 T2 : finType} (f : T1 -> T2) (u : T2 -> R) (B : {set T1}) :
      maxS u [set f t | t in B] = maxS (fun t => u (f t)) B.
    Proof.
    case (boolP (B == set0))=>[/eqP->|HB] ;
      first by rewrite imset0 !maxS0.
    have [t Ht] := pick_nonemptyset_sig HB.
    rewrite (maxSE _ Ht).
    rewrite (maxSE _ (imset_f f Ht)).
    congr (Some _).
    exact: bigmax_imset.
    Qed.

    
  End OMaxTheory.

  Lemma minmaxE {T : finType} (u : T -> R) (A : {set T}) :
    (minS u A == None) = (maxS u A == None).
  Proof.
  by rewrite minS0E maxS0E.
  Qed.

End OMinMax.
