From Coq Require Import Program.Wf.
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)
From mathcomp Require Import all_algebra. (* .none *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing GRing.Theory.
Import Num.Theory.

From decision Require Import fintype.

(* Local Open Scope ring_scope. *)



(** Pick lemmas **)
Section Pick.

  Context {T : finType}.
  Implicit Type t : T.
  Implicit Type A B C : {set T}.


  (** Pick an element in a non-empty set **)
  Section PickNonEmptySet.
    
    Lemma pick_set1E t :
      [pick x in [set t]] = Some t.
    Proof.
    case: pickP.
    - by move=> t'; rewrite inE; move/eqP=>->.
    - by move/(_ t); rewrite inE eqxx.
    Qed.

    Definition pick_nonemptyset A (H : A != set0) : T.
    case (pickP [pred x in A]) => [t _ | H0].
    - exact: t.
    - by rewrite (cards0_eq (eq_card0 H0)) eqxx in H.
    Defined.

    Definition pick_nonemptyset_sig A (H : A != set0) : {t : T | t \in A}.
    exists (pick_nonemptyset H).
    rewrite /pick_nonemptyset => //=.
    case (pickP [pred t in A]) => //= H0.
    have H' := H.
    by rewrite (cards0_eq (eq_card0 H0)) eqxx in H'.
    Defined.

    Lemma pick_set1 t A (Ht : A = [set t]) (HA : A != set0) :
      pick_nonemptyset HA = t.
    Proof.
    rewrite /pick_nonemptyset.
    case pickP => /= [y|H].
    - by rewrite Ht in_set1 => /eqP ->.
    - have := H t => /= ; by rewrite {1}Ht in_set1 eqxx.
    Qed.

  End PickNonEmptySet.


  (** Pick a subset of a given cardinality **)
  Section PickSubset.

    Definition pick_subset (A : {set T}) (i : 'I_#|A|.+1) :
      {B : {set T} | B \subset A & #|B| == i}.
    Proof.
    destruct i as [i Hi] => /=.
    set j := #|A| - i.
    have : i = #|A| - j by rewrite /j subnA // subnn add0n.
    move=>->.
    induction j.
    - exists A=>//= ; by rewrite subn0.
    - destruct IHj as [B HB1 HB2].
      case (boolP (B == set0))=> H.
      + have Hj: j >= #|A|
          by rewrite -subn_eq0 -(eqP HB2) (eqP H) cards0.
        have Hj2 : #|A| - j.+1 = 0
          by apply/eqP ; rewrite subn_eq0 ; exact: leqW.
        rewrite Hj2.
        by exists set0 ; rewrite ?sub0set ?cards0.
      + have [t Ht] := pick_nonemptyset_sig H.
        exists (B :\ t).
        * exact: subset_trans (subD1set B t) HB1.
        * rewrite cardsD (eqP HB2).
          have: B:&:[set t] = [set t]
            by apply/setP=>t' ; rewrite !inE ; case (boolP (t' == t))=>[/eqP->|_];rewrite ?Ht ?andbF//.
          move=>-> ; apply/eqP.
          by rewrite cards1 subnS [in RHS]subnS subn0.
    Qed.

  End PickSubset.
End Pick.




(** Partition of subsets wrt. their cardinality **)
Section SubsetsPartition.

  Context {T : finType}.
  Implicit Type t : T.
  Implicit Type A B C : {set T}.
  
  Notation subsets := (fun A => [set B : {set T} | B \subset A]).
  Notation subsets_of_card := (fun A i => [set B : {set T} | B \subset A & #|B| == i]).

  Definition subsets_part A : {set {set {set T}}} :=
    [set subsets_of_card A (val i) | i in 'I_#|A|.+1].

  Lemma subsets_part_cover A:
    cover (subsets_part A) == subsets A.
  Proof.
  rewrite/cover.
  apply/eqP/setP=>/=B.
  rewrite !inE.
  case (boolP (B \subset A))=>HB ; apply/bigcupP=>/=.
  - exists (subsets_of_card A #|B|) ; last by rewrite inE eqxx HB.
    apply/imsetP=>/=.
    exists (inord #|B|)=>//.
    rewrite inordK// ltnS ; exact: subset_leq_card.
  - move=> Hcontra.
    destruct Hcontra as [C HC].
    case (imsetP HC) as [i Hi1 Hi2].
    by rewrite Hi2 inE (negbTE HB) andFb in H.
  Qed.

  Lemma subsets_part_trivIset A :
    trivIset (subsets_part A).
  Proof.
  rewrite/trivIset (eqP (subsets_part_cover A)) big_imset=>/=[|i j _ _ /setP Hij].
  - apply/eqP.
    rewrite -sum1dep_card (partition_big (fun B => @inord #|A| #|B|) predT)//=.
    apply: eq_big=>//=i _.
    rewrite big_const iter_addn addn0 mul1n//=.
    apply: eq_card=>B.
    rewrite !inE unfold_in.
    case (boolP (B \subset A))=>//=H.
    have Hcard : #|B| < #|A|.+1 by exact: subset_leq_card H.
    by rewrite -{1}(inordK Hcard).
  - have [B HB1 HB2] := pick_subset i.
    have := Hij B.
    rewrite !inE HB1 HB2 (eqP HB2) !andTb=>/eqP.
    rewrite eq_sym=>/eqP//=>/eqP=>Hij2.
    by apply ord_inj.
  Qed.

  Lemma subsets_part_nset0 A :
    set0 \notin (subsets_part A).
  Proof.
  apply/imsetP=>/=Hcontra.
  destruct Hcontra as [i Hi H0].
  symmetry in H0 ; move: H0.
  apply/eqP/set0Pn.
  have [B HB1 HB2] := (pick_subset i).
  exists B ; by rewrite !inE HB1 HB2.
  Qed.

  Definition subsets_partition A : partition (subsets_part A) (subsets A).
  apply/and3P ; split.
  - exact: subsets_part_cover.
  - exact: subsets_part_trivIset.
  - exact: subsets_part_nset0.
  Defined.
  
End SubsetsPartition.






(** Some general lemmas on finite sets **)
Section SetLemmas.

  Context {T : finType}.
  Implicit Type t : T.
  Implicit Type A B C : {set T}.

  
  Lemma set10F t : [set t] != set0.
  Proof. by apply/eqP/setP=>Hcontra ; have := Hcontra t ; rewrite in_set1 in_set0 eqxx. Qed.

  (** Empty domain T **)
  Lemma setT0 :
    [forall A : {set T}, A == set0] = ([set: T] == set0).
  Proof.
  case (boolP ([set: T] == set0)) => H.
  - apply/forallP => A.
    apply/negP => /negP /set0Pn [x Hx].
    have : exists y, y \in [set: T] by exists x ; have := subsetT A => /subsetP -> //.
    move=>/card_gt0P.
    by rewrite (eqP H) cards0 ltnn.
  - by apply/negP/negP/forallPn ;  exists setT.
  Qed.

  Lemma setT0F : T -> [set: T] != set0.
  Proof.
  move=>t.
  apply/negP.
  rewrite -setT0.
  apply/negP/forallPn.
  exists [set t].
  exact: set10F.
  Qed.
  
  
  (** Set of subsets is never empty **)
  Lemma subsets_card_gt0 :
    #|{set T}| > 0.
  Proof.
  apply/card_gt0P.
  by exists set0.
  Qed.
  
  (** Equality of complements **)
  Lemma eq_setC  A B :
    (~: A == ~: B) = (A == B).
  Proof.
  have H C D : C = D -> ~:C = ~:D by move=>->.
  case (boolP (A == B)) => [/eqP ->|] /= ; first by rewrite eqxx.
  case (boolP (~: A == ~: B)) => // /eqP Hcontra.
  have := H _ _ Hcontra.
  by rewrite !setCK => -> ; rewrite eqxx.
  Qed.

  Lemma setU1_eq A t :
    t \in A -> t |: A = A.
  Proof.
  by move=>Ht ; apply/setP=>t' ; rewrite !inE ; case (boolP (t' == t))=>[/eqP->|].
  Qed.

  (** set0 has no proper subsets **)
  Lemma proper0E A :
    A \proper set0 = false.
  Proof. by rewrite properE sub0set andbF. Qed.

  (** Alterative definition of "proper" **)
  Lemma properEbis A B :
    A \proper B = (A \subset B) && (A != B).
  Proof.
  rewrite properE.
  case (boolP (A \subset B)) => H1 // ; case (boolP (B \subset A)) => H2 ; by rewrite eqEsubset H1 H2.
  Qed.

  (** The only proper subset of [set t] is set0 **)
  Lemma proper1E t A :
    (A \proper [set t]) = (A == set0).
  Proof.
  rewrite properEbis.
  rewrite subset1.
  case (boolP (A == set0)) => H ; last by case (A == [set t]).
  rewrite orbT andTb (eqP H) eq_sym.
  apply/eqP/eqP/set0Pn.
  exists t.
  by rewrite in_set1.
  Qed.
  
  (** The only subset of A and ~:A is set0 **)
  Lemma subset_set0 A B :
    (A \subset B) && (A \subset ~:B) = (A == set0).
  Proof.
  case (boolP (A == set0)) => [/eqP -> | /set0Pn [t Ht]].
  - by rewrite !sub0set.
  - case (boolP (A \subset B)) ; case (boolP (A \subset ~:B)) => //.
    rewrite !subsetE => /pred0P H1 /pred0P H2.
    have := H2 t.
    have := H1 t.
    rewrite /= Ht !andbT.
    move => Ht1 /negP/negP Ht2.
    by rewrite -in_setC setCK Ht2 in Ht1.
  Qed.

  (** If A is a subset of B and ~:B, then any t\in A implies False (corrolary of subset_set0) **)
  Lemma subsetF A B :
    A \subset B -> A \subset ~:B -> forall t, t \in A -> Logic.False.
  Proof.
  move => H1 H2 t Ht.
  have HA : A = set0. by apply/eqP ; rewrite -(subset_set0 _ B) H1 H2.
  by rewrite HA in_set0 in Ht.
  Qed.

  (** For any disjoint sets A and B, no set except set0 is a subset of both A and B **)
  Lemma subset0F_disjoint A B :
    [disjoint A & B] ->
    forall C, C != set0 -> C \subset A -> ~~ (C \subset B).
  Proof.
  move => HAB C HC /subsetP /= H.
  apply /subsetPn.
  have [x Hx] := pick_nonemptyset_sig HC.
  exists x => //.
  by rewrite (disjointFr HAB (H x Hx)).
  Qed.

  Lemma subset_neq A B C :
    B \subset A -> ~~ (C \subset A) -> B != C.
  Proof.
  move=>/subsetP HBA /subsetPn [t HtC HtA].
  apply/negP=>/eqP/setP Hcontra.
  have := HBA t.
  have := Hcontra t=>->.
  rewrite HtC (negbTE HtA)=>Hcontra2.
  by have := (Hcontra2 is_true_true).
  Qed.

  (** A and B :\: A are disjoint **)
  Lemma disjointDl A B :
    [disjoint A & B :\: A].
  Proof. by rewrite -setI_eq0 setIDA setD_eq0 subsetIl. Qed.
  Lemma disjointDr A B :
    [disjoint B :\: A & A].
  Proof. by rewrite -setI_eq0 setIDAC setD_eq0 subsetIr. Qed.

  Lemma setUD A B :
    A :|: B :\: A = A :|: B.
  Proof.
  apply/setP=>t ; rewrite !in_setU in_setD.
  by case (t \in A) ; case (t \in B).
  Qed.

  Lemma setDU A B :
    (A :|: B) :\: A = B :\: A.
  Proof.
  apply/setP=>t ; rewrite !in_setD in_setU.
  by case (t \in A) ; case (t \in B).
  Qed.

  Lemma setUDD A B :
    (A :|: B) :\: (B :\: A) = A.
  Proof.
  apply/setP=>t.
  rewrite !in_setD in_setU.
  by case (t \in A) ; case (t \in B).
  Qed.

  (** A \cap B \subseteq A \cup B **)
  Lemma subsetIU A B : A :&: B \subset A :|: B.
  Proof.
  apply/subsetP=>t.
  by rewrite in_setI in_setU=>/andP[-> ->].
  Qed.

  (** set0 has no elements **)
  Lemma set0_exists A :
    (A == set0) = (~~ [exists t, t \in A]).
  Proof.
  case (boolP [exists t, t \in A]) => /existsP/set0Pn => [H|-> //].
  by rewrite (negbTE H).
  Qed.

  (** set0 has no elements **)
  Lemma set0_forall A :
    (A == set0) = [forall t, t \notin A].
  Proof.
  rewrite -negb_exists.
  exact: set0_exists.
  Qed.

  (** set0 and X are always disjoint **)
  Lemma disjoint0 A :
    [disjoint A & set0].
  Proof. by rewrite -setI_eq0 setI0 eqxx. Qed.
  Lemma dis0joint A :
    [disjoint set0 & A].
  Proof. by rewrite disjoint_sym ; exact: disjoint0. Qed.

  (** setT is only disjoint of set0 **)
  Lemma disjointT A :
    [disjoint A & setT] = (A == set0).
  Proof.
  apply/setDidPl/eqP.
  - by rewrite setDT=>->.
  - move=>-> ; by rewrite set0D.
  Qed.
  Lemma disTjoint A :
    [disjoint setT & A] = (A == set0).
  Proof. by rewrite disjoint_sym ; exact: disjointT. Qed.

End SetLemmas.




(** Option-inverse of (set1: T -> {set T}) is (set1_oinv : {set T} -> T) such as:
    - set1_oinv [set T] = Some t
    - set1_oinv _ = None otherwise
 **)
Section Set1_inverse.

  Context {T : finType}.
  Implicit Type t : T.
  Implicit Type A B C : {set T}.

  Definition set1_oinv A : option T
    := match boolP (#|A| > 0)%N with
       | AltTrue h =>
           if (#|A| == 1)%N
           then let (x,_,_) := eq_bigmax_cond (fun=>0%N) h in Some x
           else None
       | _ => None
       end.

  Lemma set1_ocancel : ocancel set1_oinv set1.
  Proof.
  move => A.
  rewrite /oapp /set1_oinv.
  case (boolP (#|A| > 0)%N) => H //.
  destruct (eq_bigmax_cond (fun=>0%N) H) as [t Ht _].
  case (boolP (#|A| == 1)%N) => // /cards1P [t' Ht'].
  rewrite Ht' in_set1 in Ht.
  by rewrite Ht' (eqP Ht).
  Qed.

  Lemma set1_oinv_pcancel : pcancel set1 set1_oinv.
  Proof.
  move => t.
  rewrite /set1_oinv.
  case (boolP (#|[set t]| > 0)%N) => [Hx|] ; last by rewrite cards1.
  rewrite cards1 eqxx //.
  destruct (eq_bigmax_cond (fun=>0%N) Hx) as [t' Ht' _].
  rewrite in_set1 in Ht'.
  by rewrite (eqP Ht').
  Qed.

  Lemma set1_oinv_omap A (H : #|A| == 1%N) : omap set1 (set1_oinv A) = Some A.
  Proof.
  rewrite /omap/obind/oapp/set1_oinv.
  case (boolP (0 < #|A|)%N) => H0 ; case (boolP (#|A| == 1)%N) => H1.
  - destruct (eq_bigmax_cond (fun=>0%N) H0) as [w Hw _].
    destruct (cards1P H1) as [w' Hw'].
    rewrite Hw' in_set1 in Hw.
    by rewrite Hw' (eqP Hw).
  - by rewrite (eqP H) in H1.
  - by rewrite -eqn0Ngt (eqP H1) in H0.
  - by rewrite (eqP H) in H1.
  Qed.
  
End Set1_inverse.

(** Bigop lemmas *)
Section Bigops.

  Lemma big_condT R (idx : R) (op : R -> R -> R) (I : finType) (C : {set I}) (F : I -> R) :
    \big[op/idx]_(i in C | true) F i = \big[op/idx]_(i in C) F i.
  Proof. by apply: eq_bigl=>i ; by rewrite andbT. Qed.

  (* generalized (op is not a monoid) *)
  Lemma big_set0 R (idx : R) (op : R -> R -> R) (I : finType) (F : I -> R) :
    \big[op/idx]_(i in set0) F i = idx.
  Proof.
  rewrite bigop.unlock.
  elim: (index_enum I)=>//= i s IH.
  by rewrite in_set0.
  Qed.
  
  Lemma big_setT R (idx : R) (op : R -> R -> R) (I : finType) (F : I -> R) :
    \big[op/idx]_(i in [set: I]) F i = \big[op/idx]_i F i.
  Proof. by under eq_bigl do rewrite in_setT. Qed.

  Lemma bigUI R (idx : R) (op : Monoid.com_law idx) (I : finType) (A B : pred I) (F : I -> R) : 
    op (\big[op/idx]_(i in [predU A & B]) F i)
       (\big[op/idx]_(i in [predI A & B]) F i)
    =
      op (\big[op/idx]_(i in A) F i) (\big[op/idx]_(i in B) F i).
  Proof.
  rewrite [E in op E _ = _](bigID (fun i => i \in A)).
  rewrite [E in op (op E _) _ = _](bigID (fun i => i \in B)).
  rewrite -Monoid.mulmA.
  rewrite [E in _ = op _ E](bigID (fun i => i \in A)).
  rewrite [E in _ = op E _](bigID (fun i => i \in B)).
  rewrite [E in _ = op _ E]Monoid.mulmC.
  congr (op _ _) ; congr (op _ _) ; apply: eq_bigl=>i ; rewrite !inE ; by case (i \in A); case (i \in B).
  Qed.

  Lemma big_setUI R (idx : R) (op : Monoid.com_law idx) (I : finType) (A B : {set I}) (F : I -> R) : 
    op (\big[op/idx]_(i in A :|: B) F i)
       (\big[op/idx]_(i in A :&: B) F i)
    =
      op (\big[op/idx]_(i in A) F i) (\big[op/idx]_(i in B) F i).
  Proof.
  rewrite [E in op E _ = _](bigID (fun i => i \in A)).
  rewrite [E in op (op E _) _ = _](bigID (fun i => i \in B)).
  rewrite -Monoid.mulmA.
  rewrite [E in _ = op _ E](bigID (fun i => i \in A)).
  rewrite [E in _ = op E _](bigID (fun i => i \in B)).
  rewrite [E in _ = op _ E]Monoid.mulmC.
  congr (op _ _) ; congr (op _ _) ; apply: eq_bigl=>i ; rewrite !inE ; by case (i \in A); case (i \in B).
  Qed.

  Lemma big_card1_dep  R (idx : R) (op : Monoid.com_law idx) (I : finType) (P : pred {set I}) (F : {set I} -> R) :
    \big[op/idx]_(A : {set I} | (P A) && (#|A| == 1)%N) F A = \big[op/idx]_(i : I | P [set i]) F [set i].
  Proof.
  rewrite (reindex_omap set1 set1_oinv) => [|A /andP [HP H1]].
  - apply: eq_bigl => x.
    by rewrite set1_oinv_pcancel cards1 !eqxx !andbT.
  - rewrite /omap /obind /oapp /set1_oinv.
    case (boolP (0 < #|A|)%N) => [Hcard|] ; last by rewrite (eqP H1).
    rewrite H1.
    destruct (eq_bigmax_cond (fun=>0%N) Hcard) as [t Ht _].
    move: H1 => /cards1P [t' Ht'].
    rewrite Ht' in_set1 in Ht.
    by rewrite Ht' (eqP Ht).
  Qed.

  Lemma big_card1  R (idx : R) (op : Monoid.com_law idx) (I : finType) (F : {set I} -> R) :
    \big[op/idx]_(A : {set I} | #|A| == 1%N) F A = \big[op/idx]_(i : I) F [set i].
  Proof.
  rewrite -(big_card1_dep _ predT) ; by apply: eq_bigl.
  Qed.

  Lemma big_subset R (idx : R) (op : Monoid.com_law idx) (I : finType) (F : {set I} -> R) (A : {set I}) :
    \big[op/idx]_(B : {set I} | B \subset A) F B = op (F A) (\big[op/idx]_(B : {set I} | B \proper A) F B).
  Proof.
  rewrite (bigD1 A)//.
  congr (op _ _).
  apply: eq_bigl=>B.
  symmetry.
  exact: properEbis.
  Qed.

  Lemma big_subsetI R (idx : R) (op : Monoid.com_law idx) (I : finType) (F : {set I} -> R) (A B : {set I}) :
    op (\big[op/idx]_(C : {set I} | (C \subset A) && ~~(C \subset B)) F C)
    (\big[op/idx]_(C : {set I} | C \subset A :&: B) F C)
    = \big[op/idx]_(C : {set I} | C \subset A) F C.
  Proof.
  rewrite [E in _=E](bigID (fun C : {set I} => C \subset B)) [E in _=E]Monoid.mulmC.
  congr (op _ _).
  apply: eq_bigl=>/=C.
  exact: subsetI.
  Qed.

  Lemma big_eq1F (R0 : eqType) (idx : R0) (op : Monoid.law idx) (I : finType) (r : seq I) (P : pred I) (F : I -> R0) :
    \big[op/idx]_(i <- r | P i) F i != idx -> exists i, [&& i \in r, P i & F i != idx].
  Proof.
  move=>H ; apply/existsP/negbNE/existsPn=>Hcontra.
  - have Hcontra2 :  forall i : I, P i && (i \in r) -> F i = idx.
    move=>i /andP[Hi1 Hi2].
    have  := Hcontra i.
    rewrite !negb_and=>/orP// ; case=>[|/orP] ; last case.
    + by rewrite Hi2.
    + by rewrite Hi1.
    + by move/negPn/eqP->.
  - by rewrite (big1_seq _ _ _ Hcontra2) eqxx in H.
  Qed.


End Bigops.
      
Section Bigops.

  Context {T : finType}.
  Implicit Type t : T.
  Implicit Type A B C : {set T}.

  (*
  (** Bigop on singletons **)
  Lemma big_card1 {R} {idx : R} {op : Monoid.com_law idx} (f : {set T} -> R) :
    \big[op/idx]_(A : {set T} | #|A| == 1%N) f A = \big[op/idx]_(t : T) f [set t].
  Proof.
  rewrite (reindex_omap set1 set1_oinv) => [|A H].
  - apply: eq_bigl => x.
    by rewrite set1_oinv_pcancel cards1 !eqxx.
  - rewrite /omap /obind /oapp /set1_oinv.
    case (boolP (0 < #|A|)%N) => [Hcard|] ; last by rewrite (eqP H).
    rewrite H.
    destruct (eq_bigmax_cond (fun=>0%N) Hcard) as [t Ht _].
    move: H => /cards1P [t' Ht'].
    rewrite Ht' in_set1 in Ht.
    by rewrite Ht' (eqP Ht).
  Qed.
   *)


  
  (** Proof of a version of sig_big_dep about 'sig' (but not about 'sigT') **)
  Section SigBigDep2.

    (* Projection from 'T' into 'option {t : T | P T}' -- needed for sig_big_dep2 *)
    Definition osig (P : pred T) : T -> option {t : T | P t}
      := (fun t => match boolP (P t) with AltTrue h => Some (exist P t h) | _ => None end).

    Lemma osig_bij (P : pred T) :
      forall t, P t -> omap sval (osig P t) = Some t.
    move => t Ht.
    rewrite/omap/obind/oapp/osig => //=.
    case (boolP (P t)) => [Ht' //|] ; by rewrite Ht.
    Qed.

    Lemma sig_big_dep2 {R} {idx : R} {op : SemiGroup.com_law R} (P : pred T) f :
      \big[op/idx]_(s : {t : T | P t}) f (tag s) (tagged s) = \big[op/idx]_(t : T | P t) match boolP (P t) with AltTrue h => f t h | _ => idx end.
    Proof.
    rewrite (reindex_omap (op:=op) (sval) (osig P) (@osig_bij P)).
    apply eq_big => [[t Ht]|[t Ht] _] /=.
    - rewrite /osig ; case (boolP (P t)) => [Ht'|] ; last by rewrite Ht.
      by rewrite (eq_irrelevance Ht Ht') eqxx.
    - case (boolP (P t)) => [Ht'|] ; last by rewrite Ht.
      by rewrite (eq_irrelevance (svalP (exist P t Ht))).
    Qed.

    (** Non-dependent version of sig_big_dep2 **)
    Lemma sig_big {R} {idx : R} {op : SemiGroup.com_law R} (P : pred T) f :
      \big[op/idx]_(s : {t : T | P t}) f (tag s) = \big[op/idx]_(t : T | P t) f t.
    Proof.
    rewrite (sig_big_dep2 (fun t _ => f t)).
    apply eq_bigr => t Ht.
    case (boolP (P t)) => [//|] ; by rewrite Ht.
    Qed.

  End SigBigDep2.
  

  (** Similar to partition_big + big_distrl **)
  Lemma big_setI_distrl {R} {zero : R} {times : Monoid.mul_law zero} {plus : Monoid.add_law zero times} (P : pred {set T}) (h : {set T} -> {set T}) (f g : {set T} -> R) :
    \big[plus/zero]_(A : {set T} | P (h A)) times (g A) (f (h A))
    = \big[plus/zero]_(B : {set T} | P B) times (\big[plus/zero]_(A : {set T} | h A == B) g A) (f B).
  Proof.
  under [RHS]eq_bigr do rewrite big_distrl /=.
  rewrite [LHS](partition_big h P) => //.
  apply: eq_bigr => B HB ; apply: eq_big => [A | A /andP [_ HA2]].
  - case (boolP (h A == B)) => H ; last by rewrite (negbTE H) andbF.
    by rewrite H (eqP H) HB. 
  - by rewrite (eqP HA2).
  Qed.


  (** Split a commutative bigop according to a predicate P **)
  Lemma deprecated_split_big {R} {idx : R} {op : Monoid.com_law idx} {I} [r : seq I] P Q f :
    \big[op/idx]_(i <- r | P i) f i =
      op (\big[op/idx]_(i <- r | P i && Q i) f i)
      (\big[op/idx]_(i <- r | P i && ~~ Q i) f i).
  Proof. exact: bigID. Qed.

  Lemma big_partitionS [Y] (idx : Y) (op : Monoid.com_law idx) [X : finType] (f : {set X} -> X -> Y) :
    \big[op/idx]_(A : {set X}) (\big[op/idx]_(x in A) f A x) = \big[op/idx]_(x : X) \big[op/idx]_(A : {set X} | x \in A) f A x.
  Proof.
  set pair_sig : finType := [finType of {p : {set X} * X | p.2 \in p.1}].
  set f1 : pair_sig -> {set X} := fun s => (val s).1.
  set f2 : pair_sig -> X := fun s => (val s).2.
  - have proof1 :
      \big[op/idx]_x \big[op/idx]_(A : {set X} | x \in A) f A x =
      \big[op/idx]_x \big[op/idx]_(s : pair_sig | (f2 s) == x) f (f1 s) (f2 s).
    apply eq_bigr => x _.
    set f1inv : {set X} -> option pair_sig := fun A : {set X} => match (boolP (x \in A)) with AltTrue h => Some (exist _ (A,x) h) | _ => None end.
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
            exact: eq_irrelevance.
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
            exact: eq_irrelevance.
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

  
End Bigops.

#[deprecated(since="decision.2.0", note="Use ssreflect's bigID")]
Notation split_big := deprecated_split_big.



(** Set-induction wrt its cardinality. 
    Arguemnt: If (if P holds for A's subsets, then P holds for A) then P holds. 
    Note: no need for a base case (P hold for set0) since set0 has no subset
    so the inductive case encompass it
**) 
Section CardInduction.

  Context {T : finType}.
  Implicit Type t : T.
  Implicit Type A B C : {set T}.

  Section CardRectDef.
    Context {P : {set T} -> Type}.
    Variable HA : forall A : {set T}, (forall B : {set T}, (#|B| < #|A|)%coq_nat -> P B) -> P A.

    Program Fixpoint card_rect_coq_nat (A : {set T}) {measure #|A|} : P A
      := HA card_rect_coq_nat.
    Next Obligation.
    by apply measure_wf ; exact: Wf_nat.lt_wf.
    Qed.
    
  End CardRectDef.

  Definition card_rect {P} (H : forall A : {set T}, (forall B : {set T}, #|B| < #|A| -> P B) -> P A) A :=
    card_rect_coq_nat (fun A0 HB0 => H A0 (fun B H => HB0 B (elimTF ltP H))) A.
  Definition card_ind {P : _ -> Prop} := @card_rect P.
  Definition card_rec {P : _ -> Set} := @card_rect P.

  
  Section Card2RectDef.
    Context {P : {set T} -> Type}.
    Variable HA : forall A : {set T}, (forall B : {set T}, (#|B| > #|A|)%coq_nat -> P B) -> P A.

    Program Fixpoint card2_rect_coq_nat (A : {set T}) {measure (#|T|.+1 - #|A|)%N} : P A
      := HA (fun B _ => card2_rect_coq_nat B).
    Next Obligation.
    move=>A IH B Hcard.
    apply/ltP ; apply: ltn_sub2l ; last by apply/ltP.
    by rewrite ltnS ; exact: max_card.
    Qed.
    Next Obligation.
    by apply measure_wf ; exact: Wf_nat.lt_wf.
    Qed.
    
  End Card2RectDef.

  
  Definition card2_rect {P} (H : forall A : {set T}, (forall B : {set T}, #|B| > #|A| -> P B) -> P A) A : P A :=
    card2_rect_coq_nat (fun A0 HB0 => H A0 (fun B H => HB0 B (elimTF ltP H))) A.
  Definition card2_ind {P : _ -> Prop} := @card2_rect P.
  Definition card2_rec {P : _ -> Set} := @card2_rect P.

End CardInduction.

Section SubsetInduction.

  Context {T : finType}.
  Implicit Type t : T.
  Implicit Type A B C : {set T}.

  Section SubsetRectDef.
    Context {P : {set T} -> Type}.
    Variable HA : forall A : {set T}, (forall B : {set T}, (B \proper A)%coq_nat -> P B) -> P A.

    Program Fixpoint subset_rect (A : {set T}) {measure #|A|} : P A
      := HA (fun B HB => subset_rect B (recproof:= ltP (proper_card HB))).
    Next Obligation.
    by apply measure_wf ; exact: Wf_nat.lt_wf.
    Qed.
    
  End SubsetRectDef.
  Definition subset_ind {P : _ -> Prop} := @subset_rect P.
  Definition subset_rec {P : _ -> Set} := @subset_rect P.

  Section Subset2RectDef.
    Context {P : {set T} -> Type}.
    Variable HA : forall A : {set T}, (forall B : {set T}, A \proper B -> P B) -> P A.

    Program Fixpoint subset2_rect (A : {set T}) {measure (#|T|.+1 - #|A|)} : P A
      := HA (fun B _ => subset2_rect B).
    Next Obligation.
    move=>A IH B Hcard.
    apply/ltP ; apply: ltn_sub2l ; last exact: proper_card.
    by rewrite ltnS ; exact: max_card.
    Qed.
    Next Obligation.
    by apply measure_wf ; exact: Wf_nat.lt_wf.
    Qed.
    
  End Subset2RectDef.
  Definition subset2_ind {P : _ -> Prop} := @subset_rect P.
  Definition subset2_rec {P : _ -> Set} := @subset_rect P.

End SubsetInduction.

