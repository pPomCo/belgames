(* ************************************************************************************ *)
(* finite types and quantifiers
   
   Section ExistsForall
     Split exists and forall predicates (bool and Prop) 

 *)
(* ************************************************************************************ *)
From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect. (* .none *)


(** Split 'exists' predicates **)
Section ExistsForall.

  Lemma exists_l {T} {P} Q :
    (exists t : T, P t /\ Q t) -> (exists t, P t).
  Proof. case=>t [H _] ; by exists t. Qed.

  Lemma exists_r {T} {P} Q :
    (exists t : T, P t /\ Q t) -> (exists t, Q t).
  Proof. case=>t [_ H] ; by exists t. Qed.

  Lemma existsb_l {T : finType} {P} Q :
    [exists t : T, P t && Q t] -> [exists t, P t].
  Proof.
  move=>/existsP ; case=>t /andP [H _].
  apply/existsP ; by exists t.
  Qed.

  Lemma existsb_r {T : finType} {P} Q :
    [exists t : T, P t && Q t] -> [exists t, Q t].
  Proof.
  move=>/existsP ; case=>t /andP [_ H].
  apply/existsP ; by exists t.
  Qed.

  Lemma forall_l {T} {P} Q :
    (forall t : T, P t /\ Q t) -> (forall t, P t).
  Proof. move=>H t ; by have [Ht _] := H t. Qed.

  Lemma forall_r {T} {P} Q :
    (forall t : T, P t /\ Q t) -> (forall t, Q t).
  Proof. move=>H t ; by have [_ Ht] := H t. Qed.

  Lemma forallb_l {T : finType} {P} Q :
    [forall t : T, P t && Q t] -> [forall t, P t].
  Proof.
  move=>/forallP H ; apply/forallP=>t.
  by have [Ht _] := andP (H t).
  Qed.

  Lemma forallb_r {T : finType} {P} Q :
    [forall t : T, P t && Q t] -> [forall t, Q t].
  Proof.
  move=> /forallP H ; apply/forallP=>t.
  by have [_ Ht] := andP (H t).
  Qed.

End ExistsForall.
