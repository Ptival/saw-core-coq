From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCorePrelude.

From S2N Require Import Translation.Handshake.

From S2N Require Import S2N.
From S2N Require Import Translation.Connection.

(* From mathcomp Require Import eqtype. *)
(* From mathcomp Require Import ssrnat. *)
(* From mathcomp Require Import tuple. *)

(* Scheme Minimality for tuple.tuple_of Sort Prop. *)
(* Scheme Induction  for tuple.tuple_of Sort Set. *)
(* Scheme Induction  for tuple.tuple_of Sort Type. *)

(* Scheme Minimality for eqtype.Equality.type Sort Prop. *)
(* Scheme Induction  for eqtype.Equality.type Sort Set. *)
(* Scheme Induction  for eqtype.Equality.type Sort Type. *)

(* Scheme Minimality for eqtype.Equality.mixin_of Sort Prop. *)
(* Scheme Induction  for eqtype.Equality.mixin_of Sort Set. *)
(* Scheme Induction  for eqtype.Equality.mixin_of Sort Type. *)

(* Scheme Induction for eqtype.Sub_spec Sort Prop. *)
(* Scheme Induction for eqtype.Sub_spec Sort Set. *)
(* Scheme Induction for eqtype.Sub_spec Sort Type. *)

(* Scheme Induction for eqtype.insub_spec Sort Prop. *)
(* Scheme Induction for eqtype.insub_spec Sort Set. *)
(* Scheme Induction for eqtype.insub_spec Sort Type. *)

(* Scheme Induction for eqtype.subType Sort Prop. *)
(* Scheme Induction for eqtype.subType Sort Set. *)
(* Scheme Induction for eqtype.subType Sort Type. *)

From Ornamental Require Import Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)

Set Preprocess default opaque.

Preprocess
  Module Connection
  as ConnectionPP0.
(* DO NOT MAKE Handshake.handshake transparent *)

Print ConnectionPP0.connection.
Print ConnectionPP0.Connection.
Print Connection.cork.
Print ConnectionPP0.cork.

From Lift Require Import HandshakePP.

Print ConnectionPP0.connection.

From Patcher Require Import Patch.

(* Checking that these are the same *)
Goal Handshake.handshake = HandshakePP.handshake.
  reflexivity.
Qed.

(* This does not seem to do what I expect, but it's all the same anyway *)

Definition two := 2.
Definition eight := 8.
Definition thirtyTwo := 32.

(* Replace Handshake.handshake with HandshakePP.handshake (no-op) *)
Replace Convertible Module
        HandshakePP.handshake
        two
        eight
        thirtyTwo
  in ConnectionPP0
  as ConnectionPP1.

Print ConnectionPP1.connection.

(* Replace Handshake.Handshake with HandshakePP.Handshake (lift) *)
(* NOTE:
Handshake.Handshake and HandshakePP.Handshake are **NOT** convertible.
However, it's an easy lift.
*)

Print ConnectionPP1.get_handshake.
Print Connection.cork.
Print ConnectionPP1.cork.
Print ConnectionPP1.connection.


Lift Module
     HandshakePP.handshake
     HandshakePP.Handshake
  in ConnectionPP1
  as ConnectionPP2
       { opaque
           CryptolPrimitives.seq
           CryptolPrimitives.TCNum
           CryptolPrimitivesForSAWCoreExtra.natToNat
           Datatypes.fst Datatypes.snd
           SAWCoreVectorsAsCoqVectors.bvAdd
           SAWCoreVectorsAsCoqVectors.bvSub
           CryptolPrimitivesForSAWCoreExtra.natToNat
       }.

(* Coherence checks *)

Print ConnectionPP1.Connection.

Lift Module
     Handshake.Handshake
     HandshakePP.Handshake
  in ConnectionPP2
  as ConnectionPP3
       { opaque
           CryptolPrimitives.seq
           CryptolPrimitives.TCNum
           CryptolPrimitivesForSAWCoreExtra.natToNat
           Datatypes.fst Datatypes.snd
           SAWCoreVectorsAsCoqVectors.bvAdd
           SAWCoreVectorsAsCoqVectors.bvSub
           CryptolPrimitivesForSAWCoreExtra.natToNat
       }.

Print ConnectionPP3.Connection.


Print ConnectionPP2.connection.

Print ConnectionPP3.
Print ConnectionPP3.cork.

Lift Module
     ConnectionPP3.connection
     ConnectionPP3.Connection
  in ConnectionPP3
  as ConnectionPP4
       { opaque
           CryptolPrimitives.seq
           CryptolPrimitives.TCNum
           CryptolPrimitivesForSAWCoreExtra.natToNat
           SAWCoreVectorsAsCoqVectors.bvAdd
           SAWCoreVectorsAsCoqVectors.bvSub
           CryptolPrimitivesForSAWCoreExtra.natToNat
       }.

Print ConnectionPP4.connection.
Print ConnectionPP3.connection.
Print ConnectionPP2.connection.

Print ConnectionPP4.Connection.
Print ConnectionPP3.Connection.

Print ConnectionPP4.cork.

From Coq Require Import Vectors.Vector.
From Coq Require Import ssreflect.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From S2N Require Import S2N.

Import CryptolPrimitives.

From Lift Require Import Preprocess.S2NPP.

Module CorkTheoremLow.

  (* Definition justCork *)
  (*            (b : bool) (s0 : seq 8 bool) (h : Handshake.handshake) (b0 b1 : bool) (s1 : seq 32 bool) (b2 b3 : bool) := *)
  (*     S2N'.s2n_cork (b, (joinLSB (joinLSB (nil bool) false) false, (s0, (h, (b0, (b1, (s1, (b2, b3)))))))). *)

  Definition cork_theorem_low_type := forall c,
    ConnectionPP1.get_corked c = bvNat 2 0 ->
    ConnectionPP1.get_corked (ConnectionPP1.cork c) = bvNat 2 1.
    (* S2N'.s2n_cork c = bvNat 2 1. *)

End CorkTheoremLow.

Preprocess Module CorkTheoremLow as CorkTheoremLowPP.

Print ConnectionPP1.connection.

Print CorkTheoremLowPP.cork_theorem_low_type.

Lift Module
     HandshakePP.handshake
     HandshakePP.Handshake
  in CorkTheoremLowPP
  as CorkTheoremLowPP2
       { opaque
           CryptolPrimitives.seq
           CryptolPrimitives.TCNum
           CryptolPrimitivesForSAWCoreExtra.natToNat
           SAWCoreVectorsAsCoqVectors.bvAdd
           SAWCoreVectorsAsCoqVectors.bvSub
           CryptolPrimitivesForSAWCoreExtra.natToNat

       }.

Lift Module
     Handshake.Handshake
     HandshakePP.Handshake
  in CorkTheoremLowPP2
  as CorkTheoremLowPP3
       { opaque
           CryptolPrimitives.seq
           CryptolPrimitives.TCNum
           CryptolPrimitivesForSAWCoreExtra.natToNat
           SAWCoreVectorsAsCoqVectors.bvAdd
           SAWCoreVectorsAsCoqVectors.bvSub
           CryptolPrimitivesForSAWCoreExtra.natToNat
       }.

Print CorkTheoremLowPP3.cork_theorem_low_type.

Lift Module
     ConnectionPP3.connection
     ConnectionPP3.Connection
  in CorkTheoremLowPP3
  as CorkTheoremLowPP4
       { opaque
           CryptolPrimitives.seq
           CryptolPrimitives.TCNum
           CryptolPrimitivesForSAWCoreExtra.natToNat
           SAWCoreVectorsAsCoqVectors.bvAdd
           SAWCoreVectorsAsCoqVectors.bvSub
           CryptolPrimitivesForSAWCoreExtra.natToNat
       }.

Print CorkTheoremLowPP4.cork_theorem_low_type.

Module CorkTheoremHigh.

  Theorem corkTheoremHigh : CorkTheoremLowPP4.cork_theorem_low_type.
  Proof.
    intros [].
    simpl.
    intros H.
    subst.
    reflexivity.
  Defined.

End CorkTheoremHigh.

Preprocess Module CorkTheoremHigh as CorkTheoremHighPP.

Print CorkTheoremHighPP.corkTheoremHigh.

Lift Module
     ConnectionPP3.Connection
     ConnectionPP3.connection
  in CorkTheoremHighPP
  as CorkTheoremHighPP1
       { opaque
           CryptolPrimitives.seq
           CryptolPrimitives.TCNum
           CryptolPrimitivesForSAWCoreExtra.natToNat
           SAWCoreVectorsAsCoqVectors.bvAdd
           SAWCoreVectorsAsCoqVectors.bvSub
           CryptolPrimitivesForSAWCoreExtra.natToNat
       }.

Check CorkTheoremHighPP1.corkTheoremHigh.
Print CorkTheoremLowPP3.cork_theorem_low_type.

Print CorkTheoremHighPP1.corkTheoremHigh.

Find ornament
     HandshakePP.Handshake
     Handshake.Handshake.

Lift Module
     HandshakePP.Handshake
     Handshake.Handshake
  in CorkTheoremHighPP1
  as CorkTheoremHighPP2
       { opaque
           CryptolPrimitives.seq
           CryptolPrimitives.TCNum
           CryptolPrimitivesForSAWCoreExtra.natToNat
           SAWCoreVectorsAsCoqVectors.bvAdd
           SAWCoreVectorsAsCoqVectors.bvSub
           CryptolPrimitivesForSAWCoreExtra.natToNat
           Prod.fst Prod.snd
       }.

Check CorkTheoremHighPP2.corkTheoremHigh.

Lift Module
     Handshake.Handshake
     Handshake.handshake
  in CorkTheoremHighPP2
  as CorkTheoremHighPP3
       { opaque
           CryptolPrimitives.seq
           CryptolPrimitives.TCNum
           CryptolPrimitivesForSAWCoreExtra.natToNat
           SAWCoreVectorsAsCoqVectors.bvAdd
           SAWCoreVectorsAsCoqVectors.bvSub
           CryptolPrimitivesForSAWCoreExtra.natToNat
           Datatypes.fst Datatypes.snd
       }.

Check CorkTheoremHighPP3.corkTheoremHigh.

Theorem cork_theorem_low : CorkTheoremLow.cork_theorem_low_type.
Proof.
  intro c. induction c.
  apply CorkTheoremHighPP3.corkTheoremHigh.
Defined.


(*
To play with:

Decompile CorkTheoremHighPP3.corkTheoremHigh.
*)


Theorem cork_theorem_low : cork_theorem_low_type.
  Proof.
    intros [? [? [? [? [? [? [? [? ?]]]]]]]].
    simpl.
    apply lemma_3.
  Defined.

  Definition lemma_1_type :=
    forall (b : bool) (s0 : seq 8 bool) (h : HandshakePP.handshake) (b0 b1 : bool) (s1 : seq 32 bool) (b2 b3 : bool),
      S2N'.s2n_cork (b, (joinLSB (joinLSB (nil bool) false) false, (s0, (h, (b0, (b1, (s1, (b2, b3)))))))) =
      joinLSB (joinLSB (nil bool) false) true.

  Lemma lemma_1 : lemma_1_type.
  Proof.
    intros b s0 h b0 b1 s1 b2 b3.
    unfold S2N'.s2n_cork.
    simpl.
    unfold ecPlus; simpl.
    unfold Notation.Rget; simpl.
    unfold bvAdd; simpl.
    unfold joinLSB; simpl.
    reflexivity.
  Defined.

  Lemma lemma_2:
    forall (b : bool) (s : seq 2 bool) (s0 : seq 8 bool) (h : Handshake.handshake)
           (b0 b1 : bool) (s1 : seq 32 bool) (b2 b3 : bool),
      s = joinLSB (joinLSB (nil bool) false) false ->
      S2N'.s2n_cork (b, (s, (s0, (h, (b0, (b1, (s1, (b2, b3))))))))
      = joinLSB (joinLSB (nil bool) false) true.
  Proof.
    intros b s s0 h b0 b1 s1 b2 b3.
    intros.
    subst s.
    apply lemma_1.
  Defined.

  Definition lemma_3_type :=
    forall (b : bool) (s : seq 2 bool) (s0 : seq 8 bool) (h : Handshake.handshake)
           (b0 b1 : bool) (s1 : seq 32 bool) (b2 b3 : bool),
      ConnectionAccessors.get_corked (b, (s, (s0, (h, (b0, (b1, (s1, (b2, b3))))))))
      = joinLSB (joinLSB (nil bool) false) false ->
      S2N'.s2n_cork (b, (s, (s0, (h, (b0, (b1, (s1, (b2, b3))))))))
      = joinLSB (joinLSB (nil bool) false) true.

  Lemma lemma_3 : lemma_3_type.
  Proof.
    intros b s s0 h b0 b1 s1 b2 b3.
    unfold ConnectionAccessors.get_corked.
    simpl.
    apply lemma_2.
  Defined.

  Definition cork_theorem_low_type := forall c,
    ConnectionAccessors.get_corked c = bvNat 2 0 ->
    S2N'.s2n_cork c = bvNat 2 1.

  Theorem cork_theorem_low : cork_theorem_low_type.
  Proof.
    intros [? [? [? [? [? [? [? [? ?]]]]]]]].
    simpl.
    apply lemma_3.
  Defined.

End CorkTheoremLow.
