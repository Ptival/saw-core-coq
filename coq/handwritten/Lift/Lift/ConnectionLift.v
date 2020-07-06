From Coq Require Import Vectors.Vector.
From Coq Require Import ssreflect.

From mathcomp Require Import eqtype.
From mathcomp Require Import ssrfun.
From mathcomp Require Import ssrnat.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From Lift Require Import Preprocess.S2NPP.
From Lift Require Import Preprocess.HandshakePP.
From Lift Require Import Preprocess.ConnectionPP.

From Lift Require Import Lift.HandshakeLift.

From Ornamental Require Import Ornaments.

From S2N Require Import S2N.

Set DEVOID search prove equivalence.
Set DEVOID lift type.

Import CryptolPrimitives.

Module ConnectionAccessors.

  Definition get_client_auth_flag (c : Connection.connection) : bool :=
    fst c.

  Definition get_corked (c : Connection.connection) : seq 2 bool :=
    fst (snd c).

  Definition get_corked_IO (c : Connection.connection) : seq 8 bool :=
    fst (snd (snd c)).

  Definition get_handshake (c : Connection.connection) : Handshake.handshake :=
    fst (snd (snd (snd c))).

  (* Definition get_is_caching_enabled (c : connection) : bool := *)
  (*   fst (snd (snd (snd (snd c)))). *)

  (* Definition get_key_exchange_EPH (c : connection) : bool := *)
  (*   fst (snd (snd (snd (snd (snd c))))). *)

  (* Definition get_mode (c : connection) : seq 32 bool := *)
  (*   fst (snd (snd (snd (snd (snd (snd c)))))). *)

  (* Definition get_resume_from_cache (c : connection) : bool := *)
  (*   fst (snd (snd (snd (snd (snd (snd (snd c))))))). *)

  (* Definition get_server_can_send_ocsp (c : connection) : bool := *)
  (*   snd (snd (snd (snd (snd (snd (snd (snd c))))))). *)

End ConnectionAccessors.

Module ConnectionRecord.

  Record Connection :=
    MkConnection
      {
        clientAuthFlag    : bool;
        corked            : seq 2 bool;
        corkedIO          : seq 8 bool;
        handshake         : HandshakeRecordPP.Handshake;
        isCachingEnabled  : bool;
        keyExchangeEPH    : bool;
        mode              : seq 32 bool;
        resumeFromCache   : bool;
        serverCanSendOCSP : bool;
      }.

  Scheme Induction for Connection Sort Prop.
  Scheme Induction for Connection Sort Type.
  Scheme Induction for Connection Sort Set.

End ConnectionRecord.

Preprocess Module ConnectionAccessors
  as ConnectionAccessorsPP
       { opaque
           Handshake.handshake
           fst snd
           natToNat
           seq
     }.

Preprocess Module ConnectionRecord
  as ConnectionRecordPP0
       { opaque
           Handshake.handshake
           fst snd
           natToNat
           seq
     }.

Lift Module
     HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in ConnectionRecordPP0
  as ConnectionRecordPP1.

(* We need to be able to talk about the type that is just like ConnectionPP.connection, but with *)
(* HandshakePP.handshake replaced with HandshakeRecordPP.Handhake. *)
Lift Handshake.handshake
     HandshakeRecordPP.Handshake
  in ConnectionPP.connection
  as ConnectionPPconnection.

Lift Module
     ConnectionPPconnection
     ConnectionRecordPP1.Connection
  in ConnectionRecordPP1
  as ConnectionRecordPP.

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in S2N'.s2n_cork
  as s2nCork0
       { opaque ecPlus PArithSeqBool ecNumber PLiteralSeqBool
       }.

Lift ConnectionPPconnection
     ConnectionRecordPP0.Connection
  in s2nCork0
  as s2nCork
       { opaque ecPlus PArithSeqBool ecNumber PLiteralSeqBool
       }.

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in S2N'.s2n_uncork
  as s2nUncork0
       { opaque ecMinus PArithSeqBool ecNumber PLiteralSeqBool
       }.

Lift ConnectionPPconnection
     ConnectionRecordPP0.Connection
  in s2nUncork0
  as s2nUncork
       { opaque ecMinus PArithSeqBool ecNumber PLiteralSeqBool
       }.

Definition cork (c : ConnectionRecordPP0.Connection) : ConnectionRecordPP0.Connection :=
  {|
  ConnectionRecordPP0.clientAuthFlag    := ConnectionRecordPP0.clientAuthFlag c;
  ConnectionRecordPP0.corked            := s2nCork c;
  ConnectionRecordPP0.corkedIO          := ConnectionRecordPP0.corkedIO c;
  ConnectionRecordPP0.handshake         := ConnectionRecordPP0.handshake c;
  ConnectionRecordPP0.isCachingEnabled  := ConnectionRecordPP0.isCachingEnabled c;
  ConnectionRecordPP0.keyExchangeEPH    := ConnectionRecordPP0.keyExchangeEPH c;
  ConnectionRecordPP0.mode              := ConnectionRecordPP0.mode c;
  ConnectionRecordPP0.resumeFromCache   := ConnectionRecordPP0.resumeFromCache c;
  ConnectionRecordPP0.serverCanSendOCSP := ConnectionRecordPP0.serverCanSendOCSP c;
  |}.

Definition uncork (c : ConnectionRecordPP0.Connection) : ConnectionRecordPP0.Connection :=
  {|
  ConnectionRecordPP0.clientAuthFlag    := ConnectionRecordPP0.clientAuthFlag c;
  ConnectionRecordPP0.corked            := s2nUncork c;
  ConnectionRecordPP0.corkedIO          := ConnectionRecordPP0.corkedIO c;
  ConnectionRecordPP0.handshake         := ConnectionRecordPP0.handshake c;
  ConnectionRecordPP0.isCachingEnabled  := ConnectionRecordPP0.isCachingEnabled c;
  ConnectionRecordPP0.keyExchangeEPH    := ConnectionRecordPP0.keyExchangeEPH c;
  ConnectionRecordPP0.mode              := ConnectionRecordPP0.mode c;
  ConnectionRecordPP0.resumeFromCache   := ConnectionRecordPP0.resumeFromCache c;
  ConnectionRecordPP0.serverCanSendOCSP := ConnectionRecordPP0.serverCanSendOCSP c;
  |}.

Module CorkTheoremLow.

  Definition justCork
             (b : bool) (s0 : seq 8 bool) (h : Handshake.handshake) (b0 b1 : bool) (s1 : seq 32 bool) (b2 b3 : bool) :=
      S2N'.s2n_cork (b, (joinLSB (joinLSB (nil bool) false) false, (s0, (h, (b0, (b1, (s1, (b2, b3)))))))).

  Definition lemma_1_type :=
    forall (b : bool) (s0 : seq 8 bool) (h : Handshake.handshake) (b0 b1 : bool) (s1 : seq 32 bool) (b2 b3 : bool),
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

  Theorem cork_theorem_low : forall c,
    ConnectionAccessors.get_corked c = bvNat 2 0 ->
    S2N'.s2n_cork c = bvNat 2 1.
  Proof.
    intros [? [? [? [? [? [? [? [? ?]]]]]]]].
    simpl.
    unfold ConnectionAccessors.get_corked.
    simpl.
    intros.
    subst s.
    apply lemma_1.
  Defined.

End CorkTheoremLow.

Set Preprocess default opaque.

Preprocess
  Module CorkTheoremLow
  as CorkTheoremLowPP.

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in CorkTheoremLowPP.justCork
  as CorkTheoremLow_justCork0
       { opaque joinLSB
       }.

(* From Ornamental Require Import Patcher.Patch. *)

Definition two := 2.
Definition eight := 8.
Definition thirtyTwo := 32.

From Patcher Require Import Patch.

Replace Convertible Module
        two eight thirtyTwo
  in CorkTheoremLowPP
  as CorkTheoremLowPP'.

Print CorkTheoremLowPP'.lemma_1.

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in CorkTheoremLowPP'.lemma_1_type
  as CorkTheoremLow_lemma_1_type_0.

Check (CorkTheoremLowPP'.lemma_1 : CorkTheoremLowPP'.lemma_1_type).

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in CorkTheoremLowPP'.lemma_1
  as CorkTheoremLow_lemma_1_0
       { opaque

           Ascii.Ascii
           BinNums.xI
           BinNums.xO
           Bool
           CoreRecords.FScons
           CoreRecords.field
           CoreRecords.Fields
           CoreRecords.get_member
           CoreRecords.pm_Branch
           CoreRecords.pm_Leaf
           CoreRecords.record_get
           CoreRecords.string_to_p
           Datatypes.snd
           Logic.eq_refl
           Notation.Rget
           PArithWord
           PLiteralSeqBool
           String.EmptyString
           String.String
           TCNum
           bitvector
           bool
           bvAdd
           bvNat
           bvToBITS
           cons
           ecNumber
           ecPlus
           eight
           half
           joinLSB
           nil
           odd
           operations.adcB
           prod
           seq
           shiftin
           spec.BITS
           spec.toNat
           thirtyTwo
           two

           (* those should probably be transparent in the real one *)
           (* S2N'.s2n_cork *)
           (* prod *)

       }.

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in CorkTheoremLowPP'.cork_theorem_low
  as CorkTheoremLow_cork_theorem_low_0
       { opaque

           Ascii.Ascii
           BinNums.xI
           BinNums.xO
           Bool
           CoreRecords.FScons
           CoreRecords.field
           CoreRecords.Fields
           CoreRecords.get_member
           CoreRecords.pm_Branch
           CoreRecords.pm_Leaf
           CoreRecords.record_get
           CoreRecords.string_to_p
           Datatypes.snd
           Logic.eq_refl
           Notation.Rget
           PArithWord
           PLiteralSeqBool
           String.EmptyString
           String.String
           TCNum
           bitvector
           bool
           bvAdd
           bvNat
           bvToBITS
           cons
           ecNumber
           ecPlus
           eight
           half
           joinLSB
           nil
           odd
           operations.adcB
           prod
           seq
           shiftin
           spec.BITS
           spec.toNat
           thirtyTwo
           two

           (* those should probably be transparent in the real one *)
           (* S2N'.s2n_cork *)
           (* prod *)

       }.

Lift ConnectionPPconnection
     ConnectionRecordPP0.Connection
  in CorkTheoremLow_lemma_1_type_0
  as CorkTheoremLow_lemma_1_type_1.

Lift ConnectionPPconnection
     ConnectionRecordPP0.Connection
  in CorkTheoremLow_lemma_1_0
  as CorkTheoremLow_lemma_1_1
       { opaque

           Ascii.Ascii
           BinNums.xI
           BinNums.xO
           Bool
           CoreRecords.FScons
           CoreRecords.field
           CoreRecords.Fields
           CoreRecords.get_member
           CoreRecords.pm_Branch
           CoreRecords.pm_Leaf
           CoreRecords.record_get
           CoreRecords.string_to_p
           Datatypes.snd
           Logic.eq_refl
           Notation.Rget
           PArithWord
           PLiteralSeqBool
           String.EmptyString
           String.String
           TCNum
           bitvector
           bool
           bvAdd
           bvNat
           bvToBITS
           cons
           ecNumber
           ecPlus
           eight
           half
           joinLSB
           nil
           odd
           operations.adcB
           prod
           seq
           shiftin
           spec.BITS
           spec.toNat
           thirtyTwo
           two

           (* those should probably be transparent in the real one *)
           (* S2N'.s2n_cork *)
           (* prod *)

       }.

(* STUCK *)

Lift ConnectionPPconnection
     ConnectionRecordPP0.Connection
  in CorkTheoremLow_cork_theorem_low_0
  as CorkTheoremLow_cork_theorem_low_1
       { opaque

           Ascii.Ascii
           BinNums.xI
           BinNums.xO
           Bool
           CoreRecords.FScons
           CoreRecords.field
           CoreRecords.Fields
           CoreRecords.get_member
           CoreRecords.pm_Branch
           CoreRecords.pm_Leaf
           CoreRecords.record_get
           CoreRecords.string_to_p
           Logic.eq_refl
           Notation.Rget
           PArithWord
           PLiteralSeqBool
           String.EmptyString
           String.String
           TCNum
           bitvector
           bool
           bvAdd
           bvNat
           bvToBITS
           cons
           ecNumber
           ecPlus
           eight
           half
           joinLSB
           nil
           odd
           operations.adcB
           seq
           shiftin
           spec.BITS
           spec.toNat
           thirtyTwo
           two

       }.

Theorem cork_uncork_high :
  forall c,
    ConnectionRecordPP0.corked c = bvNat 2 0 ->
    s2nCork c = bvNat 2 1.
Proof.
  (* use lifted *)
Qed.

Theorem cork_uncork : forall c,
    ConnectionRecordPP0.corked c = bvNat 2 0 ->
    uncork (cork c) = c.
Proof.
  intros [] H.
  simpl in H.
  unfold cork, uncork.
  simpl.
  f_equal.
  unfold s2nCork.
  simpl.
  unfold s2nUncork.
  simpl.
  unfold ecPlus. unfold Notation.Rget. simpl.
  unfold ecMinus. unfold Notation.Rget. simpl.
  subst corked.
  unfold joinLSB.
  simpl.
  unfold bvAdd.
  simpl.
  unfold bvToBITS.
  simpl.
  unfold bvToNatFolder.
  simpl.
  compute.
  apply val_inj.
Qed.

Theorem test : forall c,
    c {| corked := _; |} = c.

    S2N'.s2n_cork (S2N'.s2n_uncork c) = c.

Stop.

(* ACTIVE_MESSAGE is too complex *)

Print S2NPP.S2N'.ACTIVE_MESSAGE.

Check (S2NPP.S2N'.ACTIVE_MESSAGE : ConnectionPP.connection -> seq 32 bool).

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in S2N'.ACTIVE_MESSAGE
  as ActiveMessage0.

Lift ConnectionPPconnection
     ConnectionRecordPP1.Connection
  in ActiveMessage0
  as ActiveMessage.

Lift connectionPP ConnectionPP.Connection
  in ActiveMessage0
  as ActiveMessage.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N'.advance_message
  as advanceMessage0.

(* This one does not terminate. *)
Lift connectionPP ConnectionPP.Connection
  in advanceMessage0
  as advanceMessage.

Definition myHandshake : HandshakePP.Handshake :=
  HandshakePP.MkHandshake
    (bvNat _ 0)
    (bvNat _ 0)
.

Definition myConnection : ConnectionPP.Connection :=
  ConnectionPP.MkConnection
    (false)
    (bvNat _ 0)
    (bvNat _ 0)
    (myHandshake)
    (false)
    (false)
    (bvNat _ 0)
    (false)
    (false)
.
