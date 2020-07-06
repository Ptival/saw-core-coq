From Bits Require Import spec.

From Coq Require Import String.
From Coq Require Import Vectors.Vector.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From Lift Require Import Preprocess.S2NPP.
From Lift Require Import Preprocess.HandshakePP.

From Ornamental Require Import Ornaments.

From S2N Require Import S2N.

Set DEVOID search prove equivalence.
Set DEVOID lift type.

Set Preprocess default opaque.

Import CryptolPrimitives.

Print HandshakePP.handshake.

Module HandshakeRecord.

  (** We can define more convenient types for [handshake] and [connection] in Coq.
Ideally, we'd like the translation to generate those, but in its current state,
it goes through an intermediate language that does not support records and
record types.
   *)
  Record Handshake :=
    MkHandshake
      {
        handshakeType : seq 32 bool;
        messageNumber : seq 32 bool;
      }.

  Scheme Induction for Handshake Sort Prop.
  Scheme Induction for Handshake Sort Type.
  Scheme Induction for Handshake Sort Set.

  Definition get_handshake_type (h : HandshakePP.handshake) : seq 32 bool :=
    fst h.

  Definition get_message_number (h : HandshakePP.handshake) : seq 32 bool :=
    snd h.

End HandshakeRecord.

Preprocess Module HandshakeRecord as HandshakeRecordPP { opaque ecAt }.

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in HandshakeRecordPP.get_handshake_type
  as getHandshakeType.

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in HandshakeRecordPP.get_message_number
  as getMessageNumber.

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in S2N'.ACTIVE_MESSAGE
  as ActiveMessage0 { opaque S2N'.handshakes }.

Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in S2N'.valid_handshake
  as validHandshake0
{ opaque
PArithSeqBool
PCmpSeq
PCmpSeqBool
PCmpSeqBool
PLiteralSeqBool
PZeroSeq
PZeroSeqBool
S2N'.and
S2N'.handshakes_fn
S2N'.length
ecAt
ecGt
ecLt
ecMinus
ecNotEq
ecNumber
ecPlus
ecZero
seq
}.
