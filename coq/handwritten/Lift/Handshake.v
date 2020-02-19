From Bits Require Import spec.

From Coq Require Import Vectors.Vector.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From Lift Require Import S2N.

From Ornamental Require Import Ornaments.

From S2N Require Import S2N.

Set DEVOID search prove equivalence.
Set DEVOID lift type.

Import CryptolPrimitives.

Module Handshake.

  (** [cry_handshake] is the [handshake] type as it comes out of the translation
from Cryptol to Coq.  The fields have been inlined into a nested tuple type.

This is what the original [handshake] type looked like:

type handshake = {handshake_type : [32]
                 ,message_number : [32]
                 }
   *)
  Definition handshake : Type := (seq S2N.Opaque32 bool * seq S2N.Opaque32 bool).

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

  Definition get_handshake_type (h : handshake) : seq 32 bool :=
    fst h.

  Definition get_message_number (h : handshake) : seq 32 bool :=
    snd h.

End Handshake.

Preprocess Module Handshake
  as HandshakePP
       { opaque
           PArithSeqBool
           PCmpSeq
           PCmpSeqBool
           PLiteralSeqBool
           ecAt
           ecGt
           ecLt
           ecMinus
           ecNotEq
           ecNumber
           ecPlus
           handshakes_fn
           natToNat
           seq
       }.

Configure Lift HandshakePP.handshake HandshakePP.Handshake
          { opaque
              PArithSeqBool
              PCmpSeq
              PCmpSeqBool
              PLiteralSeqBool
              ecAt
              ecGt
              ecLt
              ecMinus
              ecNotEq
              ecNumber
              ecPlus
              handshakes_fn
              natToNat
              seq

              S2N'.Opaque01
              S2N'.Opaque02
              S2N'.Opaque03
              S2N'.Opaque04
              S2N'.Opaque05
              S2N'.Opaque06
              S2N'.Opaque07
              S2N'.Opaque08
              S2N'.Opaque09
              S2N'.Opaque10
              S2N'.Opaque11
              S2N'.Opaque12
              S2N'.Opaque13
              S2N'.Opaque14
              S2N'.Opaque15
              S2N'.Opaque16
              S2N'.Opaque17
              S2N'.Opaque18
              S2N'.Opaque19
              S2N'.Opaque20
              S2N'.Opaque21
              S2N'.Opaque22
              S2N'.Opaque23
              S2N'.Opaque24
              S2N'.Opaque25
              S2N'.Opaque26
              S2N'.Opaque27
              S2N'.Opaque28
              S2N'.Opaque29
              S2N'.Opaque30
              S2N'.Opaque31
              S2N'.Opaque32
              S2N'.Opaque33
              S2N'.Opaque34
              S2N'.Opaque35
              S2N'.Opaque36
              S2N'.Opaque37
              S2N'.Opaque38
              S2N'.Opaque39
              S2N'.Opaque40
              S2N'.Opaque41
              S2N'.Opaque42
              S2N'.Opaque43
              S2N'.Opaque44
              S2N'.Opaque45
              S2N'.Opaque46
              S2N'.Opaque47
              S2N'.Opaque48
              S2N'.Opaque49
              S2N'.Opaque50
              S2N'.Opaque51
              S2N'.Opaque52
              S2N'.Opaque53
              S2N'.Opaque54
              S2N'.Opaque55
              S2N'.Opaque56
              S2N'.Opaque57
              S2N'.Opaque58
              S2N'.Opaque59
              S2N'.Opaque60
              S2N'.Opaque61
              S2N'.Opaque62
              S2N'.Opaque63
              S2N'.Opaque64
              S2N'.Opaque65
              S2N'.Opaque66
              S2N'.Opaque67
              S2N'.Opaque68
              S2N'.Opaque69

              S2N'.Opaque83
              S2N'.Opaque127
              S2N'.Opaque128
          }.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in HandshakePP.get_handshake_type
  as getHandshakeType.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in HandshakePP.get_message_number
  as getMessageNumber.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N'.ACTIVE_MESSAGE
  as ActiveMessage0.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N'.valid_handshake
  as validHandshake.
