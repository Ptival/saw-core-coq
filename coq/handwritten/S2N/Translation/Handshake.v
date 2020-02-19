From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.

From S2N Require Import Embedding.
From S2N Require Import Pointed.

From mathcomp Require Import ssreflect.
From mathcomp Require Import tuple.

Import CryptolPrimitives.

Definition handshake : Type
  := (seq 32 bool * seq 32 bool).

Record Handshake := MkHandshake
  {
    handshakeType : 32.-tuple bool;
    messageNumber : 32.-tuple bool;
  }.

Definition handshake_as_Handshake
'(a, b)
  : Handshake
  :=
    {|
      handshakeType := seq_to_BITS a; (* Cryptol sorts the fields *)
      messageNumber := seq_to_BITS b;
    |}.

Definition Handshake_as_handshake
(c : Handshake) : handshake
  := ( BITS_to_seq (handshakeType c)
       , BITS_to_seq (messageNumber c)
  ).

Ltac moveConcreteHandshake
  := move => [? ?].

Definition Handshake_as_handshake_as_Handshake
  : forall h,
    Handshake_as_handshake (handshake_as_Handshake h) = h.
Proof.
  moveConcreteHandshake => /=.
  rewrite /Handshake_as_handshake /=.
  rewrite !BITS_to_seq_seq_to_BITS //.
Qed.

Ltac simplHandshake :=
  rewrite /handshakeType
          /messageNumber
.


Definition handshake_as_Handshake_as_handshake
  : forall h,
    handshake_as_Handshake (Handshake_as_handshake h) = h.
Proof.
  move => [] *.
  rewrite /handshake_as_Handshake /Handshake_as_handshake.
  simplHandshake.
  rewrite !seq_to_BITS_BITS_to_seq //.
Qed.

(* Global Instance Pointed_Handshake : Pointed Handshake := *)
(*   {| *)
(*     pointed := *)
(*       {| *)
(*         handshakeType := pointed; *)
(*         messageNumber := pointed; *)
(*       |}; *)
(*   |}. *)
