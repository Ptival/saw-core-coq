From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.

From S2N Require Import Embedding.
From S2N Require Import Pointed.

From mathcomp Require Import tuple.

Import CryptolPrimitives.

Definition cry_handshake_action : Type
  := (seq 8 bool * (seq 8 bool * seq 8 bool)).

Record HandshakeAction := MkHandshakeAction
  {
    recordType  : 8.-tuple bool;
    messageType : 8.-tuple bool;
    writer      : 8.-tuple bool;
  }.

Global Instance Embedding_HandshakeAction
    : Embedding cry_handshake_action HandshakeAction :=
    {|
      toAbstract :=
        fun '(a, (b, c)) =>
          {|
            messageType := seq_to_BITS a; (* Cryptol sorts the fields *)
            recordType  := seq_to_BITS b;
            writer      := seq_to_BITS c;
          |}
      ;
      toConcrete :=
        fun c =>
          ( BITS_to_seq (messageType c)
            , ( BITS_to_seq (recordType c)
                , BITS_to_seq (writer c)
            )
          )
      ;
    |}.

  Global Instance Pointed_HandshakeAction : Pointed HandshakeAction :=
    {|
      pointed :=
        {|
          recordType  := pointed;
          messageType := pointed;
          writer      := pointed;
        |};
    |}.
