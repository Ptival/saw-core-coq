From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.

From Lift Require Import Translation.Handshake.

From S2N Require Import Embedding.
From S2N Require Import Pointed.
From S2N Require Import Translation.Handshake.

From mathcomp Require Import ssreflect.
From mathcomp Require Import tuple.

Import CryptolPrimitives.

Definition connection : Type
  := (bool (* client_auth_flag *)
      * (seq 2 bool (* corked *)
         * (seq 8 bool (* corked_io *)
            * (cry_handshake
               * (bool (* is_caching_enabled *)
                  * (bool (* key_exchange_eph *)
                     * (seq 32 bool (* mode *)
                        * (bool (* resume_from_cache *)
                           * bool (* server_can_send_ocsp *)
                        )
                     )
                  )
               )
            )
         )
      )
  )
.

Record Connection         := MkConnection
{
  handshake             : HandshakePP.Handshake;
  mode                  : 32.-tuple bool;
  corkedIO              : 8.-tuple bool;
  corked                : 2.-tuple bool;
  isCachingEnabled      : bool;
  resumeFromCache       : bool;
  serverCanSendOCSP     : bool;
  keyExchangeEPH        : bool;
  clientAuthFlag        : bool;
}.

Theorem elim_connection
        (M : connection -> Type)
  : (forall a b c d1 d2 e f g h i,
        M (a, (b, (c, ((d1, d2), (e, (f, (g, (h, i))))))))
    ) ->
    forall c, M c.
Proof.
  move => IH.
  move => [?[?[?[[? ?][?[?[?[??]]]]]]]].
  apply IH.
Qed.

Theorem elimConnection
        (M : Connection -> Type)
  : (forall a1 a2 b c d e f g h i,
        M (MkConnection (HandshakePP.MkHandshake a1 a2) b c d e f g h i)
    ) ->
    forall c, M c.
Proof.
  move => IH.
  move => [] [] *.
  apply IH.
Qed.

Definition connection_as_Connection
'(a, (b, (c, (d, (e, (f, (g, (h, i))))))))
  : Connection
  :=
    {| (* Cryptol sorts the fields *)
      clientAuthFlag        := a;
      corked                := seq_to_BITS b;
      corkedIO              := seq_to_BITS c;
      handshake             := @toAbstract _ _ HandshakePP.Embedding_Handshake d;
      isCachingEnabled      := e;
      keyExchangeEPH        := f;
      mode                  := seq_to_BITS g;
      resumeFromCache       := h;
      serverCanSendOCSP     := i;
    |}.

Definition Connection_as_connection
(c : Connection)
  : connection
  :=
    ( (clientAuthFlag c)
      , ( BITS_to_seq (corked c)
          , ( BITS_to_seq (corkedIO c)
              , ( @toConcrete _ _ HandshakePP.Embedding_Handshake (handshake c)
                  , ( (isCachingEnabled c)
                      , ( (keyExchangeEPH c)
                          , ( BITS_to_seq (mode c)
                              , ( (resumeFromCache c)
                                  , (serverCanSendOCSP c)
                              )
                          )
                      )
                  )
              )
          )
      )
    ).

Ltac moveConcreteConnection
  := move => [?[?[?[[??][?[?[?[??]]]]]]]].

Ltac simplConnection :=
  rewrite /handshake
          /mode
          /corkedIO
          /corked
          /serverCanSendOCSP
          /keyExchangeEPH
          /clientAuthFlag
          /isCachingEnabled
          /resumeFromCache
.

Definition Connection_as_connection_as_Connection
  : forall c,
    Connection_as_connection (connection_as_Connection c) = c.
Proof.
  moveConcreteConnection => /=.
  rewrite /Connection_as_connection.
  rewrite !BITS_to_seq_seq_to_BITS => //.
  simplConnection.
  simplHandshake.
  rewrite /toConcrete.
Qed.

Global Instance Isomorphism_Connection
  : Isomorphism (Embedding_Connection).
Proof.
  constructor.
  apply : elimConnection => *.
  simplConnection.
  rewrite /toConcrete.
  rewrite !seq_to_BITS_BITS_to_seq.
  f_equal.
  rewrite roundtrip' //.
Qed.

(* Global Instance Pointed_Connection : Pointed Connection := *)
(*   {| *)
(*     pointed := *)
(*       {| *)
(*         handshake             := pointed; *)
(*         mode                  := pointed; *)
(*         corkedIO              := pointed; *)
(*         corked                := pointed; *)
(*         isCachingEnabled      := pointed; *)
(*         resumeFromCache       := pointed; *)
(*         serverCanSendOCSP     := pointed; *)
(*         keyExchangeEPH        := pointed; *)
(*         clientAuthFlag        := pointed; *)
(*       |}; *)
(*   |}. *)
