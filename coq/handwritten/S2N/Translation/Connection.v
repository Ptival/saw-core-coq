From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From S2N Require Import Embedding.
From S2N Require Import Pointed.
From S2N Require Import Translation.Handshake.

From mathcomp Require Import tuple.

Import CryptolPrimitives.

Definition connection : Type
  := (bool (* client_auth_flag *)
      * (seq 2 bool (* corked *)
         * (seq 8 bool (* corked_io *)
            * (handshake
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

Definition get_client_auth_flag (c : connection) : bool :=
  fst c.

Definition get_corked (c : connection) : seq 2 bool :=
  fst (snd c).

Definition get_corked_IO (c : connection) : seq 8 bool :=
  fst (snd (snd c)).

Definition get_handshake (c : connection) : handshake :=
  fst (snd (snd (snd c))).

Definition cork (c : connection) : connection :=
  (fst c, (bvAdd _ (fst (snd c)) (bvNat _ 1), snd (snd c))).
  (* let '(a, (b, (c, (d, (e, (f, (g, h))))))) := c in
  (a, (bvAdd _ b (bvNat _ 1), (c, (d, (e, (f, (g, h))))))) *)

Definition uncork (c : connection) : connection :=
  (fst c, (bvSub _ (fst (snd c)) (bvNat _ 1), snd (snd c))).
  (* let '(a, (b, (c, (d, (e, (f, (g, h))))))) := c in
  (a, (bvSub _ b (bvNat _ 1), (c, (d, (e, (f, (g, h))))))).*)

(* ORDER MATTERS FOR AUTOMATIC LIFTING *)
Record Connection         := MkConnection
{
  clientAuthFlag        : bool;
  corked                : seq 2 bool;
  (* corked                : 2.-tuple bool; *)
  corkedIO              : seq 8 bool;
  (* corkedIO              : 8.-tuple bool; *)
  handshake             : Handshake;
  isCachingEnabled      : bool;
  keyExchangeEPH        : bool;
  mode                  : seq 32 bool;
  (* mode                  : 32.-tuple bool; *)
  resumeFromCache       : bool;
  serverCanSendOCSP     : bool;
}.

Scheme Induction for Connection Sort Prop.
Scheme Induction for Connection Sort Set.
Scheme Induction for Connection Sort Type.

(* Global Instance Embedding_Connection *)
(*   : Embedding connection Connection := *)
(*   {| *)
(*     toAbstract := *)
(*       fun '(a, (b, (c, (d, (e, (f, (g, (h, i)))))))) => *)
(*         {| (* Cryptol sorts the fields *) *)
(*           clientAuthFlag        := toAbstract a; *)
(*           corked                := toAbstract b; *)
(*           corkedIO              := toAbstract c; *)
(*           handshake             := toAbstract d; *)
(*           isCachingEnabled      := toAbstract e; *)
(*           keyExchangeEPH        := toAbstract f; *)
(*           mode                  := toAbstract g; *)
(*           resumeFromCache       := toAbstract h; *)
(*           serverCanSendOCSP     := toAbstract i; *)
(*         |} *)
(*     ; *)
(*     toConcrete := *)
(*       fun c => *)
(*         ( toConcrete (clientAuthFlag c) *)
(*           , ( toConcrete (corked c) *)
(*               , ( toConcrete (corkedIO c) *)
(*                   , ( toConcrete (handshake c) *)
(*                       , ( toConcrete (isCachingEnabled c) *)
(*                           , ( toConcrete (keyExchangeEPH c) *)
(*                               , ( toConcrete (mode c) *)
(*                                   , ( toConcrete (resumeFromCache c) *)
(*                                       , toConcrete (serverCanSendOCSP c *)
(*                                       ) *)
(*                                   ) *)
(*                               ) *)
(*                           ) *)
(*                       ) *)
(*                   ) *)
(*               ) *)
(*           ) *)
(*         ) *)
(*     ; *)
(*   |}. *)

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
