From Bits Require Import operations.
From Bits Require Import operations.properties.
From Bits Require Import spec.

From Coq Require Import Lists.List.
From Coq Require Import Morphisms.
From Coq Require Import String.
From Coq Require Import Program.Equality.
From Coq Require Import Vector.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From S2N Require Import Embedding.
From S2N Require Import Pointed.
From S2N Require Import S2N.
From S2N Require Import Translation.Connection.
From S2N Require Import Translation.Handshake.
From S2N Require Import Translation.HandshakeAction.

From mathcomp Require Import eqtype.
From mathcomp Require Import fintype.
From mathcomp Require Import seq.
From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrbool.
From mathcomp Require Import ssrfun.
From mathcomp Require Import ssrnat.
From mathcomp Require Import tuple.

Import CryptolPrimitives.
Import ListNotations.
Import SAWCorePrelude.SAWCorePrelude.
Import VectorNotations.

(**
The [handshakes] data type requires a lot of care.
 *)

Notation "array '[' index ']'" := (nth pointed array index) (at level 10).

Notation "a '||' b" := (ecOr _ (PLogicSeqBool 32) a b).

(*
coerce (seq (tcAdd 1 (tcSub 127 0)) (seq 32 (seq 32 Bool)))
  (seq 128 (seq 32 (seq 32 Bool)))
  (seq_cong1 (tcAdd 1 (tcSub 127 0)) 128 (seq 32 (seq 32 Bool))
     (identity_refl 128))
  (seqMap (seq 32 Bool) (seq 32 (seq 32 Bool))
     (tcAdd 1 (tcSub 127 0)) (fun h : seq 32 Bool => handshakes_fn h)
     (ecFromTo 0 127 (seq 32 Bool) (PLiteralSeqBool 32)))
     : seq 128 (seq 32 (seq 32 Bool))
*)

Theorem map_tuple_seq_to_tuple
  : forall A B n (f : A -> B) s,
    map_tuple (n := n) f (seq_to_tuple s)
    =
    seq_to_tuple (map A B f n s).
Proof.
Admitted.

Theorem map_map
  : forall A B C n (f : A -> B) (g : B -> C) s,
    (map B C g n (map A B f n s)) = map A C (compose A B C g f) n s.
Proof.
Admitted.

Theorem nth_seq_to_tuple
  : forall A def n (s : Vector.t A n) ix (IX : (ix < n)%coq_nat),
    nth def (seq_to_tuple s) ix = VectorDef.nth_order s IX.
Proof.
Admitted.

Theorem gen_f_sawAt
        A B n (fn : A -> B) v
  : gen n B (fun i => fn (sawAt n A v i))
    =
    map A B fn n (gen n A (fun i => sawAt n _ v i)).
Proof.
Admitted.

Theorem map_gen
        A B (f : A -> B) (g : nat -> A) n
  : map A B f n (gen n A g) = gen n B (compose nat A B f g).
Proof.
Admitted.

(* Global Instance Embedding_refl A : Embedding A A. *)
(* constructor. *)
(* exact (fun x => x). *)
(* exact (fun x => x). *)
(* Defined. *)

Theorem nth_seq_to_tuple_gen
        (A : Type) (m n : nat) (f : nat -> m.-tuple A) (ix : nat)
        `{Pointed (m.-tuple A)}
  : (seq_to_tuple (gen n (m.-tuple A) f)) [ix]
    =
    f ix.
Proof.
Admitted.

(* Theorem nth_of_fn *)
(*   : forall (fn : seq 32 bool -> seq 32 (seq 32 bool)) v index, *)
(*     (map_tuple *)
(*        _ *)
(*        (seq_to_tuple ( *)
(*             coerce (seq (tcAdd 1 (tcSub 127 0)) (seq 32 (seq 32 Bool))) *)
(*                    (seq 128 (seq 32 (seq 32 Bool))) *)
(*                    (seq_cong1 (tcAdd 1 (tcSub 127 0)) 128 (seq 32 (seq 32 Bool)) *)
(*                               (identity_refl (TCNum 128))) *)
(*                    (seqMap _ _ _ fn (ecFromTo 0 127 _ v)) *)
(*           ) : 128.-tuple (32.-tuple (32.-tuple bool)))) [ index ] *)
(*     = *)
(*     (_ (fn (v index)) : 32.-tuple (32.-tuple bool)). *)
(* Proof. *)
(*   move => fn v ix. *)
(*   rewrite /toAbstract /Embedding_seq_tuple. *)
(*   rewrite /coerce /seq_cong1 /eq_cong /Eq__rec /identity_rect /Refl. *)
(*   rewrite /ecFromTo /finNumRec. *)
(*   rewrite /seqMap /Num_rect. *)
(*   rewrite /tcAdd /tcSub /binaryNumFun /Num_rect. *)
(*   rewrite map_tuple_seq_to_tuple. *)
(*   rewrite map_map. *)
(*   rewrite map_gen. *)
(*   rewrite nth_seq_to_tuple_gen. *)
(*   rewrite /compose. *)
(*   rewrite eqNatAdd0. *)
(*   rewrite map_tuple_seq_to_tuple. *)
(*   rewrite {1}/toAbstract. *)
(*   rewrite map_tuple_seq_to_tuple //. *)
(* Qed. *)

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (a : A)
  := g (f a).

Definition handshakes : 128.-tuple (32.-tuple (32.-tuple bool))
  := map_tuple
       (compose (map_tuple seq_to_BITS) seq_to_tuple)
       (seq_to_tuple S2N.handshakes).

(* Theorem genOrdinal_tnth *)
(*         (A : Type) (n : nat) (t : n.-tuple A) *)
(*         `{Embedding A A} *)
(*   : genOrdinal n A (fun q : 'I_n => tnth t q) *)
(*     = *)
(*     (tuple_to_seq t : seq n A). *)
(* Proof. *)
(* Admitted. *)

(* This is probably wrong, might need to [rev] the RHS *)
(* Theorem genOrdinal_tnth_rev_ord *)
(*         (A : Type) (n : nat) (t : n.-tuple A) *)
(*         `{Embedding A A} *)
(*   : genOrdinal n A (fun q : 'I_n => tnth t (rev_ord q)) *)
(*     = *)
(*     toConcrete t. *)
(* Proof. *)
(* Admitted. *)

Theorem handshakesIndexing
  : forall (index : 32.-tuple bool),
    handshakes [ toNat index ]
    =
    map_tuple seq_to_BITS (seq_to_tuple (handshakes_fn (BITS_to_seq index))).
Proof.
  move => ?.
  rewrite /handshakes.
  rewrite /S2N.handshakes.
  rewrite /coerce /seq_cong1 /eq_cong /Eq__rec /identity_rect /Refl.
  rewrite /ecFromTo /finNumRec.
  rewrite /seqMap /Num_rect.
  rewrite /tcAdd /tcSub /binaryNumFun /Num_rect.
  rewrite map_tuple_seq_to_tuple.
  rewrite map_map.
  rewrite map_gen.
  rewrite nth_seq_to_tuple_gen.
  rewrite /CryptolPrimitives.compose.
  rewrite eqNatAdd0.
  rewrite map_tuple_seq_to_tuple.
  rewrite /compose.
  rewrite map_tuple_seq_to_tuple.
  rewrite /PLiteralSeqBool /Num_rect.
  rewrite bvNat_toNat //.
Qed.

Theorem ecPlus_is_bvAdd n a b
  : ecPlus (Vec n bool) (PArithSeqBool n) a b = bvAdd n a b.
Proof.
  reflexivity.
Qed.

Theorem ecEq_is_bvEq n a b
  : ecEq (seq (TCNum n) Bool) (PCmpSeqBool n) a b = bvEq n a b.
Proof.
  reflexivity.
Qed.

Theorem ecNotEq_is_not_bvEq n a b
  : ecNotEq (seq (TCNum n) Bool) (PCmpSeqBool n) a b = ~~ (bvEq n a b).
Proof.
  reflexivity.
Qed.

Theorem ecAt_is_bvAt T (n i : nat) a b
  : ecAt n T i a b = bvAt n _ i a b.
Proof.
  reflexivity.
Qed.

Theorem addNat_is_nat_rect_S a b
  : addNat a b = nat_rect _ b (fun _ => [eta S]) a.
Proof.
  reflexivity.
Qed.

(*
Goal forall P, P (handshakes_fn S2N.INITIAL).
Proof.
  move => P.
  rewrite / handshakes_fn.
  match goal with
  | [ |- context [if ?a then _ else _] ] => case A : a
  end.
  admit.
  exfalso.
  move : A.
  rewrite unfold_ecEq.
  rewrite /INITIAL /coerce /seq_cong1 /eq_cong / Eq__rec /identity_rect /Refl.
  rewrite /PLiteralSeqBool /Num_rect.
  rewrite [ecNumber _ _ _]/=.
  rewrite /joinLSB /shiftin.
  rewrite [ecZero _ _]/=.
  rewrite /joinLSB /shiftin.
  rewrite /ecZero.
  rewrite /ecCat.
  rewrite [finNumRec _ _ _]/=.
Qed.

Inductive Handshakes : seq 32 bool -> seq 32 (seq 32 bool) -> Prop :=

| H0 :
    Handshakes
      S2N.INITIAL
      (coerce (seq (tcAdd 3 29) (seq 32 Bool)) (seq 32 (seq 32 Bool))
              (seq_cong1 (tcAdd 3 29) 32 (seq 32 Bool) (identity_refl (TCNum 32)))
              (ecCat 3 29 (seq 32 Bool)
                     [CLIENT_HELLO (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_SESSION_LOOKUP (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_HELLO (seq 32 Bool) (PLiteralSeqBool 32)]
                     (ecZero (seq 29 (seq 32 Bool))
                             (PZeroSeq 29 (seq 32 Bool) (PZeroSeqBool 32)))))

| H1 :
    Handshakes
      S2N.NEGOTIATED
      (coerce (seq (tcAdd 08 24) (seq 32 Bool))
              (seq 32 (seq 32 Bool))
              (seq_cong1 (tcAdd 08 24) 32 (seq 32 Bool)
                         (identity_refl (TCNum 32)))
              (ecCat 08 24 (seq 32 Bool)
                     [CLIENT_HELLO (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_SESSION_LOOKUP (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_HELLO (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_CHANGE_CIPHER_SPEC (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_FINISHED (seq 32 Bool) (PLiteralSeqBool 32);
                     CLIENT_CHANGE_CIPHER_SPEC (seq 32 Bool) (PLiteralSeqBool 32);
                     CLIENT_FINISHED (seq 32 Bool) (PLiteralSeqBool 32);
                     APPLICATION_DATA (seq 32 Bool) (PLiteralSeqBool 32)]
                     (ecZero (seq 24 (seq 32 Bool))
                             (PZeroSeq 24 (seq 32 Bool) (PZeroSeqBool 32)))))

| H2 :
    Handshakes
      (ecOr (seq 32 Bool) (PLogicSeqBool 32) NEGOTIATED WITH_SESSION_TICKET)
      (coerce (seq (tcAdd 9 23) (seq 32 Bool)) (seq 32 (seq 32 Bool))
              (seq_cong1 (tcAdd 9 23) 32 (seq 32 Bool) (identity_refl (TCNum 32)))
              (ecCat 9 23 (seq 32 Bool)
                     [CLIENT_HELLO (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_SESSION_LOOKUP (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_HELLO (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_NEW_SESSION_TICKET (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_CHANGE_CIPHER_SPEC (seq 32 Bool) (PLiteralSeqBool 32);
                     SERVER_FINISHED (seq 32 Bool) (PLiteralSeqBool 32);
                     CLIENT_CHANGE_CIPHER_SPEC (seq 32 Bool) (PLiteralSeqBool 32);
                     CLIENT_FINISHED (seq 32 Bool) (PLiteralSeqBool 32);
                     APPLICATION_DATA (seq 32 Bool) (PLiteralSeqBool 32)]
                     (ecZero (seq 23 (seq 32 Bool))
                             (PZeroSeq 23 (seq 32 Bool) (PZeroSeqBool 32)))))
.

Theorem ecEq32IsEq : forall a b, ecEq _ (PCmpSeqBool 32) a b -> a = b.
Proof.
Admitted.

Definition HandshakesInversion
           (P : seq 32 (seq 32 bool) -> Prop)
  : forall (IH : forall index output,
          Handshakes index output ->
          P (handshakes_fn index)
      ),
    forall index, P (handshakes_fn index).
Proof.
  move => IH index.
  apply (IH index (handshakes_fn index)).
  rewrite /handshakes_fn.

  case E0 : (ecEq _ _ _ _).
  {
    have := (ecEq32IsEq _ _ E0) => ->.
    apply H0.
  }
  {

    case E1 : (ecEq _ _ _ _).
    {
      have := (ecEq32IsEq _ _ E1) => ->.
      apply H1.
    }
    {

      case E2 : (ecEq _ _ _ _).
      {
        have := (ecEq32IsEq _ _ E2) => ->.
        apply H2.
      }
      {
Admitted.

Inductive handshakesIndicesI : nat -> Prop :=
| HSI0 : handshakesIndicesI (toNat (toAbstract S2N.INITIAL))
| HSI1 : handshakesIndicesI (toNat (toAbstract S2N.NEGOTIATED))
| HSI2 : handshakesIndicesI (toNat (toAbstract (S2N.NEGOTIATED || S2N.WITH_SESSION_TICKET)))
| HSI3 : handshakesIndicesI (toNat (toAbstract (S2N.NEGOTIATED || S2N.FULL_HANDSHAKE)))
| HSI4 : handshakesIndicesI (toNat (toAbstract (S2N.NEGOTIATED || S2N.FULL_HANDSHAKE || S2N.WITH_SESSION_TICKET)))
| HSI5 : handshakesIndicesI (toNat (toAbstract (S2N.NEGOTIATED || S2N.FULL_HANDSHAKE || S2N.PERFECT_FORWARD_SECRECY)))
.
*)
