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
From CryptolToCoq Require Import SAWCorePreludeExtra.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From S2N Require Import
     CorrectTranslation
     Embedding
     Handshakes
     Pointed
     S2N
     Translation.Connection
     Translation.Handshake
     Translation.HandshakeAction
.

From mathcomp Require Import eqtype.
From mathcomp Require Import fintype.
From mathcomp Require Import seq.
From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrbool.
From mathcomp Require Import ssrfun.
From mathcomp Require Import ssrnat.
From mathcomp Require Import tuple.

Local Open Scope form_scope.

Import CryptolPrimitives.
Import ListNotations.
Import SAWCorePrelude.SAWCorePrelude.
Import VectorNotations.

Local Open Scope form_scope.

Notation "a || b" := (operations.orB a b).

(** The function [conn_set_handshake_type] as we obtain it after translation is
quite unreadable. *)
(* Print conn_set_handshake_type. *)

(** Reasoning about it would get quite messy.  We can instead "copy" its
original code and adapt it to work with [Connection]. *)
Definition fullHandshake conn :=
  if (isCachingEnabled conn && negb (resumeFromCache conn))%bool
  then # 0
  else seq_to_BITS FULL_HANDSHAKE.

Definition perfectForwardSecrecy conn :=
  if keyExchangeEPH conn
  then seq_to_BITS PERFECT_FORWARD_SECRECY
  else # 0.

Definition ocspStatus conn :=
  if serverCanSendOCSP conn
  then seq_to_BITS OCSP_STATUS
  else # 0.

Definition clientAuth conn :=
  if clientAuthFlag conn
  then seq_to_BITS CLIENT_AUTH
  else # 0.

Definition handshakeType' conn :=
  let fullHandshake := fullHandshake conn in
  seq_to_BITS NEGOTIATED
  || (fullHandshake
     || if ~~ (fullHandshake  == #0)
       then perfectForwardSecrecy conn || ocspStatus conn || clientAuth conn
       else # 0
    ).

Definition connSetHandshakeType (conn : Connection) : Connection :=
  let handshake' :=
      {|
        handshakeType := handshakeType' conn;
        messageNumber := messageNumber (handshake conn);
      |}
  in
  {|
    handshake         := handshake';
    mode              := mode conn;
    corkedIO          := corkedIO conn;
    corked            := corked conn;
    isCachingEnabled  := isCachingEnabled  conn;
    resumeFromCache   := resumeFromCache   conn;
    serverCanSendOCSP := serverCanSendOCSP conn;
    keyExchangeEPH    := keyExchangeEPH    conn;
    clientAuthFlag    := clientAuthFlag    conn;
  |}.

Definition cry_handshakes := handshakes.

Definition stateMachine
  : 17.-tuple HandshakeAction
  :=
    map_tuple toAbstract (seq_to_tuple state_machine).

Definition s2nCork (c : Connection) : 2.-tuple bool
  := incB (corked c).

Definition s2nUncork (c : Connection) : 2.-tuple bool
  := decB (corked c).

Definition ascii_A : 8.-tuple bool := fromNat 65.
Definition ascii_C : 8.-tuple bool := fromNat 67.
Definition ascii_S : 8.-tuple bool := fromNat 83.

Definition S2N_CLIENT : 32.-tuple bool := fromNat 1.

Definition modeWriter (m : 32.-tuple bool) : 8.-tuple bool :=
  if m == S2N_CLIENT
  then ascii_C
  else ascii_S.

Definition advanceMessage_handshake' conn :=
  {|
    handshakeType := handshakeType (handshake conn);
    messageNumber := incB (messageNumber (handshake conn));
  |}.

Definition getHandshake num typ :=
  (nth pointed
       stateMachine
       (toNat
          (nth pointed
               (nth pointed
                    Handshakes.handshakes
                    num
               )
               typ
          )
       )
  ).

Definition advanceMessage_activeState' conn :=
  let handshake' := advanceMessage_handshake' conn in
  getHandshake (toNat (messageNumber handshake'))
               (toNat (handshakeType handshake')).

Definition advanceMessage_previousState' conn :=
  let handshake' := advanceMessage_handshake' conn in
  getHandshake (toNat (messageNumber handshake') - 1)
               (toNat (handshakeType handshake')).

(**
Factoring out the conditions helps in controlling the simplification in proofs.
 *)

Definition advanceMessage_corked'_cond1 conn :=
  let activeState'   := advanceMessage_activeState' conn in
  let previousState' := advanceMessage_previousState' conn in
  (writer activeState' != writer previousState')
  &&
  (writer activeState' != ascii_A).

Definition advanceMessage_corked'_cond2 conn :=
  let activeState'   := advanceMessage_activeState' conn in
  let previousState' := advanceMessage_previousState' conn in
  writer activeState' == modeWriter (mode conn).

Definition advanceMessage_corked' conn :=
  if advanceMessage_corked'_cond1 conn
  then
    if advanceMessage_corked'_cond2 conn
    then s2nCork conn
    else s2nUncork conn
  else corked conn.

Definition advanceMessage (conn : Connection) : Connection :=

  {|
    handshake         := advanceMessage_handshake' conn;
    mode              := mode conn;
    corkedIO          := corkedIO conn;
    corked            := advanceMessage_corked' conn;
    isCachingEnabled  := isCachingEnabled  conn;
    resumeFromCache   := resumeFromCache   conn;
    serverCanSendOCSP := serverCanSendOCSP conn;
    keyExchangeEPH    := keyExchangeEPH    conn;
    clientAuthFlag    := clientAuthFlag    conn;
  |}.

Local Open Scope form_scope.

Lemma gen_getBit_shift
  : forall n h (t : n.-tuple bool),
    gen n bool (fun n => getBit ([ tuple of h :: t ]) n.+1)
    =
    gen n bool (fun n => getBit t n).
Proof.
  elim.
  {
    move => h t.
    rewrite [t] tuple0.
    simpl.
    reflexivity.
  }
  {
    move => n I h.
    case / tupleP => h' t.
    simpl.
    rewrite (I h').
    reflexivity.
  }
Qed.

Lemma gen_getBit
  : forall n s,
    gen n bool (fun i => getBit (n := n) (seq_to_tuple s) i) = s.
Proof.
  simpl.
  apply Vector.t_ind.
  {
    reflexivity.
  }
  {
    move => h n t IH.
    simpl.
    rewrite gen_getBit_shift.
    rewrite IH.
    unfold getBit.
    simpl.
    reflexivity.
  }
Qed.

Lemma toAbstract_gen_getBit
  : forall n v,
    seq_to_tuple (gen n bool (fun i => getBit (n := n) v i)) = v.
Proof.
  elim.
  {
    move => v.
    rewrite [v] tuple0.
    reflexivity.
  }
  {
    move => n I.
    case / tupleP => h t.
    simpl.
    rewrite gen_getBit_shift.
    rewrite I.
    unfold getBit.
    simpl.
    apply val_inj.
    simpl.
    reflexivity.
  }
Qed.

Theorem genOrdinal_toConcrete A B `{Embedding A B} n (f : 'I_n -> B)
  : genOrdinal n A (fun i => toConcrete (f i))
    =
    Vector.map toConcrete (genOrdinal n B f).
Proof.
  move : n f.
  elim => [|n' IH] f.
  {
    reflexivity.
  }
  {
    simpl.
    f_equal.
    rewrite IH.
    reflexivity.
  }
Qed.

Global Instance Proper_Vector_map {A B n} (f : A -> B) :
  Proper (eq ==> eq) (Vector.map (n := n) f).
Proof.
  move => x y XY.
  subst x.
  reflexivity.
Qed.

Global Instance Proper_toConcrete {A B} `{Embedding A B} :
  Proper (eq ==> eq) toConcrete.
Proof.
  move => x y XY.
  subst x.
  reflexivity.
Qed.

Variant ubn_eq_spec m : nat -> Type := UbnEq n of m == n : ubn_eq_spec m n.
Lemma ubnPeq m : ubn_eq_spec m m.      Proof. by []. Qed.

(* Lemma gen_getBit' *)
(*   : forall n v, gen n bool (fun i => getBit (n := n) (toAbstract v) i) = v. *)
(* Proof. *)
(*   simpl. *)
(*   apply Vector.t_ind. *)
(*   { *)
(*     simpl. *)
(*     reflexivity. *)
(*   } *)
(*   { *)
(*     move => h n t IH /=. *)
(*     setoid_rewrite IH. *)
(*     compute. *)
(*     reflexivity. *)
(*   } *)
(* Qed. *)

Theorem unfold_ecOr n a b
  : ecOr (Vec n bool) (PLogicWord n) a b = bvOr n a b.
Proof.
  reflexivity.
Qed.

Theorem ecOr_cons m h1 h2 t1 t2
  : ecOr (Vec m.+1 bool) (PLogicWord m.+1) (h1 :: t1) (h2 :: t2)
    =
    Vector.cons _ (or h1 h2) _ (ecOr (Vec m bool) (PLogicWord m) t1 t2).
Proof.
  by do ! rewrite unfold_ecOr.
Qed.

Theorem seq_to_tuple_ecOr
  : forall {n} a b,
    seq_to_tuple (ecOr (Vec n bool) (PLogicWord n) a b)
    =
    seq_to_tuple a || seq_to_tuple b.
Proof.
  setoid_rewrite unfold_ecOr.
  apply : Vector.t_ind => [|h m t IH b] /=.
  {
    apply case0.
    apply val_inj => //.
  }
  {
    move : m b t IH => /=.
    apply (caseS (fun n v => forall t, _ -> _)) => h' m b t IH /=.
    apply val_inj.
    rewrite IH //.
  }
Qed.

Theorem shiftin_false_zero n
  : shiftin false (bvNat n 0) = bvNat n.+1 0.
Proof.
  reflexivity.
Qed.

Theorem bvNat_S_zero n
  : bvNat n.+1 0 = Vector.append (Vector.cons _ false _ (Vector.nil _)) (bvNat n 0).
Proof.
  simpl.
  induction n.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite IHn.
    unfold joinLSB.
    simpl.
    rewrite shiftin_false_zero.
    simpl.
    now rewrite IHn.
  }
Qed.

Theorem append_assoc :
  forall {T} {sa} (a : Vector.t T sa)
    {sb} (b : Vector.t T sb)
    {sc} (c : Vector.t T sc)
  , existT (fun s => Vector.t T s) _ (Vector.append (Vector.append a b) c)
    =
    existT (fun s => Vector.t T s) _ (Vector.append a (Vector.append b c)).
Proof.
  move => T sa a sb b sc c.
  move : a.
  apply (Vector.t_ind T (fun a sa => _)) with (n := sa).
  {
    simpl.
    reflexivity.
  }
  {
    move => h n t IH.
    simpl.
    dependent rewrite IH.
    reflexivity.
  }
Qed.

Theorem decompose_bvNat_sum
  : forall m n x,
    bvNat (m + n) x
    =
    Vector.append
      (bvNat m (iter n (fun n => n./2) x))
      (bvNat n x).
Proof.
  elim.
  {
    simpl.
    reflexivity.
  }
  {
    move => m' IH n x.
    simpl.
    admit.
  }
Admitted.

Theorem append_bvNat_is_padding' m n x
  : n > Nat.log2 x ->
    Vector.append (bvNat m 0) (bvNat n x) = bvNat (m + n) x.
Proof.
  move : m n x.
  elim.
  {
    reflexivity.
  }
  {
    move => n IH m x L.
    rewrite bvNat_S_zero.
    simpl.
    rewrite (IH _ _ L).
    unfold bvNat.
    (* This is tedious to prove, skipping it since low interest *)
    admit.
  }
Admitted.

Theorem t_for_n_equal_1 v :
  let n := 1 in
  ecPlus (Vec n bool) (PArithSeqBool n) v (ecNumber 1 (Vec n bool) (PLiteralSeqBool n))
  =
  BITS_to_seq (incB (seq_to_BITS v)).
Proof.
  do 2 dependent destruction v.
  move : h.
  elim => /=.
  {
    cbv -[bvAdd].
    rewrite / bvAdd /=.
    rewrite properties.toNat_addB.
    cbv.
    reflexivity.
  }
  {
    cbv -[bvAdd].
    rewrite / bvAdd /=.
    rewrite toNat_addB.
    cbv.
    reflexivity.
  }
Qed.

Theorem half_toNat s (n : BITS s.+1) : (toNat n)./2 = toNat (droplsb n).
Proof.
Admitted.

Theorem tnth_rshift {A n} (t : n.+1.-tuple A) (i : 'I_n)
  : tnth t (rshift 1 i) = tnth (behead_tuple t) i.
Proof.
  elim (tupleP t) => hd tl /=.
  setoid_rewrite (tnth_nth hd) => //.
Qed.

Theorem rev_ord_rshift s n (i : 'I_s) (j : 'I_(n + s))
  : nat_of_ord j = n + nat_of_ord i ->
    rshift n i = j.
Proof.
  move => E.
  apply val_inj => //.
Qed.

(* Theorem fromNat_double n a *)
(*   : @fromNat n.+1 (a.*2) = joinlsb (@fromNat n a, false). *)
(* Proof. *)
(*   move : n a. *)
(*   Set Printing All. *)
(*   elim  *)
(*   rewrite / fromNat. *)
(* Qed. *)

(* Compute *)
(*   let n := 0 in *)
(*   let a := 2 in *)
(*   let b := 0 in *)
(*   b < 2 ^ n -> *)
(*   tval (@fromNat n.+1 (a * 2 ^ n + b)) = tval (joinmsb (odd a, @fromNat n b)). *)

Lemma decompose_fromNat_S n a b
  : b < 2 ^ n ->
    @fromNat n.+1 (a * 2 ^ n + b) = joinmsb (odd a, @fromNat n b).
Proof.
  move => H.
  apply : val_inj.
  move : n a b H.
  elim => [|n IH] a b H.
  {
    rewrite expn0.
    rewrite muln1.
    rewrite tuple0 /=.
    rewrite odd_add.
    move : b H => [|b] //= => _.
    case (odd a) => //.
  }
  {
    rewrite /= - / fromNat.
    f_equal.
    {
      admit.
    }
    {
      rewrite halfD.
      rewrite expnSr.
      (* This is not looking good... *)
      admit.
    }
  }
Admitted.

Theorem fromNat_bvToNat n v
  : fromNat (bvToNat n v) = seq_to_tuple v.
Proof.
  move : n v.
  apply Vector.t_ind => // h n t IH /=.
  rewrite / bvToNatFolder -/ bvToNatFolder.
  rewrite double0.
  rewrite addn0.
  admit.
Admitted.

Theorem bvToBITS_seq_tuple n (a : bitvector n)
  : bvToBITS a = seq_to_tuple a.
Proof.
  move : n a.
  apply Vector.t_ind => // h n t IH /=.
  unfold bvToBITS.
  admit.
Admitted.

Theorem bvAdd_adcB (n : nat) (a b : seq n bool)
  : bvAdd n a b
    =
    BITS_to_seq ((adcB false (seq_to_BITS a) (seq_to_BITS b)).2).
Proof.
Admitted.

Theorem bitvector_to_BITS_bvNat s n
  : seq_to_BITS (bvNat s n) = # n.
Proof.
  move : s n.
  elim => // s IH n.
  rewrite bvNatS.
Admitted.

Theorem ecPlus_1_is_incB n v
  : ecPlus (Vec n bool) (PArithSeqBool n) v (ecNumber 1 (Vec n bool) (PLiteralSeqBool n))
    =
    BITS_to_seq (incB (seq_to_BITS v)).
Proof.
  rewrite ecPlus_is_bvAdd.
  rewrite bvAdd_adcB.
  rewrite [ecNumber _ _ _]/=.
  admit.
Admitted.

Theorem ecMinus_1_is_decB n v
  : ecMinus (Vec n bool) (PArithSeqBool n) v (ecNumber 1 (Vec n bool) (PLiteralSeqBool n))
    =
    BITS_to_seq (decB (seq_to_BITS v)).
Proof.
Admitted.

Definition conn_seq_handshake_type_as_connSetHandshakeType
  : forall c,
    conn_set_handshake_type c =
    toConcrete (connSetHandshakeType (toAbstract c)).
Proof.
  move => [b0[?[?[[??][b1[b2[?[b3 b4]]]]]]]].
  rewrite /conn_set_handshake_type.
  cbv [fst snd Datatypes.fst Datatypes.snd].
  rewrite /connSetHandshakeType.
  rewrite /handshakeType'.
  rewrite /fullHandshake /perfectForwardSecrecy /ocspStatus /clientAuth.
  rewrite /toAbstract /Embedding_Connection.
  simplConnection.
  simplHandshake.
  rewrite /toConcrete.
  rewrite !BITS_to_seq_seq_to_BITS.
  repeat f_equal.
  move : b1 b3 b2 b4 b0 => [] [] [] [] [] //.
Qed.

Lemma s2n_cork_as_s2nCork
  : forall s,
    s2n_cork s = BITS_to_seq (s2nCork (toAbstract s)).
Proof.

Admitted.

Theorem bvAt_nth
        T (t : T) (sn si : nat) n i
  : bvAt sn T si n i = nth t (seq_to_tuple n) (bvToNat _ i).
Proof.

Admitted.

Definition nth_map_tuple
           A B `{Pointed A} `{Pointed B}
           (f : A -> B)
           n (t : n.-tuple A)
  : (map_tuple f t) [n] = f (t [n]).
Proof.
Admitted.

Global Instance Pointed_bitvector
       {n : nat}
  : Pointed (seq n bool)
  :=
    {|
      pointed := bvNat _ 0;
    |}.

Global Instance Pointed_seq
       {n : nat} T `{Pointed T}
  : Pointed (seq n T)
  :=
    {|
      pointed := replicate n T pointed;
    |}.

Theorem stateMachine_indexing n : stateMachine [n] = toAbstract ((seq_to_tuple state_machine) [n]).
Proof.
  pose proof nth_map_tuple.
  (* This is very annoying due to some unification issues. *)
  (* It should hold from `nth_map_tuple`, but it does not. *)
  admit.
Admitted.

Theorem ecAt_as_nth :
  forall T `{Pointed T} (n : nat) (i : nat) (sn : seq n T) (si : seq i bool),
    ecAt n T i sn si
    =
    (seq_to_tuple sn) [bvToNat _ si].
Proof.
  move => *.
  rewrite !ecAt_is_bvAt.
  erewrite !bvAt_nth.
  reflexivity.
Qed.

Theorem as_getHandshake :
  forall a b,
    ecAt Opaque17 (seq Opaque08 Bool * (seq Opaque08 Bool * seq Opaque08 Bool)) Opaque32 state_machine
         (ecAt Opaque32 (seq Opaque32 Bool) Opaque32
               (ecAt Opaque128 (seq Opaque32 (seq Opaque32 Bool)) Opaque32 handshakes a)
               b)
    =
    toConcrete (getHandshake (bvToNat _ b) (bvToNat _ a)).
Proof.
  move => a b.
  rewrite !ecAt_as_nth.
  rewrite /getHandshake.
  rewrite stateMachine_indexing.
  rewrite /Handshakes.handshakes.
Admitted.

Theorem bvToNat_BITS_to_seq
        n (bits : BITS n)
  : bvToNat n (BITS_to_seq bits) = toNat bits.
Proof.

Admitted.

Theorem bvToNat_as_toNat_seq_to_BITS
        n (v : bitvector n)
  : bvToNat n v = toNat (seq_to_BITS v).
Proof.
Admitted.

Theorem bvEq_BITS_to_seq
        n (bits1 bits2 : BITS n)
  : bvEq n (BITS_to_seq bits1) (BITS_to_seq bits2)
    =
    (bits1 == bits2).
Proof.
Admitted.

(** TODO: this will most likely need some underflow logic *)
Theorem toNat_decB
        n (bits : BITS n)
  : toNat (decB bits) = toNat bits - 1.
Proof.
Admitted.

Lemma advance_message_as_advanceMessage
  : forall conn,
    advance_message conn = toConcrete (advanceMessage (toAbstract conn)).
Proof.
  moveConcreteConnection.

  rewrite /advanceMessage.
  rewrite /toConcrete /toAbstract /Embedding_Connection.
  simplConnection.
  simplHandshake.
  rewrite !BITS_to_seq_seq_to_BITS.

  rewrite /advance_message.
  cbv [fst snd Datatypes.fst Datatypes.snd].

  rewrite !as_getHandshake.
  rewrite /toConcrete /Embedding_HandshakeAction.
  rewrite !ecPlus_1_is_incB.
  rewrite !ecMinus_1_is_decB.
  rewrite !ecEq_is_bvEq.
  rewrite !ecNotEq_is_not_bvEq.

  rewrite /advanceMessage_corked'.
  rewrite /advanceMessage_corked'_cond1.
  rewrite /advanceMessage_activeState'.
  rewrite /advanceMessage_previousState'.
  rewrite /advanceMessage_handshake'.
  simplConnection.
  simplHandshake.

  rewrite !bvToNat_BITS_to_seq.
  rewrite !bvEq_BITS_to_seq.
  rewrite !bvToNat_as_toNat_seq_to_BITS.
  rewrite toNat_decB.
  rewrite seq_to_BITS_BITS_to_seq.

  case E1 : (writer _ == writer _).
  => [X Y].
  {
    case W2 : (writer _).
  }
  rewrite !BITS_to_seq_seq_to_BITS.
  repeat f_equal.

  {

    rewrite !ecEq_is_bvEq.
    rewrite !ecNotEq_is_not_bvEq.



    rewrite /advanceMessage_corked'.
    simplConnection.
    simplHandshake.

    case E1 : (ecNotEq _ _ _ _).

    {
      case E1' : (advanceMessage_corked'_cond1 _).

      {
        admit.
      }

      {
        exfalso.
        admit.
      }

    }

    {
      case E1' : (advanceMessage_corked'_cond1 _).

      {
        admit.
      }

      {
        exfalso.
        admit.
      }

    }

    }

  }


      case E2 : (ecNotEq _ _ _ _).

      {
        case E3 : (ecEq _ _ _ _).

        {
          repeat f_equal.

          {
            rewrite /and.
            rewrite s2n_cork_as_s2nCork.
            rewrite /advanceMessage_corked'.
            simplConnection.
            rewrite /s2nCork.
            reflexivity.
            rewrite /s2n_cork.
          }

          rewrite /and.
        }
      }
    }

    repeat f_equal.
    {
      case A : (and _ _).


      rewrite /advanceMessage_corked'
              /advanceMessage_corked'_cond1
              /advanceMessage_corked'_cond2
              /advanceMessage_activeState'
              /advanceMessage_handshake'
      .
      simplConnection.
      simplHandshake.
      simpl
        admit.
    }
    {
      rewrite /advanceMessage_handshake'.
      simplConnection.
      simplHandshake.
      rewrite /toConcrete.
      rewrite BITS_to_seq_seq_to_BITS.
      f_equal.
      rewrite ecPlus_1_is_incB //.
    }
Admitted.

(* The 2-bit vector must always be between 0 and 1.  In other terms, the bit of
order 1 should always remain equal to 0. *)
Definition in_bounds_corked : forall (corked : seq 2 bool), Prop.
  move N : 2 => n v.
  move : n N v.
  case => // n N v.
  move : v N.
  apply (caseS (fun n v => 2 = n.+1 -> _)).
  move : n => _ b1 n1 _ _.
  exact (b1 = false).
Defined.

Definition in_bounds_corked_connection (conn : cry_connection) : Prop :=
  in_bounds_corked (fst (snd conn)).

Definition inBoundsCorked : forall (corked : BITS 2), Prop
  := fun r =>
       let (r, b0) := splitlsb r in
       let (_, b1) := splitlsb r in
       b1 = false.

Class CorrectTranslationProp
      {CI AI}
      `{ProperEmbedding CI AI}
      (concreteProp : CI -> Prop) (abstractProp : AI -> Prop)
  :=
    {
      correctTranslationProp :
        forall ci ai,
          toAbstract ci = ai ->
          concreteProp ci <-> abstractProp ai;
    }.

Global Instance
       CorrectTranslationProp_inBoundsCorked
  : CorrectTranslationProp in_bounds_corked inBoundsCorked.
Proof.
  constructor.
  move => ci ai H.
  apply (f_equal (@toConcrete (seq (TCNum 2) bool) _ _)) in H.
  move : H.
  rewrite roundtrip => ->.
  constructor.
  {
    destruct ai => //=.
    rewrite / tnth /=.
    destruct tval => //=.
    destruct tval => //=.
  }
  {
    move : ai => [] [|b0] // [|b1] //.
  }
Qed.

Definition inBoundsCorkedConnection (conn : Connection) : Prop :=
  inBoundsCorked (corked conn).

Theorem noDoubleCorkUncork_connSetHandshakeType
  : forall conn,
    inBoundsCorkedConnection conn ->
    inBoundsCorkedConnection (connSetHandshakeType conn).
Proof.
  move => conn IB.
  unfold connSetHandshakeType.
  rewrite / inBoundsCorkedConnection.
  simpl.
  apply IB.
Qed.

Definition UNCORKED : 2.-tuple bool := [tuple false; false].
Definition   CORKED : 2.-tuple bool := [tuple true;  false].

(*
It helps to separate this from the whole invariant, so that the part of the
proofs about [CorkedInvariant] can ignore all the other fields in [Connection].
It also helps to delay the index as an equation, as as to be able to use
[val_inj].
 *)
Inductive CorkedInvariant : 2.-tuple bool -> Prop :=
| Corked   : forall c, c =   CORKED -> CorkedInvariant c
| Uncorked : forall c, c = UNCORKED -> CorkedInvariant c
.

Inductive ConnectionInvariant : Connection -> Prop :=
| MkConnectionInvariant :
    forall conn,
      CorkedInvariant (corked conn) ->
      ConnectionInvariant conn
.

Theorem initial_connection_satisfies_Invariant
  : forall conn,
    initial_connection conn = true ->
    ConnectionInvariant (toAbstract conn).
Proof.
  move => [a [corked b]].
  move : corked.
  elim /elimVector2 => c1 c2.
  move : b => [?[[??][?[?[?[??]]]]]] /=.
  repeat rewrite map_tuple_id.
  rewrite /initial_connection /=.
  rewrite /joinLSB /shiftin.
  setoid_rewrite ecEq_is_bvEq.
  case : (bvEq _ _ _) => //.
  case : (bvEq _ _ _) => //.
  case C : (bvEq _ _ _) => //.
  {
    move => _.
    constructor => /=.
    apply Uncorked.
    move : C.
    move /bvEq_eq => [] -> -> /=.
    apply val_inj => //.
  }
  {
    rewrite /=.
    move /bvEq_eq => [] -> -> .
    constructor => /=.
    apply Corked.
    apply val_inj => //.
  }
Qed.

Definition activeMessage (c : Connection)
  : 32.-tuple bool
  :=
    let handshake := handshake c in
    nth pointed (nth pointed handshakes (toNat (handshakeType handshake)))
        (toNat (messageNumber handshake)).

Definition clientHello : 32.-tuple bool
  := fromNat (intToNat (CLIENT_HELLO _ PLiteralInteger)).

Definition serverHello : 32.-tuple bool
  := fromNat (intToNat (SERVER_HELLO _ PLiteralInteger)).

Definition s2nTransConnection_cond (c : Connection)
  : bool
  := (activeMessage c == clientHello)
     ||
     (activeMessage c == serverHello).

Definition s2nTransConnection (c : Connection)
  : Connection
  :=
    advanceMessage (
        if s2nTransConnection_cond c
        then connSetHandshakeType c
        else c
      ).


Lemma s2nTrans_as_s2nTransConnection
  : forall c,
    s2nTrans c = toConcrete (s2nTransConnection (toAbstract c)).
Proof.
  move => conn.
  rewrite /s2nTrans /s2nTransConnection.
  case O : (boolOr _ _).
  {
    case C : (s2nTransConnection_cond _).
    {
      admit.
    }
    {
      rewrite /=.
      exfalso.
      move : O.
      rewrite /boolOr.
      case E : (ecEq _ _ _).
      {
        move => _.
        move : E.
        rewrite /ACTIVE_MESSAGE.
        rewrite /fst /snd.
        rewrite /Datatypes.fst /Datatypes.snd.
        rewrite /ecAt /Num_rect.
        rewrite /bvAt /sawAt.
      }

      case : O.
      move : O C.
      rewrite /s2nTransConnection_cond.
      rewrite /=.
      (* TODO: show contradiction *)
    }
    rewrite !byCorrectTranslation.
    rewrite roundtrip'.
    rewrite /advanceMessage.
    rewrite /connSetHandshakeType.
    rewrite {1}/toConcrete /Embedding_Connection.
    simplConnection.
    rewrite /handshakeType'.
    simplConnection.
  }




Qed.

Theorem connSetHandshakeType_preserves_Invariant
  : forall (conn : Connection),
    ConnectionInvariant conn ->
    ConnectionInvariant (connSetHandshakeType conn).
Proof.
  move => conn [] //.
Qed.

Theorem s2nTrans_preserves_Invariant
  : forall (conn : cry_connection),
    ConnectionInvariant (toAbstract conn) ->
    ConnectionInvariant (toAbstract (s2nTrans conn)).
Proof.
  move => conn I.
  rewrite byCorrectTranslation.
  rewrite roundtrip'.
  rewrite /s2nTransConnection.
  case C : (s2nTransConnection_cond _) => //.
  apply connSetHandshakeType_preserves_Invariant => //.
Qed.

(**
We will later show that [s2nCork] is only called when [corked] is [00].
 *)
Theorem noDoubleCorkUncork_s2nCork
  : forall conn,
    corked conn = [tuple false; false] ->
    inBoundsCorked (s2nCork conn).
Proof.
  move => [[handshakeType messageNumber]?? corked ?????].
  move : corked => [] [|[]] // [|[]] // [] // I _.
Qed.

(**
We will later show that [s2nUncork] is only called when [corked] is [10].
 *)
Theorem noDoubleCorkUncork_s2nUncork
  : forall conn,
    corked conn = [tuple true; false] ->
    inBoundsCorked (s2nUncork conn).
Proof.
  move => [[handshakeType messageNumber]?? corked ?????].
  move : corked => [] [|[]] // [|[]] // [] // I _.
Qed.

Theorem noDoubleCorkUncork_advanceMessage
  : forall conn,
    ConnectionInvariant conn ->
    inBoundsCorkedConnection conn ->
    inBoundsCorkedConnection (advanceMessage conn).
Proof.
  move => [[handshakeType messageNumber]?? corked ?????].
  (* let's break down [corked], bit 1 must be [false] *)
  move : corked => [] [|c0] // [|[]] // [] // ? INV I.
  rewrite /inBoundsCorkedConnection.
  rewrite /advanceMessage.
  simplConnection.
  rewrite /advanceMessage_corked'.
  case C1 : (advanceMessage_corked'_cond1 _) => //.
  case C2 : (advanceMessage_corked'_cond2 _).
  {
    apply noDoubleCorkUncork_s2nCork => //.
    rewrite /corked.
    move : C1 C2.
    rewrite /advanceMessage_corked'_cond1.
    admit.

  }
  {
    apply noDoubleCorkUncork_s2nUncork => //.
    admit.
  }
Admitted.

Theorem corked_expansion
  : forall (conn : Connection),
    bitvector_to_BITS (fst (snd (toConcrete conn))) = corked conn.
Proof.
  apply : elimConnection => ? ? ? ? [] [] // ? [] // ? [] // ? ? ? ? ? ?.
  apply val_inj => //=.
Qed.

Theorem noDoubleCorkUncork
  : forall conn,
    in_bounds_corked_connection conn ->
    in_bounds_corked_connection (s2nTrans conn).
Proof.
  apply : elim_connection => ??????????.
  rewrite / in_bounds_corked_connection.
  setoid_rewrite correctTranslationProp => //.
  rewrite [s2nTrans]lock /= -lock.
  setoid_rewrite map_tuple_id => IB.
  rewrite / s2nTrans.

  rewrite byCorrectTranslation.
  rewrite byCorrectTranslation.
  rewrite corked_expansion.
  apply noDoubleCorkUncork_advanceMessage.
  apply noDoubleCorkUncork_connSetHandshakeType.
  rewrite /inBoundsCorkedConnection.

  destruct boolOr eqn:D1.
  {
    rewrite roundtrip'.
    apply noDoubleCorkUncork_connSetHandshakeType.
    rewrite /inBoundsCorkedConnection.
    rewrite [toAbstract _]/=.
    simplConnection.
    rewrite map_tuple_id //.
  }
  {
    rewrite /inBoundsCorkedConnection.
    rewrite [toAbstract _]/=.
    simplConnection.
    rewrite map_tuple_id //.
  }
Qed.
