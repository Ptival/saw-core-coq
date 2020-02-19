From Bits Require Import operations.
From Bits Require Import spec.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Program.Equality.
From Coq Require Import Vector.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From S2N Require Import S2N.

From mathcomp Require Import eqtype.
From mathcomp Require Import fintype.
From mathcomp Require Import seq.
From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrbool.
From mathcomp Require Import ssrnat.
From mathcomp Require Import tuple.

Import CryptolPrimitives.
Import ListNotations.
Import SAWCorePrelude.
Import VectorNotations.

Class Embedding A B :=
  {
    toAbstract : A -> B;
    toConcrete : B -> A;
  }.

(**
Keeping [ProperEmbedding] separate allows computations that depend on
[Embedding] to go through even when we admit the proof of [ProperEmbedding].
 *)
Class ProperEmbedding {A B} `(Embedding A B) :=
  {
    roundtrip : forall a, toConcrete (toAbstract a) = a;
  }.

Class Isomorphism {A B} `(E : Embedding A B) `{! ProperEmbedding E} :=
  {
    roundtrip' : forall c, toAbstract (toConcrete c) = c;
  }.

Fixpoint seq_to_tuple {T} {n : nat} (s : seq n T) : n.-tuple T :=
  match s with
  | nil => [tuple]
  | cons h _ t => cat_tuple [tuple of [:: h]] (seq_to_tuple t)
  end.

Theorem fromNat_bvToNat s v
  : fromNat (bvToNat s v) = rev_tuple (seq_to_tuple v).
Proof.
  apply val_inj.
  move : s v.
  elim.
  {
    elim /(@Vector.case0 bool) => //.
  }
  {
    move => s IH v.
    move : v IH.
    elim /@Vector.caseS => h s' t IH.
    move : IH (IH t) => _.
    rewrite [val (rev_tuple _)]/=.
    rewrite [val (rev_tuple _)]/=.
    rewrite rev_cons => <- .
    rewrite bvToNat_S.
    rewrite /hd /tl /caseS.
    admit.
    (*
This is a bit of a pain to prove but should hold:
- [h] is the bit of order s.+1, so it goes last
- [bvToNat s' t] is [s'] bits so does not interfere
     *)
  }
Admitted.

(* Global Instance Embedding_seq_tuple A B (n : nat) `{Embedding A B} *)
(*   : Embedding (seq n A) (n.-tuple B) := *)
(*   {| *)
(*     toAbstract c := map_tuple toAbstract (seq_to_tuple c); *)
(*     toConcrete b := genOrdinal _ _ (fun i => toConcrete (tnth b i)); *)
(*   |}. *)

(**
NOTE: while this is equivalent to [bvToBITS], it has different computational
behaviour, that makes it easier to handle for certain proofs.
 *)
Fixpoint seq_to_BITS {s : nat} (v : seq s bool) : BITS s :=
  match v in Vector.t _ s' return s'.-tuple _ with
  | nil => [tuple]
  | cons h _ t => rcons_tuple (seq_to_BITS t) h
  end.

Definition BITS_to_seq {s : nat} (b : BITS s)
  : seq s bool
  := genOrdinal _ _ (fun i => tnth b (rev_ord i)).

Theorem BITS_to_seq_seq_to_BITS
  : forall s (v : bitvector s),
    BITS_to_seq (seq_to_BITS v) = v.
Proof.

Admitted.

Theorem seq_to_BITS_BITS_to_seq
  : forall s (t : s.-tuple bool),
    seq_to_BITS (BITS_to_seq t) = t.
Proof.

Admitted.

Theorem BITS_to_seq_is_bvNat_toNat
  : forall s (v : BITS s),
    BITS_to_seq v = bvNat s (toNat v).
Proof.

Admitted.

Theorem seq_to_BITS_seq_to_tuple
  : forall s (v : bitvector s),
    seq_to_BITS v = rev_tuple (seq_to_tuple v).
Proof.

Admitted.

Theorem seq_to_BITS_is_bvToBITS (s : nat) (v : seq s bool)
  : seq_to_BITS v = bvToBITS v.
Proof.
  move : s v.
  elim.
  {
    elim /(@Vector.case0 bool) => //.
  }
  {
    move => s IH v.
    move : v IH.
    elim /@Vector.caseS => h s' t IH /=.
    apply val_inj.
    rewrite /bvToBITS.
    rewrite IH.
    rewrite fromNat_bvToNat /=.
    rewrite rev_cons //.
    f_equal.
    rewrite /bvToBITS.
    rewrite fromNat_bvToNat //.
  }
Qed.

(* NOTE this is risky, Embedding_seq_tuple and Embedding_bitvector_BITS are
overlapping and not compatible.
 *)
(* Global Instance Embedding_bitvector_BITS (n : nat) *)
(*   : Embedding (bitvector n) (BITS n) := *)
(*   {| *)
(*     toAbstract c := map_tuple toAbstract (bitvector_to_BITS c); *)
(*     toConcrete b := genOrdinal _ _ (fun i => toConcrete (tnth b (rev_ord i))); *)
(*   |}. *)

Theorem tnth_rshift {A n} (h : A) (t : n.-tuple A) (i : 'I_n)
  : tnth (cat_tuple [tuple h] t) (rshift 1 i) = tnth t i.
Proof.
  setoid_rewrite (tnth_nth h).
  simpl.
  reflexivity.
Qed.

Lemma genOrdinal_tnth_seq_to_tuple
  : forall (A : Type) (n : nat) (t : t A n),
    genOrdinal n A (fun q : 'I_n => tnth (seq_to_tuple t) q) = t.
Proof.
  move => A.
  apply Vector.t_ind => [|h n t IH].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    f_equal.
    setoid_rewrite tnth_rshift.
    assumption.
  }
Qed.

(* Global Instance ProperEmbedding_seq_tuple A B n `{ProperEmbedding A B} *)
(*        : ProperEmbedding (Embedding_seq_tuple A B n). *)
(* Proof. *)
(*   apply Build_ProperEmbedding. *)
(*   move : n. *)
(*   apply Vector.t_ind. *)
(*   { *)
(*     reflexivity. *)
(*   } *)
(*   { *)
(*     move => h n t IH. *)
(*     simpl. *)
(*     f_equal. *)
(*     { *)
(*       apply roundtrip. *)
(*     } *)
(*     { *)
(*       setoid_rewrite tnth_map. *)
(*       setoid_rewrite roundtrip. *)
(*       setoid_rewrite tnth_rshift. *)
(*       apply genOrdinal_tnth_seq_to_tuple. *)
(*     } *)
(*   } *)
(* Qed. *)

Theorem map_tuple_seq_to_tuple
  : forall A B n (f : A -> B) s,
    map_tuple (n := n) f (seq_to_tuple s)
    =
    seq_to_tuple (map A B f n s).
Proof.
Admitted.

Theorem seq_to_tuple_cons T n h (t : Vector.t T n)
  : seq_to_tuple (h :: t) = [tuple of h :: (seq_to_tuple t)].
Proof.
Admitted.

Theorem map_tuple_cons A B (f : A -> B) n h (t : n.-tuple A)
  : map_tuple f [tuple of h :: t] = [tuple of f h :: (map_tuple f t)].
Proof.
Admitted.

(**
While this holds definitionally, it helps to have it as a means of unfolding
just enough.
 *)
Theorem genOrdinal_S A s f
  : genOrdinal s.+1 A f
    =
    (f (Ordinal (ltn0Sn s))) :: genOrdinal s A (fun i => f (rshift 1 i)).
Proof.
  rewrite //.
Qed.

From Coq Require Import Morphisms.

Global Instance Proper_genOrdinal n a :
    Proper (@pointwise_relation _ _ eq ==> eq) (@genOrdinal n a).
Proof.
Admitted.

Theorem tnth_rshift' {A n} (t : (n.+1).-tuple A) (i : 'I_n)
  : tnth t (rshift 1 i) = tnth [tuple of behead t] i.
Proof.
  move : t => [] [] //= h.
  setoid_rewrite (tnth_nth h) => //.
Qed.

(* Global Instance Isomorphism_seq_tuple A B n `{Isomorphism A B} *)
(*   : Isomorphism (Embedding_seq_tuple A B n). *)
(* Proof. *)
(*   constructor. *)
(*   elim : n. *)
(*   { *)
(*     move => [] [] //= ?. *)
(*     apply val_inj => //. *)
(*   } *)
(*   { *)
(*     move => n IH t. *)
(*     rewrite /toAbstract /toConcrete /Embedding_seq_tuple. *)
(*     rewrite genOrdinal_S. *)
(*     rewrite seq_to_tuple_cons. *)
(*     rewrite map_tuple_cons. *)
(*     move : t IH (IH [tuple of behead t]) => [] [] // h t ? _ IH. *)
(*     apply val_inj => /=. *)
(*     rewrite roundtrip'. *)
(*     f_equal. *)
(*     (* huh this is annoying... *) *)
(*     admit. *)
(*   } *)
(* Admitted. *)

Theorem map_tuple_id {A n} (t : n.-tuple A) : map_tuple Datatypes.id t = t.
Proof.
  apply val_inj.
  move : n t.
  elim => [|n IH].
  {
    move => t.
    rewrite [t] tuple0.
    reflexivity.
  }
  {
    case / tupleP => h t.
    simpl.
    f_equal.
    apply IH.
  }
Qed.

Theorem tnth_cons_tuple_ord0 {T n} h (t : n.-tuple T)
  : tnth [tuple of h :: t] ord0 = h.
Proof.
  reflexivity.
Qed.

Theorem decompose_rcons_tuple {T n} h (t : n.-tuple T) l
  : rcons_tuple [tuple of h :: t] l = [tuple of h :: rcons_tuple t l].
Proof.
  apply val_inj => /=.
  reflexivity.
Qed.

Theorem nth_rcons_tuple_last {T n} def (tuple : n.-tuple T) last
  : nth def (rcons_tuple tuple last) n = last.
Proof.
  rewrite nth_rcons.
  rewrite size_tuple.
  rewrite ltnn.
  rewrite eqxx.
  reflexivity.
Qed.

Theorem tnth_rcons_tuple_rev_ord0 {T n} (tuple : n.-tuple T) last
  : tnth (rcons_tuple tuple last) (rev_ord ord0) = last.
Proof.
  rewrite / tnth /=.
  rewrite subSS.
  rewrite subn0.
  rewrite nth_rcons_tuple_last.
  reflexivity.
Qed.

Lemma nth_cons
      (T : Type) (n : nat) (last : T) (i : nat) (def1 def2 hd : T) (tl : n.-tuple T)
  : i < size tl ->
    nth def1 (hd :: tl) i.+1 = nth def2 tl i.
Proof.
  move => I /=.
  by apply set_nth_default.
Qed.

Theorem ltsubn n i
  : 0 < i <= n -> n - i < n.
Proof.
  move => /andP [? ?].
  rewrite <- subn_gt0.
  rewrite subKn //.
Qed.

(* This comes up a lot... *)
Theorem ord_lt_le n (i : 'I_n)
  : 0 < i ->
    0 < i <= n.
Proof.
  move : i => [i I] /= A.
  rewrite A /=.
  by apply ltnW.
Qed.

Lemma nth_rcons_tuple_nat
      (T : Type) (n : nat) (tuple : n.-tuple T) (last : T) (i : nat) def1 def2
  : 0 < i <= n ->
    nth def1 (rcons_tuple tuple last) (n - i)
    =
    nth def2 tuple (n - i).
Proof.
  move => I.
  rewrite nth_rcons.
  rewrite size_tuple.
  rewrite ltsubn //.
  apply set_nth_default.
  rewrite size_tuple.
  rewrite ltsubn //.
Qed.

Lemma nth_rcons_tuple_ord
      (T : Type) (n : nat) (tuple : n.-tuple T) (last : T) (i : 'I_n) def1 def2
  : 0 < i ->
    nth def1 (rcons_tuple tuple last) (n - i)
    =
    nth def2 tuple (n - i).
Proof.
  move => I.
  erewrite nth_rcons_tuple_nat.
  {
    reflexivity.
  }
  {
    by apply ord_lt_le.
  }
Qed.

Lemma nth_rev_tuple
      (T : Type) (n : nat) (tuple : n.-tuple T) (i : 'I_n) def1 def2
  : nth def1 (rev_tuple tuple) i
    =
    nth def2 tuple (n - i.+1).
Proof.
  rewrite nth_rev size_tuple //.
  apply set_nth_default.
  rewrite size_tuple.
  apply rev_ord_proof.
Qed.

Theorem tnth_rcons_tuple_rev_ord_rshift {T n} (tuple : n.-tuple T) last i
  : tnth (rcons_tuple tuple last) (rev_ord (rshift 1 i)) = tnth (rev_tuple tuple) i.
Proof.
  rewrite / tnth.
  rewrite (lock rcons_tuple) (lock rev_tuple) /=.
  unlock.
  rewrite subSS.
  erewrite nth_rcons_tuple_nat with (def2 := last) => //=.
  setoid_rewrite nth_rev_tuple => //=.
Qed.

Theorem rev_tuple_seq_to_BITS {n} (v : bitvector n)
  : rev_tuple (seq_to_BITS v) = seq_to_tuple v.
Proof.
  apply val_inj.
  rewrite / rev_tuple / rcons_tuple /=.
  move : n v.
  apply Vector.t_ind => [|h n' t IH] //=.
  rewrite rev_rcons IH //=.
Qed.

Theorem tnth_rev_tuple {T n} (t : n.-tuple T) i
  : tnth (rev_tuple t) i = tnth t (rev_ord i).
Proof.
  rewrite / tnth.
  rewrite nth_rev size_tuple //=.
  apply set_nth_default.
  by rewrite size_tuple rev_ord_proof.
Qed.

Lemma genOrdinal_tnth_bitvector_to_BITS
  : forall (n : nat) (v : bitvector n),
    genOrdinal n bool (fun q : 'I_n => tnth (seq_to_BITS v) (rev_ord q)) = v.
Proof.
  apply Vector.t_ind => [|h n t IH] //=.
  {
    f_equal.
    {
      rewrite / tnth.
      rewrite nth_rcons.
      rewrite size_tuple /=.
      rewrite subn1 /=.
      rewrite ltnn.
      rewrite eqxx.
      reflexivity.
    }
    {
      setoid_rewrite genOrdinal_domain_eq ; [ apply IH  | ] => i.
      rewrite tnth_rcons_tuple_rev_ord_rshift.
      by rewrite tnth_rev_tuple.
    }
  }
Qed.

(* Global Instance ProperEmbedding_bitvector_BITS n *)
(*   : ProperEmbedding (Embedding_bitvector_BITS n). *)
(* Proof. *)
(*   apply Build_ProperEmbedding. *)
(*   move : n. *)
(*   apply Vector.t_ind. *)
(*   { *)
(*     reflexivity. *)
(*   } *)
(*   { *)
(*     move => h n t IH. *)
(*     simpl. *)
(*     f_equal. *)
(*     { *)
(*       rewrite map_tuple_id. *)
(*       rewrite tnth_rcons_tuple_rev_ord0. *)
(*       reflexivity. *)
(*     } *)
(*     { *)
(*       setoid_rewrite tnth_map. *)
(*       erewrite genOrdinal_domain_eq; [ apply genOrdinal_tnth_bitvector_to_BITS | ]. *)
(*       move => i /=. *)
(*       rewrite tnth_rcons_tuple_rev_ord_rshift. *)
(*       apply tnth_rev_tuple. *)
(*     } *)
(*   } *)
(* Qed. *)

(* Global Instance Isomorphism_bitvector_BITS n *)
(*   : Isomorphism (Embedding_bitvector_BITS n). *)
(* Proof. *)
(*   constructor. *)
(* Admitted. *)

Global Instance Embedding_prod {A B C D} `{Embedding A B} `{Embedding C D}
  : Embedding (A * C) (B * D) :=
  {|
    toAbstract '(a, c) := (toAbstract a, toAbstract c);
    toConcrete '(b, d) := (toConcrete b, toConcrete d);
  |}.
