From Bits Require Import operations.
From Bits Require Import operations.properties.
From Bits Require Import spec.

From Coq Require Import Lists.List.
From Coq Require        Numbers.NatInt.NZLog.
From Coq Require Import PeanoNat.
From Coq Require        Strings.String.
From Coq Require Import Vectors.Vector.

From CryptolToCoq Require Import SAWCoreScaffolding.

From mathcomp Require Import eqtype.
From mathcomp Require Import fintype.
From mathcomp Require Import seq.
From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrbool.
From mathcomp Require Import ssrnat.
From mathcomp Require Import tuple.

Import VectorNotations.

Definition Vec (n : nat) (a : Type) : Type := VectorDef.t a n.

Definition Vector_caseS' T n
  : forall P : Vector.t T (S n) -> Type,
    (forall h t, P (Vector.cons _ h _ t)) ->
    forall v, P v.
Proof.
  move => P IH v.
  move : v P IH.
  elim /@Vector.caseS => //.
Defined.

Fixpoint gen (n : nat) (a : Type) (f : nat -> a) {struct n} : Vec n a.
  refine (
      match n with
      | O   => Vector.nil _
      | S p => Vector.cons _ (f O) _ (gen _ _ (fun n => f (S n)))
      end
    ).
Defined.

Theorem gen_domain_eq n T : forall f g (domain_eq : forall i, f i = g i),
    gen n T f = gen n T g.
Proof.
  move : n.
  elim => [|n' IH] f g DEQ.
  { reflexivity. }
  {
    simpl.
    f_equal.
    {
      apply DEQ.
    }
    {
      apply IH.
      intuition.
    }
  }
Qed.

Fixpoint genOrdinal (n : nat) (a : Type) {struct n}
  : forall (f : 'I_n -> a), Vec n a.
  refine (
      match n as n' with
      | O   => fun _ => Vector.nil _
      | S p =>
        fun f =>
          Vector.cons
            _
            (f (Ordinal (ltn0Sn _)))
            _
            (genOrdinal _ _ (fun q => f (rshift 1 q)))
      end
    ).
Defined.

Theorem genOrdinal_domain_eq n T : forall f g (domain_eq : forall i, f i = g i),
    genOrdinal n T f = genOrdinal n T g.
Proof.
  move : n.
  elim => [|n' IH] f g DEQ.
  { reflexivity. }
  {
    simpl.
    f_equal.
    {
      apply DEQ.
    }
    {
      apply IH.
      intuition.
    }
  }
Qed.

Fixpoint atWithDefault (n : nat) (a : Type) (default : a) (v : Vec n a) (index : nat) : a.
  refine (
      match v with
      | Vector.nil => default
      | Vector.cons h n' t =>
        match index with
        | O => h
        | S index' => atWithDefault n' _ default t index'
        end
      end
  ).
Defined.

Definition map (a b : Type) (f : a -> b) (n : Nat) (xs : Vec n a) :=
  VectorDef.map f xs.

Fixpoint foldr (a b : Type) (n : Nat) (f : a -> b -> b) (base : b) (v : Vec n a) : b :=
  match v with
  | Vector.nil => base
  | Vector.cons hd _ tl => f hd (foldr _ _ _ f base tl)
  end.

Definition EmptyVec := Vector.nil.

Definition coerceVec (a : sort 0) (m n : Nat) (eq : Eq Nat m n) (v : Vec m a) : Vec n a :=
  match
    identity_sym eq in identity _ n'
    return Vec n' a -> Vec n a
  with
  | identity_refl => fun x => x
  end v.

Theorem gen_add m n T : forall f, gen (m + n) T f = Vector.append (gen m T f) (gen n T (fun x => f (m + x))).
Proof.
  induction m; intros.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    f_equal.
    now rewrite IHm.
  }
Qed.

(* NOTE: This version of `zip` accepts two vectors of different size, unlike the
 * one in `CoqVectorsExtra.v` *)
Fixpoint zipFunctional (a b : sort 0) (m n : Nat) (xs : Vec m a) (ys : Vec n b)
  : Vec (Nat.min m n) (a * b) :=
  match
    xs in Vector.t _ m'
    return Vector.t _ (Nat.min m' n)
  with
  | Vector.nil => Vector.nil _
  | Vector.cons x pm xs =>
    match
      ys in Vector.t _ n'
      return Vector.t _ (Nat.min (S pm) n')
    with
    | Vector.nil => Vector.nil _
    | Vector.cons y pm' ys => Vector.cons _ (x, y) _ (zipFunctional _ _ _ _ xs ys)
    end
  end
.

Definition zipWithFunctional
           (a b c : Type) (f : a -> b -> c) (n : Nat) (xs : Vec n a) (ys : Vec n b) :=
  VectorDef.map (fun p => f (fst p) (snd p)) (zipFunctional _ _ _ _ xs ys).

Definition bitvector (n : Nat) : Type := Vector.t bool n.

Definition joinLSB {n} (v : bitvector n) (lsb : bool) : bitvector n.+1 :=
  Vector.shiftin lsb v.

Fixpoint bvNat (size : Nat) (number : Nat) : bitvector size :=
  if size is size'.+1
  then joinLSB (bvNat size' (number./2)) (odd number)
  else Vector.nil _
.

Definition bvToNatFolder (n : nat) (b : bool) := b + n.*2.

Fixpoint bvToNat (size : Nat) (v : bitvector size) : Nat :=
  Vector.fold_left bvToNatFolder 0 v.

Definition bvToNat'Helper size (v : bitvector size) : (nat * nat) :=
  Vector.fold_right (fun (b : bool) '(i, n) => (i.*2, n + b*i)) v (1, 0).

Definition bvToNat' size (v : bitvector size) : nat :=
  snd (bvToNat'Helper size v).

Theorem fold_left_bvToNatFolder n h t
  : fold_left bvToNatFolder h t = bvToNat n t + h * 2 ^ n.
Proof.
  move : n t h.
  apply : Vector.t_ind => [| h' n t IH] n' //=.
  {
    rewrite add0n expn0 muln1 //.
  }
  {
    do ! rewrite IH.
    rewrite <- addnA.
    f_equal.
    rewrite / bvToNatFolder /=.
    rewrite double0.
    rewrite addn0.
    rewrite mulnDl.
    f_equal.
    rewrite <- doubleMl.
    rewrite doubleMr.
    rewrite <- mul2n.
    rewrite <- expnS.
    reflexivity.
  }
Qed.

Theorem bvToNat'Helper_bvToNat s v
  : bvToNat'Helper s v = (2 ^ s, bvToNat s v).
Proof.
  move : s v.
  apply : Vector.t_ind => //= h n t.
  rewrite / bvToNat'Helper - / bvToNat'Helper /=.
  move => ->.
  rewrite <- muln2.
  rewrite <- expnSr.
  f_equal.
  rewrite fold_left_bvToNatFolder.
  f_equal.
  rewrite / bvToNatFolder.
  rewrite double0 addn0 //.
Qed.

Theorem bvToNat_bvToNat' s v
  : bvToNat s v = bvToNat' s v.
Proof.
  rewrite / bvToNat'.
  rewrite bvToNat'Helper_bvToNat //.
Qed.

Lemma bvToNat_S
  : forall n (v : bitvector n.+1),
    bvToNat n.+1 v
    =
    (hd v * 2 ^ n) + (bvToNat n (tl v)).
Proof.
  apply : Vector.caseS => h n t.
  rewrite / hd / tl / caseS.
  rewrite bvToNat_bvToNat' //=.
  rewrite / bvToNat'.
  rewrite bvToNat'Helper_bvToNat /=.
  rewrite fold_left_bvToNatFolder.
  rewrite addnC.
  f_equal.
  rewrite / bvToNatFolder.
  rewrite double0 addn0 //.
Qed.

(* NOTE: BITS are stored in reverse order than bitvector *)
Definition bvToBITS {size : nat} (v : bitvector size)
  : BITS size
  := fromNat (bvToNat size v).

(* This is annoying to implement, so using BITS conversion *)
Definition bvAdd (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := bvNat _ (toNat (addB (bvToBITS a) (bvToBITS b))).

(* This is annoying to implement, so using BITS conversion *)
Definition bvSub (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := bvNat _ (toNat (subB (bvToBITS a) (bvToBITS b))).

(* This is annoying to implement, so using BITS conversion *)
Definition bvMul (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := bvNat _ (toNat (mulB (bvToBITS a) (bvToBITS b))).

(* This is annoying to implement, so using BITS conversion *)
Definition bvNeg (n : nat) (a : bitvector n)
  : bitvector n
  := bvNat _ (toNat (invB (bvToBITS a))).

(* FIXME this is not implemented *)
Definition bvUDiv (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := a.
Opaque bvUDiv.

(* FIXME this is not implemented *)
Definition bvURem (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := a.
Opaque bvURem.

(* FIXME this is not implemented *)
Definition bvSDiv (n : nat) (a : bitvector n.+1) (b : bitvector n.+1)
  : bitvector n.+1
  := a.
Opaque bvSDiv.

(* FIXME this is not implemented *)
Definition bvSRem (n : nat) (a : bitvector n.+1) (b : bitvector n.+1)
  : bitvector n.+1
  := a.
Opaque bvSRem.

(* FIXME this is not implemented (base 2 logarithm) *)
Definition bvLg2 (n : nat) (a : bitvector n)
  : bitvector n
  := a.
Opaque bvLg2.

(* FIXME this is not implemented *)
Definition bvShiftL (n : nat) (T : Type) (w : nat) (v : T) (a : Vector.t T n) (b : bitvector w)
  : Vector.t T n
  := a.
Opaque bvShiftL.

(* FIXME this is not implemented *)
Definition bvShiftR (n : nat) (T : Type) (w : nat) (v : T) (a : Vector.t T n) (b : bitvector w)
  : Vector.t T n
  := a.
Opaque bvShiftR.

(* FIXME this is not implemented *)
Definition bvSShr (w : nat) (a : bitvector w.+1) (n : nat)
  : bitvector w.+1
  := a.
Opaque bvSShr.

(* FIXME this is not implemented *)
Definition bvCarry (w : nat) (a : bitvector w.+1) (n : nat)
  : bitvector w.+1
  := a.
Opaque bvCarry.

(* FIXME this is not implemented *)
Definition rotateL (n : nat) (A : Type) (v : Vector.t A n) (i : nat)
  : Vector.t A n
  := v.
Opaque rotateL.

(* FIXME this is not implemented *)
Definition rotateR (n : nat) (A : Type) (v : Vector.t A n) (i : nat)
  : Vector.t A n
  := v.
Opaque rotateR.

(* FIXME this is not implemented *)
Definition shiftL (n : nat) (A : Type) (x : A) (v : Vector.t A n) (i : nat)
  : Vector.t A n
  := v.
Opaque shiftL.

(* FIXME this is not implemented *)
Definition shiftR (n : nat) (A : Type) (x : A) (v : Vector.t A n) (i : nat)
  : Vector.t A n
  := v.
Opaque shiftR.

Definition bvult (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  ltB (bvToBITS a) (bvToBITS b).

(* FIXME not implemented *)
Definition bvslt (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  false.
Opaque bvslt.

(* FIXME not implemented *)
Definition bvsgt (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  false.
Opaque bvsgt.

(* FIXME not implemented *)
Definition bvsle (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  false.
Opaque bvsle.

(* FIXME not implemented *)
Definition bvsge (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  false.
Opaque bvsge.

(* Axiom intToBv : forall (n : Nat), Integer -> bitvector n. *)

(* Axiom bvToInt : forall (n : Nat), bitvector n -> Integer. *)

Theorem joinLSB_consL {n} h (t : bitvector n) x
  : joinLSB (h :: t) x = h :: (joinLSB t x).
Proof.
  reflexivity.
Qed.

(** [bvNat] reduces innermost first, which is not convenient to do proofs
against functions which produce head first.  This equality allows to produce a
head first. *)
Theorem bvNatS s n
  : bvNat s.+1 n = odd (iter s half n) :: bvNat s n.
Proof.
  move : s n.
  elim => [|s IH] n; [ rewrite //= | ].
  rewrite (lock s.+1) /=.
  unlock.
  rewrite IH.
  rewrite //=.
  rewrite joinLSB_consL.
  f_equal.
  f_equal.
  rewrite <- iterS.
  rewrite -> iterSr.
  reflexivity.
Qed.

Theorem odd_iter_half s n b
  : b > s ->
    odd (iter s half n) = nth false (@fromNat b n) s.
Proof.
  move : s n b.
  elim => [|s IH] n b SB //=.
  {
    destruct b => //=.
  }
  {
    destruct b => //=.
    rewrite <- IH => //=.
    rewrite <- iterS.
    rewrite -> iterSr.
    reflexivity.
  }
Qed.

Lemma nth_fromNat_S (s : nat) (n : nat) (i : nat) def
  : i < s ->
    nth def (@fromNat (S s) n) i
    =
    nth def (@fromNat s n) i.
Proof.
  move : s i n.
  elim => [|s IHs] i n I //=.
  move : i I.
  case => [| i] I //=.
  rewrite IHs //=.
Qed.

Theorem bvNat_genOrdinal size n
  : bvNat size n = genOrdinal _ _ (fun i => tnth (fromNat n) (rev_ord i)).
Proof.
  move : size n.
  elim => [|s IH] n; [ rewrite // | ].
  rewrite bvNatS /=.
  f_equal => //=.
  {
    move : IH => _.
    rewrite (tnth_nth false).
    rewrite <- properties.fromNatHalf => /=.
    rewrite subn1 /=.
    apply odd_iter_half => //=.
  }
  {
    rewrite IH.
    apply genOrdinal_domain_eq => i.
    do ! rewrite (tnth_nth false).
    rewrite nth_fromNat_S //=.
    rewrite subSS.
    apply rev_ord_proof.
  }
Qed.

Theorem bvNat_toNat size (n : BITS size)
  : bvNat size (toNat n) = genOrdinal _ _ (fun i => tnth n (rev_ord i)).
Proof.
  rewrite bvNat_genOrdinal.
  rewrite properties.toNatK //.
Qed.
