From Coq          Require Import Lists.List.
From Coq          Require Import ssreflect.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.

From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCorePrelude.

From Records      Require Import Records.

Import ListNotations.
Import SAWCorePrelude.
Import VectorNotations.

Fixpoint Nat_cases2_match a f1 f2 f3 (x y : nat) : a :=
  match (x, y) with
  | (O,   _)   => f1 y
  | (S x, O)   => f2 x
  | (S x, S y) => f3 x y (Nat_cases2_match a f1 f2 f3 x y)
  end.

Theorem Nat_cases2_match_spec a f1 f2 f3 x y :
  Nat_cases2 a f1 f2 f3 x y = Nat_cases2_match a f1 f2 f3 x y.
Proof.
  revert y.
  induction x; intros y.
  {
    reflexivity.
  }
  {
    destruct y.
    {
      reflexivity.
    }
    {
      simpl.
      now rewrite IHx.
    }
  }
Qed.

Theorem minNat_min a b : minNat a b = min a b.
Proof.
  revert b.
  induction a; intros b.
  {
    reflexivity.
  }
  {
    destruct b; simpl; intuition.
  }
Qed.

Theorem minNat_Succ n : minNat n (Succ n) = n.
Proof.
  unfold minNat.
  rewrite Nat_cases2_match_spec.
  induction n.
  {
    reflexivity.
  }
  {
    unfold Succ in *.
    simpl.
    intuition.
  }
Qed.

(**
I end up eliminating vectors of size 2 a lot.  This abstracts over the tedium of
it.
 *)
Theorem elimVector2 (A : Type) (M : Vector.t A 2 -> Type)
  : (forall h1 h2, M ([h1 ; h2])%vector) ->
    forall v, M v.
Proof.
  move => IH v.
  pose goal :=
    fun n v =>
      match n as n' return Vector.t A n' -> Type with
      | 2 => fun v => M v
      | _ => fun _ => Logic.True
      end v.
  cut (goal 2 v) => //.
  have := eq_refl 2.
  move : v.
  move : {1 3 4} 2 => n2.
  elim /@Vector.t_rect => // h1 n1 t _.
  move : t.
  elim /@Vector.t_rect => // h2 [] //.
  apply : (Vector.case0 (A := A)) => _ _ //.
Qed.
