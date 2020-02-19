From Coq Require Import
     Lists.List
     Numbers.NaryFunctions
     Morphisms
     String
     Program.Equality
     Vector
.

From S2N Require Import Embedding.

From mathcomp Require Import
     eqtype
     fintype
     seq
     ssreflect
     ssrbool
     ssrfun
     ssrnat
     tuple
.

Class CorrectTranslation
      {CI AI CO AO}
      `{ProperEmbedding CI AI}
      `{ProperEmbedding CO AO}
      (concreteFun : CI -> CO) (abstractFun : AI -> AO)
  :=
    {
      correctTranslation :
        forall ci ai co ao,
          toAbstract ci = ai ->
          concreteFun ci = co ->
          abstractFun ai = ao ->
          toAbstract co = ao;
    }.

Theorem byCorrectTranslation
        {CI AI CO AO}
        (concreteFun : CI -> CO) (abstractFun : AI -> AO)
        `{ProperEmbedding CI AI}
        `{ProperEmbedding CO AO}
        `{CT : ! CorrectTranslation concreteFun abstractFun}
  : forall ci, concreteFun ci = toConcrete (abstractFun (toAbstract ci)).
Proof.
  move => ci.
  destruct CT as [CT].
  specialize (CT ci _ _ _ (Logic.eq_refl _) (Logic.eq_refl) (Logic.eq_refl)).
  apply f_equal with (f := toConcrete) in CT.
  rewrite roundtrip in CT.
  apply CT.
Qed.

(* Fixpoint nary n (args : n.-tuple Set) (ret : Set) : Set := *)
(*   match n as n' return n'.-tuple Set -> Set with *)
(*   | 0    => fun _    => ret *)
(*   | n.+1 => fun args => thead args -> nary n (behead_tuple args) ret *)
(*   end args. *)

(* Import ListNotations. *)

(* Definition plus a b := a + b. *)

(* Check (plus : nary 2 [tuple of [nat; nat]] nat). *)

(* Definition plus2 a b := (a + 1) + (b + 1). *)

(* Check (plus2 : nary 2 [tuple of [nat; nat]] nat). *)

(* Class NaryTranslation *)
(*       n args__f ret__f args__g ret__g *)
(*       (f : nary n args__f ret__f) *)
(*       (g : nary n args__g ret__g) *)
(*       (pp : forall (i : 'I_n), (tnth args__f i) -> (tnth args__g i)) *)
(*   := *)
(*     { *)

(*     }. *)

(* Fixpoint napply *)
(*          n (args : n.-tuple Set) (ret : Set) *)
(*          (f : nary n args ret) *)
(*          (a : forall (i : 'I_n), tnth args i) *)
(*          {struct n} *)
(*   : ret *)
(*   := *)
(*     match n as n' *)
(*           return *)
(*           forall (args' : n'.-tuple Set), *)
(*             nary n' args' ret -> *)
(*             (forall (i : 'I_n'), tnth args' i) -> *)
(*             ret *)
(*     with *)
(*     | 0   => fun args f a => f *)
(*     | S n => fun args f a => *)
(*               napply n *)
(*                      [tuple of (behead args)] *)
(*                      ret *)
(*                      (f (a ord0)) *)
(*                      (fun i => *)
(*                         match Logic.eq_sym (tnth_behead args i) *)
(*                               in eq _ T *)
(*                               return T *)
(*                         with *)
(*                         | Logic.eq_refl => a (inord i.+1) *)
(*                         end *)
(*                      ) *)
(*     end args f a. *)

(* Theorem test : forall n, n.+2 < 2 -> False. *)
(*   move => n //. *)
(* Qed. *)

(* Definition foo : nat. *)
(*   refine ( *)
(*     napply 2 [tuple of [nat; nat]] nat plus *)
(*            (fun i => *)
(*               match i as i' return nat_of_ord i' < 2 -> tnth [tuple of [nat; nat]] i' with *)
(*               | Ordinal 0 _ => fun _ => 2 *)
(*               | Ordinal 1 _ => fun _ => 3 *)
(*               | Ordinal m M => fun X => _ *)
(*               end _ *)
(*            ) *)
(*     ). *)
(*   exfalso. *)
(*   eauto. *)
(*   eauto. *)
(* Qed. *)
