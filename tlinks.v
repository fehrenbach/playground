(* Set Warnings "-notation-overridden,-parsing". *)
Require Import String.
(* Require Import Coq.Lists.List. Import ListNotations. *)

Inductive K :=
| k_type : K
.

Inductive C :=
| c_bool : C
with A :=
| a_t: C -> A
| a_bool : A
| a_arrow : A -> A -> A
.

Inductive Constant :=
| const_true : Constant
| const_false : Constant
.

Inductive M :=
| m_c : Constant -> M
| m_var : string -> M
| m_lam : string -> M -> M
| m_app : M -> M -> M
.

Inductive Context :=
| empty_context : Context
| bind_term_var : string -> A -> Context -> Context
.

Definition type_of_constant (c: Constant) : A :=
  match c with
  | const_true => a_bool
  | const_false => a_bool
  end.

Inductive type_eq : A -> A -> Prop :=
| te_bool : type_eq a_bool (a_t c_bool)
(* | te_symm : forall a b, type_eq a b -> type_eq b a *)
.

Fixpoint lookup_term_var (Gamma : Context) (v : string) : option A :=
  match Gamma with
  | empty_context => None
  | bind_term_var x x0 x1 => if string_dec x v then Some x0 else lookup_term_var x1 v
  end.

Inductive has_type : Context -> M -> A -> Prop :=
| t_c : forall G c, has_type G (m_c c) (type_of_constant c)
| t_var : forall G v a, lookup_term_var G v = Some a -> has_type G (m_var v) a
| t_lam : forall G v m a b, has_type (bind_term_var v a G) m b -> has_type G (m_lam v m) (a_arrow a b)
| t_app : forall G m n a b, has_type G m (a_arrow a b) -> has_type G n a -> has_type G (m_app m n) b
| t_ab : forall G m a b, type_eq a b -> has_type G m a -> has_type G m b
.

Example true_has_type_bool : forall G, has_type G (m_c const_true) a_bool.
Proof.
  intros.
  constructor.
Qed.

Example true_has_type_c_bool : forall G, has_type G (m_c const_true) (a_t c_bool).
Proof.
  intros.
  eapply t_ab.
  apply te_bool.
  constructor.
Qed.

Fixpoint subst (inM : M) (x : string) (withN : M) : M :=
  match inM with
  | m_c _ => inM
  | m_var y => if string_dec x y then withN else inM
  | m_lam y body =>
    if string_dec x y
    then inM
    else m_lam y (subst body x withN)
  | m_app m n =>
    m_app (subst m x withN) (subst n x withN)
  end.

Notation "m [ x := n ]" := (subst m x n) (at level 90).

Inductive reduces : M -> M -> Prop :=
| r_lam : forall x m m', reduces m m' -> reduces (m_lam x m) (m_lam x m')
| r_lam_app : forall x m n, reduces (m_app (m_lam x m) n) (m[x:=n])
| r_app1 : forall m m' n, reduces m m' -> reduces (m_app m n) (m_app m' n)
| r_app2 : forall m n n', reduces n n' -> reduces (m_app m n) (m_app m n')
.

Inductive nf : M -> Prop :=
| nf_lam : forall x m, nf m -> nf (m_lam x m)
| nf_bb : forall b, nf_b b -> nf b
with nf_b : M -> Prop :=
| nf_app : forall b m, nf_b b -> nf m -> nf_b (m_app b m)
| nf_c : forall c, nf_b (m_c c)
| nf_var : forall v, nf_b (m_var v)
. (* I don't like this at all *)

Lemma progress_empty : forall m a, has_type empty_context m a -> (exists m', reduces m m') \/ nf m.
Proof.
  induction 1.
  - right.
    repeat constructor.
  - right.
    repeat constructor.
  - destruct IHhas_type.
    + destruct H0.
      left.
      exists (m_lam v x).
      constructor.
      assumption.
    + right.
      constructor.
      assumption.
  - destruct IHhas_type1.
    + left.
      destruct H1.
      eexists. constructor. apply H1.
    + (* We have Γ ⊢ m : a → b  and  m in NF *)
      inversion H1; subst.
      * left. eexists. apply r_lam_app.
      * destruct IHhas_type2.
        -- left. destruct H3. exists (m_app m x). constructor. assumption.
        -- right. eauto using nf, nf_b.
  - assumption.
Qed.

Lemma progress_m : forall G m a, has_type G m a -> (exists m', reduces m m') \/ nf m.
Proof.
  induction 1.
  - right.
    repeat constructor.
  - right.
    repeat constructor.
  - destruct IHhas_type.
    + destruct H0.
      left.
      exists (m_lam v x).
      constructor.
      assumption.
    + right.
      constructor.
      assumption.
  - destruct IHhas_type1.
    + left.
      destruct H1.
      eexists. constructor. apply H1.
    + (* We have Γ ⊢ m : a → b  and  m in NF *)
      inversion H1; subst.
      * left. eexists. apply r_lam_app.
      * destruct IHhas_type2.
        -- left. destruct H3. exists (m_app m x). constructor. assumption.
        -- right. apply nf_bb. constructor. assumption. assumption.
  - assumption. 
Qed.

Lemma substitution_lemma : forall G x m n a b,
    has_type (bind_term_var x a G) m b -> has_type G n a -> has_type G (m [x := n]) b.
Proof.
  intros.
Admitted.

Lemma preservation_m : forall G m n a, has_type G m a -> reduces m n -> has_type G n a.
Proof.
  intros G m m' t.
  intros H step.
  generalize dependent m'.
  induction H; subst.
  - inversion 1.
  - inversion 1.
  - inversion 1. subst.
    constructor.
    auto.
  - inversion 1; subst.
    + inversion H; subst.
      * eauto using substitution_lemma.
      * (* deal with types that are equal to function types (at the moment there are none) *)
        inversion H1. 
    + eauto using t_app.
    + eauto using t_app.
  - eauto using t_ab.
Qed.
