(* Set Warnings "-notation-overridden,-parsing". *)

Require Import FunctionalExtensionality.
Require Import Program.Equality.
Require Import String.

(* Require Import Coq.Lists.List. Import ListNotations. *)

Inductive K :=
| k_type : K
.

Inductive C :=
| c_bool : C
| c_list : C -> C
with A :=
| a_t: C -> A
| a_bool : A
| a_arrow : A -> A -> A
| a_list : A -> A
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
| m_empty : M
.

Definition Context : Type := string -> option A.

Definition lookup_term_var (G: Context) (x: string) : option A :=
  G x.

Definition bind_term_var (G: Context) (x: string) (a: A) : Context :=
  fun y => if string_dec x y then Some a else G x.

(* Inductive Context := *)
(* | empty_context : Context *)
(* | bind_term_var : string -> A -> Context -> Context *)
(* . *)

Definition type_of_constant (c: Constant) : A :=
  match c with
  | const_true => a_bool
  | const_false => a_bool
  end.

Inductive type_eq : A -> A -> Prop :=
| te_bool : type_eq a_bool (a_t c_bool)
| te_list : forall a b, type_eq a b -> type_eq (a_list a) (a_list b)
(* | te_symm : forall a b, type_eq a b -> type_eq b a *)
.

(* Fixpoint lookup_term_var (Gamma : Context) (v : string) : option A := *)
  (* match Gamma with *)
  (* | empty_context => None *)
  (* | bind_term_var x x0 x1 => if string_dec x v then Some x0 else lookup_term_var x1 v *)
  (* end. *)

Inductive has_type : Context -> M -> A -> Prop :=
| t_c : forall G c, has_type G (m_c c) (type_of_constant c)
| t_var : forall G v a, lookup_term_var G v = Some a -> has_type G (m_var v) a
| t_lam : forall G v m a b, has_type (bind_term_var G v a) m b -> has_type G (m_lam v m) (a_arrow a b)
| t_app : forall G m n a b, has_type G m (a_arrow a b) -> has_type G n a -> has_type G (m_app m n) b
| t_ab : forall G m a b, type_eq a b -> has_type G m a -> has_type G m b
| t_empty : forall G a, has_type G m_empty (a_list a)
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
  | m_empty => m_empty
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
| nf_empty : nf m_empty
with nf_b : M -> Prop :=
| nf_app : forall b m, nf_b b -> nf m -> nf_b (m_app b m)
| nf_c : forall c, nf_b (m_c c)
| nf_var : forall v, nf_b (m_var v)
. (* I don't like this at all *)

Definition empty_context := fun (x: string) => @None A.

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
      * inversion H. subst. inversion H2.
  - assumption.
  - right. auto using nf.
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
      * inversion H. subst. inversion H2.
  - assumption. 
  - auto using nf.
Qed.

Lemma lookup_bound : forall G v a b, lookup_term_var (bind_term_var G v a) v = Some b -> b = a.
Proof.
  intros.
  unfold lookup_term_var, bind_term_var in H.
  destruct (string_dec _ _); inversion H; intuition.
Qed.

Lemma substitution_lemma : forall G x m n a b,
    has_type (bind_term_var G x a) m b -> has_type G n a -> has_type G (m [x := n]) b.
Proof.
  intros.
  dependent induction H; simpl; eauto using has_type.
  - simpl in H.
    destruct (string_dec _ _).
    + subst. apply lookup_bound in H. subst. assumption.
    + eauto using has_type. apply t_var.
      (* Uh, do I need that x is unbound in G? That's not easy with
      the functional representation. Ugh. This is why people don't
      want to do substitution themselves... *) 
      admit.
  - destruct (string_dec _ _).
    + admit.
    + simpl.
      constructor.
      eapply IHhas_type.
      (* Crap. This is not true. I think I need to change my contexts.
      I need to be able to reshuffle them. *)
Admitted.

Lemma preservation_m : forall G m n a, has_type G m a -> reduces m n -> has_type G n a.
Proof.
  intros G m m' t.
  intros H step.
  generalize dependent m'.
  induction H; subst; try solve [ inversion 1 ].
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
