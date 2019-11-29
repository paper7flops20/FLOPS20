
Require Import BTLC_Lib.


(** ** Types *)
Inductive Ty : Type :=
  | TArrow   : nat -> Ty -> Ty -> Ty
  | TProd    : Ty  -> Ty -> Ty
  | TSum     : Ty  -> Ty -> Ty
  | TUnit    : Ty. 


Notation "T1 '-:' n '>' T2" := (TArrow n T1 T2) (right associativity, at level 61) : Ty_scope.
Notation "()"               := (TUnit) (at level 58) : Ty_scope.
Notation "T1 ''*'' T2"        := (TProd T1 T2) (left associativity, at level 59) : Ty_scope.
Notation "T1 ''+'' T2"        := (TSum T1 T2) (right associativity, at level 60) : Ty_scope.

Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with Ty.

Local Open Scope Ty_scope.

(** ** Terms *)

Inductive term : Type :=
  | tvar     :> id -> term
  | tapp     : term -> term -> term
  | tabs     : id -> Ty -> term -> term      (* ty is type of binder *)
  | tunit    : term                          (* the unit value *)
  | tpair    : term -> term -> term          (* pairs *)
  | tpi1     : term -> term                  (* the 1st projection of a pair *)
  | tpi2     : term -> term                  (* the 1st projection of a pair *)
  | tinl     : term -> Ty -> term            (* ty is type on right of sum *)
  | tinr     : term -> Ty -> term            (* ty is type on left of sum *)
  | tcase    : term -> term -> term -> term  (* case expressions *).

          

Infix "$"                 := tapp (at level 77) : term_scope.

Notation "\( x ':' T ) t" := (tabs x T t) 
                              (at level 78, x at level 99, format "'[hv ' \( x ':' T )  t ']'") : term_scope.
Notation "< t1 , t2 >"    := (tpair t1 t2) (at level 73, t1 at level 100, t2 at level 101): term_scope.
Notation "()"             := tunit : term_scope.
Notation "'pi1' t"        := (tpi1 t) (at level 72) : term_scope.
Notation "'pi2' t"        := (tpi2 t) (at level 72) : term_scope.
Notation "'Inl' t T"      := (tinl t T) (at level 72) : term_scope.
Notation "'Inr' t T"      := (tinr t T) (at level 72) : term_scope. 
Notation "'case' t l r"   := (tcase t l r) (at level 77) : term_scope.

Bind Scope term_scope with term.
Delimit Scope term_scope with term.
Local Open Scope term_scope. 

Theorem type_eq_dec : forall (T U : Ty), {T = U} + {T <> U}. 
Proof. decide equality. decide equality. Qed.

Theorem term_eq_dec : forall (t u : term), {t = u} + {t <> u}.
Proof. decide equality; decide equality; decide equality; decide equality.
Qed. 

Ltac decide_term_eq t u := destruct (term_eq_dec t u) as [HEq | HNeq].

Tactic Notation "term_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar"
  | Case_aux c "tapp"
  | Case_aux c "tabs"
  | Case_aux c "tunit"
  | Case_aux c "tpair"
  | Case_aux c "tpi1"
  | Case_aux c "tpi2"
  | Case_aux c "tinl"
  | Case_aux c "tinr"
  | Case_aux c "tcase"].

(** ** Values *)

Inductive value : term -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_unit : value tunit
  | v_pair : forall t1 t2,
      value t1 -> value t2 -> value (tpair t1 t2)
  | v_inl : forall t T,
      value t -> value (tinl t T)
  | v_inr : forall t T,
      value t -> value (tinr t T).

Hint Constructors value.

Theorem value_dec : forall (t:term), value t \/ ~ (value t). 
  intro.
  induction t; try (right; intro H; inversion H; fail);
               try (left; constructor; fail);
               try (destruct IHt; [left; constructor; auto | right; intro Hval; inversion Hval; contradiction]; fail);
               try (destruct IHt1;
                    [ destruct IHt2; [ left; constructor; assumption
                                     | right; intro Hval; inversion Hval; contradiction ]
                    | right; intro Hval; inversion Hval; contradiction ];
                    fail).
Qed.

Ltac decide_value e := destruct (value_dec e) as [?Hval | ?Hnotval].

(** * Typing Judgments *)

(** ** For terms *)
Definition context := partial_map Ty.


Reserved Notation "Gamma '|--' t '\in' T n" (at level 40).


Inductive has_type : context -> term -> Ty -> nat -> Prop :=
  | T_Var  : forall Gamma x T,
               Gamma x = Some T ->
               has_type Gamma (tvar x) T 0
  | T_Abs  : forall Gamma x T1 T2 t n,
               has_type (extend Gamma x T1) t T2 n ->
               has_type Gamma (tabs x T1 t) (TArrow n T1 T2) 0
  | T_App  : forall T1 T2 Gamma f t1 n m p,
               has_type Gamma f (TArrow n T1 T2) m ->
               has_type Gamma t1 T1 p ->
               has_type Gamma (tapp f t1) T2 (n + m + p + 1)
  | T_Nil : forall Gamma,
               has_type Gamma tunit TUnit 0
  | T_Pair : forall Gamma T1 T2 t1 t2 n m,
               has_type Gamma t1 T1 n ->
               has_type Gamma t2 T2 m ->
               has_type Gamma (tpair t1 t2) (TProd T1 T2) (n + m)
  | T_Pi1  : forall Gamma T1 T2 t n,
               has_type Gamma t (TProd T1 T2) n ->
               has_type Gamma (tpi1 t) T1 (n + 1)
  | T_Pi2  : forall Gamma T1 T2 t n,
               has_type Gamma t (TProd T1 T2) n ->
               has_type Gamma (tpi2 t) T2 (n + 1)
  | T_Inl  : forall Gamma T1 T2 t n,
               has_type Gamma t T1 n ->
               has_type Gamma (tinl t T2) (TSum T1 T2) n
  | T_Inr  : forall Gamma T1 T2 t n,
               has_type Gamma t T2 n ->
               has_type Gamma (tinr t T1) (TSum T1 T2) n
  | T_Case : forall Gamma Tl Tr Tres ts tl tr n,
      has_type Gamma ts (TSum Tl Tr) n ->
      forall nl m nr p,
        nl + m = nr + p ->
               has_type Gamma tl (TArrow nl Tl Tres) m ->
               has_type Gamma tr (TArrow nr Tr Tres) p ->
               has_type Gamma (tcase ts tl tr) Tres (n + (nl + m) + 2).


Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"
  | Case_aux c "T_Abs"
  | Case_aux c "T_App"
  | Case_aux c "T_Unit"
  | Case_aux c "T_Pair"
  | Case_aux c "T_Pi1"
  | Case_aux c "T_Pi2"
  | Case_aux c "T_Inl"
  | Case_aux c "T_Inr"
  | Case_aux c "T_Case"]. 

(** * Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

(* Substitution function. *)
Fixpoint subst (x:id) (s:term) (t:term) : term :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1))
  | tunit =>
      tunit
  | tpair t1 t2 =>
      tpair ([x:=s] t1) ([x:=s] t2)
  | tpi1 t1 =>
      tpi1 ([x:=s] t1)
  | tpi2 t1 =>
      tpi2 ([x:=s] t1)
  | tinl t1 T =>
      tinl ([x:=s] t1) T
  | tinr t1 T =>
      tinr ([x:=s] t1) T
  | tcase t1 t2 t3 =>
      tcase ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end 
where "'[' x ':=' s ']' t" := (subst x s t).

Inductive appears_free_in : id -> term -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> 
      appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> 
      appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tpair t1 t2)
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tpair t1 t2)
  | afi_pi1 : forall x t,
      appears_free_in x t ->
      appears_free_in x (tpi1 t)
  | afi_pi2 : forall x t,
      appears_free_in x t ->
      appears_free_in x (tpi2 t)
  | afi_tinl : forall x t TR,
      appears_free_in x t ->
      appears_free_in x (tinl t TR)
  | afi_tinr : forall x t TL,
      appears_free_in x t ->
      appears_free_in x (tinr t TL)
  | afi_tcase1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tcase t1 t2 t3)
  | afi_tcase2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tcase t1 t2 t3)
  | afi_tcase3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tcase t1 t2 t3).

Hint Constructors appears_free_in.

Definition closed (t:term) := forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Gamma Gamma' t S n,
      has_type Gamma t S n  ->
      (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
      has_type Gamma' t S n. 
Proof with eauto.
  intros. generalize dependent Gamma'.
  induction H; intros Gamma' Heqv; auto; try (econstructor;eauto;fail)...
  Case "tvar".
    apply T_Var... rewrite <- Heqv...
  Case "tabs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend. destruct (eq_id_dec x y)...
Qed.


Lemma free_in_context : forall x t T Gamma n,
      appears_free_in x t ->
      has_type Gamma t T n ->
        (exists T', Gamma x = Some T').
Proof with eauto.
  intros x t T Gamma n Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend in Hctx. 
    rewrite neq_id in Hctx...
Qed.

(** * Reduction *)


Reserved Notation "t1 '~>' t2" (at level 80).
Reserved Notation "t1 '~>>' t2 '//' n" (at level 80). 


Inductive step : term -> term -> Prop := 
  | ST_AppAbs : forall x T t v,
                  value v ->
                  (tapp (tabs x T t) v) ~> [x:=v]t
  | ST_App1   : forall t1 t1' t2,
                  t1 ~> t1' ->
                  tapp t1 t2 ~> tapp t1' t2
  | ST_App2   : forall v t2 t2',
                  value v ->
                  t2 ~> t2' ->
                  tapp v t2 ~> tapp v t2'
  | ST_Pair1  : forall t1 t1' t2,
                  t1 ~> t1' ->
                  tpair t1 t2 ~> tpair t1' t2
  | ST_Pair2  : forall v t2 t2',
                  value v ->
                  t2 ~> t2' ->
                  tpair v t2 ~> tpair v t2'
  | ST_Pi1    : forall v1 v2,
                  value v1 ->
                  value v2 ->
                  tpi1 (tpair v1 v2) ~> v1
  | ST_Pi2    : forall v1 v2,
                  value v1 ->
                  value v2 ->
                  tpi2 (tpair v1 v2) ~> v2
  | ST_Pi1E   : forall t t',
                  t ~> t' ->
                  tpi1 t ~> tpi1 t'
  | ST_Pi2E   : forall t t',
                  t ~> t' ->
                  tpi2 t ~> tpi2 t'
  | ST_InL    : forall t1 T t1',
                  t1 ~> t1' ->
                  tinl t1 T ~> tinl t1' T
  | ST_InR    : forall t1 T t1',
                  t1 ~> t1' ->
                  tinr t1 T ~> tinr t1' T
  | ST_Case   : forall t1 t1' t2 t3,
                  t1 ~> t1' ->
                  tcase t1 t2 t3 ~> tcase t1' t2 t3
  | ST_CaseL  : forall v1 T t2 t3,
                  value v1 ->
                  tcase (tinl v1 T) t2 t3 ~> tapp t2 v1
  | ST_CaseR  : forall v1 T t2 t3,
                  value v1 ->
                  tcase (tinr v1 T) t2 t3 ~> tapp t3 v1
where "t1 '~>' t2" := (step t1 t2). 

Ltac beta_reduce' E ty x E' tac :=
      let HTemp := fresh "ST_AppAbs" in (
        match goal with 
        | [H: value E |- _] => pose proof (ST_AppAbs x ty E' E H) as HTemp; tac
        end).

Ltac beta_reduce E ty x E' :=  beta_reduce' E ty x E' intuition.

Inductive nstep : term -> term -> nat -> Prop := 
| nstep_refl  : forall (t   : term), 
                       t ~>> t // 0
| nstep_step  : forall (n : nat) (t u v: term),
                       t ~> u ->
                       u ~>> v // n ->
                       t ~>> v // (S n)
where "t1 '~>>' t2 '//' n" := (nstep t1 t2 n).
Hint Constructors nstep. 

Theorem step_incl_nstep : forall (t u : term),
                          t ~> u ->
                          t ~>> u // 1.
Proof. intros.  
       apply nstep_step with u; intuition. 
Qed.

Theorem nstep_trans : forall (t u v : term) (i j : nat),
                       t ~>> u // i ->
                       u ~>> v // j ->
                       t ~>> v // (i + j). 
Proof. intros. induction H; intros; intuition.
       rewrite (plus_Sn_m n j); 
       apply nstep_step with u; intuition.
Qed. 


Scheme step_nat_ind  := Induction for nstep Sort Prop.


Theorem type_unique : forall t Gamma T1 T2 n m, 
      has_type Gamma t T1 n  -> 
      has_type Gamma t T2 m  -> (T1 = T2 /\ n = m).

Proof.
  induction t; intros Gamma T1 T2 n m Ht1 Ht2.
  Case "tvar".
       inversion Ht1; inversion Ht2; subst; eauto.
       rewrite H1 in H6.
       inversion H6.
       auto.
  Case "app".
       inversion Ht1; inversion Ht2; subst; eauto.
       destruct (IHt1 _ _ _ _ _ H2 H9) as [HL HR].
       rewrite HR in *.
       destruct (IHt2 _ _ _ _ _ H5 H12) as [HL1 HR1].
       rewrite HL1 in *.
       inversion HL.
       subst.
       auto.
  Case "tabs".
       inversion Ht1; inversion Ht2; subst; eauto.
       destruct (IHt _ _ _ _ _ H5 H12); subst. 
       auto.
  Case "tunit".
       inversion Ht1; inversion Ht2; subst; eauto.
  Case "tpair".
       inversion Ht1; inversion Ht2; subst; eauto.
       destruct (IHt1 _ _ _ _ _ H2 H9) as [HL1 HR1];
       destruct (IHt2 _ _ _ _ _ H5 H12) as [HL2 HR2]; subst.
       auto.
  Case "tpi1".
       inversion Ht1; inversion Ht2; subst; eauto.
       destruct (IHt _ _ _ _ _ H1 H6) as [HL1 HR1]; subst.
       inversion HL1; subst.
       auto.
  Case "tpi2".
       inversion Ht1; inversion Ht2; subst; eauto.
       destruct (IHt _ _ _ _ _ H1 H6) as [HL1 HR1]; subst.
       inversion HL1; subst.
       auto.
  Case "tinl".
       inversion Ht1; inversion Ht2; subst; eauto.
       destruct (IHt _ _ _ _ _ H4 H10) as [HL1 HR1]; subst.
       auto.
  Case "tinr".
       inversion Ht1; inversion Ht2; subst; eauto.
       destruct (IHt _ _ _ _ _ H4 H10) as [HL1 HR1]; subst.
       auto.
  Case "tcase".
       
  inversion Ht1; inversion Ht2; subst. 
       destruct (IHt1 _ _ _ _ _ H2 H12) as [HL1 HR1]; subst.
       destruct (IHt2 _ _ _ _ _ H7 H17) as [HL2 HR2]; subst.
       destruct (IHt3 _ _ _ _ _ H8 H18) as [HL3 HR3]; subst.
       inversion HL2; subst.
  
       auto.
Qed.



Corollary type_unique_type : forall t Gamma T1 T2 n m, 
      has_type Gamma t T1 n  -> 
      has_type Gamma t T2 m  -> T1 = T2.

Proof. apply type_unique.
Qed.

Corollary type_unique_complexity : forall t Gamma T1 T2 n m, 
      has_type Gamma t T1 n  -> 
      has_type Gamma t T2 m  -> n = m.

Proof. apply type_unique.
Qed.

Lemma typable_stronger :
  forall Gamma Gamma' T t n,
    (forall x T, Gamma x = Some T -> Gamma' x = Some T) ->
    has_type Gamma t T n ->
    has_type Gamma' t T n.

Proof.
  intros Gamma Gamma' T t n Hstronger HTt;
  generalize dependent Gamma';
  generalize dependent Gamma;
  generalize dependent T;
  generalize dependent n.
  induction t; intros; try (inversion HTt; subst; econstructor; eauto).
  Case "tabs".
    inversion HTt; subst; eauto.
      eapply IHt.
      eapply H5.
      intros.
      destruct (eq_id_dec i x).
        SCase "i = x".
          unfold extend.
          subst.
          unfold extend in H.
          rewrite eq_id in H.
          inversion H; subst.
          rewrite eq_id.
          reflexivity.
        SCase "i <> x".
          unfold extend in H.
          rewrite neq_id in H; auto.
          unfold extend.
          rewrite neq_id; auto.
Qed.

Theorem typable_empty_everywhere:
  forall Gamma T t n,
    has_type empty t T n ->  has_type Gamma t T n.

Proof.
  intros.
  assert ((forall (x : id) (T0 : Ty), empty x = Some T0 -> Gamma x = Some T0)) by (intros; inversion H0).
  apply (typable_stronger empty Gamma T t n H0 H).
Qed.


Lemma values_irreducible : forall v, value v -> forall t, ~(v ~> t).

Proof.
  induction v; intros Hval t';
    try (intro Hstep; inversion Hstep; fail);
    try (inversion Hval; fail).

  Case "pair".
    inversion Hval; subst.
    intro Hstep; inversion Hstep.
    SCase "left steps". contradict H4; auto.
    SCase "right steps". contradict H5; auto.
  Case "inl".
    inversion Hval; subst.
    intro Hstep; inversion Hstep; subst; contradict H3; auto.
  Case "inr".
    inversion Hval; subst.
    intro Hstep; inversion Hstep; subst; contradict H3; auto.
Qed.

Lemma values_irreducible' : forall v, value v -> ~exists t, v ~> t.

Proof.
  intros v Hval [t' Hstep].
  contradict Hstep; apply values_irreducible; auto.
Qed.

Lemma step_not_value : forall t, (exists t', t ~> t') -> ~ value t.
Proof.
  intros t [t' Hstep] Hval; contradict Hstep; apply values_irreducible; auto.
Qed.


Theorem complexity_of_well_typed_values :
  forall t T n,
     has_type empty t T n -> value t -> n = 0.
Proof. induction t; intros ? ? HTt HVt;
       try (inversion HTt; auto;fail);
       try (inversion HVt;fail);
       ((inversion HTt; subst);(inversion HVt; subst));
       try (eapply IHt;eauto).
 Case "tpair".
      assert (n0 = 0) by (eapply IHt1; eauto).
      assert (m  = 0) by (eapply IHt2; eauto).
      subst.
      auto.
Qed.


Lemma values_subst_preserves_typing : forall Gamma x U v t T n m,
      has_type (extend Gamma x U) t T n ->
      has_type empty v U m  ->
      value v ->
      has_type Gamma ([x:=v] t) T n.
Proof with eauto.
  intros Gamma x U v t T n m HText HTt HVv.
  generalize dependent Gamma;
  generalize dependent T;
  generalize dependent n;
  generalize dependent m;
  generalize dependent v.
  induction t; intros; simpl;
  try (inversion HText; subst;
       econstructor;[
         eapply IHt1; eauto|
         eapply IHt2; eauto]; fail);
  try (inversion HText; subst;econstructor; eauto; fail);
  [Case "tvar"|Case "tabs"];
   match goal with
       | [ |- context [eq_id_dec ?a ?b] ] =>
         destruct (eq_id_dec a b); [SCase "a = b"| SCase "a <> b"]
   end.                                     
   inversion HText; subst.
   unfold extend in H1. rewrite eq_id in H1.
   inversion H1; subst. 
    eapply typable_empty_everywhere;eauto.
    assert (m = 0) by (eapply complexity_of_well_typed_values;eauto);
      subst;auto.
   inversion HText.
    subst.
    eapply T_Var... unfold extend in H1. rewrite neq_id in H1...
   inversion HText; subst.
   constructor.
   eapply context_invariance...
          intros x0 Hafi.
          apply extend_shadow.
   inversion HText; subst.
   constructor.
   apply IHt with (m := m); auto.
   eapply context_invariance...
         intros x0 Hafi. 
         unfold extend.
         destruct (eq_id_dec i x0)... 
         subst. rewrite neq_id... 
Qed.
 

Corollary typable_empty_closed : forall t T n, 
          has_type empty t T n ->
          closed t.
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ n H1 H) as [T' HC].
  inversion HC.  
Qed.

Lemma vacuous_substitution : forall  t x, 
     ~ appears_free_in x t  ->
     forall t', [x:=t']t = t.
Proof.
  intros t x H t' ; induction t; simpl; eauto;
   try (match goal with
   | [ |- context[(eq_id_dec ?x ?i)] ] => destruct (eq_id_dec x i); eauto; try (exfalso; subst; apply H;eauto; fail)
   end);
  try (repeat (match goal with
          | [H : context[([?x := ?t']?t1) = ?t1] |- _ ] => rewrite H; eauto; hide hyp H
          end)). 
Qed.

Lemma subst_closed: forall t, 
      closed t  ->
      forall x t', [x:=t']t = t.
Proof.
  intros; apply vacuous_substitution; apply H.
Qed.

Lemma subst_not_afi : forall t x v, 
      closed v ->  
      ~ appears_free_in x ([x:=v]t).
Proof.
  unfold closed, not.
  intros t x v P Hcond; induction t;
  simpl in Hcond; try (inv Hcond; eauto; fail).
  destruct (eq_id_dec x i); [eauto|inv Hcond].
  destruct (eq_id_dec x i); eauto; [inv Hcond|inv Hcond].
Qed.
       
Lemma duplicate_subst : forall t' x t v, 
      closed v -> [x:=t]([x:=v]t') = [x:=v]t'.
Proof.
  intros; 
  eapply vacuous_substitution;
  apply subst_not_afi; eauto.
Qed.

Lemma swap_subst : forall t x x1 v v1, 
        x <> x1 -> 
       closed v ->
      closed v1 -> 
      [x1:=v1]([x:=v]t) = [x:=v]([x1:=v1]t).
Proof. 
  intros t x x1 v v1 Hneq Hclv Hclv1.
   induction t;intros; simpl; auto;
   try (repeat (match goal with
                | [H: ?X = ?Y |- _ ] => rewrite H; eauto; hide hyp H
                end); fail);
  destruct (eq_id_dec x i); destruct (eq_id_dec x1 i);
  [ subst ++; apply ex_falso_quodlibet; auto
  | subst ++; simpl; rewrite eq_id; apply subst_closed; auto
  | subst ++; simpl; rewrite eq_id; rewrite subst_closed; auto                                                         
  | simpl; rewrite neq_id; eauto; rewrite neq_id; auto
  | reflexivity|reflexivity|reflexivity|rewrite IHt; auto].
Qed.

(** ** Canonical Forms *)
Lemma canonical_forms_fun : forall t T1 T2 n m,
      has_type empty t (TArrow n T1 T2) m ->
      value t ->
      exists x u, t = tabs x T1 u.
Proof.
  intros ? ? ? ? ? HT HVal. 
  inversion HVal;subst; eauto; (inversion HT; subst; eauto); eexists; eauto.
Qed.

Lemma canonical_forms_pair : forall t T1 T2 n,
      has_type empty t (TProd T1 T2) n ->
      value t ->
      exists t1 t2, t = tpair t1 t2.
Proof.
  intros ? ? ? ? HT HVal.
  inversion HVal; subst; eauto; (inversion HT; subst; eauto); eexists; eauto.
Qed.

Lemma canonical_forms_sum : forall t T1 T2 n,
      has_type empty t (TSum T1 T2) n ->
      value t ->
      (exists t', t = tinl t' T2) \/ (exists t', t = tinr t' T1).
Proof.
  intros ? ? ? ? HT HVal.
  inversion HVal; subst; eauto; (inversion HT; subst; eauto). 
Qed.


Lemma canonical_forms_tunit : forall t n,
      has_type empty t TUnit n ->
                      value t ->
                      t = tunit /\ n = 0.
Proof.
  intros ? ? HT HVal.
  inversion HVal; subst; eauto; (inversion HT; subst; eauto).
Qed.


(** *** Progress *)
Theorem progress : forall t T n,
                     has_type empty t T n -> value t \/ exists t', t ~> t'.

Proof with eauto.
  intros ? ? ? Ht.
  remember (@empty Ty) as Gamma.
  induction Ht; try (left; constructor; fail); subst Gamma...
  Case "T_Var".
    inversion H.

  Case "T_App".
    right. destruct IHHt1...
    SCase "f is a value".
      destruct IHHt2...
      SSCase "t1 is also a value".
        assert (exists x t, f = tabs x T1 t) by (eapply canonical_forms_fun; eauto).
        destruct H1 as [x [t Heq]];subst.
        eexists; eapply ST_AppAbs; eauto.
      SSCase "t1 steps".
        destruct H0 as [t' Hstp].
        eexists; apply ST_App2; eauto.
    SCase "f steps".
      destruct H as [f' Hstp].
      eexists; eapply ST_App1; eauto.

  Case "T_Pair".
    destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t_2 is a value".
      right.  destruct H0 as [t_2' Hstp];
        eexists; eapply ST_Pair2; eauto.
    SCase "t1 steps".
      destruct H as [t_1' Hstp]. right.
      eexists; eapply ST_Pair1; eauto.

  Case "T_Pi1".
    destruct IHHt...
    SCase "t is a value".
    right.
    assert (exists t_1 t_2, t = tpair t_1 t_2) by (eapply canonical_forms_pair; eauto).
    destruct H0 as [t_1 [t_2 Heq]]. subst.
    eexists; eapply ST_Pi1; inversion H; auto.
    SCase "t steps".
    right. destruct H as [t' Hstep].
      eexists;eapply ST_Pi1E; eauto.

  Case "T_Pi2".
    destruct IHHt...
    SCase "t is a value".
      right. assert (exists t_1 t_2, t = tpair t_1 t_2).
      eapply canonical_forms_pair; eauto.
      destruct H0 as [t_1 [t_2 Heq]]. rewrite Heq. exists t_2.
      apply ST_Pi2. rewrite Heq in H.
      inversion H; auto. rewrite Heq in H. inversion H; auto.
    SCase "t steps".
      right. destruct H as [t' Hstep].
      exists (tpi2 t'). apply ST_Pi2E; auto.

  Case "T_Inl".
    destruct IHHt...
    SCase "t steps".
    right. destruct H as [t' Heq].
    eexists;eapply ST_InL; eauto.

  Case "T_Inr".
    destruct IHHt...
    SCase "t steps".
    right. destruct H as [t' Heq].
    eexists;eapply ST_InR; eauto.

  Case "T_Case".
    destruct IHHt1...
    SCase "ts is a value".
      assert ((exists t1, ts = tinl t1 Tr)
               \/ (exists t2, ts = tinr t2 Tl)).
      eapply canonical_forms_sum; eauto. 
      destruct H1 as [HL | HR]; [ destruct HL as [t1 Heq]
                                | destruct HR as [t2 Heq]]; subst.
      SSCase "ts = tinl t1 Tr".
        right. eexists; eapply ST_CaseL. inversion H0; auto.
      SSCase "ts = tinr t2 Tl".
        right. eexists; eapply ST_CaseR. inversion H0; auto.
    SCase "ts steps".
    right. destruct H0 as [ts' Hstep].
    eexists; eapply ST_Case; eauto.
Qed.


Corollary not_value_step : forall t T n,
     has_type empty t T n -> ~ value t -> exists t', t ~> t'.

Proof.
  intros t T n Ht Hnv.
  destruct (progress t T n Ht); [contradiction | assumption].
Qed.

Theorem for_cases : forall nl nr p,
 S nl < max (S (S nl)) (S (S (nr + p))).
Proof. intuition.
Qed.


Require Import Omega.

(** *** Preservation *)
Theorem preservation :
  forall t t' T n,
     has_type empty t T n ->
                     t ~> t' -> 
   exists m, m < n  /\ has_type empty t' T m.

Proof with eauto.
  remember (@empty Ty) as Gamma.
  intros ? ? ? ? HTt HSt';
  generalize dependent t'.
    has_type_cases (induction HTt) intuition; intros;
    try (solve [inversion HSt';subst;auto]).
  inversion HSt';subst.
  SCase "Beta".
        inversion HTt1; subst.
        exists n. 
        split; [omega | eapply values_subst_preserves_typing; eauto].
  SCase "App1".
        destruct (IHHTt1 eq_refl t1' H2) as [m0 [? ?]].
        exists (n + m0 + p + 1).
        split; [omega | eapply T_App; eauto].
  SCase "App2". 
        destruct (IHHTt2 eq_refl t2' H3) as [p0 [? ?]].
        exists (n + m + p0 + 1).
        split; [omega | eapply T_App; eauto].
  inversion HSt'; subst.
  SCase "TPair 1".
        destruct (IHHTt1 eq_refl t1' H2) as [n0 [? ?]].
        exists (n0 + m).
        split; [omega | eapply T_Pair; eauto].
  SCase "TPair 2".
        destruct (IHHTt2 eq_refl t2' H3) as [m0 [? ?]].
        exists (n + m0).
        split; [omega | eapply T_Pair; eauto].
  inversion HSt';subst.
  SCase "T_Pi1E".
        inversion HTt; subst.
        exists n0.
        split; [omega|auto].
  SCase "T_Pi1".
        destruct (IHHTt eq_refl t'0 H0) as [n0 [? ?]].
        exists (n0 + 1).
        split; [omega |eapply T_Pi1;eauto].
  inversion HSt';subst.      
  SCase "T_Pi2E".
        inversion HTt; subst.
        exists m.
        split; [omega|auto].
  SCase "T_Pi1".
        destruct (IHHTt eq_refl t'0 H0) as [n0 [? ?]].
        exists (n0 + 1).
        split; [omega |eapply T_Pi2;eauto].
  inversion HSt';subst.
  SCase "T_Inl". 
        destruct (IHHTt eq_refl t1' H2) as [n0 [? ?]].
        exists n0.
        split; [omega |eapply T_Inl;eauto].
  inversion HSt';subst.
  SCase "T_Inr". 
        destruct (IHHTt eq_refl t1' H2) as [m0 [? ?]].
        exists m0.
        split; [omega |eapply T_Inr;eauto].
  inversion HSt';subst.
  SCase "ts".
        destruct (IHHTt1 eq_refl _ H4) as [n0 [HTC1 HTC2]].  
        exists (n0 + (nl + m) + 2).
        split; [omega | eapply T_Case;eauto].
  SCase "tl".
  inversion HTt1;subst.
  exists (nl + m + n + 1).
  split; [ | eapply T_App;eauto].
 assert (n = 0) by (eapply complexity_of_well_typed_values;eauto); subst;
        simpl. 
 firstorder.
 SCase "tr".
  inversion HTt1;subst. Check (T_App).
 pose proof (T_App Tr Tres _ tr v1 _ _ _ HTt3 H7). 
   exists (nl + m + n + 1). 
   rewrite H in *.
   split; [firstorder | auto].
Qed.



(** *** Preservation Nstep *)
Corollary preservation_nstep :
  forall n m t t' T,
     has_type empty t T n ->
                     t ~>> t' // m -> 
                     exists o, o <= (n - m) /\
                                has_type empty t' T o.

Proof with eauto. 
 intros n m t t' T HTt Hstep. 
  generalize dependent n;
  generalize dependent T.
  induction Hstep; intros T X HTt. 
     exists X; split. firstorder. auto.
     destruct (preservation t u T X HTt H) as [Y [HLE HTu]]. 
     pose proof (IHHstep T Y HTu) as [Z [HLT HTv]]. 
     exists Z; split; [firstorder| ]; auto.
Qed.


(** *** Determinism *)
Theorem step_deterministic : forall t u v,
                               t ~> u ->
                               t ~> v ->
                               u = v.

Proof.
  induction t; try (intros u v Hstep; inversion Hstep; fail).
  Case "tapp".
    intros u v Hstep1 Hstep2.
    inversion Hstep1; subst.
      inversion Hstep2; subst.
        auto.
        inversion H3.
        contradict H4; apply values_irreducible; auto.
      inversion Hstep2; subst.
        inversion H2.
        assert (t1' = t1'0). apply IHt1. assumption. assumption.
        subst. reflexivity.
        contradict H2; apply values_irreducible; auto.
      inversion Hstep2; subst.
        contradict H3; apply values_irreducible; auto.
        contradict H4; apply values_irreducible; auto.
        assert (t2' = t2'0). apply IHt2. assumption. assumption.
        subst. reflexivity.
  Case "tpair".
    intros u v HstepU HstepV.
    inversion HstepU; subst.
      inversion HstepV; subst.
        assert (t1'=t1'0). apply IHt1. assumption. assumption.
        subst. reflexivity.
        contradict H2; apply values_irreducible; auto.
      inversion HstepV; subst.
        contradict H4; apply values_irreducible; auto.
        assert (t2'=t2'0). apply IHt2. assumption. assumption.
        subst. reflexivity.
  Case "tpi1".
    intros u v HstepU HstepV.
    inversion HstepU; subst.
      inversion HstepV; subst.
        reflexivity.
        inversion H2; subst.
          contradict H5; apply values_irreducible; auto.
          contradict H6; apply values_irreducible; auto.
      inversion HstepV; subst.
        inversion H0; subst.
          contradict H5; apply values_irreducible; auto.
          contradict H6; apply values_irreducible; auto.
          assert (t'=t'0). apply IHt. assumption. assumption.
          subst; reflexivity.
  Case "tpi2".
    intros u v HstepU HstepV.
    inversion HstepU; subst.
      inversion HstepV; subst.
        reflexivity.
        inversion H2; subst.
          contradict H5; apply values_irreducible; auto.
          contradict H6; apply values_irreducible; auto.
      inversion HstepV; subst.
        inversion H0; subst.
          contradict H5; apply values_irreducible; auto.
          contradict H6; apply values_irreducible; auto.
          assert (t'=t'0). apply IHt. assumption. assumption.
          subst; reflexivity.
  Case "tinl".
    intros u v HstepU HstepV.
    inversion HstepU; subst.
      inversion HstepV; subst.
        assert (t1'=t1'0). apply IHt. assumption. assumption.
        subst; reflexivity.
  Case "tinr".
    intros u v HstepU HstepV.
    inversion HstepU; subst.
      inversion HstepV; subst.
        assert (t1'=t1'0). apply IHt. assumption. assumption.
        subst; reflexivity.
  Case "case".
    intros u v HstepU HstepV.
    inversion HstepU; subst.
      inversion HstepV; subst.
        assert (t1'=t1'0). apply IHt1. assumption. assumption. subst; reflexivity.
        assert (value (tinl v1 T)). constructor. assumption.
        contradict H3; apply values_irreducible; auto.
        assert (value (tinr v1 T)). constructor. assumption.
        contradict H3; apply values_irreducible; auto.
     inversion HstepV; subst.
        assert (value (tinl v1 T)). constructor. assumption.
        contradict H4; apply values_irreducible; auto.
        reflexivity.
     inversion HstepV; subst.
        assert (value (tinr v1 T)). constructor. assumption.
        contradict H4; apply values_irreducible; auto.
        reflexivity.
Qed.

Corollary preservation_nstep' :
  forall n m t t' T,
     has_type empty t T n ->
     t ~>> t' // m ->
                     exists o, o + m <= n /\
                                has_type empty t' T o.
Proof with eauto. 
 intros n m t t' T HTt Hstep. 
  generalize dependent n;
  generalize dependent T.
  induction Hstep; intros T X HTt. 
     exists X; split. firstorder. auto.
     destruct (preservation t u T X HTt H) as [Y [HLE HTu]]. 
     pose proof (IHHstep T Y HTu) as [Z [HLT HTv]]. 
     exists Z; split; [firstorder| ]; auto.
Qed.

(** ** Congruence Lemmmas *) 

Lemma Congruence_AppAbs : forall (x : id) (T : Ty) (t v : term),
      value v -> 
      (\(x:T) t) $ v ~>> [x := v] t // 1.

Proof.
  intros. eapply nstep_step. 
          eapply ST_AppAbs; eauto.
          eapply nstep_refl;eauto.
Qed.


Lemma Congruence_App1 : forall t1 t1' t2 n,
      (t1 ~>> t1' // n) ->
      (tapp t1 t2) ~>> (tapp t1' t2) // n.

Proof.
 intros t1 t1' t2 n STM. induction STM.
    apply nstep_refl.
    eapply nstep_step.
      apply ST_App1. apply H. auto.
Qed.


Lemma Congruence_App2 : forall v t t' n, 
          value v -> 
      (t ~>> t' // n) -> 
      (tapp v t) ~>> (tapp v t') // n.

Proof.
  intros v t t' n HV STM. induction STM. 
   apply nstep_refl.
   eapply nstep_step.
     apply ST_App2; eauto.  auto.
Qed.


Lemma Congruence_Pair1 : forall t1 t1' t2 n,
      (t1 ~>> t1' // n) -> 
      (tpair t1 t2) ~>> (tpair t1' t2) // n.

Proof.
  intros t1 t1' t2 n STM. induction STM.
    apply nstep_refl.
    eapply nstep_step.
      apply ST_Pair1. apply H. auto.
Qed.


Lemma Congruence_Pair2 : forall v1 t2 t2' n,
       value v1 -> 
       t2 ~>> t2' // n -> 
       (tpair v1 t2) ~>> (tpair v1 t2') // n.

Proof.
  intros v1 t2 t2' V n STM. induction STM.
    apply nstep_refl.
    eapply nstep_step.
      apply ST_Pair2. auto. apply H. auto.
Qed.


Lemma Congruence_Pi1 : forall v1 v2,
      value v1 ->
      value v2 ->
      tpi1 (tpair v1 v2) ~>> v1 // 1.

Proof.
  intros v1 v2 V1 V2. eapply nstep_step.
    eapply ST_Pi1;eauto.
    eapply nstep_refl.
Qed.


Lemma Congruence_Pi2 : forall v1 v2,
      value v1 ->
      value v2 ->
      tpi2 (tpair v1 v2) ~>> v2 // 1.
Proof.
  intros v1 v2 V1 V2. eapply nstep_step.
    eapply ST_Pi2;eauto.
    eapply nstep_refl.
Qed.


Lemma Congruence_Pi1E: forall t t' n,
       t ~>> t' // n -> 
       (tpi1 t ~>> tpi1 t' // n).
Proof.
  intros t t' n STM. induction STM.
  apply nstep_refl.
  eapply nstep_step. eapply ST_Pi1E. eapply H.
  auto.
Qed.


Lemma Congruence_Pi2E: forall t t' n,
       t ~>> t' // n -> 
       (tpi2 t ~>> tpi2 t' // n).
Proof.
  intros t t' n STM. induction STM.
  apply nstep_refl.
  eapply nstep_step. eapply ST_Pi2E. eapply H.
  auto.
Qed.

Lemma Congruence_Tinl : forall T t1 t2 n,
      t1 ~>> t2 // n -> (tinl t1 T) ~>> (tinl t2 T) // n.
Proof.
  intros t1 t2 T n STM. induction STM.
    apply nstep_refl.
    eapply nstep_step.
      apply ST_InL. apply H. auto.
Qed.

Lemma Congruence_Tinr : forall T t1 t2 n,
      t1 ~>> t2 // n -> (tinr t1 T) ~>> (tinr t2 T) // n.
Proof.
  intros t1 t2 T n STM. induction STM.
    apply nstep_refl.
    eapply nstep_step.
      apply ST_InR. apply H. auto.
Qed.

Lemma Congruence_Tcase : forall t1 t1' t2 t3 n,
      t1 ~>> t1' // n -> tcase t1 t2 t3 ~>> tcase t1' t2 t3 // n.
Proof.
  intros t1 t1' t2 t3 n STM. induction STM.
    apply nstep_refl. eapply nstep_step.
    apply ST_Case. apply H. apply IHSTM.
Qed.

Lemma Congruence_ST_CaseL  : forall T v1 t2 t3,
      value v1 ->
      tcase (tinl v1 T) t2 t3 ~>> tapp t2 v1 // 1.
Proof.
  intros T v1 t2 t3 STM. 
   eapply nstep_step.
   eapply ST_CaseL;eauto.
   apply nstep_refl; auto.
Qed.

Lemma Congruence_ST_CaseR  : forall T v1 t2 t3,
      value v1 ->
      tcase (tinr v1 T) t2 t3 ~>> tapp t3 v1 // 1.
Proof.
   intros T v1 t2 t3 STM. 
   eapply nstep_step.
   eapply ST_CaseR;eauto.
   apply nstep_refl; auto.
Qed.


Theorem id_not_step : forall i (u :term),
        ~ (tvar i ~> u).
Proof. 
  intros. unfold not; intros. inversion H.
Qed.

Corollary id_not_nstep' : forall i (u :term),
        ~ (tvar i ~>> u // 1).
Proof. 
   intros. unfold not; intros. 
   inv H.
   apply (id_not_step i u). inv H4.
Qed.

Corollary id_not_nstep : forall i (u :term) n, 
        tvar i <> u ->
        ~ (tvar i ~>> u // n).
Proof. 
   intros. generalize dependent n; induction n; unfold not; intros. 
   inv H0. inv H0. apply (id_not_step i u0). auto.
Qed.

(** ** Inversion Principles *) 

Lemma var_inv1  : forall (i : id) u,
      i ~> u -> u = i.
Proof. intros. inv H.
Qed.

Lemma var_inv2  : forall (i : id) u,
      ~ (i ~> u).
Proof. intros. unfold not;intros;inv H.
Qed.

Lemma pair_inv1 : forall l r l' r',
      tpair l r ~> tpair l' r' -> 
      ~ value l ->
      (l ~> l').
Proof. intros. inv H. exfalso. unfold not in *. apply (H0 H4).
Qed.

Lemma pair_inv2 : forall l r l' r',
      tpair l r ~> tpair l' r' -> 
      value l ->
      (r ~> r').
Proof. intros. inv H. exfalso. eapply values_irreducible;[eapply H0;eauto| eapply H2;eauto].
Qed.

Lemma pair_inv_l : forall l r p,
      tpair l r ~> p ->
      ~ value l      ->
      exists l', l ~> l'.
Proof. intros. inv H. exists t1';auto. 
       exfalso. unfold not in *. apply (H0 H3).
Qed.

Lemma pair_inv_l' : forall l r l' r',
      tpair l r ~> tpair l' r' ->
      ~ value l      ->
      l ~> l'.
Proof. intros. inv H. 
       exfalso. unfold not in *. apply (H0 H4).
Qed.

Lemma pair_inv_r : forall l r p,
      tpair l r ~> p ->
      value l        ->
      exists r', r ~> r'.
Proof. intros. inv H.
       eapply values_irreducible in H0.
       exfalso. unfold not in *. eapply (H0 H4).
       exists t2';auto.
Qed.

Lemma pair_step_pair : forall l r p,
      tpair l r ~> p ->
      exists l' r', p = (tpair l' r').
Proof. intros. inv H; repeat eexists;eauto.
Qed.

Lemma app_inv1 : forall m n p, 
      m $ n ~> p ->
      ~ value m        ->
      (exists n', n ~> n') \/ (exists m', m ~> m').
Proof. intros. inv H. assert (HV: value (\(x:T) t)) by eauto.
       exfalso. unfold not in *. eapply (H0 HV).
       right. eexists;eauto.
       left.  eexists;eauto.
Qed.

Lemma app_inv2 : forall m n p, 
      m $ n ~> p ->
      ~ value n          ->
      (exists n', n ~> n') \/ (exists m', m ~> m').
Proof. intros. inv H;  unfold not in *. exfalso. apply (H0 H4). 
       right. eexists;eauto.
       left.  eexists;eauto.
Qed.

Lemma app_inv3 : forall m n p,
      m $ n ~> p ->
      value m    ->
      ~ value n    ->
      (exists n', n ~> n').
Proof. intros. inv H. 
       unfold not in H1. exfalso. apply (H1 H5).
       exfalso. eapply values_irreducible;eauto.
       eexists;eauto.
Qed.

Lemma app_inv4 : forall m n p,
      m $ n ~> p ->
      ~ value m    ->
      ~ value n    ->
      (exists m', m ~> m').
Proof. intros. inv H. 
       unfold not in H1. exfalso. apply (H1 H5).
       eexists;eauto.
       unfold not in H0. exfalso. apply (H0 H4).
Qed.

Lemma app_abs_inv : forall m n p,
      m $ n ~> p ->
      value m    ->
      value n    ->
      ~ (exists m', m ~> m').
Proof. intros. unfold not; intros. destruct H2. eapply values_irreducible. eapply H0;eauto. eassumption.
Qed.

Lemma val_inv : forall v u n,
      value v ->
      v ~>> u // n -> v = u.
Proof. intros. inv H0. inv H2. exfalso. eapply values_irreducible;eauto.
                               exfalso. eapply values_irreducible;eauto.
Qed.

Lemma step_value_second : forall t t' v n,
                            value v ->
                            t ~> t' ->
                            t ~>> v // n ->
                            t' ~>> v // (n - 1).
Proof.
  intros t t' v n Hvalv Hsteptt' Hsteptv.
  generalize dependent t'.
  generalize dependent Hvalv.
  generalize dependent n.
  induction 1; intros.
    contradict Hvalv; eapply step_not_value; eauto.
    assert (u=t') by (eapply step_deterministic; eauto). 
    subst. 
    assert (S n - 1 = n). firstorder. 
    rewrite H0 in *; auto.
Qed.

Lemma step_value_unique : forall t v v' n m,
                       value v ->
                       value v' ->
                       t ~>> v  // n ->
                       t ~>> v' // m ->
                       v = v'.
Proof.
  intros t v v' n m Hdonev Hdonev' Hsteptv.
  generalize dependent v' n m.
  induction 2; intros.
  eapply val_inv;eauto. 
  eapply IHHsteptv; eauto.
  eapply step_value_second.
  auto.
  eapply H.
  eapply H0.
Qed.

Lemma step_same_value : forall t t' v n m,
                          value v ->
                          t  ~>> t' // n ->
                          t  ~>> v  // m ->
                          t' ~>> v  // (m - n).
Proof.
  intros t t' v n m Hvalv Hstept'. 
    generalize dependent v n m. induction 2;intros.
    assert (HRe: m - 0 = m) by firstorder; rewrite HRe in *; auto.
    assert (u ~>> v // m - 1). 
           eapply step_value_second;eauto.
    pose proof (IHHstept' (m - 1) H1).
    assert (HRe': (m - 1 - n) = m - S n) by firstorder; rewrite HRe' in *;auto.
Qed.

Lemma step_values_same : forall t v n m,
                          value v  ->
                          t  ~>> v // n ->
                          t  ~>> v // m ->
                          (m = n).
Proof. 
  intros t v n m HV HStep HStep'.
  generalize dependent t v n m. 
  induction 2;intros.
  inv HStep'. 
      exfalso; eapply values_irreducible;eauto. 
  inv HStep'.
      exfalso; eapply values_irreducible;eauto. 
  assert (u = u0) by (eapply step_deterministic;eauto);subst.
  f_equal. 
  eapply IHHStep;eauto.
Qed.

Lemma step_values_same' : forall t v v' n m,
                          value v  ->
                          value v' ->
                          t  ~>> v  // n ->
                          t  ~>> v' // m ->
                          (m = n).
Proof. 
  intros t v v' n m HV HV' HStep HStep'. 
  assert (v = v') by (eapply step_value_unique;eauto).
  subst.
  eapply step_values_same;eauto.
Qed.


Definition normal_form (t : term) : Prop :=
  ~ exists t', t ~> t'.

Lemma value_normal_form : forall (v : term),
                            value v -> normal_form v.
Proof.
    intros v Hval; induction Hval; intros [t' Hval']; inversion Hval'; eauto.
Qed.
  
  
Inductive terminates : term -> Prop :=
| terminates_intro : forall t n v, t ~>> v // n -> value v -> terminates t.

Hint Constructors terminates.

Definition terminates' (t : term) :=
  exists v n, t ~>> v // n /\ value v.
Hint Unfold terminates'.

Theorem teqt : forall t, terminates t <-> terminates' t.
Proof. intuition.
       inversion H; eauto.
       destruct H as [? [? [? ?]]]; eauto.
Qed.
      
  
Lemma values_terminate : forall v,
      value v -> terminates v.
Proof.
intros;eauto.
Qed.

(** * Reducibility *)
Fixpoint R (T:Ty) (t:term) {struct T} : Prop := 
  (exists n, has_type empty t T n) /\ (terminates t) /\
  (match T with
   | TArrow m T1 T2 => forall s,
                            R T1 s -> R T2 (tapp t s)
   | TProd    T1 T2 => exists t1 t2 o,
                         t ~>> (tpair t1 t2) // o /\
                         value t1 /\
                         value t2 /\
                         R T1 t1  /\
                         R T2 t2
   | TSum     T1 T2 => exists t' o,
                         value t' /\
                         ((t ~>> tinl t' T2 // o /\ R T1 t') \/
                          (t ~>> tinr t' T1 // o /\ R T2 t'))
   | TNil           => True
    end).

Theorem R_terminates : forall T t,
                         R T t -> terminates t.
Proof. intros;
  destruct T; unfold R in *; fold R in *; destruct H as [? [? _]]; eauto.
Qed. 

Hint Immediate R_terminates.

Theorem R_typable_empty : forall T t,
                          R T t -> exists n, has_type empty t T n.
Proof. intros;
    destruct T; unfold R in *; fold R in *; destruct H as [? [? _]]; eauto.
Qed.

Hint Immediate R_typable_empty.

Lemma step_preserves_termination : forall t t', 
      (t ~> t') -> (terminates t <-> terminates t').
Proof. 
  intros t t' tstept'.
  split; [Case_aux Case "->";intros HTermt; inversion HTermt; subst
         |Case_aux Case "<-";intros HTermt';inversion HTermt';subst].
  inversion H; subst.
  apply ex_falso_quodlibet.
        pose proof (value_normal_form _ H0) as HV.
        unfold normal_form in HV.
        apply HV.
        exists t'.
        auto.
        rewrite (step_deterministic _ _ _ tstept' H1).
        econstructor;eauto.
        pose proof (nstep_step _ _ _ _ tstept' H).
        econstructor.
        eapply H1.
        auto.
Qed.

Lemma nstep_preserves_termination : forall t t' n, 
      (t ~>> t' // n) -> (terminates t <-> terminates t').
Proof. 
  intros t t' n Hnsteptt'.
  induction Hnsteptt'; intros.
  split; [Case_aux Case "->";intros HTermt
         |Case_aux Case "<-";intros HTermt'];auto.
  split; [Case_aux Case "->";intros HTermt
         |Case_aux Case "<-";intros HTermt'];auto.
  eapply step_preserves_termination in H.
  rewrite H in HTermt.
  rewrite IHHnsteptt' in HTermt;auto.
  eapply step_preserves_termination.
  eapply H.
  rewrite IHHnsteptt';auto.
Qed.

Lemma step_preserves_R : forall T t t',
                           t ~> t' ->
                           R T t   -> 
                           R T t'.
Proof.
  induction T; [Case_aux Case "TArrow"
               |Case_aux Case "TProd"
               |Case_aux Case "TSum"
               |Case_aux Case "TNil"  ];
  intros t t' tstept' ?;
  match goal with | [H: R ?T ?t |- _] => destruct H as [[n' HTt] [HTerm ?]] end;
  match goal with
        | [H1: t ~> t', H2: has_type empty t ?T ?n |- _] => 
                destruct (preservation _ _ _ _ H2 H1) as [? [HypLE Hyp]]
        end;
  match goal with
  | [H1: t ~> t', H2: terminates t |- _] => 
                pose proof (step_preserves_termination _ _ H1) as HTRewrite; rewrite HTRewrite in H2; clear HTRewrite
  end; try (split; [eexists;eauto|split;[auto|]]).
  (* TArrow *)
            intros.   
            apply (IHT2 (t $ s) (t' $ s) (ST_App1 _ _ s tstept') (H _ H0)).
  (* TProd *) 
           destruct H as [t1 [t2 [o [Htstep [HV1 [HV2 [HR1 HR2]]]]]]]. 
           assert (Htstep' : t' ~>> tpair t1 t2 // (o - 1)) by (
                  eapply step_value_second;eauto).
           repeat eexists;eauto.
  (* TSum *)
           destruct H as [v [o [HVv HSum]]]. 
           destruct HSum as [[HS1 HR1] | [HS1 HR1]]. 
           assert (HLV: value (tinl v T2)) by (constructor;auto).
           assert (Htstep' : t' ~>> tinl v T2 // (o - 1)) by (
                  eapply step_value_second;eauto).
           exists v, (o - 1); split; [auto| left;auto].
           assert (HRV: value (tinr v T1)) by (constructor;auto).
           assert (Htstep' : t' ~>> tinr v T1 // (o - 1)) by (
                  eapply step_value_second;eauto).
           exists v, (o - 1); split; [auto| right;auto].
   auto.
Qed.

Lemma nstep_preserves_R : forall T t t' n,
                           t ~>> t' // n -> 
                           R T t ->
                           R T t'.
Proof.
   intros T t t' n STM; induction STM; intros. 
   assumption.
   apply IHSTM. eapply step_preserves_R;eauto.
Qed.

Lemma step_preserves_R' : forall T t t' n, 
      has_type empty t T n -> 
                t ~> t' ->
                R T t'  -> 
                R T t. 
Proof. induction T; [Case_aux Case "TArrow"
                    |Case_aux Case "TProd"
                    |Case_aux Case "TSum"
                    |Case_aux Case "TNil"  ];
       intros;
       match goal with
       | [H: R ?T ?t |- _ ] => destruct H as [HTt [HTerm HEx]]
       end;
       match goal with
       | [H1: ?t ~> ?t', H2: has_type empty ?t ?T ?n |- _] => 
                destruct (preservation _ _ _ _ H2 H1) as [? [HypLE Hyp]]
       end;
       match goal with
       | [H1: ?t ~> ?t', H2: terminates ?t' |- _ ] =>
                rewrite <- (step_preserves_termination _ _ H1) in H2
       end;try (split; [eexists;eauto|split;[auto|]]).
 (* TArrow *)
       intros. destruct (R_typable_empty _ _ H1) as [? ?].
       eapply IHT2;eauto. 
       eapply ST_App1;eauto.
 (* TProd *) 
       destruct HEx as [t1 [t2 [o [HTs [HVt1 [HVt2 [HRt1 HRt2]]]]]]]. 
       exists t1, t2, (S o); repeat split; auto.
       eapply nstep_step;eauto.
 (* TSum *)
       destruct HEx as [v [o [HVv [[HSL HRL] | [HSR HRR]]]]]; exists v, (S o); split;auto.
       left;split;[eapply nstep_step;eauto|auto].
       right;split;[eapply nstep_step;eauto|auto].
       auto.
Qed.

Lemma nstep_preserves_R' : forall T t t' n m, 
      has_type empty t T n  ->
                t ~>> t' // m  ->
                R T t'          ->
                R T t.
Proof. intros T t t' n m HT STM ?.
       generalize dependent n.
       induction STM; intros. 
       assumption. 
       destruct (preservation _ _ _ _ HT H0) as [? [? ?]].
       eapply step_preserves_R'; [eapply HT |eapply H0| ].
       eapply (IHSTM H); eauto.
Qed.

(** *** Definition pertaining to multi-substitutions, enviroments, type assignments,
        extension of a context thereby, closed enviroments, etc. Again, fairly
        standard machinery. *)

Definition env := list (id * term). 

Fixpoint closed_env (env:env) {struct env} :=
         match env with
         | nil         => True
         | (x,t)::env' => closed t /\ closed_env env'
         end.

Fixpoint msubst (ss:env) (t:term) {struct ss} : term :=
         match ss with
         | nil => t
         | ((x,s)::ss') => msubst ss' ([x:=s]t)
         end.

Definition tass := list (id * Ty).

Fixpoint mextend (Gamma : context) (xts : tass) :=
         match xts with
         | nil => Gamma
         | ((x,v)::xts') => extend (mextend Gamma xts') x v
         end.

Fixpoint lookup {X:Set} (k : id) (l : list (id * X)) {struct l} : option X :=
         match l with
         | nil => None
         | (j,x) :: l' => if eq_id_dec j k then Some x else lookup k l'
         end.

Fixpoint drop {X:Set} (n:id) (nxs:list (id * X)) {struct nxs} : list (id * X) :=
         match nxs with
         | nil => nil
         | ((n',x)::nxs') => if eq_id_dec n' n then drop n nxs' else (n',x)::(drop n nxs')
         end.

Inductive instantiation :  tass -> env -> Prop :=
  | V_nil  : instantiation nil nil 
  | V_cons : forall x T v c e, 
                       value v  -> 
                         R T v  -> 
             instantiation c e  -> 
             instantiation ((x,T)::c) ((x,v)::e).

(** *** Lemmas concerning various properties of the functions defined above. *)

Lemma mextend_lookup : forall (c:tass) (x:id), 
      lookup x c = (mextend empty c) x. 
Proof.
  induction c; intros. 
    auto.
    destruct a. unfold lookup, mextend, extend. destruct (eq_id_dec i x); auto.  
Qed.

Lemma mextend_drop : forall (c:tass) Gamma x x', 
      mextend Gamma (drop x c) x' = if eq_id_dec x x' then Gamma x' else mextend Gamma c x'.
Proof. 
  induction c; intros. 
      destruct (eq_id_dec x x'); auto. 
      destruct a. simpl.
      destruct (eq_id_dec i x).
         subst. rewrite IHc. 
            destruct (eq_id_dec x x').  auto. unfold extend. rewrite neq_id; auto. 
         simpl. unfold extend.  destruct (eq_id_dec i x').
            subst.
               destruct (eq_id_dec x x'). 
                  subst. exfalso. auto. 
                  auto. 
           auto. 
Qed.

(** *** Properties of Instantiations *)

Lemma instantiation_domains_match: forall {c} {e}, 
      instantiation c e -> 
      forall {x} {T}, lookup x c = Some T -> exists t, lookup x e = Some t.
Proof.
  intros c e V. induction V; intros x0 T0 C.
    inversion C. 
    simpl in *.
    destruct (eq_id_dec x x0); eauto. 
Qed.

Lemma instantiation_env_closed : forall c e,  
      instantiation c e -> closed_env e.
Proof.
  intros c e V; induction V; intros.
    econstructor. 
    unfold closed_env. fold closed_env. 
    split.  
        destruct (R_typable_empty _ _ H0) as [? ?]. eapply typable_empty_closed; eauto.   
        auto.
Qed.

Lemma instantiation_R : forall c e, 
      instantiation c e -> 
                        forall x t T, 
      lookup x c = Some T -> 
      lookup x e = Some t -> 
      R T t.
Proof.
  intros c e V. induction V; intros x' ? T' G E;[inv G |inv E; inv G]. 
  destruct (eq_id_dec x x'); subst.
      inv H2; inv H3. 
      eapply IHV;eauto.
Qed.

Lemma instantiation_drop : forall c env, 
  instantiation c env -> forall x, instantiation (drop x c) (drop x env).
Proof.
  intros c e V. induction V.  
    intros.  simpl.  constructor.  
    intros. unfold drop. destruct (eq_id_dec x x0); auto. econstructor; eauto. 
Qed.

Lemma mextend_empty_lookup : forall c x, (mextend empty c) x = lookup x c.
Proof. 
  intros; rewrite mextend_lookup; reflexivity. 
Qed.

Lemma msubst_closed: forall t, 
              closed t -> 
                    forall ss, 
                      msubst ss t = t.
Proof. 
  induction ss as [|x]; intros; [reflexivity|destruct x; simpl].
    rewrite subst_closed; assumption.
Qed.

Lemma msubst_preserves_typing : forall c e,
     instantiation c e -> 
     forall Gamma t S n, has_type (mextend Gamma c) t S n -> 
     has_type Gamma (msubst e t) S n.
Proof.
    induction 1; intros.  
    simpl in H. simpl. auto. 
    simpl in H2.  simpl. 
    apply IHinstantiation. 
    destruct (R_typable_empty _ _ H0) as [? ?].
    eapply values_subst_preserves_typing; eauto.  
Qed.

Lemma subst_msubst: forall env x v t, 
            closed v -> 
      closed_env env ->
      msubst env ([x:=v]t) = [x:=v](msubst (drop x env) t).
Proof. 
  induction env0; intros. 
    auto. 
    destruct a. simpl. 
    inversion H0. fold closed_env in H2.
    destruct (eq_id_dec i x).
      subst. rewrite duplicate_subst; auto. 
      simpl. rewrite swap_subst; eauto. 
Qed.

Lemma msubst_var:  forall ss x, closed_env ss -> 
      msubst ss (tvar x) = 
      match lookup x ss with
      | Some t => t
      | None => tvar x
      end.
Proof.
  induction ss as [|x]; intros; [reflexivity|destruct x; simpl].
      destruct (eq_id_dec i x0).
      apply msubst_closed. inversion H; auto. 
      apply IHss. inversion H; auto. 
Qed.


Lemma msubst_abs: forall ss x T t,  
      msubst ss (tabs x T t) = tabs x T (msubst (drop x ss) t).
Proof.
  induction ss; intros.
    reflexivity. 
    destruct a. 
      simpl. destruct (eq_id_dec i x); simpl; auto.
Qed.

Lemma msubst_app : forall ss t1 t2, 
      msubst ss (tapp t1 t2) = tapp (msubst ss t1) (msubst ss t2).
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.  
    simpl. rewrite <- IHss. auto. 
Qed.

Lemma msubst_pair : forall ss t1 t2,
      msubst ss (tpair t1 t2) = tpair (msubst ss t1) (msubst ss t2).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_pi1 : forall ss t1,
      msubst ss (tpi1 t1) = tpi1 (msubst ss t1).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_pi2 : forall ss t1,
      msubst ss (tpi2 t1) = tpi2 (msubst ss t1).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_tinl : forall ss T t,
      msubst ss (tinl t T) = tinl (msubst ss t) T.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_tinr : forall ss T t,
      msubst ss (tinr t T) = tinr (msubst ss t) T.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_tcase : forall ss t1 t2 t3, 
      msubst ss (tcase t1 t2 t3) = tcase (msubst ss t1) (msubst ss t2) (msubst ss t3).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. rewrite <- IHss. auto.
Qed.


Lemma msubst_tunit : forall ss,
      msubst ss tunit = tunit.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. rewrite IHss. auto.
Qed.

Hint Rewrite msubst_var msubst_abs msubst_app msubst_pair msubst_pi1 msubst_pi2 msubst_tinl msubst_tinr msubst_tcase msubst_tunit : msubstlib.


(* ###################################################################### *)
(** *** From msubst_R it follows that the ReWire calculus is strongly normalizing, 
        for both lambda and monadic expressions. This is because in order to be 
        a member of their respective [R T]'s, a term must be well-typed, and either 
        have or possess the property of halting. This lemma is more commonly
        referred to as the 'Substitution Lemma' in textbooks and whatnot. *)

Lemma msubst_R : forall c env t T n, 
     has_type (mextend empty c) t T n -> 
     instantiation c env -> 
     R T (msubst env t).
Proof.
  intros c env0 t T n HT V; 
         generalize dependent env0;
         remember (mextend empty c) as Gamma;
         generalize (mextend_empty_lookup c) as H; intros H.
  generalize dependent c. 
  induction HT; intros; autorewrite with msubstlib;
    try (pose proof (instantiation_env_closed _ _ V);auto).
  Case "T_Var".
   rewrite HeqGamma in H.
  rewrite -> (H0 x) in H.
  destruct (instantiation_domains_match V H) as [? TEMP].
  rewrite TEMP. eapply instantiation_R;eauto.
  Case "T_Abs".
     rewrite <- HeqGamma in H.
    
     assert (WT: has_type empty (tabs x T1 (msubst (drop x env0) t)) (TArrow n T1 T2) 0).
     eapply T_Abs. eapply msubst_preserves_typing.  eapply instantiation_drop; eauto.  
      eapply context_invariance.  apply HT.  
      intros. 
      unfold extend. rewrite mextend_drop. destruct (eq_id_dec x x0). auto.
      
          rewrite (H x0).  
          clear - x x0 c n0. induction c. 
              simpl. rewrite neq_id; auto. 
              simpl. destruct a.  unfold extend. destruct (eq_id_dec i x0); auto.

              
     split; [eexists;eauto|split;[eapply values_terminate;eauto|]].      
     intros.
     destruct (R_terminates _ _ H1).
     pose proof (nstep_preserves_R _ _ _ _ H2 H1).
     destruct (R_typable_empty _ _ H1) as [? ?]. 
     destruct (R_typable_empty _ _ H4) as [? ?].
      assert (HGoal1: (\(x:T1) msubst (drop x env0) t) $ t0 ~>> msubst env0 ([x := v] t) // (n0 + 1)). 
            eapply nstep_trans; [eapply Congruence_App2;eauto|rewrite subst_msubst at 1].
            eapply Congruence_AppAbs;eauto. 
            eapply typable_empty_closed;eauto.
            auto.
     eapply nstep_preserves_R';eauto.
     assert (IHHT1: (forall x0 : id, extend Gamma x T1 x0 = lookup x0 ((x, T1) :: c))).
        
          intros. unfold extend, lookup.
                  destruct (eq_id_dec x x2); auto.
                  assert (IHHT2: instantiation ((x, T1) :: c) ((x,v)::env0)) by (econstructor;eauto).

  assert (ExMex: extend (mextend \empty c) x T1 = mextend \empty ((x, T1) :: c)). simpl. auto.  
  assert (Int1:  (forall x0 : id,
        mextend \empty
          ((x, T1) :: c) x0 =
        lookup x0
               ((x, T1) :: c))).
         intros. simpl. destruct (eq_id_dec x x2); auto.
                 unfold extend. rewrite e. rewrite eq_id.
                 auto.
                 unfold extend.
                 rewrite neq_id; auto.
                 rewrite mextend_empty_lookup;auto.
  rewrite HeqGamma in IHHT.
  pose proof (IHHT ((x,T1)::c) ExMex Int1  ((x,v)::env0) IHHT2) as HG.
  simpl in HG.
  auto.              
  Case "T_App".
  rewrite HeqGamma in *.
  destruct (IHHT1 c eq_refl H env0 V) as [_ [_ P1]]. 
    pose proof (IHHT2 c eq_refl H env0 V) as P2. auto. 
  Case "TNil".
    split;[eexists;eapply T_Nil;eauto |split;[eapply values_terminate;eauto|auto]].
    Case "TProd".
     rewrite HeqGamma in *.
    pose proof (IHHT1 c eq_refl H env0 V) as HR1; 
    pose proof (IHHT2 c eq_refl H env0 V) as HR2.
    destruct (R_typable_empty _ _ HR1) as [? ?]; 
    destruct (R_typable_empty _ _ HR2) as [? ?].
    destruct (R_terminates _ _ HR1);
    destruct (R_terminates _ _ HR2). 
    assert (tpair t t0 ~>> tpair v v0 // n0 + n1).
           eapply nstep_trans.
           eapply (Congruence_Pair1 _ _ t0 n0 H3). 
           eapply (Congruence_Pair2 _ _ _ n1 H4 H5).
    split;[exists (x + x0); econstructor;eauto|split;[|]].
    econstructor;eauto. 
    exists v, v0, (n0 + n1); repeat split; auto; 
           eapply nstep_preserves_R;eauto.
  Case "T_Pi1".
     rewrite HeqGamma in *.
    pose proof (IHHT c eq_refl H env0 V) as HR1.
    destruct (R_typable_empty _ _ HR1) as [? ?]; 
    destruct (R_terminates _ _ HR1).
    edestruct HR1 as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    eapply nstep_preserves_R'.  
           econstructor;eauto. 
           eapply (nstep_trans _ _ _ _ _ 
    (Congruence_Pi1E _ _ _ H6)
    (Congruence_Pi1 _ _ H7 H8)).
           auto.
   Case "T_Pi2".
     rewrite HeqGamma in *.
    pose proof (IHHT c eq_refl H env0 V) as HR1.
    destruct (R_typable_empty _ _ HR1) as [? ?]; 
    destruct (R_terminates _ _ HR1).
    edestruct HR1 as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    eapply nstep_preserves_R'. 
           econstructor;eauto. 
           eapply (nstep_trans _ _ _ _ _ 
    (Congruence_Pi2E _ _ _ H6)
    (Congruence_Pi2 _ _ H7 H8)).
           auto.
  Case "T_Inl".
     rewrite HeqGamma in *.
    pose proof (IHHT c eq_refl H env0 V) as HR1.
    destruct (R_typable_empty _ _ HR1) as [? ?]; 
    destruct (R_terminates _ _ HR1).
    split; [eexists;econstructor;eauto|split; [|]]. 
           eapply nstep_preserves_termination.
                  eapply Congruence_Tinl;eauto.
                  eapply values_terminate.
                         econstructor;eauto.
    exists v, n0. split; auto.
                  left. split;[eapply Congruence_Tinl;eauto|eapply nstep_preserves_R;eauto].
  Case "T_InR".
    rewrite HeqGamma in *.
    pose proof (IHHT c eq_refl H env0 V) as HR1.
    destruct (R_typable_empty _ _ HR1) as [? ?]; 
    destruct (R_terminates _ _ HR1).
    split; [eexists;econstructor;eauto|split; [|]]. 
           eapply nstep_preserves_termination.
                  eapply Congruence_Tinr;eauto.
                  eapply values_terminate.
                         econstructor;eauto.
    exists v, n0. split; auto.
                  right. split;[eapply Congruence_Tinr;eauto|eapply nstep_preserves_R;eauto].
 Case "T_Case".
   rewrite HeqGamma in *.
  pose proof (IHHT2 c eq_refl H0 env0 V) as HRL;
  pose proof (IHHT3 c eq_refl H0 env0 V) as HRR;
  pose proof (IHHT1 c eq_refl H0 env0 V) as HRS;
  destruct (R_typable_empty _ _ HRL) as [i HTL];
  destruct (R_typable_empty _ _ HRR) as [j HTR];
  destruct (R_typable_empty _ _ HRS) as [k HTS];
  pose proof (msubst_preserves_typing c env0 V empty _ _ _ HT1);
  pose proof (msubst_preserves_typing c env0 V empty _ _ _ HT2);
  pose proof (msubst_preserves_typing c env0 V empty _ _ _ HT3).
  assert (HCaseEmpty: has_type empty (tcase (msubst env0 ts)
     (msubst env0 tl)
     (msubst env0 tr)) Tres (n + (nl + m) + 2)) by
     (econstructor;eauto).  
  destruct HRL as [[l HTl] [HTerm1 Hlapp]];
  destruct HRR as [[r HTr] [HTerm2 Hrapp]];
  destruct HRS as [[s HTs] [HTerm3 [v [g [HVv [[HSUM HRs] | [HSUM HRs]]]]]]].
  SCase "left".
  apply (nstep_preserves_R' _ _ _ _ _ HCaseEmpty
                            (nstep_trans _ _ _ _ _
                                         (Congruence_Tcase _ _
                               (msubst env0 tl)
                               (msubst env0 tr) _ HSUM)
             (step_incl_nstep
                (tcase (tinl v Tr)
                       (msubst env0 tl)
                       (msubst env0 tr))
                (msubst env0 tl $ v)
                (ST_CaseL v Tr
                          (msubst env0 tl)
                          (msubst env0 tr) HVv))) (Hlapp _ HRs)). 
  SCase "right".
        apply (nstep_preserves_R' _ _ _ _ _ HCaseEmpty
                            (nstep_trans _ _ _ _ _
                                         (Congruence_Tcase _ _
                               (msubst env0 tl)
                               (msubst env0 tr) _ HSUM)
             (step_incl_nstep
                (tcase (tinr v Tl)
                       (msubst env0 tl)
                       (msubst env0 tr))
                (msubst env0 tr $ v)
                (ST_CaseR v Tl
                          (msubst env0 tl)
                          (msubst env0 tr) HVv))) (Hrapp _ HRs)). 
Qed. 

Theorem normalization : forall (T:Ty) (t:term) (n:nat),
        has_type empty t T n -> terminates t.
Proof.
  intros ? ? ? H.
  replace t with (msubst nil t).
  eapply R_terminates. 
  eapply msubst_R; eauto. instantiate (3:= nil). eauto.  
  eapply V_nil.
  auto.
Qed.

Theorem normalization' : forall (T:Ty) (t:term) (n:nat),
        has_type empty t T n -> terminates' t.
Proof.
  intros ? ? ? H.
  pose proof (normalization T t n H).
  eapply teqt.
  assumption.
Qed.

Corollary timing_freedom : forall (T:Ty) (t u : term) (n m : nat),
    has_type empty t T n ->
           t ~>> u // m  ->
           value u ->
           0 <= n - m.
Proof.
  intros.
  destruct (preservation_nstep n m t u T H H0) as [k [HLeq ?]].                     assert (k = 0) by (eapply complexity_of_well_typed_values;eauto).
  subst.
  assumption.
Qed.


Section TimingChannels.

  Definition Boolean := TSum TUnit TUnit.
  Definition TTrue   := tinr tunit TUnit.
  Definition TFalse  := tinl tunit TUnit.

  Definition ITE a b c := tcase a
                              (tabs 1 TUnit b)
                              (tabs 1 TUnit c).

  Definition AND1 := tabs 1 (TProd Boolean Boolean)
                        (ITE (tpi1 1)
                             (ITE (tpi2 1) TTrue TFalse) TFalse).

  Definition AND2 := tabs 1 (TProd Boolean Boolean)
                        (ITE (tpi1 1) (tpi2 1) (tpi1 1)).

  
End TimingChannels.