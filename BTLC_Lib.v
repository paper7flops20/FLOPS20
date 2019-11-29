(** Tactics **)

Require Utf8 String.
Require Import Omega.
Require Export Bool List Arith Arith.Max Arith.EqNat.
Require Import Coq.Numbers.Natural.Abstract.NMaxMin Coq.Arith.Lt. 

Ltac omegaContradiction :=
  cut False; [contradiction|omega].

Definition relation (T : Type) := T -> T -> Prop.

Definition admit {T: Type} : T. Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=  
  match reverse goal with | H : _ |- _ => try move x after H  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in (assert (H : x = v) by reflexivity; clear H).

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [ set (x := name);  move_to_top x
        | assert_eq x name; move_to_top x
        | fail 1 "[working on a different case]"].

Tactic Notation "Case"        constr(name) := Case_aux Case        name.
Tactic Notation "SCase"       constr(name) := Case_aux SCase       name.
Tactic Notation "SSCase"      constr(name) := Case_aux SSCase      name.
Tactic Notation "SSSCase"     constr(name) := Case_aux SSSCase     name.
Tactic Notation "SSSSCase"    constr(name) := Case_aux SSSSCase    name.
Tactic Notation "SSSSSCase"   constr(name) := Case_aux SSSSSCase   name.
Tactic Notation "SSSSSSCase"  constr(name) := Case_aux SSSSSSCase  name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Ltac inv H := inversion H; subst; auto.

Tactic Notation "subst" "++" :=
    repeat (
      match goal with
      | x : _ |- _ => subst x
      end);
    cbv zeta beta in *.

(** ** Identifiers *)

Inductive id : Type := 
  Id :> nat -> id.

Theorem ex_falso_quodlibet : forall (P:Prop), False -> P.
Proof. intuition. Qed.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. decide equality. decide equality.
Defined.

Lemma eq_id : forall (T:Type) (x : id) (p q : T), 
              (if eq_id_dec x x then p else q) = p. 
Proof. intros; 
  destruct (eq_id_dec x x); [reflexivity|apply ex_falso_quodlibet;auto].
Qed.

Lemma neq_id : forall (T:Type) (x y : id) (p q:T), 
               x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  intros;
  destruct (eq_id_dec x y); [apply ex_falso_quodlibet;auto|reflexivity].
Qed.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Notation "'\empty'" := empty.

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
           fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall (A : Type) (ctxt: partial_map A) (x : id) (T : A),
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id; auto. 
Qed.

Lemma extend_neq : forall (A : Type) (ctxt: partial_map A) (x1 : id) (T : A) (x2 : id),
                   x2 <> x1 ->
                   (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto. 
Qed.

Lemma extend_shadow : forall (A : Type) (ctxt: partial_map A) (t1 t2 : A) (x1 x2 : id),
      extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
Proof with auto.
  intros. unfold extend. destruct (eq_id_dec x2 x1)...
Qed. 

Ltac remove_exts tac :=
  let rec go' :=
      match goal with
        | [ |- (extend _ ?X _ ?X) = _ ] => rewrite extend_eq; auto; go'
        | [ |- (extend _ ?X _ ?Y) = _ ] => rewrite extend_neq; go'
        | [ |- ?X <> ?Y               ] => discriminate; go'
        | _                             => auto
      end
  in match goal with
       | [ |- context[(extend _ _ _ _ = _)] ] => go'
       | _                                    => tac
     end.

Ltac smash2 tac1 tac2 :=
  let rec go' :=
      match goal with
        | [ |- context[(if eq_id_dec ?x ?x then _ else _) = _] ] => rewrite eq_id; eauto; go'
        | [ |- context[(if eq_id_dec ?x ?y then _ else _) = _] ] => rewrite neq_id;eauto; go'
        | [ |- ?x <> ?y ] => discriminate; go'
        | _ => auto                                            
      end
  in (tac1; (match goal with
               | [ |- context[(extend _ _ _ _ = _)] ] => unfold extend; go'
               | _                                    => try (eapply tac2; eauto)
             end)).

Ltac prim_neq_in_hyp H1 x y :=
  let H := fresh in (
    let H' := fresh in (
      assert (H : Id x <> Id y) by (intros H'; inversion H'));
    rewrite (@neq_id _ x y _ _ H) in H1; clear H
  ). 

Ltac prim_neq_in_hyp' H1 x y :=
  let H := fresh in (
      assert (H : x <> y) by discriminate;
      rewrite (@neq_id _ x y _ _ H) in H1; clear H
  ). 

Ltac prim_neq_in_goal x y :=
  let H := fresh in (
    let H' := fresh in (
      assert (H : Id x <> Id y) by (intros H'; inversion H'));
    rewrite (@neq_id _ x y _ _ H); clear H
  ).

Ltac prim_neq_in_goal' x y :=
  let H := fresh in (
      assert (H : x <> y) by discriminate;
      rewrite (@neq_id _ x y _ _ H); clear H
  ).


Ltac remove_id_in_hyps :=
  let rec go' :=
     lazymatch goal with
      | [H: context[(eq_id_dec ?x ?x)] |- _ ] => 
        rewrite eq_id in H; go'
      | [H: context[(eq_id_dec ?x ?y)] |- _ ] => 
        let H' := fresh in (
          assert (H' : x <> y) by discriminate;
          rewrite (@neq_id _ x y _ _ H') in H; clear H');go'
      | _ => idtac                                                                 
      end
    in (lazymatch goal with
       | [H: context[(eq_id_dec _ _)] |- _ ] => go'
       | _ => fail "No clauses for the match"
       end).

Ltac remove_id_in_goal :=
  let rec go' :=
     lazymatch goal with
      | [ |- context[(eq_id_dec ?x ?x)] ] => rewrite eq_id; go'
      | [ |- context[(eq_id_dec ?x ?y)] ] => 
        let H' := fresh in (
          assert (H' : x <> y) by discriminate;
          rewrite (@neq_id _ x y _ _ H'); clear H'); go'
      | _ => idtac                                                                 
      end
    in (lazymatch goal with
       | [ |- context[(eq_id_dec _ _)] ] => go'
       | _ => fail "No clauses for the match"
       end).

Ltac remove_ids :=
  let rec go' :=
      lazymatch goal with
      | [H: context[(eq_id_dec ?x ?x)] |- _ ] => 
        rewrite eq_id in H; go'
      | [H: context[(eq_id_dec ?x ?y)] |- _ ] => 
        let H' := fresh in (
          assert (H' : x <> y) by discriminate;
          rewrite (@neq_id _ x y _ _ H') in H; clear H');go'
      | [ |- context[(eq_id_dec ?x ?x)] ]     => 
        rewrite eq_id; go'
      | [ |- context[(eq_id_dec ?x ?y)] ]     => 
        let H' := fresh in (
          assert (H' : x <> y) by discriminate;
          rewrite (@neq_id _ x y _ _ H'); clear H'); go'
      | _ => idtac                                                                 
      end
   in (lazymatch goal with
      | [                            |- context[(eq_id_dec _ _)] ] => go'
      | [H: context[(eq_id_dec _ _)] |- _                        ] => go'
      | _ => fail "No clauses for the match"
       end).

(** ** Hiding hypotheses 
        This is adapted from LibTactics.v in the SF library. *)

Definition ltac_some (T:Type) (x:T) := x.

Notation "'Some_T'" := (@ltac_some _ _).

Lemma ltac_some_Term : forall (x:Type),
                         x = (@ltac_some _ x).
Proof. auto. Qed.

Lemma ltac_some_Hide : forall (x:Type),
                       x -> (@ltac_some _ x).
Proof. auto. Qed.

Lemma ltac_some_Show : forall (x:Type),
                      (@ltac_some _ x) -> x.
Proof. auto. Qed.  

Tactic Notation "hide_term" constr(X) :=
  change X with (@ltac_some _ X).
Tactic Notation "show_term" constr(X) :=
  change (@ltac_some _ X) with X.
Tactic Notation "show_term" :=
  unfold ltac_some.
Tactic Notation "hide_term" constr(X) "in" hyp(H) :=
  change X with (@ltac_some _ X) in H.
Tactic Notation "show_term" constr(X) "in" hyp(H) :=
  change (@ltac_some _ X) with X in H.
Tactic Notation "show_term" "in" hyp(H) :=
  unfold ltac_some in H.
Tactic Notation "hide" "hyp" hyp(H) :=
  apply ltac_some_Hide in H.
Tactic Notation "show" "hyp" hyp(H) :=
  apply ltac_some_Show in H.  

Tactic Notation "show" "all" "hyps" :=
  repeat (match goal with
              H: @ltac_some _ _ |- _ => show hyp H
          end).

Ltac remove_duplicate :=
  match goal with
    | [ H1 : ?A |- _ ] =>
      match goal with
        | [ H2 : ?B |- _ ] =>
          match H1 with
            | H2 => fail 2
            | _  => unify A B ; (clear H2 || clear H1)
          end
      end
  end.

Ltac remove_duplicates :=
     repeat (match goal with
                 | [ H1 : ?A |- _ ] =>
                 match goal with
                     | [ H2 : ?B |- _ ] =>
                     match H1 with
                         | H2 => fail 2
                         | _  => unify A B ; (clear H2 || clear H1)
                     end
                 end
             end).

Ltac gen_dep E :=
     let go E := (generalize dependent E) in
         match E with
         | (?X1, ?X2, ?X3, ?X4, ?X5, ?X6, ?X7, ?X8, ?X9, ?X10) => 
           go X10;go X9; go X8; go X7; go X6; go X5; go X4; go X3; go X2; go X1
         | (?X1, ?X2, ?X3, ?X4, ?X5, ?X6, ?X7, ?X8, ?X9)       => 
           go X9; go X8; go X7; go X6; go X5; go X4; go X3; go X2; go X1
         | (?X1, ?X2, ?X3, ?X4, ?X5, ?X6, ?X7, ?X8)            => 
           go X8; go X7; go X6; go X5; go X4; go X3; go X2; go X1
         | (?X1, ?X2, ?X3, ?X4, ?X5, ?X6, ?X7)                 => 
           go X7; go X6; go X5; go X4; go X3; go X2; go X1
         | (?X1, ?X2, ?X3, ?X4, ?X5, ?X6)                      => 
           go X6; go X5; go X4; go X3; go X2; go X1
         | (?X1, ?X2, ?X3, ?X4, ?X5)                           => 
           go X5; go X4; go X3; go X2; go X1
         | (?X1, ?X2, ?X3, ?X4)                                => 
           go X4; go X3; go X2; go X1
         | (?X1, ?X2, ?X3)                                     => 
           go X3; go X2; go X1
         | (?X1, ?X2)                                          => 
           go X2; go X1
         | ?X1                                                 => 
           go X1
         | _                                                   => idtac
         end. 

Tactic Notation "generalize" "dependent" ident(X1) := 
                 gen_dep X1.
Tactic Notation "generalize" "dependent" ident(X1) ident(X2) :=
                 gen_dep (X1,X2).
Tactic Notation "generalize" "dependent" ident(X1) ident(X2) ident(X3) :=
                 gen_dep (X1,X2,X3).
Tactic Notation "generalize" "dependent" ident(X1) ident(X2) ident(X3) ident(X4) :=
                 gen_dep (X1,X2,X3,X4).
Tactic Notation "generalize" "dependent" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
                 gen_dep (X1,X2,X3,X4,X5).
Tactic Notation "generalize" "dependent" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) ident(X6) :=
                 gen_dep (X1,X2,X3,X4,X5,X6).
Tactic Notation "generalize" "dependent" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) :=
                 gen_dep (X1,X2,X3,X4,X5,X6,X7).
Tactic Notation "generalize" "dependent" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) ident(X8) :=
                 gen_dep (X1,X2,X3,X4,X5,X6,X7,X8).
Tactic Notation "generalize" "dependent" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) ident(X8) ident(X9) :=
                 gen_dep (X1,X2,X3,X4,X5,X6,X7,X8,X9).
Tactic Notation "generalize" "dependent" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) ident(X8) ident(X9) ident(X10) :=
                 gen_dep (X1,X2,X3,X4,X5,X6,X7,X8,X9,X10).



Require Import Eqdep Omega.

Set Implicit Arguments.


Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

Ltac simplHyp invOne :=
  let invert H F :=
    inList F invOne;
     (inversion H; fail)
     || (inversion H; [idtac]; clear H; try subst) in

  match goal with
    | [ H : ex _ |- _ ] => destruct H
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (assert (X = Y); [ assumption | fail 1 ])
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F _ |- _ ] => invert H F
    | [ H : ?F _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ _ |- _ ] => invert H F
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.

Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
Ltac rewriter := autorewrite with core in *; rewriterP.

Hint Rewrite app_ass.

Definition done (T : Type) (x : T) := True.

Ltac inster e trace :=
  match type of e with
    | forall x : _, _ =>
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
     match trace with
        | (_, _) =>
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              fail 1
            | _ =>
              let T := type of e in
                match type of T with
                  | Prop =>
                    generalize e; intro;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.

Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

Require Import JMeq.

Ltac crush' lemmas invOne :=
  let sintuition := simpl in *; intuition; try subst;
    repeat (simplHyp invOne; intuition; try subst); try congruence in
  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] =>
                match P with
                  | context[JMeq] => fail 1 
                  | _ => rewrite H by crush' lemmas invOne
                end
            end; autorewrite with core in *) in
    (sintuition; rewriter;
      match lemmas with
        | false => idtac
        | _ =>
          repeat ((app ltac:(fun L => inster L L) lemmas
            || appHyps ltac:(fun L => inster L L));
          repeat (simplHyp invOne; intuition)); un_done
      end;
      sintuition; rewriter; sintuition;
      try omega; try (elimtype False; omega)).

Ltac crush := crush' false fail.

Require Import Program.Equality.

Ltac dep_destruct E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
          end.

Ltac clear_all :=
  repeat match goal with
           | [ H : _ |- _ ] => clear H
         end.

Ltac guess v H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T); [
                     solve [ eauto 6 ]
                     | specialize (H H'); clear H' ])
                 || fail 1
               | _ =>
                 specialize (H v)
                 || let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

Ltac guessKeep v H :=
  let H' := fresh "H'" in
    generalize H; intro H'; guess v H'.

Ltac my_crush' :=
  crush;
  repeat (match goal with
            | [ H : _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H
          end; crush).

Section MiscArith.

Theorem strong_induction : forall (P : nat -> Prop),
                             (forall n : nat,
                                (forall m, m < n -> P m) -> P n) ->
                             (forall n : nat, P n).
Proof.
 assert (Peano_aux_1 : forall (P : nat -> Prop),
                       (forall n : nat, (forall m : nat, m < n -> P m) -> P n) ->
                                 (forall n : nat,
                                    (forall m : nat, ((m < n) -> P m)))).
        induction n as [ | n' IHn' ]; [intros m H1; inversion H1 |]. 
        intros.
        assert (H_dec: m < n' \/ m = n') by omega.
        inversion H_dec.
        apply IHn'; auto. subst.
        apply (H n'); auto.
 assert (Peano_aux_2 : forall (P : nat -> Prop),
                       (forall n : nat, (forall m : nat, ((m < n) -> P m))) ->
                         (forall n : nat, P n))by (intros P H n; eauto). 
  intros.
  apply Peano_aux_2.
  apply Peano_aux_1; auto. 
Qed.

Lemma strong_induction' : forall (P: nat -> Prop),
                               (forall n : nat, (forall m : nat, m < n -> P m) -> P n) ->
                               (forall n : nat, P n).
Proof.
  intros ? H.
  assert (H_aux : forall n : nat, 
                  (forall m : nat, m < n -> P m)) by
           (induction n as [ |n' IHn']; intros; [omegaContradiction
                                                |apply H; intros; apply IHn'; omega]).
  intro n; apply H_aux with (S n); omega.
Qed.

Lemma le_le_max_l : forall i j k,
                    i <= j -> 
                    i <= max j k.
Proof. firstorder using le_trans. 
Qed. 

Hint Resolve le_le_max_l : arith.

Lemma le_le_max_r : forall i j k,
                    i <= j -> 
                    i <= max k j.
Proof. intros; rewrite <- max_comm; firstorder. 
Qed. 

Hint Resolve le_le_max_r : arith.

Lemma le_spec : forall i j,
                   i <= j -> 
                   exists k, i + k = j.
Proof. intros; eexists; firstorder.
Qed.

Hint Resolve le_spec : arith.

Lemma SS_le_eq_SS :
      forall i, (exists j, S (S j) <= i) -> (exists k, i = S (S k)).
Proof. intros i E; 
       destruct E as [j Hj];
       destruct (@le_spec (S (S j)) i Hj) as [k Hk]; 
       simpl in *; exists (j + k); intuition.
Qed.

End MiscArith.