From Stdlib Require Import Reals.Reals.
From Equations Require Import Equations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import order ssralg ssrnum boolp classical_sets.
From mathcomp Require Import cardinality reals Rstruct_topology.
Import preorder.Order Order.TTheory Num.Theory GRing.Theory.
From HOLLight Require Export HOL.mappings Library.analysis Library.rstc.
Require Export HOLLight.Examples.multiwf.
From HB Require Import structures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(*****************************************************************************)
(* Miscelaneous *)
(*****************************************************************************)

Fixpoint seq_Union {A : Type'} (s : seq (set A)) : A -> Prop :=
  match s with
  | [::] => set0
  | S0::s => S0 `|` (seq_Union s) end.

Lemma LIST_UNION_def {_184792 : Type'} : seq_Union = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) -> (seq (_184792 -> Prop)) -> _184792 -> Prop) (fun LIST_UNION' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) -> (seq (_184792 -> Prop)) -> _184792 -> Prop => forall _204636 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))), ((LIST_UNION' _204636 (@nil (_184792 -> Prop))) = (@set0 _184792)) /\ (forall h : _184792 -> Prop, forall t : seq (_184792 -> Prop), (LIST_UNION' _204636 (@cons (_184792 -> Prop) h t)) = (@setU _184792 h (LIST_UNION' _204636 t)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))))))))).
Proof. by total_align. Qed.

(*****************************************************************************)
(* Aligning the type of first order terms *)
(*****************************************************************************)

Unset Elimination Schemes.
Inductive term : Set := V of nat | Fn of nat & seq term.
Set Elimination Schemes.

HB.instance Definition _ := is_Type' (V 0).

Unset Implicit Arguments.

(* defining induction principles and tactics *)
Section term_rect.

Variables
  (P : term -> Type)
  (Q : seq term -> Type)
  (H1 : forall x, P (V x))
  (H2 : forall n s, Q s -> P (Fn n s))
  (H3 : Q nil)
  (H4 : forall t s, P t -> Q s -> Q (t :: s)).

Fixpoint term_rect t : P t :=
  match t as t return P t with
    | V x => H1 x
    | Fn n s => H2 n _
      ((fix ts_rect (s : seq term) : Q s :=
        match s with
          | [::] => H3
          | t'::s' => H4 _ _ (term_rect t') (ts_rect s')
        end) s)
  end.

Fixpoint ts_rect s : Q s :=
  match s with
  | [::] => H3
  | t::s => H4 t s (term_rect t) (ts_rect s) end.

End term_rect.

Definition term_ind_full (P : term -> Prop) (Q : seq term -> Prop) :=
  term_rect P Q.

Definition ts_ind (P : term -> Prop) (Q : seq term -> Prop) :=
  ts_rect P Q.

Definition term_ts_ind P Q H1 H2 H3 H4 :=
  conj (term_ind_full P Q H1 H2 H3 H4) (ts_ind P Q H1 H2 H3 H4).

Program Definition term_ind : forall (P : term -> Prop),
       (forall n, P (V n)) ->
       (forall n s, all P s -> P (Fn n s)) ->
       forall t, P t :=
  (fun P Hv HFn => term_ind_full P (all P) Hv HFn (all_nil _) _).
Next Obligation.
  by move=> P _ _ t s Pt /= -> ; rewrite (asboolT Pt).
Qed.

Definition term_rec (P : term -> Set) (Q : seq term -> Set) := term_rect P Q.

Set Implicit Arguments.

Register Scheme term_rect as rect_nodep for term.
Register Scheme term_rec as rec_nodep for term.
Register Scheme term_ind as ind_nodep for term.

(* _dest_term and _dest_tseq are codefined but Rocq doesn't accept it so it is split in two with
   a fix inside. *)
Fixpoint _dest_term t : recspace nat :=
  match t with
  | V n => CONSTR 0 n []_rec
  | Fn n s => let fix _dest_ts s := match s with
    | [::] => CONSTR 2 (ε (fun _ => True)) []_rec
    | t::s => CONSTR 3 (ε (fun _ => True))
      [_dest_term t ; _dest_ts s]_rec end
    in CONSTR 1 n [_dest_ts s]_rec
  end.

Fixpoint _dest_tseq s : recspace nat :=
  match s with
  | [::] => CONSTR 2 (ε (fun _ => True)) []_rec
  | t::s => CONSTR 3 (ε (fun _ => True))
    [_dest_term t ; _dest_tseq s]_rec end.

Definition _mk_term := finv _dest_term.
Definition _mk_tseq := finv _dest_tseq.

Lemma _dest_term_ts_inj : (forall t t', _dest_term t = _dest_term t' -> t = t')
  /\ (forall s s', _dest_tseq s = _dest_tseq s' -> s = s').
Proof.
  apply term_ts_ind.
  intros n t. induction t;simpl;inversion 1. reflexivity.
  - induction s ; intros H t' ; induction t' using term_ind ; simpl ; inversion 1.
    induction s. 3 : induction s0. reflexivity.
    1,2 : rewrite FCONS_inj in H4 ; destruct H4 as (H4 , _) ; inversion H4.
    f_equal. apply H. now rewrite FCONS_inj in H4.
  - induction s'. reflexivity. simpl. inversion 1.
  - induction s'; simpl ; inversion 1. do 2 rewrite FCONS_inj in H3. f_equal.
    now apply H. now apply H0.
Qed.

Lemma _mk_dest_term : forall t, (_mk_term (_dest_term t)) = t.
Proof.
  finv_inv_l. exact (proj1 _dest_term_ts_inj).
Qed.

Lemma _mk_dest_tseq : forall s, (_mk_tseq  (_dest_tseq  s)) = s.
Proof.
  finv_inv_l. exact (proj2 _dest_term_ts_inj).
Qed.

Definition term_ts_pred term' tseq' :=
    ((forall a0' : recspace nat,
      ((exists a : nat, a0' = ((fun a' : nat => @CONSTR nat (NUMERAL 0) a' (fun n : nat => @BOTTOM nat)) a)) \/
        (exists a0 : nat, exists a1 : recspace nat, (a0' = ((fun a0'' : nat => fun a1' : recspace nat =>
          @CONSTR nat (S (NUMERAL 0)) a0'' (@FCONS (recspace nat) a1' (fun n : nat => @BOTTOM nat))) a0 a1)) /\
            (tseq' a1))) -> term' a0') /\ 
              (forall a1' : recspace nat, ((a1' = (@CONSTR nat (S (S (NUMERAL 0)))
              (@ε nat (fun v : nat => True)) (fun n : nat => @BOTTOM nat))) \/
                (exists a0 : recspace nat, exists a1 : recspace nat,
                (a1' = ((fun a0'' : recspace nat => fun a1'' : recspace nat =>
                @CONSTR nat (S (S (S (NUMERAL 0)))) (@ε nat (fun v : nat => True))
                (@FCONS (recspace nat) a0'' (@FCONS (recspace nat) a1'' (fun n : nat => @BOTTOM nat)))) a0 a1)) /\
                  ((term' a0) /\ (tseq' a1)))) -> tseq' a1')).

Lemma _dest_mk_term_ts0 : forall P P' : recspace nat -> Prop, term_ts_pred P P' ->
  (forall t, P (_dest_term t)) /\ forall s, P' (_dest_tseq s).
Proof.
  intros P P' H. apply term_ts_ind.
  - intro n. apply H. left. now exists n.
  - intros n s IHs. apply H. right. exists n. now exists (_dest_tseq s).
  - apply H. now left.
  - intros t s IHt IHs. apply H. right. by exist (_dest_term t) (_dest_tseq s).
Qed.

Lemma _dest_mk_tseq : forall r, (fun r' => forall P P', term_ts_pred P P' -> P' r') r =
  (_dest_tseq (_mk_tseq r) = r).
Proof.
  intro r.
  let H := fresh in
  let x := fresh "x" in
  apply finv_inv_r ; intro H ;
  [ apply (H (fun y => exists x, _dest_term x = y)) ;
    clear H ; split ; intros x H ;
    firstorder ; rewrite H ;
    clear H ; simpl in * ; blindrewrite_rev ;
    by unshelve eexists ; first econstructor
  | destruct H as (x,H) ; rewrite <- H ; clear H ;
    intros P P' H ; exact (proj2 (_dest_mk_term_ts0 H) x) ].
Qed.

Lemma _dest_mk_term : forall r, (fun r' => forall P P', term_ts_pred P P' -> P r') r =
  (_dest_term (_mk_term r) = r).
Proof.
  intro r.
  let H := fresh in
  let x := fresh "x" in
  apply finv_inv_r ; intro H ;
  [ apply (H (fun y => exists x, _dest_term x = y) (fun y => exists x, _dest_tseq x = y)) ;
    clear H ; split ; intros x H ;
    firstorder ; rewrite H ;
    clear H ; simpl in * ; blindrewrite_rev ;
    by unshelve eexists ; first econstructor
  | destruct H as (x,H) ; rewrite <- H ; clear H ;
    intros P P' H ; exact (proj1 (_dest_mk_term_ts0 H) x) ].
Qed.

Lemma V_def : V = (fun a : nat => _mk_term ((fun a' : nat => @CONSTR nat (NUMERAL 0) a' (fun n : nat => @BOTTOM nat)) a)).
Proof. constr_align _mk_dest_term. Qed.

Lemma Fn_def_internal : Fn = (fun a0 : nat => fun a1 : seq term => _mk_term ((fun a0' : nat => fun a1' : recspace nat => @CONSTR nat (S (NUMERAL 0)) a0' (@FCONS (recspace nat) a1' (fun n : nat => @BOTTOM nat))) a0 (_dest_tseq a1))).
Proof. constr_align _mk_dest_term. Qed.

Definition tnil := Nil term.
Lemma tnil_def : tnil = (_mk_tseq (@CONSTR nat (S (S (NUMERAL 0))) (@ε nat (fun v : nat => True)) (fun n : nat => @BOTTOM nat))).
Proof. constr_align _mk_dest_tseq. Qed.

Definition tcons := Cons term.

Lemma tcons_def : tcons = (fun a0 : term => fun a1 : seq term => _mk_tseq ((fun a0' : recspace nat => fun a1' : recspace nat => @CONSTR nat (S (S (S (NUMERAL 0)))) (@ε nat (fun v : nat => True)) (@FCONS (recspace nat) a0' (@FCONS (recspace nat) a1' (fun n : nat => @BOTTOM nat)))) (_dest_term a0) (_dest_tseq a1))).
Proof. constr_align _mk_dest_tseq. Qed.

Lemma Fn_def : Fn = (fun a0 : nat => fun a1 : seq term => Fn a0 (@ε ((seq term) -> seq term) (fun fn : (seq term) -> seq term => ((fn (@nil term)) = tnil) /\ (forall a0' : term, forall a1' : seq term, (fn (@cons term a0' a1')) = (tcons a0' (fn a1')))) a1)).
Proof.
  ext=> t s. f_equal. rewrite-{1}/(id s). apply (f_equal (fun f => f s)).
  align_ε ; first by [].
  by move=> f' H H' ; full_destruct ; ext ; elim => // a {}s ; rewrite H1=> <-.
Qed.

(*****************************************************************************)
(* tactics to align recursive functions on terms *)
(*****************************************************************************)

Ltac term_align1 := total_align1_general use_induction solve_total_align_with_lists.
Ltac term_align2 := total_align2_general use_induction solve_total_align_with_lists.
Ltac term_align3 := total_align3_general use_induction solve_total_align_with_lists.
Ltac term_align4 := total_align4_general use_induction solve_total_align_with_lists.
Ltac term_align5 := total_align5_general use_induction solve_total_align_with_lists.
Ltac term_align := total_align_general use_induction solve_total_align_with_lists.

(*****************************************************************************)
(* first order formulae *)
(*****************************************************************************)

Inductive form := 
| FFalse : form
| Atom : nat -> seq term -> form
| FImp : form -> form -> form
| FAll : nat -> form -> form.

HB.instance Definition _ := is_Type' FFalse.

Fixpoint _dest_form (f : form) : recspace (nat * (seq term)) :=
match f with
| FFalse => CONSTR 0 (ε (fun n => True) , ε (fun s => True)) []_rec
| Atom n s => CONSTR 1 (n,s) []_rec
| FImp f f' => CONSTR 2 (ε (fun n => True) , ε (fun s => True))
  [_dest_form f ; _dest_form f']_rec
| FAll n f => CONSTR 3 (n , ε (fun s => True))
  [_dest_form f]_rec end.

Definition _mk_form := finv _dest_form.

Lemma _mk_dest_form : forall (a : form), (_mk_form (_dest_form a)) = a.
Proof. _mk_dest_inductive. Qed.

Lemma _dest_mk_form : forall (r : recspace (prod nat (seq term))), ((fun a : recspace (prod nat (seq term)) => forall form' : (recspace (prod nat (seq term))) -> Prop, (forall a' : recspace (prod nat (seq term)), ((a' = (@CONSTR (prod nat (seq term)) (NUMERAL 0) (@pair nat (seq term) (@ε nat (fun v : nat => True)) (@ε (seq term) (fun v : seq term => True))) (fun n : nat => @BOTTOM (prod nat (seq term))))) \/ ((exists a0 : nat, exists a1 : seq term, a' = ((fun a0' : nat => fun a1' : seq term => @CONSTR (prod nat (seq term)) (S (NUMERAL 0)) (@pair nat (seq term) a0' a1') (fun n : nat => @BOTTOM (prod nat (seq term)))) a0 a1)) \/ ((exists a0 : recspace (prod nat (seq term)), exists a1 : recspace (prod nat (seq term)), (a' = ((fun a0' : recspace (prod nat (seq term)) => fun a1' : recspace (prod nat (seq term)) => @CONSTR (prod nat (seq term)) (S (S (NUMERAL 0))) (@pair nat (seq term) (@ε nat (fun v : nat => True)) (@ε (seq term) (fun v : seq term => True))) (@FCONS (recspace (prod nat (seq term))) a0' (@FCONS (recspace (prod nat (seq term))) a1' (fun n : nat => @BOTTOM (prod nat (seq term)))))) a0 a1)) /\ ((form' a0) /\ (form' a1))) \/ (exists a0 : nat, exists a1 : recspace (prod nat (seq term)), (a' = ((fun a0' : nat => fun a1' : recspace (prod nat (seq term)) => @CONSTR (prod nat (seq term)) (S (S (S (NUMERAL 0)))) (@pair nat (seq term) a0' (@ε (seq term) (fun v : seq term => True))) (@FCONS (recspace (prod nat (seq term))) a1' (fun n : nat => @BOTTOM (prod nat (seq term))))) a0 a1)) /\ (form' a1))))) -> form' a') -> form' a) r) = ((_dest_form (_mk_form r)) = r).
Proof. by _dest_mk_inductive. Qed.

Lemma FFalse_def : FFalse = (_mk_form (@CONSTR (prod nat (seq term)) (NUMERAL 0) (@pair nat (seq term) (@ε nat (fun v : nat => True)) (@ε (seq term) (fun v : seq term => True))) (fun n : nat => @BOTTOM (prod nat (seq term))))).
Proof. constr_align _mk_dest_form. Qed.

Lemma Atom_def : Atom = (fun a0 : nat => fun a1 : seq term => _mk_form ((fun a0' : nat => fun a1' : seq term => @CONSTR (prod nat (seq term)) (S (NUMERAL 0)) (@pair nat (seq term) a0' a1') (fun n : nat => @BOTTOM (prod nat (seq term)))) a0 a1)).
Proof. constr_align _mk_dest_form. Qed.

Lemma FImp_def : FImp = (fun a0 : form => fun a1 : form => _mk_form ((fun a0' : recspace (prod nat (seq term)) => fun a1' : recspace (prod nat (seq term)) => @CONSTR (prod nat (seq term)) (S (S (NUMERAL 0))) (@pair nat (seq term) (@ε nat (fun v : nat => True)) (@ε (seq term) (fun v : seq term => True))) (@FCONS (recspace (prod nat (seq term))) a0' (@FCONS (recspace (prod nat (seq term))) a1' (fun n : nat => @BOTTOM (prod nat (seq term)))))) (_dest_form a0) (_dest_form a1))).
Proof. constr_align _mk_dest_form. Qed.

Lemma FAll_def : FAll = (fun a0 : nat => fun a1 : form => _mk_form ((fun a0' : nat => fun a1' : recspace (prod nat (seq term)) => @CONSTR (prod nat (seq term)) (S (S (S (NUMERAL 0)))) (@pair nat (seq term) a0' (@ε (seq term) (fun v : seq term => True))) (@FCONS (recspace (prod nat (seq term))) a1' (fun n : nat => @BOTTOM (prod nat (seq term))))) a0 (_dest_form a1))).
Proof. constr_align _mk_dest_form. Qed.

Definition Not f := FImp f FFalse.
Lemma Not_def : Not = (fun _204912 : form => FImp _204912 FFalse).
Proof. exact erefl. Qed.

Definition FTrue : form := Not FFalse.
Lemma FTrue_def : FTrue = (Not FFalse).
Proof. exact erefl. Qed.

Definition FOr f f' := FImp (FImp f f') f'.
Lemma FOr_def : FOr = (fun _204917 : form => fun _204918 : form => FImp (FImp _204917 _204918) _204918).
Proof. exact erefl. Qed.

Definition FAnd f f' := Not (FOr (Not f) (Not f')).
Lemma FAnd_def : FAnd = (fun _204929 : form => fun _204930 : form => Not (FOr (Not _204929) (Not _204930))).
Proof. exact erefl. Qed.

Definition FEquiv f f' := FAnd (FImp f f') (FImp f' f).
Lemma FEquiv_def : FEquiv = (fun _204941 : form => fun _204942 : form => FAnd (FImp _204941 _204942) (FImp _204942 _204941)).
Proof. exact erefl. Qed.

Definition FEx n f := Not (FAll n (Not f)).
Lemma FEx_def : FEx = (fun _204953 : nat => fun _204954 : form => Not (FAll _204953 (Not _204954))).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* Functions on terms and formulae. *)
(*****************************************************************************)

Fixpoint functions_term t : set (nat * nat) :=
  match t with
  | V _ => set0
  | Fn n s => (n , size s) |` (seq_Union (map (functions_term) s)) end.

Lemma functions_term_def : functions_term = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))))) -> term -> (prod nat nat) -> Prop) (fun functions_term' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))))) -> term -> (prod nat nat) -> Prop => forall _204968 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))), (forall v : nat, (functions_term' _204968 (V v)) = (@set0 (prod nat nat))) /\ (forall f : nat, forall l : seq term, (functions_term' _204968 (Fn f l)) = (@INSERT (prod nat nat) (@pair nat nat f (@size term l)) (@seq_Union (prod nat nat) (@map term ((prod nat nat) -> Prop) (functions_term' _204968) l))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))))))))))))))))).
Proof. by term_align. Qed.

Fixpoint functions_form f : set (nat * nat) :=
  match f with
  | FFalse => set0
  | Atom _ s => seq_Union (map functions_term s)
  | FImp f f' => (functions_form f) `|` (functions_form f')
  | FAll _ f => functions_form f end.

Lemma functions_form_def : functions_form = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))))) -> form -> (prod nat nat) -> Prop) (fun functions_form' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))))) -> form -> (prod nat nat) -> Prop => forall _204976 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))), ((functions_form' _204976 FFalse) = (@set0 (prod nat nat))) /\ ((forall a : nat, forall l : seq term, (functions_form' _204976 (Atom a l)) = (@seq_Union (prod nat nat) (@map term ((prod nat nat) -> Prop) functions_term l))) /\ ((forall p : form, forall q : form, (functions_form' _204976 (FImp p q)) = (@setU (prod nat nat) (functions_form' _204976 p) (functions_form' _204976 q))) /\ (forall x : nat, forall p : form, (functions_form' _204976 (FAll x p)) = (functions_form' _204976 p))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))))))))))))))))).
Proof. by total_align. Qed.

Fixpoint predicates_form f : set (nat * nat) :=
  match f with
  | FFalse => set0
  | Atom a s => [set (a , size s)]
  | FImp f f' => (predicates_form f) `|` (predicates_form f')
  | FAll _ f => predicates_form f end.

Lemma predicates_form_def : predicates_form = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))))) -> form -> (prod nat nat) -> Prop) (fun predicates_form' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))))) -> form -> (prod nat nat) -> Prop => forall _204984 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))))), ((predicates_form' _204984 FFalse) = (@set0 (prod nat nat))) /\ ((forall a : nat, forall l : seq term, (predicates_form' _204984 (Atom a l)) = (@INSERT (prod nat nat) (@pair nat nat a (@size term l)) (@set0 (prod nat nat)))) /\ ((forall p : form, forall q : form, (predicates_form' _204984 (FImp p q)) = (@setU (prod nat nat) (predicates_form' _204984 p) (predicates_form' _204984 q))) /\ (forall x : nat, forall p : form, (predicates_form' _204984 (FAll x p)) = (predicates_form' _204984 p))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0))))))))))))))))))))))).
Proof.
  by total_align => * /3=.
Qed.

Definition functions (s : set form) := \bigcup_(x in s) (functions_form x).

Lemma functions_def : functions = (fun _204985 : form -> Prop => @UNIONS (prod nat nat) (@GSPEC ((prod nat nat) -> Prop) (fun GEN_PVAR_444 : (prod nat nat) -> Prop => exists f : form, @SETSPEC ((prod nat nat) -> Prop) GEN_PVAR_444 (@IN form f _204985) (functions_form f)))).
Proof.
  by funext => * /3= ; rewrite bigcup_image.
Qed.

Definition predicates (s : set form) := \bigcup_(x in s) (predicates_form x).

Lemma predicates_def : predicates = (fun _204990 : form -> Prop => @UNIONS (prod nat nat) (@GSPEC ((prod nat nat) -> Prop) (fun GEN_PVAR_445 : (prod nat nat) -> Prop => exists f : form, @SETSPEC ((prod nat nat) -> Prop) GEN_PVAR_445 (@IN form f _204990) (predicates_form f)))).
Proof.
  by funext => * /3= ; rewrite bigcup_image.
Qed.

Definition language (s : form -> Prop) := (functions s, predicates s).

Lemma language_def : language = (fun _204995 : form -> Prop => @pair ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) (functions _204995) (predicates _204995)).
Proof. exact erefl. Qed.

Definition Structure (A : Type') := prod (A -> Prop) (prod (nat -> (seq A) -> A)  (nat -> (seq A) -> Prop)).

Definition Dom {A : Type'} (M : Structure A) := fst M.

Lemma Dom_def {A : Type'} : (@Dom A) = (fun _205074 : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) => @fst (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) _205074).
Proof. exact erefl. Qed.

Definition Fun {A : Type'} (M : Structure A) := fst (snd M).

Lemma Fun_def {A : Type'} : (@Fun A) = (fun _205087 : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) => @fst (nat -> (seq A) -> A) (nat -> (seq A) -> Prop) (@snd (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) _205087)).
Proof. exact erefl. Qed.

Definition Pred {A : Type'} (M : Structure A) := snd (snd M).

Lemma Pred_def {A : Type'} : (@Pred A) = (fun _205100 : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) => @snd (nat -> (seq A) -> A) (nat -> (seq A) -> Prop) (@snd (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) _205100)).
Proof. exact erefl. Qed.

Fixpoint free_variables_term t : nat -> Prop :=
  match t with
  | V n => [set n]
  | Fn _ s => seq_Union (map free_variables_term s) end.

Lemma FVT_def : free_variables_term = (@ε ((prod nat (prod nat nat)) -> term -> nat -> Prop) (fun FVT' : (prod nat (prod nat nat)) -> term -> nat -> Prop => forall _205116 : prod nat (prod nat nat), (forall x : nat, (FVT' _205116 (V x)) = (@INSERT nat x (@set0 nat))) /\ (forall f : nat, forall l : seq term, (FVT' _205116 (Fn f l)) = (@seq_Union nat (@map term (nat -> Prop) (FVT' _205116) l)))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof.
  by term_align => * /3=.
Qed.

Fixpoint free_variables f : nat -> Prop := 
  match f with
  | FFalse => set0
  | Atom _ s => seq_Union (map free_variables_term s)
  | FImp f f' => free_variables f `|` free_variables f'
  | FAll n f => free_variables f `\ n end.

Lemma FV_def : free_variables = (@ε ((prod nat nat) -> form -> nat -> Prop) (fun FV' : (prod nat nat) -> form -> nat -> Prop => forall _205124 : prod nat nat, ((FV' _205124 FFalse) = (@set0 nat)) /\ ((forall a : nat, forall l : seq term, (FV' _205124 (Atom a l)) = (@seq_Union nat (@map term (nat -> Prop) free_variables_term l))) /\ ((forall p : form, forall q : form, (FV' _205124 (FImp p q)) = (@setU nat (FV' _205124 p) (FV' _205124 q))) /\ (forall x : nat, forall p : form, (FV' _205124 (FAll x p)) = (@DELETE nat (FV' _205124 p) x))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))).
Proof. by total_align. Qed.

Fixpoint bound_variables f : nat -> Prop :=
  match f with
  | FFalse | Atom _ _ => set0
  | FImp f f' => bound_variables f `|` bound_variables f'
  | FAll n f => n |` bound_variables f end.

Lemma BV_def : bound_variables = (@ε ((prod nat nat) -> form -> nat -> Prop) (fun BV' : (prod nat nat) -> form -> nat -> Prop => forall _205132 : prod nat nat, ((BV' _205132 FFalse) = (@set0 nat)) /\ ((forall a : nat, forall l : seq term, (BV' _205132 (Atom a l)) = (@set0 nat)) /\ ((forall p : form, forall q : form, (BV' _205132 (FImp p q)) = (@setU nat (BV' _205132 p) (BV' _205132 q))) /\ (forall x : nat, forall p : form, (BV' _205132 (FAll x p)) = (@INSERT nat x (BV' _205132 p)))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))).
Proof. by total_align. Qed.

Definition valmod {B A : Type'} (c : prod A B) (f : A -> B) (a : A) : B :=
  if a = fst c then snd c else f a. 

Lemma valmod_def {_185561 _185570 : Type'} : (@valmod _185561 _185570) = (fun _205133 : prod _185570 _185561 => fun _205134 : _185570 -> _185561 => fun y : _185570 => @COND _185561 (y = (@fst _185570 _185561 _205133)) (@snd _185570 _185561 _205133) (_205134 y)).
Proof. exact erefl. Qed.

Definition valuation {A : Type'} (M : Structure A) : (nat -> A) -> Prop :=
  fun v => forall n, Dom M (v n).

Lemma valuation_def {_185712 : Type'} : (@valuation _185712) = (fun _205170 : prod (_185712 -> Prop) (prod (nat -> (seq _185712) -> _185712) (nat -> (seq _185712) -> Prop)) => fun _205171 : nat -> _185712 => forall x : nat, @IN _185712 (_205171 x) (@Dom _185712 _205170)).
Proof. by funext => * /3=. Qed.

Fixpoint termval {A : Type'} (M : Structure A) (v : nat -> A) (t : term) : A :=
  match t with
  | V n => v n
  | Fn n l => Fun M n (map (termval M v) l) end.

Lemma termval_def {_185808 : Type'} : (@termval _185808) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod (_185808 -> Prop) (prod (nat -> (seq _185808) -> _185808) (nat -> (seq _185808) -> Prop))) -> (nat -> _185808) -> term -> _185808) (fun termval' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod (_185808 -> Prop) (prod (nat -> (seq _185808) -> _185808) (nat -> (seq _185808) -> Prop))) -> (nat -> _185808) -> term -> _185808 => forall _205201 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), forall M : prod (_185808 -> Prop) (prod (nat -> (seq _185808) -> _185808) (nat -> (seq _185808) -> Prop)), forall v : nat -> _185808, (forall x : nat, (termval' _205201 M v (V x)) = (v x)) /\ (forall f : nat, forall l : seq term, (termval' _205201 M v (Fn f l)) = (@Fun _185808 M f (@map term _185808 (termval' _205201 M v) l)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0))))))))))))))).
Proof.
  (* Defined using a specific macro new_nested_recursive_definition unique
     to the Logic library, so total_align doesn't work. *)
  align_ε. easy.
  intros f' H H'. ext => M v t. destruct (H M v) as (HV , HFn).
  destruct (H' M v) as (HV' , HFn').
  induction t. now rewrite HV HV'.
  rewrite HFn HFn'. f_equal. now apply map_ALLE.
  Qed.

Fixpoint holds {A : Type'} (M : Structure A) (v : nat -> A) (f : form) : Prop :=
  match f with
  | FFalse => False
  | Atom n s => Pred M n (map (termval M v) s)
  | FImp f f' => holds M v f -> holds M v f'
  | FAll n f => forall a : A, IN a (Dom M) -> holds M (valmod (n , a) v) f end.

Lemma holds_def {_185905 : Type'} : (@holds _185905) = (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> (prod (_185905 -> Prop) (prod (nat -> (seq _185905) -> _185905) (nat -> (seq _185905) -> Prop))) -> (nat -> _185905) -> form -> Prop) (fun holds' : (prod nat (prod nat (prod nat (prod nat nat)))) -> (prod (_185905 -> Prop) (prod (nat -> (seq _185905) -> _185905) (nat -> (seq _185905) -> Prop))) -> (nat -> _185905) -> form -> Prop => forall _205213 : prod nat (prod nat (prod nat (prod nat nat))), (forall M : prod (_185905 -> Prop) (prod (nat -> (seq _185905) -> _185905) (nat -> (seq _185905) -> Prop)), forall v : nat -> _185905, (holds' _205213 M v FFalse) = False) /\ ((forall M : prod (_185905 -> Prop) (prod (nat -> (seq _185905) -> _185905) (nat -> (seq _185905) -> Prop)), forall v : nat -> _185905, forall a : nat, forall l : seq term, (holds' _205213 M v (Atom a l)) = (@Pred _185905 M a (@map term _185905 (@termval _185905 M v) l))) /\ ((forall M : prod (_185905 -> Prop) (prod (nat -> (seq _185905) -> _185905) (nat -> (seq _185905) -> Prop)), forall v : nat -> _185905, forall p : form, forall q : form, (holds' _205213 M v (FImp p q)) = ((holds' _205213 M v p) -> holds' _205213 M v q)) /\ (forall M : prod (_185905 -> Prop) (prod (nat -> (seq _185905) -> _185905) (nat -> (seq _185905) -> Prop)), forall v : nat -> _185905, forall x : nat, forall p : form, (holds' _205213 M v (FAll x p)) = (forall a : _185905, (@IN _185905 a (@Dom _185905 M)) -> holds' _205213 M (@valmod _185905 nat (@pair nat _185905 x a) v) p))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))).
Proof.
  total_align3 => //. ext => H' a. 
  - rewrite <- IHform. exact (H' a).
  - rewrite IHform. exact (H' a).
Qed.

Definition hold {A : Type'} (M : Structure A) (v : nat -> A) (s : set form) :=
  subset s (holds M v).

Lemma hold_def {_185927 : Type'} : (@hold _185927) = (fun _205214 : prod (_185927 -> Prop) (prod (nat -> (seq _185927) -> _185927) (nat -> (seq _185927) -> Prop)) => fun _205215 : nat -> _185927 => fun _205216 : form -> Prop => forall p : form, (@IN form p _205216) -> @holds _185927 _205214 _205215 p).
Proof. by funext=> * /3=. Qed.

Definition satisfies {A : Type'} (M : Structure A) (s : set form) : Prop :=
  forall v f, (valuation M v /\ s f) -> holds M v f.

Lemma satisfies_def {_185947 : Type'} : (@satisfies _185947) = (fun _205235 : prod (_185947 -> Prop) (prod (nat -> (seq _185947) -> _185947) (nat -> (seq _185947) -> Prop)) => fun _205236 : form -> Prop => forall v : nat -> _185947, forall p : form, ((@valuation _185947 _205235 v) /\ (@IN form p _205236)) -> @holds _185947 _205235 v p).
Proof. by funext=> * /3=. Qed.

Definition satisfiable {A : Type'} (_ : set A) (s : set form) : Prop :=
  exists M : Structure A, (Dom M) <> set0 /\ satisfies M s.

Lemma satisfiable_def {A : Type'} : (@satisfiable A) = (fun _205939 : A -> Prop => fun _205940 : form -> Prop => exists M : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)), (~ ((@Dom A M) = (@set0 A))) /\ (@satisfies A M _205940)).
Proof. exact erefl. Qed.

Definition valid {A : Type'} (_ : set A) (s : set form) : Prop :=
  forall M : Structure A, satisfies M s.

Lemma valid_def {A : Type'} : (@valid A) = (fun _205951 : A -> Prop => fun _205952 : form -> Prop => forall M : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)), @satisfies A M _205952).
Proof. exact erefl. Qed.

Definition entails {A : Type'} (_ : set A) (s : set form) (f : form) : Prop :=
  forall (M : Structure A) v, hold M v s -> holds M v f.

Lemma entails_def {A : Type'} : (@entails A) = (fun _205963 : A -> Prop => fun _205964 : form -> Prop => fun _205965 : form => forall M : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)), forall v : nat -> A, (@hold A M v _205964) -> @holds A M v _205965).
Proof. exact erefl. Qed.

Definition equivalent {A : Type'} (_ : set A) (f f' : form) : Prop :=
  forall (M : Structure A) v, holds M v f = holds M v f'.

Lemma equivalent_def {A : Type'} : (@equivalent A) = (fun _205984 : A -> Prop => fun _205985 : form => fun _205986 : form => forall M : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)), forall v : nat -> A, (@holds A M v _205985) = (@holds A M v _205986)).
Proof. exact erefl. Qed.

Definition interpretation {A : Type'} (funpred : (prod ((prod nat nat) -> Prop) ((prod nat nat) -> Prop)))
  (M : Structure A) : Prop := forall (n : nat) (l : seq A),
  fst funpred (n , size l) -> all (Dom M) l
  -> Dom M (Fun M n l).

Lemma interpretation_def {_186534 : Type'} : (@interpretation _186534) = (fun _206005 : prod ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) => fun _206006 : prod (_186534 -> Prop) (prod (nat -> (seq _186534) -> _186534) (nat -> (seq _186534) -> Prop)) => forall f : nat, forall l : seq _186534, ((@IN (prod nat nat) (@pair nat nat f (@size _186534 l)) (@fst ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) _206005)) /\ (@ALL _186534 (fun x : _186534 => @IN _186534 x (@Dom _186534 _206006)) l)) -> @IN _186534 (@Fun _186534 _206006 f l) (@Dom _186534 _206006)).
Proof. ext=>M v /3= ; firstorder. Qed.

Fixpoint termsubst (v : nat -> term) (t : term) : term :=
  match t with
  | V n => v n
  | Fn n s => Fn n (map (termsubst v) s) end.

Lemma termsubst_def : termsubst = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (nat -> term) -> term -> term) (fun termsubst' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (nat -> term) -> term -> term => forall _206161 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), forall v : nat -> term, (forall x : nat, (termsubst' _206161 v (V x)) = (v x)) /\ (forall f : nat, forall l : seq term, (termsubst' _206161 v (Fn f l)) = (Fn f (@map term term (termsubst' _206161 v) l)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))))).
Proof.
  align_ε. easy.
  intros f' H H'. ext=> v t. destruct (H v) as (HV , HFn).
  destruct (H' v) as (HV' , HFn').
  induction t. now rewrite HV HV'.
  rewrite HFn HFn'. f_equal. now apply map_ALLE.
Qed.

Definition SETMAX (s : nat -> Prop) : nat := fold_set maxn s 0.

Lemma SETMAX_def : SETMAX = (fun _206207 : nat -> Prop => @fold_set nat nat maxn _206207 (NUMERAL 0)).
Proof. exact erefl. Qed.

Definition VARIANT s := (SETMAX s).+1.
Lemma VARIANT_def : VARIANT = (fun _206212 : nat -> Prop => addn (SETMAX _206212) (NUMERAL (BIT1 0))).
Proof.
  by ext=> ? ; rewrite addn1.
Qed.

Fixpoint formsubst (v : nat -> term) f :=
  match f with
  | FFalse => FFalse
  | Atom n s => Atom n (map (termsubst v) s)
  | FImp f f' => FImp (formsubst v f) (formsubst v f')
  | FAll n f => let v' := valmod (n , V n) v in
       let n':= if exists n0 : nat, (IN n0 (free_variables (FAll n f))) /\ (IN n (free_variables_term (v' n0)))
         then VARIANT (free_variables (formsubst v' f)) else n in
       FAll n' (formsubst (valmod (n, V n') v) f) end.

Lemma formsubst_def : formsubst = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (nat -> term) -> form -> form) (fun formsubst' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (nat -> term) -> form -> form => forall _206432 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), (forall v : nat -> term, (formsubst' _206432 v FFalse) = FFalse) /\ ((forall p : nat, forall v : nat -> term, forall l : seq term, (formsubst' _206432 v (Atom p l)) = (Atom p (@map term term (termsubst v) l))) /\ ((forall q : form, forall v : nat -> term, forall r : form, (formsubst' _206432 v (FImp q r)) = (FImp (formsubst' _206432 v q) (formsubst' _206432 v r))) /\ (forall q : form, forall x : nat, forall v : nat -> term, (formsubst' _206432 v (FAll x q)) = (@Basics.apply (nat -> term) form (fun v' : nat -> term => @Datatypes.id form (@Basics.apply nat form (fun z : nat => @Datatypes.id form (FAll z (formsubst' _206432 (@valmod term nat (@pair nat term x (V z)) v) q))) (@COND nat (exists y : nat, (@IN nat y (free_variables (FAll x q))) /\ (@IN nat x (free_variables_term (v' y)))) (VARIANT (free_variables (formsubst' _206432 v' q))) x))) (@valmod term nat (@pair nat term x (V x)) v)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))))).
Proof.
  total_align2 => //. by rewrite/Basics.apply/Datatypes.id 2!IHform.
Qed.

(****************************************************************************)
(* Conversion to prenex form. *)
(****************************************************************************)

Fixpoint qfree f :=
  match f with 
  | FAll _ _ => False
  | FImp f f' => qfree f /\ qfree f'
  | _ => True end.

Lemma qfree_def : qfree = (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> form -> Prop) (fun qfree' : (prod nat (prod nat (prod nat (prod nat nat)))) -> form -> Prop => forall _215105 : prod nat (prod nat (prod nat (prod nat nat))), ((qfree' _215105 FFalse) = True) /\ ((forall n : nat, forall l : seq term, (qfree' _215105 (Atom n l)) = True) /\ ((forall p : form, forall q : form, (qfree' _215105 (FImp p q)) = ((qfree' _215105 p) /\ (qfree' _215105 q))) /\ (forall x : nat, forall p : form, (qfree' _215105 (FAll x p)) = False)))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0))))))))))))).
Proof. by total_align. Qed.

Definition PPAT {A : Type} (f1 f2 : nat -> form -> A) (f3 : form -> A) (f : form) : A :=
  match f with
  | FAll n f' => f1 n f'
  | FImp (FAll n (FImp f' FFalse)) FFalse => f2 n f'
  | _ => f3 f end.

Lemma PPAT_def {_190311 : Type'} : (@PPAT _190311) = (fun _216511 : nat -> form -> _190311 => fun _216512 : nat -> form -> _190311 => fun _216513 : form -> _190311 => fun _216514 : form => @COND _190311 (exists x : nat, exists p : form, _216514 = (FAll x p)) (_216511 (@ε nat (fun x : nat => exists p : form, _216514 = (FAll x p))) (@ε form (fun p : form => _216514 = (FAll (@ε nat (fun x : nat => exists p' : form, _216514 = (FAll x p'))) p)))) (@COND _190311 (exists x : nat, exists p : form, _216514 = (FEx x p)) (_216512 (@ε nat (fun x : nat => exists p : form, _216514 = (FEx x p))) (@ε form (fun p : form => _216514 = (FEx (@ε nat (fun x : nat => exists p' : form, _216514 = (FEx x p'))) p)))) (_216513 _216514))).
Proof.
  ext=> f1 f2 f3 f. repeat if_intro.
  1,2 : intros (n , (f' , ->)) ; try intros _ ; try unfold FEx , Not ;
        simpl ; f_equal ; align_ε.
  1,5 : now exists f'.
  2,5 : repeat f_equal ; align_ε ; [ now exists f' | idtac ].
  1-3,5 : intros n' _ (f'' , H) ; now injection H.
  1,2 : intros f'' _ H ; now injection H.
  induction f;intros H H';auto.
  - destruct f4 ; simp PPAT ; auto.
    destruct f4 ; simp PPAT ; auto.
    destruct f4_2 ; simp PPAT ; auto.
    destruct f5 ; simp PPAT ; auto.
    contradiction H. exists n. now exists f4_1.
  - contradiction H'. exists n. now exists f.
Qed.

Inductive prenex : form -> Prop :=
| prenex_qfree : forall f, qfree f -> prenex f
| prenex_FAll : forall f n, prenex f -> prenex (FAll n f)
| prenex_FEx : forall f n, prenex f -> prenex (FEx n f).

Lemma prenex_def : prenex = (fun a : form => forall prenex' : form -> Prop, (forall a' : form, ((qfree a') \/ ((exists x : nat, exists p : form, (a' = (FAll x p)) /\ (prenex' p)) \/ (exists x : nat, exists p : form, (a' = (FEx x p)) /\ (prenex' p)))) -> prenex' a') -> prenex' a).
Proof. ind_align. Qed.

Inductive universal : form -> Prop :=
| universal_qfree : forall f, qfree f -> universal f
| universal_FAll : forall f n, universal f -> universal (FAll n f).

Lemma universal_def : universal = (fun a : form => forall universal' : form -> Prop, (forall a' : form, ((qfree a') \/ (exists x : nat, exists p : form, (a' = (FAll x p)) /\ (universal' p))) -> universal' a') -> universal' a).
Proof. ind_align. Qed.

Fixpoint form_size f :=
  match f with
  | FFalse | Atom _ _ => 1
  | FImp f f' => form_size f + form_size f'
  | FAll n f => (form_size f).+1 end.

Lemma size_def : form_size = (@ε ((prod nat (prod nat (prod nat nat))) -> form -> nat) (fun size' : (prod nat (prod nat (prod nat nat))) -> form -> nat => forall _216494 : prod nat (prod nat (prod nat nat)), ((size' _216494 FFalse) = (NUMERAL (BIT1 0))) /\ ((forall p : nat, forall l : seq term, (size' _216494 (Atom p l)) = (NUMERAL (BIT1 0))) /\ ((forall q : form, forall r : form, (size' _216494 (FImp q r)) = (addn (size' _216494 q) (size' _216494 r))) /\ (forall x : nat, forall q : form, (size' _216494 (FAll x q)) = (addn (NUMERAL (BIT1 0)) (size' _216494 q)))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))))))).
Proof.
  by total_align ; rewrite// addn1.
Qed.

Lemma size_formsubst : forall f v, form_size (formsubst v f) = form_size f.
Proof.
  induction f ; intro v ; reflexivity + now simpl ; f_equal.
Qed.

 (*
  Unfruitful attempts at defining the conversion to prenex form without equations


Lemma COND_elim' {A : Type'} {P Q' : Prop} {x y : A} (Q : A -> Prop) :
  Q (COND P x y) -> (P -> Q x -> Q') -> (~P -> Q y -> Q') -> Q'.
Proof.
  intros H H1 H2. destruct (classic P) as [H' | H'].
  - apply H1. auto. rewrite <- (is_True P) in H'. now rewrite H', COND_True in H.
  - apply H2. auto. rewrite <- (is_False P) in H'. now rewrite H', COND_False in H.
Qed.

Ltac COND_elim Q H' intropattern1 intropattern2 :=
  apply (COND_elim' Q H') ; clear H' ;
  [ intros intropattern1 H' | intros intropattern2 H' ].

Lemma valmod_permut {A B : Type'} (x x' : A) (y y' : B) (f : A -> B) :
  x <> x' -> valmod (x,y) (valmod (x',y') f) = valmod (x',y') (valmod (x,y) f).
Proof.
  intro H. unfold valmod. ext x0. simpl.
  repeat apply COND_intro ; try easy.
  intros H0 H1. destruct (H (eq_trans (eq_sym H1) H0)).
Qed.

Lemma valmod_triv {A B : Type'} (x : A) (f : A -> B) :
  valmod (x , f x) f = f.
Proof.
  unfold valmod. ext x0. apply COND_intro;auto. intro H. now rewrite H.
Qed.

Lemma termsubst_V : termsubst V = (fun t => t).
Proof.
  ext t. all_induction t;auto. simpl. f_equal.
  rewrite <- map_id. now apply map_ALLE.
Qed.

Lemma formsubst_V : formsubst V = (fun f => f).
Proof.
  ext f. induction f ; auto ; simpl.
  - induction l;auto. simpl. repeat f_equal.
    now rewrite termsubst_V. inversion IHl. now rewrite H0.
  - now rewrite IHf1,IHf2.
  - rewrite valmod_triv. apply COND_intro ; intro H.
    + destruct H as (n' , (H , H')). destruct H'. destruct H as (_ , H).
      contradiction H. exists.
    + rewrite valmod_triv. now rewrite IHf.
Qed.

Definition PRENEX_RIGHT : form -> form -> form := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form => forall _216639 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))), (forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))))))).

Definition varswitch (l : seq (N*N)) (f : form) :=
  fold_left (fun f' c => formsubst (valmod (fst c , V (snd c)) V) f') l f.

Fixpoint Prenex_right0 (f f' : form) (l : seq (nat * nat)) :=
  match f' with
  | FAll n' f' =>
    let m := VARIANT
      (Union (free_variables f) (free_variables (varswitch l (FAll n' f'))))
    in FAll m (Prenex_right0 f f' ((n',m)::l))
  | FImp f0 f1 => match f1 with
    | FFalse => match f0 with
      | FAll n' f0 => match f0 with
        | FImp f'' f0 => match f0 with
          | FFalse => let m := VARIANT
              (Union (free_variables f)
              (free_variables (varswitch l (FEx n' f''))))
            in FEx m (Prenex_right0 f f'' ((n',m)::l))
          | _ => FImp f (varswitch l f') end
        | _ => FImp f (varswitch l f') end
      | _ => FImp f (varswitch l f') end
    | _ => FImp f (varswitch l f') end
  | _ => FImp f (varswitch l f') end.

Definition Prenex_right f f' := COND (prenex f') (Prenex_right0 f f' nil) (PRENEX_RIGHT f f').

Definition not_quantifier f :=
  match f with
  | FAll n f | FImp (FAll n (FImp f FFalse)) FFalse => False
  | _ => True end.

Definition test_hyp f P := 
  match f with
  | FAll n f' => P f'
  | FImp f0 f1 => match f1 with
    | FFalse => match f0 with
      | FAll _ f0 => match f0 with
        | FImp f' f0 => match f0 with
          | FFalse => P f'
          | _ => True end
        | _ => True end
      | _ => True end
    | _ => True end
  | _ => True end.

Fixpoint test_ind P (H : forall f, test_hyp f P -> P f) f : P f :=
  H f
  ( match f return test_hyp f P with
    | FAll n f' => test_ind P H f'
    | FImp f0 f1 => match f1 with
      | FFalse => match f0 with
        | FAll _ f0 => match f0 with
          | FImp f' f0 => match f0 with
            | FFalse => test_ind P H f'
            | _ => I end
          | _ => I end
        | _ => I end
      | _ => I end
    | _ => I end ).

Ltac test_ind f :=
  let IH := fresh "IH" in
  revert f ; match goal with |- forall f, ?P => apply (test_ind (fun f => P)) end ;
  intro f ; destruct f ; simpl test_hyp ; intro IH ;
  match type of IH with True => clear IH | _ => idtac end.

Lemma Prenex_right0_quantifier_case f f' : forall n m l,
  Prenex_right0 f f' ((n , m) :: l) =
  Prenex_right0 f (formsubst (valmod (n, V m) V) f') l.
Proof.
  test_ind f' ; intros n' m' l'.
  1,2 : reflexivity.
  - destruct f'2 ; auto. destruct f'1 ; auto. destruct f'1 ; auto.
    destruct f'1_2 ; auto. simpl. f_equal.
    repeat rewrite IH. f_equal. remember (VARIANT
      (Union (free_variables f)
         (Subtract (free_variables (FImp (FAll n (FImp f'1_1 FFalse)) FFalse)) n'))) as m.
    simpl. f_equal.
    + simpl.
    2 : simpl ; now repeat rewrite Union_empty.
    
Qed.

Lemma Prenex_right_def : Prenex_right = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form => forall _216639 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))), (forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))))).
Proof.
  ext f f'. unfold Prenex_right. apply COND_intro ; auto ; intro H.
  - apply (partial_align1_spec2 prenex (fun _ f f' => Prenex_right0 f f' nil)) ; auto ;
    clear f f' H. intros _. repeat split.
    + intros f n' f'. let_clear. simpl. rewrite valmod_triv. simpl.
      apply COND_intro.
      * intros (n , (H , H')). destruct H'.
        destruct H as (_,H). contradiction H. exists.
      * intros _. f_equal. rewrite valmod_triv. now rewrite formsubst_V.
        
    + intros. unfold FEx,Not. now simp Prenex_right0.
    + intros f f' H. funelim (Prenex_right0 f f') ; auto.
      destruct (proj1 H0). destruct H0.
    + simpl. clear f f' H. intros g uv f f' H H' Pf'.
      specialize (H uv). specialize (H' uv). full_destruct.
      funelim (Prenex_right0 f f') ; try now (inversion Pf' ; rewrite H1 ; auto).
      * unfold FEx,Not in *. rewrite H1. let_clear. simpl in *. repeat f_equal. rewrite (H g uv);auto.
        apply formsubst_prenex. inversion Pf';auto. destruct (proj1 H5).
      * rewrite H'. let_clear. simpl in *. repeat f_equal. rewrite (H g uv);auto.
        apply formsubst_prenex. inversion Pf';easy.
  - reflexivity.
Qed.

Lemma form_Varswitch_triv l : all (fun c => fst c = snd c) l ->
  form_Varswitch l = (fun f => f).
Proof.
  intro H. ext f. revert l H. induction f ; intros l' H' ; simpl.
  - reflexivity.
  - rewrite term_Varswitch_triv;auto. now rewrite map_id.
  - f_equal ; auto.
  - induction H'. simpl. now rewrite IHf.
    destruct x as (m,m'). simpl in *.
Qed.

Lemma foldr_cons {A B : Type} {f : A -> B -> B} x x0 l :
  (f x (foldr f x0 l)) = foldr f x0 (x::l).
Proof. reflexivity. Qed.

Lemma form_Varswitch_filter n l :
  form_Varswitch ((n,n)::l) = form_Varswitch (filter (fun c => negb (fst c =? n)) l).
Proof.
  induction l. simpl. rewrite form_Varswitch_nil.
  ext f. induction f;auto.
Qed.



Lemma formsubst_valmod_V l : NoDup (map fst l) ->
  formsubst (foldr valmod V (map (fun c => (fst c, V (snd c))) l)) =
  form_Varswitch l.
Proof.
  intro H. ext f. revert l H. induction f ; intros l' H'.
  - reflexivity.
  - simpl. now rewrite termsubst_valmod_V.
  - simpl. f_equal;auto.
  - induction l'.
    + simpl form_Varswitch. rewrite <- IHf. simpl foldr.
      now rewrite formsubst_V. auto.
    + destruct a as (m,m'). simpl. apply COND_intro.
      * intros (n0 , (H1,H2)). unfold valmod in H2. simpl in H2.
        COND_elim (fun t => IN n (free_variables_term t)) H2 e ne.
        rewrite e in H1. contradiction (proj2 H1).
        COND_elim (fun t => IN n (free_variables_term t)) H2 e ne'.
        { inversion_clear H2. rewrite N.eqb_refl. f_equal.
          { do 2 f_equal. do 2 rewrite foldr_cons.
            rewrite <- (map_cons (fun c => (fst c , V (snd c))) (m,n)).
            rewrite <- (map_cons (fun c => (fst c , V (snd c))) (n,n)).
            rewrite IHf. rewrite valmod_permut.
            rewrite IHf. all : destruct e. rewrite <- N.eqb_neq in ne.
            now rewrite ne. now symmetry. }
        { rewrite valmod_permut.
          
      apply (COND_elim' (fun t => IN n0 (free_variables_term t)) H') ; clear H'.

Qed.
       let n':= COND (exists n0 : nat, (IN n0 (free_variables (FAll n f))) /\ (IN n (free_variables_term (v' n0)))) 
       (VARIANT (free_variables (formsubst v' f)))
       n in
      FAll n' (formsubst (valmod (n, V n') v) f) end.

Fixpoint Prenex_right0 (f f' : form) (v : nat -> term) :=
  match f' with
  | FAll n' f' => 
    let m := VARIANT 
      (Union (free_variables f) (free_variables (formsubst v (FAll n' f'))))
    in FAll m (Prenex_right0 f f' (valmod (n' , V m) v))
  | FImp (FAll n' (FImp f' FFalse)) FFalse => 
    let m := VARIANT 
      (Union (free_variables f) (free_variables (formsubst v (FEx n' f'))))
    in FEx m (Prenex_right0 f f' (valmod (n' , V m) v))
  | qfreeform => FImp f (formsubst v qfreeform)
  end.

Lemma formsubst_qfree : forall f v, qfree f -> qfree (formsubst v f).
Proof.
  intros f v. induction f ; auto.
  simpl. split. now apply IHf1. now apply IHf2.
Qed.

Lemma formsubst_prenex : forall f v, prenex f -> prenex (formsubst v f).
Proof.
  intros f v H. revert v. induction H ; intro v.
  - apply prenex_qfree. now apply formsubst_qfree.
  - exact (prenex_FAll _ _ (IHprenex _)).
  - exact (prenex_FEx _ _ (IHprenex _)).
Qed.

Lemma Prenex_right0_prenex : forall f f', qfree f -> prenex f' -> forall v, prenex (Prenex_right0 f f' v).
Proof.
  intros f f' H H'. induction H' ; intro v.
  - destruct f0 ; try now constructor. destruct f0_1.
    1-3 : apply prenex_qfree ; repeat split ; (try apply formsubst_qfree) ;
          simpl in H0 ; full_destruct ; auto.
    destruct (proj1 H0).
  - apply prenex_FAll. apply IHH'.
  - apply prenex_FEx. apply IHH'.
Qed.

Definition PRENEX_RIGHT : form -> form -> form := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form => forall _216639 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))), (forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))))))).

Definition Prenex_right f f' := COND (prenex f') (Prenex_right0 f f' V) (PRENEX_RIGHT f f').

Lemma valmod_V_triv : forall n, valmod (n , V n) V = V.
Proof.
  intro n. ext n'. unfold valmod. apply COND_intro ; auto. intro H.
  now rewrite H.
Qed.

Lemma termsubst_V_triv : termsubst V = (fun t => t).
Proof.
  ext t. all_induction t;auto. simpl. f_equal.
  rewrite <- map_id. now apply map_ALLE.
Qed.

Lemma formsubst_V_triv : formsubst V = (fun f => f).
Proof.
  ext f. induction f ; auto ; simpl.
  - induction l;auto. simpl. repeat f_equal.
    now rewrite termsubst_V_triv. inversion IHl. now rewrite H0.
  - now rewrite IHf1,IHf2.
  - rewrite valmod_V_triv. apply COND_intro ; intro H.
    + destruct H as (n' , (H , H')). destruct H'. destruct H as (_ , H).
      contradiction H. exists.
    + rewrite valmod_V_triv. now rewrite IHf.
Qed.
(*
Lemma Prenex_right_forall_def : forall f f' v n,
  VARIANT (Union (free_variables f) (free_variables (formsubst v (FAll n f')))) = 0.
  simpl.
  VARIANT
  (Union (free_variables f)
     (Subtract
        (free_variables
           (formsubst
              (valmod
                 (n,
                  V n) v) f')) n))
                    (COND
                       (exists n0 : nat,
                          IN n0 (Subtract (free_variables f') n) /\
                          IN n (free_variables_term (valmod (n, V n) v n0)))
                       (VARIANT (free_variables (formsubst (valmod (n, V n) v) f'))) n)) v)
              f'))
        (COND
           (exists n0 : nat,
              IN n0 (Subtract (free_variables f') n) /\
              IN n (free_variables_term (valmod (n, V n) v n0)))
           (VARIANT (free_variables (formsubst (valmod (n, V n) v) f'))) n))) = 0
 *) (*
Lemma Prenex_right_def0 : forall f n f' v,
  (Prenex_right0 f f' (valmod (n , V (VARIANT
    (Union (free_variables f)
      (Subtract
        (free_variables
           (formsubst
              (valmod
                 (n,
                  V n) v) f')) n)))) v) =
      Prenex_right0 f (formsubst (valmod (n , V (VARIANT
        (Union (free_variables f) (free_variables (FAll n f'))))) V) f') v).
Proof.
 intros f n. induction f' ; intro v ; auto.
 - simpl. do 2 f_equal.
   induction l ; auto.
   simpl. f_equal.
   + clear IHl. all_induction a.
     * simpl. unfold valmod at 1 4. apply COND_intro.
       { simpl. intro H. rewrite H. 
         apply COND_intro ; try (intro H' ; now contradiction H') ; intros _.
         simpl. *)

Lemma Prenex_right_def0 : forall f n' f', Prenex_right0 f f'
  (valmod
     (n',
      V
        (VARIANT
           (Union (free_variables f)
              (Subtract (free_variables (formsubst (valmod (n', V n') V) f')) n')))) V) =
Prenex_right0 f
  (formsubst
     (valmod (n', V (VARIANT (Union (free_variables f) (Subtract (free_variables f') n')))) V)
     f') V.
Proof.
 intros f n. induction f' ; auto.
 - simpl. do 2 f_equal.
   induction l ; auto.
   simpl. f_equal.
   + clear IHl. all_induction a ; simpl.
     * unfold valmod at 1 4. simpl. apply COND_intro ; intro H.
       { rewrite H.
         apply COND_intro ; try (intro H' ; now contradiction H') ; intros _.
         simpl. rewrite valmod_V_triv. rewrite termsubst_V_triv. now rewrite map_id. }
       { apply COND_intro. intro H'. destruct (H H').
         reflexivity. }
     * f_equal. apply map_ALLE in IHt. rewrite (map_map _ (termsubst V)). simpl in IHt. rewrite IHt. repeat rewrite map_map. f_equal.
  *)

Instance ltn_wf : WellFounded ltn.
Proof. exact theorems.thm_WF_num. Qed.

Opaque formsubst free_variables valmod VARIANT.

Equations? Prenex_right0 (f f' : form) : form by wf (form_size f') ltn :=
  Prenex_right0 f (FAll n' f') =>
    let y := VARIANT (setU (free_variables f) (free_variables (FAll n' f')))
    in FAll y (Prenex_right0 f (formsubst (valmod (n' , V y) V) f'));
  Prenex_right0 f (FImp (FAll n' (FImp f' FFalse)) FFalse) =>
    let y := VARIANT (setU (free_variables f) (free_variables (FEx n' f')))
    in FEx y (Prenex_right0 f (formsubst (valmod (n' , V y) V) f'));
  Prenex_right0 f qfree => FImp f qfree.
Proof.
  1,2: by rewrite size_formsubst /= ; elim: (form_size f').
Qed.

Lemma formsubst_qfree : forall f v, qfree f -> qfree (formsubst v f).
Proof.
  intros f v. induction f ; auto.
  simpl. split. now apply IHf1. now apply IHf2.
Qed.

Lemma formsubst_prenex : forall f v, prenex f -> prenex (formsubst v f).
Proof.
  intros f v H. revert v. induction H ; intro v.
  - apply prenex_qfree. now apply formsubst_qfree.
  - exact (prenex_FAll _ (IHprenex _)).
  - exact (prenex_FEx _ (IHprenex _)).
Qed.

Lemma Prenex_right0_prenex : forall f f', qfree f -> prenex f' -> prenex (Prenex_right0 f f').
Proof.
  intros f f' H H'. funelim (Prenex_right0 f f') ;
  try (inversion H' ; now apply prenex_qfree).
  - apply prenex_FEx. apply H;auto. inversion H'. destruct (proj1 H1).
    now apply (formsubst_prenex).
  - apply prenex_FAll. apply H;auto. inversion H'. destruct H1.
    now apply (formsubst_prenex).
Qed.

Definition PRENEX_RIGHT : form -> form -> form := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form => forall _216639 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))), (forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))))))).

Definition Prenex_right f f' := if prenex f' then Prenex_right0 f f' else PRENEX_RIGHT f f'.

Lemma Prenex_right_def : Prenex_right = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form) (fun Prenex_right' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) -> form -> form -> form => forall _216639 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))), (forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FAll x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FAll y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FAll x q)))))) /\ ((forall p : form, forall x : nat, forall q : form, (Prenex_right' _216639 p (FEx x q)) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FEx y (Prenex_right' _216639 p (formsubst (@valmod term nat (@pair nat term x (V y)) V) q)))) (VARIANT (@setU nat (free_variables p) (free_variables (FEx x q)))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_right' _216639 p q) = (FImp p q)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))))).
Proof.
  unfold Prenex_right, PRENEX_RIGHT.
  align_ε_if.
  - repeat split.
    + intros f n' f'. now simp Prenex_right0.
    + intros. unfold FEx,Not. now simp Prenex_right0.
    + intros f f' H. funelim (Prenex_right0 f f') ; auto.
      destruct (proj1 H0). destruct H0.
  - simpl. intros g H H' f f' Pf'. full_destruct.
      funelim (Prenex_right0 f f') ; try now (inversion Pf' ; rewrite H2 ; auto).
      * unfold FEx,Not in *. rewrite H2. simpl in *. repeat f_equal. rewrite (H g);auto.
        apply formsubst_prenex. inversion Pf';auto. destruct (proj1 H6).
      * rewrite H1. simpl in *. repeat f_equal. rewrite (H g);auto.
        apply formsubst_prenex. inversion Pf';easy.
Qed.

Equations? Prenex_left0 (f f' : form) : form by wf (form_size f) ltn :=
  Prenex_left0 (FAll n f) f' =>
    let y := VARIANT (setU (free_variables (FAll n f)) (free_variables f'))
    in FEx y (Prenex_left0 (formsubst (valmod (n , V y) V) f) f');
  Prenex_left0 (FImp (FAll n (FImp f FFalse)) FFalse) f' =>
    let y := VARIANT (setU (free_variables (FEx n f)) (free_variables f'))
    in FAll y (Prenex_left0 (formsubst (valmod (n , V y) V) f) f');
  Prenex_left0 f f' => Prenex_right0 f f'.
Proof.
  1,2 : by rewrite size_formsubst //= ; elim:(form_size f).
Qed.

Equations? Prenex_left1 (f f' : form) : form by wf (form_size f) lt :=
  Prenex_left1 (FAll n f) f' =>
    let y := VARIANT (setU (free_variables (FAll n f)) (free_variables f'))
    in FEx y (Prenex_left1 (formsubst (valmod (n , V y) V) f) f');
  Prenex_left1 (FImp (FAll n (FImp f FFalse)) FFalse) f' =>
    let y := VARIANT (setU (free_variables (FEx n f)) (free_variables f'))
    in FAll y (Prenex_left1 (formsubst (valmod (n , V y) V) f) f');
  Prenex_left1 f f' => Prenex_right f f'.
Proof.
  1,2 : by rewrite size_formsubst /= ; elim:(form_size f).
Qed.

Lemma Prenex_left0_prenex : forall f f', prenex f -> prenex f' -> prenex (Prenex_left0 f f').
Proof.
  intros f f' H H'. funelim (Prenex_left0 f f') ;
  try now inversion H ; apply Prenex_right0_prenex.
  - apply prenex_FAll. apply H;auto. inversion H0. destruct (proj1 H1).
    now apply (formsubst_prenex).
  - apply prenex_FEx. apply H;auto. inversion H0. destruct H1.
    now apply (formsubst_prenex).
Qed.

Definition PRENEX_LEFT : form -> form -> form := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> form -> form -> form) (fun Prenex_left' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> form -> form -> form => forall _216680 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))), (forall p : form, forall x : nat, forall q : form, (Prenex_left' _216680 (FAll x q) p) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FEx y (Prenex_left' _216680 (formsubst (@valmod term nat (@pair nat term x (V y)) V) q) p))) (VARIANT (@setU nat (free_variables (FAll x q)) (free_variables p))))) /\ ((forall p : form, forall x : nat, forall q : form, (Prenex_left' _216680 (FEx x q) p) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FAll y (Prenex_left' _216680 (formsubst (@valmod term nat (@pair nat term x (V y)) V) q) p))) (VARIANT (@setU nat (free_variables (FEx x q)) (free_variables p))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_left' _216680 q p) = (Prenex_right q p)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))).

Definition Prenex_left f f' := if prenex f then Prenex_left1 f f' else PRENEX_LEFT f f'.

Lemma Prenex_left_def : Prenex_left = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> form -> form -> form) (fun Prenex_left' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> form -> form -> form => forall _216680 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))), (forall p : form, forall x : nat, forall q : form, (Prenex_left' _216680 (FAll x q) p) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FEx y (Prenex_left' _216680 (formsubst (@valmod term nat (@pair nat term x (V y)) V) q) p))) (VARIANT (@setU nat (free_variables (FAll x q)) (free_variables p))))) /\ ((forall p : form, forall x : nat, forall q : form, (Prenex_left' _216680 (FEx x q) p) = (@Basics.apply nat form (fun y : nat => @Datatypes.id form (FAll y (Prenex_left' _216680 (formsubst (@valmod term nat (@pair nat term x (V y)) V) q) p))) (VARIANT (@setU nat (free_variables (FEx x q)) (free_variables p))))) /\ (forall p : form, forall q : form, (qfree q) -> (Prenex_left' _216680 q p) = (Prenex_right q p)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))))))).
Proof.
  unfold Prenex_left, PRENEX_LEFT.
  align_ε_if.
  - repeat split.
    + intros. now simp Prenex_left1.
    + intros. unfold FEx,Not.  now simp Prenex_left1.
    + intros f' f H. destruct f ; try now simp Prenex_left1.
      destruct f1 ; try now simp Prenex_left1. destruct (proj1 H).
  - simpl. intros g H H' f f' Pf. full_destruct.
      funelim (Prenex_left1 f f') ; try now (inversion Pf ; rewrite H2 ; auto).
      * unfold FEx,Not in *. rewrite H2. let_clear. simpl in *. repeat f_equal. rewrite (H g);auto.
        apply formsubst_prenex. inversion Pf;auto. destruct (proj1 H6).
      * rewrite H1. let_clear. simpl in *. repeat f_equal. rewrite (H g);auto.
        apply formsubst_prenex. inversion Pf;easy.
Qed.

Fixpoint Prenex (f : form) : form :=
  match f with
  | FAll n f => FAll n (Prenex f)
  | FImp f f' => Prenex_left0 (Prenex f) (Prenex f')
  | _ => f end.

Lemma Prenex_def0 : forall f, prenex (Prenex f).
Proof.
  induction f.
  1,2 : now apply prenex_qfree.
  - now apply Prenex_left0_prenex.
  - exact (prenex_FAll _ IHf).
Qed.

Lemma Prenex_def : Prenex = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> form -> form) (fun Prenex' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> form -> form => forall _216688 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), ((Prenex' _216688 FFalse) = FFalse) /\ ((forall a : nat, forall l : seq term, (Prenex' _216688 (Atom a l)) = (Atom a l)) /\ ((forall p : form, forall q : form, (Prenex' _216688 (FImp p q)) = (Prenex_left (Prenex' _216688 p) (Prenex' _216688 q))) /\ (forall x : nat, forall p : form, (Prenex' _216688 (FAll x p)) = (FAll x (Prenex' _216688 p)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))))))))).
Proof.
  total_align => // p q /=. unfold Prenex_left. if_intro=>[_|H].
  - generalize (Prenex p). clear p. intro f. funelim (Prenex_left0 f (Prenex q)) ;
    try now simp Prenex_left1 ; unfold Prenex_right ; if_intro ;
    [ reflexivity | intro H' ; destruct (H' (Prenex_def0 q)) ].
    all : simp Prenex_left1 ; now rewrite H.
  - destruct (H (Prenex_def0 p)).
Qed.

(****************************************************************************)
(* Conversion to Skollem form. *)
(****************************************************************************)
Definition Skolem1 (k n : nat) (f : form) := formsubst (valmod (n , (Fn k (map V (seq_of_set (free_variables (FEx n f)))))) V) f.

Lemma Skolem1_def : Skolem1 = (fun _221139 : nat => fun _221140 : nat => fun _221141 : form => formsubst (@valmod term nat (@pair nat term _221140 (Fn _221139 (@map nat term V (@seq_of_set nat (free_variables (FEx _221140 _221141)))))) V) _221141).
Proof. exact erefl. Qed.

Equations? Skolems n f k : form by wf (form_size f) ltn :=
Skolems n (FAll m f) k => FAll m (Skolems n f k);
Skolems n (FImp (FAll m (FImp f FFalse)) FFalse) k => Skolems n (Skolem1 (NUMPAIR n k) m f) (S k);
Skolems _ f _ => f.
Proof.
  - by rewrite/Skolem1 size_formsubst /= ; elim:(form_size f).
  - exact: leqnn.
Qed.

Lemma Skolems_def : Skolems = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> form -> nat -> form) (fun Skolems' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> form -> nat -> form => forall _221561 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), forall J : nat, forall r : form, forall k : nat, (Skolems' _221561 J r k) = (@PPAT form (fun x : nat => fun q : form => FAll x (Skolems' _221561 J q k)) (fun x : nat => fun q : form => Skolems' _221561 J (Skolem1 (NUMPAIR J k) x q) (S k)) (fun p : form => p) r)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))).
Proof.
  align_ε.
  - intros n f k. funelim (Skolems n f k) ; auto ; now destruct f1.
  - intros f' H H'. ext=> n f k.
    funelim (Skolems n f k) ; rewrite H' ; auto ;
    try destruct f1 ; simpl ; f_equal ; auto.
Qed.

Definition Skopre n f := Skolems n (Prenex f) 0.

Lemma Skopre_def : Skopre = (fun _223892 : nat => fun _223893 : form => Skolems _223892 (Prenex _223893) (NUMERAL 0)).
Proof. exact erefl. Qed.

Definition bumpmod {A : Type'} (M : Structure A) : Structure A :=
  (Dom M , ((fun n s => Fun M (NUMSND n) s) , Pred M)).

Lemma bumpmod_def {_195501 : Type'} : (@bumpmod _195501) = (fun _223909 : prod (_195501 -> Prop) (prod (nat -> (seq _195501) -> _195501) (nat -> (seq _195501) -> Prop)) => @pair (_195501 -> Prop) (prod (nat -> (seq _195501) -> _195501) (nat -> (seq _195501) -> Prop)) (@Dom _195501 _223909) (@pair (nat -> (seq _195501) -> _195501) (nat -> (seq _195501) -> Prop) (fun k : nat => fun zs : seq _195501 => @Fun _195501 _223909 (NUMSND k) zs) (@Pred _195501 _223909))).
Proof. exact erefl. Qed.

Fixpoint bumpterm t :=
  match t with
  | V n => V n
  | Fn n s => Fn (NUMPAIR 0 n) (map bumpterm s) end.

Lemma bumpterm_def : bumpterm = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> term -> term) (fun bumpterm' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> term -> term => forall _223917 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall x : nat, (bumpterm' _223917 (V x)) = (V x)) /\ (forall k : nat, forall l : seq term, (bumpterm' _223917 (Fn k l)) = (Fn (NUMPAIR (NUMERAL 0) k) (@map term term (bumpterm' _223917) l)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))))))))))).
Proof. by term_align. Qed.

Fixpoint bumpform f :=
  match f with
  | FFalse => FFalse
  | Atom n s => Atom n (map bumpterm s)
  | FImp f f' => FImp (bumpform f) (bumpform f')
  | FAll n f => FAll n (bumpform f) end.
  
Lemma bumpform_def : bumpform = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> form -> form) (fun bumpform' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> form -> form => forall _223925 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), ((bumpform' _223925 FFalse) = FFalse) /\ ((forall p : nat, forall l : seq term, (bumpform' _223925 (Atom p l)) = (Atom p (@map term term bumpterm l))) /\ ((forall q : form, forall r : form, (bumpform' _223925 (FImp q r)) = (FImp (bumpform' _223925 q) (bumpform' _223925 r))) /\ (forall x : nat, forall r : form, (bumpform' _223925 (FAll x r)) = (FAll x (bumpform' _223925 r)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))))))))))).
Proof. by total_align. Qed.

Fixpoint unbumpterm t :=
  match t with
  | V n => V n
  | Fn n s => Fn (NUMSND n) (map unbumpterm s) end.

Lemma unbumpterm_def : unbumpterm = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) -> term -> term) (fun unbumpterm' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) -> term -> term => forall _225051 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))), (forall x : nat, (unbumpterm' _225051 (V x)) = (V x)) /\ (forall k : nat, forall l : seq term, (unbumpterm' _225051 (Fn k l)) = (Fn (NUMSND k) (@map term term (unbumpterm' _225051) l)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))))))))))))).
Proof. by term_align. Qed.

Fixpoint unbumpform f :=
  match f with
  | FFalse => FFalse
  | Atom n s => Atom n (map unbumpterm s)
  | FImp f f' => FImp (unbumpform f) (unbumpform f')
  | FAll n f => FAll n (unbumpform f) end.

Lemma unbumpform_def : unbumpform = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) -> form -> form) (fun unbumpform' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) -> form -> form => forall _225059 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))), ((unbumpform' _225059 FFalse) = FFalse) /\ ((forall p : nat, forall l : seq term, (unbumpform' _225059 (Atom p l)) = (Atom p (@map term term unbumpterm l))) /\ ((forall q : form, forall r : form, (unbumpform' _225059 (FImp q r)) = (FImp (unbumpform' _225059 q) (unbumpform' _225059 r))) /\ (forall x : nat, forall r : form, (unbumpform' _225059 (FAll x r)) = (FAll x (unbumpform' _225059 r)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))))))))))))).
Proof. by total_align. Qed.

Definition unbumpmod {A : Type'} (M : Structure A) : Structure A :=
  (Dom M , ((fun n s => Fun M (NUMPAIR 0 n) s) , Pred M)).

Lemma unbumpmod_def {_195825 : Type'} : (@unbumpmod _195825) = (fun _225060 : prod (_195825 -> Prop) (prod (nat -> (seq _195825) -> _195825) (nat -> (seq _195825) -> Prop)) => @pair (_195825 -> Prop) (prod (nat -> (seq _195825) -> _195825) (nat -> (seq _195825) -> Prop)) (@Dom _195825 _225060) (@pair (nat -> (seq _195825) -> _195825) (nat -> (seq _195825) -> Prop) (fun k : nat => fun zs : seq _195825 => @Fun _195825 _225060 (NUMPAIR (NUMERAL 0) k) zs) (@Pred _195825 _225060))).
Proof. exact erefl. Qed.

Fixpoint NUMLIST s :=
  match s with
  | [::] => 0
  | a::s => NUMPAIR a (NUMLIST s) + 1 end.

Lemma NUMLIST_def : NUMLIST = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (seq nat) -> nat) (fun NUMLIST' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (seq nat) -> nat => forall _225068 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), ((NUMLIST' _225068 (@nil nat)) = (NUMERAL 0)) /\ (forall h : nat, forall t : seq nat, (NUMLIST' _225068 (@cons nat h t)) = (addn (NUMPAIR h (NUMLIST' _225068 t)) (NUMERAL (BIT1 0))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))))).
Proof. by total_align. Qed.

Fixpoint num_of_term t :=
  match t with
  | V n => NUMPAIR 0 n
  | Fn n s => NUMPAIR 1 (NUMPAIR n (NUMLIST (map num_of_term s))) end.

Lemma num_of_term_def : num_of_term = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> term -> nat) (fun num_of_term' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> term -> nat => forall _225072 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))), (forall x : nat, (num_of_term' _225072 (V x)) = (NUMPAIR (NUMERAL 0) x)) /\ (forall f : nat, forall l : seq term, (num_of_term' _225072 (Fn f l)) = (NUMPAIR (NUMERAL (BIT1 0)) (NUMPAIR f (NUMLIST (@map term nat (num_of_term' _225072) l)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0))))))))))))))))))). 
Proof. by term_align. Qed.

Fixpoint num_of_form f :=
  match f with
  | FFalse => 1
  | Atom n s => NUMPAIR 1 (NUMPAIR n (NUMLIST (map num_of_term s)))
  | FImp f f' => NUMPAIR 2 (NUMPAIR (num_of_form f) (num_of_form f'))
  | FAll n f => NUMPAIR 3 (NUMPAIR n (num_of_form f)) end.

Lemma num_of_form_def : num_of_form = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> form -> nat) (fun num_of_form' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> form -> nat => forall _225305 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))), ((num_of_form' _225305 FFalse) = (NUMPAIR (NUMERAL 0) (NUMERAL 0))) /\ ((forall p : nat, forall l : seq term, (num_of_form' _225305 (Atom p l)) = (NUMPAIR (NUMERAL (BIT1 0)) (NUMPAIR p (NUMLIST (@map term nat num_of_term l))))) /\ ((forall q : form, forall r : form, (num_of_form' _225305 (FImp q r)) = (NUMPAIR (NUMERAL (BIT0 (BIT1 0))) (NUMPAIR (num_of_form' _225305 q) (num_of_form' _225305 r)))) /\ (forall x : nat, forall q : form, (num_of_form' _225305 (FAll x q)) = (NUMPAIR (NUMERAL (BIT1 (BIT1 0))) (NUMPAIR x (num_of_form' _225305 q))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0))))))))))))))))))).
Proof. by total_align. Qed.

Definition form_of_num := finv num_of_form. (* Could construct it, but it would require using
                                               NUMFST which is not constructed anyway. *)
Lemma form_of_num_def : form_of_num = (fun _225306 : nat => @ε form (fun p : form => (num_of_form p) = _225306)).
Proof. exact erefl. Qed.

Definition SKOLEMIZE f := Skopre (num_of_form (bumpform f) + 1) (bumpform f).

Lemma SKOLEMIZE_def : SKOLEMIZE = (fun _225311 : form => Skopre (addn (num_of_form (bumpform _225311)) (NUMERAL (BIT1 0))) (bumpform _225311)).
Proof. exact erefl. Qed.

Definition SKOMOD1 {A : Type'} (f : form) (M : Structure A) : Structure A :=
  if forall v : nat -> A, valuation M v -> holds M v f
  then ε (fun M' : Structure A => Dom M' = Dom M /\ Pred M' = Pred M /\
       (forall n l, Fun M' n l <> Fun M (NUMSND n) l -> exists k, n = (NUMPAIR (num_of_form (bumpform f) + 1) k)) /\ 
       interpretation (language [set (SKOLEMIZE f)]) M' /\
       (forall v : nat -> A, valuation M' v -> holds M' v (SKOLEMIZE f)))
  else (Dom M , ((fun n l => ε (fun a : A => IN a (Dom M))), Pred M)).

Lemma SKOMOD1_def {A : Type'} : (@SKOMOD1 A) = (fun _226669 : form => fun _226670 : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) => @COND (prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop))) (forall v : nat -> A, (@valuation A _226670 v) -> @holds A _226670 v _226669) (@ε (prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop))) (fun M' : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) => ((@Dom A M') = (@Dom A (@bumpmod A _226670))) /\ (((@Pred A M') = (@Pred A (@bumpmod A _226670))) /\ ((forall g : nat, forall zs : seq A, (~ ((@Fun A M' g zs) = (@Fun A (@bumpmod A _226670) g zs))) -> exists l : nat, g = (NUMPAIR (addn (num_of_form (bumpform _226669)) (NUMERAL (BIT1 0))) l)) /\ ((@interpretation A (language (@INSERT form (SKOLEMIZE _226669) (@set0 form))) M') /\ (forall v : nat -> A, (@valuation A M' v) -> @holds A M' v (SKOLEMIZE _226669))))))) (@pair (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) (@Dom A _226670) (@pair (nat -> (seq A) -> A) (nat -> (seq A) -> Prop) (fun g : nat => fun zs : seq A => @ε A (fun a : A => @IN A a (@Dom A _226670))) (@Pred A _226670)))).
Proof.
  ext=> f M. rewrite/SKOMOD1. if_intro=>_ ; last by [].
  f_equal. funext => M'. by (do 5 f_equal) => /3=.
Qed.

Definition SKOMOD {A : Type'} (M : Structure A) : Structure A :=
  (Dom M,
  ((fun n s => match (NUMFST n) with
  | 0 => Fun M (NUMSND n) s
  | _ => Fun (SKOMOD1 (unbumpform (form_of_num (predn (NUMFST n)))) M) n s end),
  Pred M)).

Lemma SKOMOD_def {_196878 : Type'} : (@SKOMOD _196878) = (fun _226687 : prod (_196878 -> Prop) (prod (nat -> (seq _196878) -> _196878) (nat -> (seq _196878) -> Prop)) => @pair (_196878 -> Prop) (prod (nat -> (seq _196878) -> _196878) (nat -> (seq _196878) -> Prop)) (@Dom _196878 _226687) (@pair (nat -> (seq _196878) -> _196878) (nat -> (seq _196878) -> Prop) (fun g : nat => fun zs : seq _196878 => @COND _196878 ((NUMFST g) = (NUMERAL 0)) (@Fun _196878 _226687 (NUMSND g) zs) (@Fun _196878 (@SKOMOD1 _196878 (unbumpform (form_of_num (predn (NUMFST g)))) _226687) g zs)) (@Pred _196878 _226687))).
Proof.
  ext=> M. unfold SKOMOD. repeat f_equal.
  ext=> n l. if_intro ; induction (NUMFST n) ; auto.
  inversion 1. contradiction.
Qed.

Fixpoint specialize f :=
  match f with
  | FAll n f => specialize f
  | _ => f end.

Lemma specialize_def : specialize = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) -> form -> form) (fun specialize' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) -> form -> form => forall _227760 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))), ((specialize' _227760 FFalse) = FFalse) /\ ((forall p : nat, forall l : seq term, (specialize' _227760 (Atom p l)) = (Atom p l)) /\ ((forall q : form, forall r : form, (specialize' _227760 (FImp q r)) = (FImp q r)) /\ (forall x : nat, forall r : form, (specialize' _227760 (FAll x r)) = (specialize' _227760 r))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))))))))))))).
Proof. by total_align. Qed.

Definition SKOLEM f := specialize (SKOLEMIZE f).

Lemma SKOLEM_def : SKOLEM = (fun _227960 : form => specialize (SKOLEMIZE _227960)).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* Propositional calculus *)
(*****************************************************************************)

(* Representing Propositional calculus in FOL by considering that every atomic formula
   and every universally quantified formula is simply a propositional variable. *)

Fixpoint pholds (TrueVar : set form) (f : form) : Prop :=
  match f with
  | FFalse => False
  | FImp f f' => pholds TrueVar f -> pholds TrueVar f'
  | _ => TrueVar f end.

Lemma pholds_def : pholds = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (form -> Prop) -> form -> Prop) (fun pholds' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (form -> Prop) -> form -> Prop => forall _228069 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall v : form -> Prop, (pholds' _228069 v FFalse) = False) /\ ((forall v : form -> Prop, forall p : nat, forall l : seq term, (pholds' _228069 v (Atom p l)) = (v (Atom p l))) /\ ((forall q : form, forall v : form -> Prop, forall r : form, (pholds' _228069 v (FImp q r)) = ((pholds' _228069 v q) -> pholds' _228069 v r)) /\ (forall v : form -> Prop, forall x : nat, forall q : form, (pholds' _228069 v (FAll x q)) = (v (FAll x q)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))).
Proof. by total_align. Qed.

Definition psatisfies (s s' : form -> Prop) := forall f, s' f -> pholds s f.
Lemma psatisfies_def : psatisfies = (fun _228082 : form -> Prop => fun _228083 : form -> Prop => forall p : form, (@IN form p _228083) -> pholds _228082 p).
Proof. exact erefl. Qed.

Definition psatisfiable s' := exists s, psatisfies s s'.

Lemma psatisfiable_def : psatisfiable = (fun _228094 : form -> Prop => exists v : form -> Prop, forall p : form, (@IN form p _228094) -> pholds v p).
Proof. exact erefl. Qed.

Definition finsat (s : set form) : Prop :=
  forall F, subset F s /\ finite_set F -> psatisfiable F.

Lemma finsat_def : finsat = (fun _228106 : form -> Prop => forall B : form -> Prop, ((@subset form B _228106) /\ (@finite_set form B)) -> psatisfiable B).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* canonical models *)
(*****************************************************************************)

Fixpoint terms_bool (functions : set (nat * nat)) (t : term) := if t is Fn n s
  then functions (n, size s) && all (terms_bool functions) s
  else true.

Definition terms : _ -> set term := terms_bool.

Lemma ext_asboolb A (P : A -> bool) : (fun x => `[< P x >]) = P.
Proof.
  by ext=> ? ; rewrite asboolb.
Qed.

Lemma terms_def : terms = (fun fns : (prod nat nat) -> Prop => fun a : term => forall terms' : term -> Prop, (forall a' : term, ((exists x : nat, a' = (V x)) \/ (exists f : nat, exists l : seq term, (a' = (Fn f l)) /\ ((@IN (prod nat nat) (@pair nat nat f (@size term l)) fns) /\ (@ALL term terms' l)))) -> terms' a') -> terms' a).
Proof.
  rewrite/terms => /` functions t H.
  - move=>P H' ; elim: t H ; first by move=> * ; apply H' ; breakgoal.
    move => n s IHs /= ; case/andP ; rewrite asboolE=> fn allts ; apply H'.
    right ; exist n s ; do 2 (split ; first by []) ; rewrite/ALL.
    elim: {n fn H'} s IHs allts => //= t s IHs.
    by rewrite -3!andP** 2!asboolE => -[? /IHs {}IHs] [? /IHs {}IHs] ; auto.
  - apply H ; clear ; intros_namelast H0 ; full_destruct ; blindrewrite => //.
    by rewrite/ALL ext_asboolb in H1 ; apply/andP ; rewrite asboolE.
Qed.

Definition canonical (L : prod (set (prod nat nat)) (set (prod nat nat)))
  (M : Structure term) := (Dom M = terms (fst L) /\ (forall n, Fun M n = Fn n)).

Lemma canonical_def : canonical = (fun _230099 : prod ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) => fun _230100 : prod (term -> Prop) (prod (nat -> (seq term) -> term) (nat -> (seq term) -> Prop)) => ((@Dom term _230100) = (terms (@fst ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) _230099))) /\ (forall f : nat, (@Fun term _230100 f) = (Fn f))).
Proof. exact erefl. Qed.

Lemma prop_of_model_def {_199383 : Type'} : holds = (fun _230111 : prod (_199383 -> Prop) (prod (nat -> (seq _199383) -> _199383) (nat -> (seq _199383) -> Prop)) => fun _230112 : nat -> _199383 => fun _230113 : form => @holds _199383 _230111 _230112 _230113).
Proof. exact erefl. Qed.

Definition canon_of_prop (L : prod (set (prod nat nat)) (set (prod nat nat)))
  (Predval : form -> Prop)  := (terms (fst L), (Fn, fun (p : nat) (l : seq term) => Predval (Atom p l))).

Lemma canon_of_prop_def : canon_of_prop = (fun _230132 : prod ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) => fun _230133 : form -> Prop => @pair (term -> Prop) (prod (nat -> (seq term) -> term) (nat -> (seq term) -> Prop)) (terms (@fst ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) _230132)) (@pair (nat -> (seq term) -> term) (nat -> (seq term) -> Prop) Fn (fun p : nat => fun l : seq term => _230133 (Atom p l)))).
Proof. exact erefl. Qed.

Definition term_of_num := finv num_of_term.

Lemma term_of_num_def : term_of_num = (fun _230920 : nat => @ε term (fun t : term => (num_of_term t) = _230920)).
Proof. exact erefl. Qed.

Definition LOWMOD (M : Structure term) : Structure nat := ([set num_of_term t | t in Dom M], 
  (fun n s => num_of_term (Fun M n (map term_of_num s)),
  fun n s => Pred M n (map term_of_num s))).

Lemma LOWMOD_def : LOWMOD = (fun _230925 : prod (term -> Prop) (prod (nat -> (seq term) -> term) (nat -> (seq term) -> Prop)) => @pair (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)) (@GSPEC nat (fun GEN_PVAR_501 : nat => exists t : term, @SETSPEC nat GEN_PVAR_501 (@IN term t (@Dom term _230925)) (num_of_term t))) (@pair (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop) (fun g : nat => fun zs : seq nat => num_of_term (@Fun term _230925 g (@map nat term term_of_num zs))) (fun p : nat => fun zs : seq nat => @Pred term _230925 p (@map nat term term_of_num zs)))).
Proof. by ext=>* /3=. Qed.

(*****************************************************************************)
(* herbrand.ml *)
(*****************************************************************************)

Fixpoint herbase_bool (functions : set (nat * nat)) (t : term) := match t with
  | V n => (n == 0) && (0 \notin snd @` functions)
  | Fn n s => functions (n, size s) && all (herbase_bool functions) s end.

Definition herbase : _ -> set term := herbase_bool.

Lemma herbase_def : herbase = (fun fns : (prod nat nat) -> Prop => fun a : term => forall herbase' : term -> Prop, (forall a' : term, (((a' = (V (NUMERAL 0))) /\ (~ (exists c : nat, @IN (prod nat nat) (@pair nat nat c (NUMERAL 0)) fns))) \/ (exists f : nat, exists l : seq term, (a' = (Fn f l)) /\ ((@IN (prod nat nat) (@pair nat nat f (@size term l)) fns) /\ (@ALL term herbase' l)))) -> herbase' a') -> herbase' a).
Proof.
  rewrite/herbase => /` functions t H.
  - move=> P H'; elim: t H => /= [n|n s IHs]; case/andP; last rewrite asboolE.
    + move/eqP=> -> /negP ; rewrite in_setE => noconst ; apply H' ; left.
      by split => // -[i ?] ; apply: noconst ; exists (i, 0).
    + move=> fn allts ; apply H' ; right ; exist n s ; repeat split => //.
      rewrite/ALL ; elim: {n fn H'} s IHs allts => //= t s IHs.
      by rewrite -3!andP** 2!asboolE => -[? /IHs {}IHs] [? /IHs {}IHs] ; auto.
  - apply H ; clear ; intros_namelast H0 ; full_destruct ; blindrewrite => /=.
    + rewrite -negP** in_setE => -[[k _] /[swap] /= -> ?] ; apply: H0.
      by exists k.
    + by rewrite/ALL ext_asboolb in H1 ; apply/andP ; rewrite asboolE.
Qed.

Definition herbrand (L : prod (set (prod nat nat)) (set (prod nat nat)))
  (M : Structure term) := (Dom M = herbase (fst L) /\ (forall n, Fun M n = Fn n)).

Lemma herbrand_def : herbrand = (fun _232129 : prod ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) => fun _232130 : prod (term -> Prop) (prod (nat -> (seq term) -> term) (nat -> (seq term) -> Prop)) => ((@Dom term _232130) = (herbase (@fst ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) _232129))) /\ (forall f : nat, (@Fun term _232130 f) = (Fn f))).
Proof. exact erefl. Qed.

Definition herbrand_of_prop (L : prod (set (prod nat nat)) (set (prod nat nat)))
  (Predval : form -> Prop)  := (herbase (fst L), (Fn, fun (p : nat) (l : seq term) => Predval (Atom p l))).

Lemma herbrand_of_prop_def : herbrand_of_prop = (fun _232334 : prod ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) => fun _232335 : form -> Prop => @pair (term -> Prop) (prod (nat -> (seq term) -> term) (nat -> (seq term) -> Prop)) (herbase (@fst ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) _232334)) (@pair (nat -> (seq term) -> term) (nat -> (seq term) -> Prop) Fn (fun p : nat => fun l : seq term => _232335 (Atom p l)))).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* fole.ml : FOL with defined equality  *)
(*****************************************************************************)

Definition FEq t t' := Atom 0 (cons t (cons t' nil)).

Lemma FEq_def : FEq = (fun _232588 : term => fun _232589 : term => Atom (NUMERAL 0) (@cons term _232588 (@cons term _232589 (@nil term)))).
Proof. exact erefl. Qed.

Definition uclose f := ITLIST FAll (seq_of_set (free_variables f)) f.

Lemma uclose_def : uclose = (fun _232600 : form => @ITLIST nat form FAll (@seq_of_set nat (free_variables _232600)) _232600).
Proof. exact erefl. Qed.

Definition normal {A : Type'} functions (M : Structure A) :=
  (forall t t' v, valuation M v /\ IN t (terms functions) /\ IN t' (terms functions) ->
  holds M v (FEq t t') <-> (termval M v t = termval M v t')).

Lemma normal_def {_201755 : Type'} : (@normal _201755) = (fun _232605 : (prod nat nat) -> Prop => fun _232606 : prod (_201755 -> Prop) (prod (nat -> (seq _201755) -> _201755) (nat -> (seq _201755) -> Prop)) => forall s : term, forall t : term, forall v : nat -> _201755, ((@valuation _201755 _232606 v) /\ ((@IN term s (terms _232605)) /\ (@IN term t (terms _232605)))) -> (@holds _201755 _232606 v (FEq s t)) = ((@termval _201755 _232606 v s) = (@termval _201755 _232606 v t))).
Proof.
  ext=> functions M H t t' v H' ; apply H in H'.
  now apply propext. now rewrite H'.
Qed.

Fixpoint Varpairs n :=
  if n is n.+1 then (V n.*2, V n.*2.+1) :: (Varpairs n) else nil.

Lemma Varpairs_def : Varpairs = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> seq (prod term term)) (fun Varpairs' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> seq (prod term term) => forall _232620 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), ((Varpairs' _232620 (NUMERAL 0)) = (@nil (prod term term))) /\ (forall n : nat, (Varpairs' _232620 (S n)) = (@cons (prod term term) (@pair term term (V (muln (NUMERAL (BIT0 (BIT1 0))) n)) (V (addn (muln (NUMERAL (BIT0 (BIT1 0))) n) (NUMERAL (BIT1 0))))) (Varpairs' _232620 n)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))).
Proof.
  by total_align => // ? /2= ; rewrite mul2n addn1.
Qed.

Definition FEqc c := FEq (fst c) (snd c).

Lemma FEqc_exists : FEqc = ε (fun f : term * term -> form => forall s t : term, f (s, t) = FEq s t).
Proof.
  align_ε. reflexivity.
  intros Eq' _ H'. ext=> [[t t']]. now rewrite H'.
Qed.

Definition Eqaxiom_Func (f : prod nat nat) := uclose
  (FImp (foldr FAnd FTrue (map FEqc (Varpairs (snd f))))
    (FEq (Fn (fst f) (map fst (Varpairs (snd f)))) (Fn (fst f) (map snd (Varpairs (snd f)))))).

Lemma Eqaxiom_Func_def : Eqaxiom_Func = (fun _232621 : prod nat nat => uclose (FImp (@ITLIST form form FAnd (@map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (FEq s t))) (Varpairs (@snd nat nat _232621))) FTrue) (FEq (Fn (@fst nat nat _232621) (@map (prod term term) term (@fst term term) (Varpairs (@snd nat nat _232621)))) (Fn (@fst nat nat _232621) (@map (prod term term) term (@snd term term) (Varpairs (@snd nat nat _232621))))))).
Proof.
  unfold Eqaxiom_Func. now rewrite FEqc_exists.
Qed.

Definition Eqaxiom_Pred (P : prod nat nat) := uclose
  (FImp (foldr FAnd FTrue (map FEqc (Varpairs (snd P))))
    (FEquiv (Atom (fst P) (map fst (Varpairs (snd P)))) (Atom (fst P) (map snd (Varpairs (snd P)))))).

Lemma Eqaxiom_Pred_def : Eqaxiom_Pred = (fun _232630 : prod nat nat => uclose (FImp (@ITLIST form form FAnd (@map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (FEq s t))) (Varpairs (@snd nat nat _232630))) FTrue) (FEquiv (Atom (@fst nat nat _232630) (@map (prod term term) term (@fst term term) (Varpairs (@snd nat nat _232630)))) (Atom (@fst nat nat _232630) (@map (prod term term) term (@snd term term) (Varpairs (@snd nat nat _232630))))))).
Proof.
  unfold Eqaxiom_Pred. now rewrite FEqc_exists.
Qed.

Definition FEq_refl := FAll 0 (FEq (V 0) (V 0)).

Definition FEq_trans_sym := FAll 0 (FAll 1 (FAll 2 (FImp (FEq (V 0) (V 1))
 (FImp (FEq (V 2) (V 1)) (FEq (V 0) (V 2)))))).

Definition Eqaxioms (L : prod (set (prod nat nat)) (set (prod nat nat))) :=
  FEq_refl |` (FEq_trans_sym |` [set Eqaxiom_Func f | f in fst L] `|`
    [set Eqaxiom_Pred p | p in snd L]).

Lemma Eqaxioms_def : Eqaxioms = (fun _232639 : prod ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) => @setU form (@INSERT form (FAll (NUMERAL 0) (FEq (V (NUMERAL 0)) (V (NUMERAL 0)))) (@set0 form)) (@setU form (@INSERT form (FAll (NUMERAL 0) (FAll (NUMERAL (BIT1 0)) (FAll (NUMERAL (BIT0 (BIT1 0))) (FImp (FEq (V (NUMERAL 0)) (V (NUMERAL (BIT1 0)))) (FImp (FEq (V (NUMERAL (BIT0 (BIT1 0)))) (V (NUMERAL (BIT1 0)))) (FEq (V (NUMERAL 0)) (V (NUMERAL (BIT0 (BIT1 0)))))))))) (@set0 form)) (@setU form (@GSPEC form (fun GEN_PVAR_508 : form => exists fa : prod nat nat, @SETSPEC form GEN_PVAR_508 (@IN (prod nat nat) fa (@fst ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) _232639)) (Eqaxiom_Func fa))) (@GSPEC form (fun GEN_PVAR_509 : form => exists pa : prod nat nat, @SETSPEC form GEN_PVAR_509 (@IN (prod nat nat) pa (@snd ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) _232639)) (Eqaxiom_Pred pa)))))).
Proof.
  by ext 1 => ? ; rewrite/Eqaxioms/3= 4!setUA.
Qed.

Definition DOWNFROM n := rev (iota 0 n).

Lemma DOWNFROMSn n : DOWNFROM n.+1 = n :: DOWNFROM n.
Proof. by rewrite/DOWNFROM -addn1 iotaD rev_cat. Qed.

Lemma DOWNFROM_def : DOWNFROM = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> seq nat) (fun DOWNFROM' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> seq nat => forall _232733 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), ((DOWNFROM' _232733 (NUMERAL O)) = (@nil nat)) /\ (forall n : nat, (DOWNFROM' _232733 (S n)) = (@cons nat n (DOWNFROM' _232733 n)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))))))))))).
Proof. total_align ; [by [] | exact: DOWNFROMSn]. Qed.

(*****************************************************************************)
(* retval : bool with a 3rd possibility, exception *)
(*****************************************************************************)

Inductive retval := TT | FF | Exception.

HB.instance Definition _ := is_Type' TT.

Definition _dest_retval (v : retval) : recspace Prop :=
match v with
| TT => CONSTR 0 (ε (fun _ => True)) []_rec
| FF => CONSTR 1 (ε (fun _ => True)) []_rec
| Exception => CONSTR 2 (ε (fun _ => True)) []_rec end.

Definition _mk_retval := finv _dest_retval.

Lemma _mk_dest_retval : forall v, (_mk_retval (_dest_retval v)) = v.
Proof.
  _mk_dest_inductive.
Qed.

Lemma _dest_mk_retval : forall (r : recspace Prop), ((fun a : recspace Prop => forall retval' : (recspace Prop) -> Prop, (forall a' : recspace Prop, ((a' = (@CONSTR Prop (NUMERAL 0) (@ε Prop (fun x : Prop => True)) (fun n : nat => @BOTTOM Prop))) \/ ((a' = (@CONSTR Prop (S (NUMERAL 0)) (@ε Prop (fun x : Prop => True)) (fun n : nat => @BOTTOM Prop))) \/ (a' = (@CONSTR Prop (S (S (NUMERAL 0))) (@ε Prop (fun x : Prop => True)) (fun n : nat => @BOTTOM Prop))))) -> retval' a') -> retval' a) r) = ((_dest_retval (_mk_retval r)) = r).
Proof. by _dest_mk_inductive. Qed.

Lemma TT_def : TT = (_mk_retval (@CONSTR Prop (NUMERAL 0) (@ε Prop (fun x : Prop => True)) (fun n : nat => @BOTTOM Prop))).
Proof. constr_align _mk_dest_retval. Qed.

Lemma FF_def : FF = (_mk_retval (@CONSTR Prop (S (NUMERAL 0)) (@ε Prop (fun x : Prop => True)) (fun n : nat => @BOTTOM Prop))).
Proof. constr_align _mk_dest_retval. Qed.

Lemma Exception_def : Exception = (_mk_retval (@CONSTR Prop (S (S (NUMERAL 0))) (@ε Prop (fun x : Prop => True)) (fun n : nat => @BOTTOM Prop))).
Proof. constr_align _mk_dest_retval. Qed.

(*****************************************************************************)
(* Logic/unif.ml *)
(*****************************************************************************)

Definition OCC (env : seq (prod nat term)) n m :=
  exists t, (n, t) \in env /\ free_variables_term t m.

Lemma OCC_def : OCC = (fun _259304 : seq (prod nat term) => fun _259305 : nat => fun _259306 : nat => exists t : term, (@MEM (prod nat term) (@pair nat term _259305 t) _259304) /\ (@IN nat _259306 (free_variables_term t))).
Proof. exact erefl. Qed.

Definition LOOPFREE s := forall n, ~ Relation_Operators.clos_trans nat (OCC s) n n.

Lemma LOOPFREE_def : LOOPFREE = (fun _259325 : seq (prod nat term) => forall z : nat, ~ (@Relation_Operators.clos_trans nat (OCC _259325) z z)).
Proof. exact erefl. Qed.

Definition rightsubst (c c' : prod nat term) := (fst c',termsubst (valmod c V) (snd c')).

Lemma rightsubst_def : rightsubst = (fun _260241 : prod nat term => fun _260242 : prod nat term => @pair nat term (@fst nat term _260242) (termsubst (fun z : nat => @COND term (z = (@fst nat term _260241)) (@snd nat term _260241) (V z)) (@snd nat term _260242))).
Proof. exact erefl. Qed.

Fixpoint seq_rightsubst s c' :=
  if s is c::s then rightsubst c (seq_rightsubst s c') else c'.

Fixpoint lsubst s :=
  if s is c::s then seq_rightsubst (lsubst s) c :: lsubst s else nil.

Fixpoint self_rightsubst s := if s is c::s
  then let c' := seq_rightsubst (lsubst s) c in
    c'::map (rightsubst c') (self_rightsubst s)
  else nil.

Definition SOLVE s s' := let s'' := rev s' in
  (self_rightsubst s'') ++ (map (seq_rightsubst (lsubst s'')) s).

Definition SOLVEC c := SOLVE (fst c) (snd c).

Lemma seq_rightsubst_rcons c s c' :
  seq_rightsubst (rcons s c) c' = seq_rightsubst s (rightsubst c c').
Proof. by elim:s => //= ? ? ->. Qed.

Lemma lsubst_rcons s c :
  lsubst (rcons s c) =
  rcons (lsubst (map (rightsubst c) s)) c.
Proof.
  by elim: s => //= ? ? -> ; rewrite seq_rightsubst_rcons.
Qed.

Lemma self_rightsubst_rcons s c :
  self_rightsubst (rcons s c) = let s' := map (rightsubst c) s in
  rcons (self_rightsubst s') (seq_rightsubst (lsubst s') c).
Proof.
  by elim: s => //= ? ? -> ; rewrite map_rcons lsubst_rcons seq_rightsubst_rcons.
Qed.

Lemma SOLVEC_def : SOLVEC = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (prod (seq (prod nat term)) (seq (prod nat term))) -> seq (prod nat term)) (fun SOLVE' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (prod (seq (prod nat term)) (seq (prod nat term))) -> seq (prod nat term) => forall _260267 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), forall pr : prod (seq (prod nat term)) (seq (prod nat term)), (SOLVE' _260267 pr) = (@COND (seq (prod nat term)) ((@snd (seq (prod nat term)) (seq (prod nat term)) pr) = (@nil (prod nat term))) (@fst (seq (prod nat term)) (seq (prod nat term)) pr) (SOLVE' _260267 (@pair (seq (prod nat term)) (seq (prod nat term)) (@cons (prod nat term) (@HD (prod nat term) (@snd (seq (prod nat term)) (seq (prod nat term)) pr)) (@map (prod nat term) (prod nat term) (rightsubst (@HD (prod nat term) (@snd (seq (prod nat term)) (seq (prod nat term)) pr))) (@fst (seq (prod nat term)) (seq (prod nat term)) pr))) (@map (prod nat term) (prod nat term) (rightsubst (@HD (prod nat term) (@snd (seq (prod nat term)) (seq (prod nat term)) pr))) (@TL (prod nat term) (@snd (seq (prod nat term)) (seq (prod nat term)) pr))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof.
  rewrite/SOLVEC/SOLVE. align_ε.
  - case=> s s' /= ; if_seq ; case: s' => [|a s'] /= ; first exact: map_id.
    rewrite rev_cons self_rightsubst_rcons cat_rcons map_rev ; do 2 f_equal.
    rewrite lsubst_rcons map_rev -map_comp ; f_equal => /` c.
    by rewrite seq_rightsubst_rcons.
  - move=> f' H H' /` -[s s']. rewrite -(map_id s') -/(seq_rightsubst nil).
    elim: s' nil s => [|c' s' IHs'] c s ; rewrite H H' /= ; do 2 if_seq => //.
    by rewrite -{H H'}map_comp -[X in map X _]/
      (fun x=> seq_rightsubst ((seq_rightsubst c c')::c) x) -IHs'.
Qed.

Lemma SOLVE_def : SOLVE = (fun _260268 : seq (prod nat term) => fun _260269 : seq (prod nat term) => SOLVEC (@pair (seq (prod nat term)) (seq (prod nat term)) _260268 _260269)).
Proof. exact erefl. Qed.

Definition CONFLICTFREE (s : seq (nat*term)) :=
  forall n, size (filter (fun c => fst c == n) s) <= 1.

Lemma asbool_inj P Q : (`[< P >] = `[< Q >]) = (P = Q).
Proof.
  move => /1` ; [(do 2 case:asboolP) => // HP HQ | by move=> ->].
  - by is_True HP ; is_True HQ.
  - by is_False HP ; is_False HQ.
Qed.

Lemma CONFLICTFREE_def : CONFLICTFREE = (fun _260280 : seq (prod nat term) => forall x : nat, leqn (@size (prod nat term) (@filter (prod nat term) (@ε ((prod nat term) -> Prop) (fun f : (prod nat term) -> Prop => forall y : nat, forall s : term, @eq Prop (f (@pair nat term y s)) (y = x))) _260280)) (NUMERAL (BIT1 0))).
Proof.
  rewrite/CONFLICTFREE => /f` s /=.
  apply (f_equal (fun f => forall n : nat, size (filter (f n) s) <= 1)).
  ext => n c /= ; rewrite -[LHS]asboolb asbool_inj.
  apply (f_equal (fun f => f c) (x := fun c => is_true (c.1 == n))).
  align_ε ; first by move=> * ; rewrite -eqP**.
  by move=> ? + + /1` -[? ?] => -> ->.
Qed.

(* again, a difficult partial function. *) 
Definition istriv : (seq (prod nat term)) -> nat -> term -> retval := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq (prod nat term)) -> nat -> term -> retval) (fun istriv' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq (prod nat term)) -> nat -> term -> retval => forall _262675 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), forall env : seq (prod nat term), forall x : nat, ((LOOPFREE env) /\ (CONFLICTFREE env)) -> forall t : term, (istriv' _262675 env x t) = (@COND retval (t = (V x)) TT (@COND retval (exists y : nat, (t = (V y)) /\ (@MEM nat y (@map (prod nat term) nat (@fst nat term) env))) (istriv' _262675 env x (@ASSOC nat term (@ε nat (fun y : nat => (t = (V y)) /\ (@MEM nat y (@map (prod nat term) nat (@fst nat term) env)))) env)) (@COND retval (@IN nat x (free_variables_term t)) Exception (@COND retval (exists y : nat, exists s : term, (@IN nat y (free_variables_term t)) /\ ((@MEM (prod nat term) (@pair nat term y s) env) /\ (~ ((istriv' _262675 env x s) = FF)))) Exception FF))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))).
Lemma istriv_def : istriv = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq (prod nat term)) -> nat -> term -> retval) (fun istriv' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq (prod nat term)) -> nat -> term -> retval => forall _262675 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), forall env : seq (prod nat term), forall x : nat, ((LOOPFREE env) /\ (CONFLICTFREE env)) -> forall t : term, (istriv' _262675 env x t) = (@COND retval (t = (V x)) TT (@COND retval (exists y : nat, (t = (V y)) /\ (@MEM nat y (@map (prod nat term) nat (@fst nat term) env))) (istriv' _262675 env x (@ASSOC nat term (@ε nat (fun y : nat => (t = (V y)) /\ (@MEM nat y (@map (prod nat term) nat (@fst nat term) env)))) env)) (@COND retval (@IN nat x (free_variables_term t)) Exception (@COND retval (exists y : nat, exists s : term, (@IN nat y (free_variables_term t)) /\ ((@MEM (prod nat term) (@pair nat term y s) env) /\ (~ ((istriv' _262675 env x s) = FF)))) Exception FF))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))).
Proof. exact erefl. Qed.

Definition EQV {A : Type'} s (a : A) n := MEM (a, V n) s.

Lemma EQV_def {_208558 : Type'} : (@EQV _208558) = (fun _263122 : seq (prod _208558 term) => fun _263123 : _208558 => fun _263124 : nat => @MEM (prod _208558 term) (@pair _208558 term _263123 (V _263124)) _263122).
Proof. exact erefl. Qed.

Definition SUB1 t t' := exists n s, t' = Fn n s /\ t \in s.

Lemma SUB1_def : SUB1 = (fun _267259 : term => fun _267260 : term => exists f : nat, exists args : seq term, (_267260 = (Fn f args)) /\ (@MEM term _267259 args)).
Proof. exact erefl. Qed.

Definition termcases {A : Type} caseV caseFn t : A :=
  match t with
  | V n => caseV n
  | Fn n s => caseFn n s end.

Lemma termcases_def {_209078 : Type'} : (@termcases _209078) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (nat -> _209078) -> (nat -> (seq term) -> _209078) -> term -> _209078) (fun termcases' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (nat -> _209078) -> (nat -> (seq term) -> _209078) -> term -> _209078 => forall _267400 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), (forall cf : nat -> (seq term) -> _209078, forall cv : nat -> _209078, forall v : nat, (termcases' _267400 cv cf (V v)) = (cv v)) /\ (forall cv : nat -> _209078, forall cf : nat -> (seq term) -> _209078, forall f : nat, forall args : seq term, (termcases' _267400 cv cf (Fn f args)) = (cf f args))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))))).
Proof. by term_align. Qed.

Definition tpcases {A : Type} caseFn_Fn caseV caseFn_V c : A :=
    match fst c with
    | V n => caseV n (snd c)
    | Fn n s => match snd c with
      | V n' => caseFn_V n s n'
      | Fn n' s' => caseFn_Fn n s n' s' end end.

Lemma tpcases_def {_209138 : Type'} : (@tpcases _209138) = (fun _267401 : nat -> (seq term) -> nat -> (seq term) -> _209138 => fun _267402 : nat -> term -> _209138 => fun _267403 : nat -> (seq term) -> nat -> _209138 => fun _267404 : prod term term => @termcases _209138 (fun v1 : nat => @termcases _209138 (fun v2 : nat => _267402 v1 (V v2)) (fun f2 : nat => fun args2 : seq term => _267402 v1 (Fn f2 args2)) (@snd term term _267404)) (fun f1 : nat => fun args1 : seq term => @termcases _209138 (fun v2 : nat => _267403 f1 args1 v2) (fun f2 : nat => fun args2 : seq term => _267401 f1 args1 f2 args2) (@snd term term _267404)) (@fst term term _267404)).
Proof. ext => f f' f'' [t t']. now induction t'. Qed.

Definition MLEFT c :=
  match c with (env,eqs) =>
    CARD (setU (free_variables_term (Fn 0 (map fst eqs)))
    (setU (free_variables_term (Fn 0 (map snd eqs)))
    (setU (free_variables_term (Fn 0 (map snd env)))
    (free_variables_term (Fn 0 (map (Basics.compose V fst) env)))))) -
    CARD (free_variables_term (Fn 0 (map (Basics.compose V fst) env))) end.

Lemma MLEFT_def : MLEFT = (fun _267440 : prod (seq (prod nat term)) (seq (prod term term)) => subn (@CARD nat (@setU nat (free_variables_term (Fn (NUMERAL 0) (@map (prod term term) term (@fst term term) (@snd (seq (prod nat term)) (seq (prod term term)) _267440)))) (@setU nat (free_variables_term (Fn (NUMERAL 0) (@map (prod term term) term (@snd term term) (@snd (seq (prod nat term)) (seq (prod term term)) _267440)))) (@setU nat (free_variables_term (Fn (NUMERAL 0) (@map (prod nat term) term (@snd nat term) (@fst (seq (prod nat term)) (seq (prod term term)) _267440)))) (free_variables_term (Fn (NUMERAL 0) (@map (prod nat term) term (@Basics.compose (prod nat term) nat term V (@fst nat term)) (@fst (seq (prod nat term)) (seq (prod term term)) _267440)))))))) (@CARD nat (free_variables_term (Fn (NUMERAL 0) (@map (prod nat term) term (@Basics.compose (prod nat term) nat term V (@fst nat term)) (@fst (seq (prod nat term)) (seq (prod term term)) _267440)))))).
Proof. ext=> [[env eqs]]. reflexivity. Qed.

Definition CRIGHT c c' := match c,c' with (env', eqs'),(env, eqs) =>
  (LOOPFREE env /\
   env' = env /\
   ((exists (f : nat) (args1 args2 : seq term) (oth : seq (term * term)),
       size args1 = size args2 /\
       eqs = (Fn f args1, Fn f args2) :: oth /\ eqs' = ZIP args1 args2 ++ oth) \/
    (exists (x : nat) (t : term) (oth : seq (term * term)),
       eqs = (V x, t) :: oth /\
       (x \in (map fst env) /\ eqs' = (ASSOC x env, t) :: oth \/
        x \notin (map fst env) /\ istriv env x t = TT /\ eqs' = oth)) \/
    (exists (x f : nat) (args : seq term) (oth : seq (term * term)),
       eqs = (Fn f args, V x) :: oth /\ eqs' = (V x, Fn f args) :: oth))) end. 

Lemma CRIGHT_def : CRIGHT = (fun _267449 : prod (seq (prod nat term)) (seq (prod term term)) => fun _267450 : prod (seq (prod nat term)) (seq (prod term term)) => (LOOPFREE (@fst (seq (prod nat term)) (seq (prod term term)) _267450)) /\ (((@fst (seq (prod nat term)) (seq (prod term term)) _267449) = (@fst (seq (prod nat term)) (seq (prod term term)) _267450)) /\ ((exists f : nat, exists args1 : seq term, exists args2 : seq term, exists oth : seq (prod term term), ((@size term args1) = (@size term args2)) /\ (((@snd (seq (prod nat term)) (seq (prod term term)) _267450) = (@cons (prod term term) (@pair term term (Fn f args1) (Fn f args2)) oth)) /\ ((@snd (seq (prod nat term)) (seq (prod term term)) _267449) = (@app (prod term term) (@ZIP term term args1 args2) oth)))) \/ ((exists x : nat, exists t : term, exists oth : seq (prod term term), ((@snd (seq (prod nat term)) (seq (prod term term)) _267450) = (@cons (prod term term) (@pair term term (V x) t) oth)) /\ (((@MEM nat x (@map (prod nat term) nat (@fst nat term) (@fst (seq (prod nat term)) (seq (prod term term)) _267450))) /\ ((@snd (seq (prod nat term)) (seq (prod term term)) _267449) = (@cons (prod term term) (@pair term term (@ASSOC nat term x (@fst (seq (prod nat term)) (seq (prod term term)) _267450)) t) oth))) \/ ((~ (@MEM nat x (@map (prod nat term) nat (@fst nat term) (@fst (seq (prod nat term)) (seq (prod term term)) _267450)))) /\ (((istriv (@fst (seq (prod nat term)) (seq (prod term term)) _267450) x t) = TT) /\ ((@snd (seq (prod nat term)) (seq (prod term term)) _267449) = oth))))) \/ (exists x : nat, exists f : nat, exists args : seq term, exists oth : seq (prod term term), ((@snd (seq (prod nat term)) (seq (prod term term)) _267450) = (@cons (prod term term) (@pair term term (Fn f args) (V x)) oth)) /\ ((@snd (seq (prod nat term)) (seq (prod term term)) _267449) = (@cons (prod term term) (@pair term term (V x) (Fn f args)) oth))))))).
Proof.
  funext=> [[? ?] [? ?]] ; rewrite/CRIGHT/MEM/= ; (do 4 f_equal).
  by do 3 f_equal => /1` ? ; do 3 f_equal ; rewrite negP**.
Qed.

Definition CALLORDER c' c :=
  MEASURE MLEFT c' c \/ CRIGHT c' c.

Lemma CALLORDER_def : CALLORDER = (fun _267471 : prod (seq (prod nat term)) (seq (prod term term)) => fun _267472 : prod (seq (prod nat term)) (seq (prod term term)) => (@MEASURE (prod (seq (prod nat term)) (seq (prod term term))) MLEFT (@pair (seq (prod nat term)) (seq (prod term term)) (@fst (seq (prod nat term)) (seq (prod term term)) _267471) (@snd (seq (prod nat term)) (seq (prod term term)) _267471)) (@pair (seq (prod nat term)) (seq (prod term term)) (@fst (seq (prod nat term)) (seq (prod term term)) _267472) (@snd (seq (prod nat term)) (seq (prod term term)) _267472))) \/ (CRIGHT (@pair (seq (prod nat term)) (seq (prod term term)) (@fst (seq (prod nat term)) (seq (prod term term)) _267471) (@snd (seq (prod nat term)) (seq (prod term term)) _267471)) (@pair (seq (prod nat term)) (seq (prod term term)) (@fst (seq (prod nat term)) (seq (prod term term)) _267472) (@snd (seq (prod nat term)) (seq (prod term term)) _267472)))).
Proof. funext=> [[env' eqs'] [env eqs]]. reflexivity. Qed.

(*****************************************************************************)
(* Trivial definitions *)
(*****************************************************************************)
Definition V_def' : V = V := erefl.
Definition Fn_def' : Fn = Fn := erefl.
Definition FFalse_def' : FFalse = FFalse:= erefl.
Definition FImp_def' : FImp = FImp := erefl.
Definition Atom_def' : Atom = Atom := erefl.
Definition FAll_def' : FAll = FAll := erefl.
Definition TT_def' : TT = TT := erefl.
Definition FF_def' : FF = FF := erefl.
Definition Exception_def' : Exception = Exception := erefl.
