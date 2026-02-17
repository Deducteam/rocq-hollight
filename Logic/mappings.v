From Equations Require Import Equations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq ssrAC.
From mathcomp Require Import choice bigop finmap boolp classical_sets.
From mathcomp Require Import cardinality.
Require Export HOLLight.Unif.mappings.
Require Import HOLLight.Unif.theorems.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Inductive loopcheck_ind (env : seq (prod nat term)) : nat -> term -> Prop :=
  | loopcheck_isfreein : forall n t, free_variables_term t n -> loopcheck_ind env n t
  | loopcheck_rec : forall n t n' t', free_variables_term t n' ->
                    (n',t') \in env -> loopcheck_ind env n t' -> loopcheck_ind env n t.

Definition loopcheck_HOL : (seq (prod nat term)) -> nat -> term -> Prop := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (seq (prod nat term)) -> nat -> term -> Prop) (fun loopcheck' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (seq (prod nat term)) -> nat -> term -> Prop => forall _260318 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), forall env : seq (prod nat term), forall x : nat, (LOOPFREE env) -> forall t : term, (loopcheck' _260318 env x t) = (exists y : nat, (@IN nat y (free_variables_term t)) /\ ((y = x) \/ (exists s : term, (@MEM (prod nat term) (@pair nat term y s) env) /\ (loopcheck' _260318 env x s))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))))))))))).

Definition loopcheck env := if LOOPFREE env then loopcheck_ind env else loopcheck_HOL env.

Lemma loopcheck_def : loopcheck = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (seq (prod nat term)) -> nat -> term -> Prop) (fun loopcheck' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (seq (prod nat term)) -> nat -> term -> Prop => forall _260318 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), forall env : seq (prod nat term), forall x : nat, (LOOPFREE env) -> forall t : term, (loopcheck' _260318 env x t) = (exists y : nat, (@IN nat y (free_variables_term t)) /\ ((y = x) \/ (exists s : term, (@MEM (prod nat term) (@pair nat term y s) env) /\ (loopcheck' _260318 env x s))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 O))))))))))))))))).
Proof.
  move=> /1` env.
  apply: (partial_align_case1 (fun env => ~LOOPFREE env) (fun=> loopcheck)) => {env} /=.
  - move=> _ * ; rewrite/loopcheck /1= ; ext.
    + elim => * ; breakgoal.
    + case=> ? /3= [? [<- | [? [*]]]].
      * exact: loopcheck_isfreein.
      * apply: loopcheck_rec ; eassumption.
  - by rewrite/loopcheck => * /1=.
  - move=> f' uv env Hf Hf' /[spec env]trivcase /f` + t.
    case: (EM (LOOPFREE env)) => [LOOPFREEenv | /trivcase ->] ; last by [].
    elim: (thm_LOOPFREE_WF_TERM _ LOOPFREEenv t) => {}t _ IHt n.
    rewrite (Hf uv env n LOOPFREEenv t) (Hf' uv env n LOOPFREEenv t).
    ext => -[y [? [? | [? [?]]]]].
    2 : rewrite IHt => *. 5 : rewrite -IHt => *.
    all : breakgoal.
Qed.

Instance WF_CALLORDER : WellFounded CALLORDER := thm_WF_CALLORDER.

Definition istriv_with_witness env n t : {istriv env n t = TT} + {istriv env n t = FF} +
  {istriv env n t = Exception}.
Proof. by case: (istriv env n t) ; constructor ; try constructor. Defined.

Definition sumboolB : forall b : bool, {b} + {~~b}.
Proof. by case ; constructor. Defined.

Lemma CARD_setU_min_l {A : Type'} (s1 s2 : set A) :
  finite_set s1 -> finite_set s2 -> CARD s1 <= CARD (s1 `|` s2).
Proof.
  intros H1 H2. apply thm_CARD_SUBSET. split.
  apply thm_SUBSET_UNION. now apply thm_FINITE_UNION_IMP.
Qed.

Lemma CARD_setU_min_r {A : Type'} (s1 s2 : set A) :
  finite_set s1 -> finite_set s2 -> CARD s2 <= CARD (s1 `|` s2).
Proof.
  intros H1 H2. apply thm_CARD_SUBSET. split.
  apply thm_SUBSET_UNION. now apply thm_FINITE_UNION_IMP.
Qed.

Lemma finite_set_lUmapfvt : forall s, finite_set (seq_Union (map free_variables_term s)).
Proof.
  induction s ; first by [].
  apply thm_FINITE_UNION_IMP. split;auto.
  apply thm_FVT_FINITE.
Qed.

Opaque CALLORDER.

Equations? unify (c : seq (nat * term) * seq (term * term)) :
option (seq (nat * term)) by wf c CALLORDER :=
  unify (env,_) with pselect (LOOPFREE env) => {
    unify _ (right _ notloopfree) => None;
    unify (env,nil) _ => Some env;
    unify (env , (V n , t') :: eqs) _
    with (sumboolB (n \in map fst env)) => {
      unify (env , (V n , t') :: eqs) (left _ loopfree) (left _ n_mapped) =>
        unify (env , (ASSOC n env , t') :: eqs);
      unify (env , (V n , t') :: eqs) (left _ loopfree) (right _ n_notmapped)
      with istriv_with_witness env n t' => {
        | inright _ t'_Vn_ununifiable => None;
        | inleft _ (left _ t'_Vn_unified) => unify (env,eqs);
        | inleft _ (right _ t'_Vn_unifiable) => unify ((n,t') :: env , eqs)}};
    unify (env , (Fn n s , V n') :: eqs) (left _ loopfree) =>
      unify (env , (V n' , Fn n s) :: eqs);
    unify (env , (Fn n s , Fn n' s') :: eqs) (left _ loopfree)
    with pselect (n = n' /\ size s = size s') => {
      | right _ _ => None;
      | left _ same_fun => unify (env , ZIP s s' ++ eqs)}}.
Proof.
  1,2,4,5 : right ; repeat split ; auto.
  4 : case:same_fun=> -> ?.
  1-4: breakgoal.
  left ; rewrite/MEASURE/MLEFT/=.
  match goal with |- is_true (_ < CARD ((?sn `|` ?e1) `|`
    ((?e3 `|` ?e2) `|` (?e4 `|` ?e5))) - CARD ?e5) =>
    remember e1 as s1 ; remember e2 as s2 ; remember e3 as E3 ;
    remember e4 as E4 ; remember e5 as E5 ; remember sn as Sn end.
  have Fs1 : finite_set s1 by subst s1 ; exact: finite_set_lUmapfvt.
  have Fs2 : finite_set s2 by subst s2 ; exact: finite_set_lUmapfvt.
  have FE3 : finite_set E3 by subst E3 ; exact: thm_FVT_FINITE.
  have FE4 : finite_set E4 by subst E4 ; exact: finite_set_lUmapfvt.
  have FE5 : finite_set E5 by subst E5 ; exact: finite_set_lUmapfvt.
  have FSn : finite_set Sn by subst Sn.
  have n_notmapped' : ~ IN n E5.
  { rewrite HeqE5 thm_IN_LIST_UNION (map_comp V fst) /3=.
    elim:(map fst env) n_notmapped => [|a s /= IHs] ; first by inversion 1.
    rewrite in_cons negb_or /= => /andP [? /IHs].
    rewrite/EX 2!negP** /= => /negbTE -> ; rewrite Bool.orb_false_r.
    by rewrite eqP** asboolb. }
  have Sn_E5 : CARD (Sn `&` E5) = 0.
  { rewrite -/(NUMERAL 0) thm_CARD_EQ_0 ; last by apply:finite_setI ; left.
    by ext => k [] ; rewrite HeqSn => ->. }
  replace (CARD (setU Sn E5)) with (CARD E5 + 1).
  match goal with |- is_true (?n - _ < ?m - _) => replace m with n end.
  - rewrite subnDA ltn_subLR ; first by [].
    apply: (@leq_trans (CARD (Sn `|` E5) - CARD E5)).
    + rewrite thm_CARD_UNION_GEN // Sn_E5 subn0 addnK -(setU0 Sn) HeqSn.
      by rewrite thm_CARD_SING.
    + apply leq_sub2r ; rewrite 2!setUA.
      by apply: CARD_setU_min_r ; rewrite !finite_setU.
  - by rewrite [X in CARD X = _](AC (1*(1*(2*2))) (5*1*(3*2*(4*6)))).
  - by rewrite HeqSn addn1 (proj2 thm_CARD_CLAUSES) //1=.
Qed.

Lemma unify_def : unify = (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> (prod (seq (prod nat term)) (seq (prod term term))) -> option (seq (prod nat term))) (fun unify' : (prod nat (prod nat (prod nat (prod nat nat)))) -> (prod (seq (prod nat term)) (seq (prod term term))) -> option (seq (prod nat term)) => forall _268410 : prod nat (prod nat (prod nat (prod nat nat))), forall pr : prod (seq (prod nat term)) (seq (prod term term)), (unify' _268410 pr) = (@COND (option (seq (prod nat term))) (~ (LOOPFREE (@fst (seq (prod nat term)) (seq (prod term term)) pr))) (@None (seq (prod nat term))) (@COND (option (seq (prod nat term))) ((@snd (seq (prod nat term)) (seq (prod term term)) pr) = (@nil (prod term term))) (@Some (seq (prod nat term)) (@fst (seq (prod nat term)) (seq (prod term term)) pr)) (@tpcases (option (seq (prod nat term))) (fun f : nat => fun fargs : seq term => fun g : nat => fun gargs : seq term => @COND (option (seq (prod nat term))) ((f = g) /\ ((@size term fargs) = (@size term gargs))) (unify' _268410 (@pair (seq (prod nat term)) (seq (prod term term)) (@fst (seq (prod nat term)) (seq (prod term term)) pr) (@app (prod term term) (@ZIP term term fargs gargs) (@TL (prod term term) (@snd (seq (prod nat term)) (seq (prod term term)) pr))))) (@None (seq (prod nat term)))) (fun x : nat => fun t : term => @COND (option (seq (prod nat term))) (@MEM nat x (@List.map (prod nat term) nat (@fst nat term) (@fst (seq (prod nat term)) (seq (prod term term)) pr))) (unify' _268410 (@pair (seq (prod nat term)) (seq (prod term term)) (@fst (seq (prod nat term)) (seq (prod term term)) pr) (@cons (prod term term) (@pair term term (@ASSOC nat term x (@fst (seq (prod nat term)) (seq (prod term term)) pr)) t) (@TL (prod term term) (@snd (seq (prod nat term)) (seq (prod term term)) pr))))) (@COND (option (seq (prod nat term))) ((istriv (@fst (seq (prod nat term)) (seq (prod term term)) pr) x t) = Exception) (@None (seq (prod nat term))) (@COND (option (seq (prod nat term))) ((istriv (@fst (seq (prod nat term)) (seq (prod term term)) pr) x t) = TT) (unify' _268410 (@pair (seq (prod nat term)) (seq (prod term term)) (@fst (seq (prod nat term)) (seq (prod term term)) pr) (@TL (prod term term) (@snd (seq (prod nat term)) (seq (prod term term)) pr)))) (unify' _268410 (@pair (seq (prod nat term)) (seq (prod term term)) (@cons (prod nat term) (@pair nat term x t) (@fst (seq (prod nat term)) (seq (prod term term)) pr)) (@TL (prod term term) (@snd (seq (prod nat term)) (seq (prod term term)) pr))))))) (fun f : nat => fun args : seq term => fun x : nat => unify' _268410 (@pair (seq (prod nat term)) (seq (prod term term)) (@fst (seq (prod nat term)) (seq (prod term term)) pr) (@cons (prod term term) (@pair term term (V x) (Fn f args)) (@TL (prod term term) (@snd (seq (prod nat term)) (seq (prod term term)) pr))))) (@HD (prod term term) (@snd (seq (prod nat term)) (seq (prod term term)) pr)))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))))))))).
Proof.
  align_ε.
  - intros (env,eqs). funelim (unify (env,eqs)) ; rewrite/tpcases/= => //1=.
    all: move: {Heq0} n_notmapped => /negP ? /1=.
    + by rewrite t'_Vn_unified/1=.
    + by rewrite t'_Vn_unifiable/1=.
    + by [].
  - intros g _ Hg. ext => [[env eqs]]. funelim (unify (env,eqs)) ;
    rewrite Hg ; (try match goal with H : _ |- _ =>
      specialize (H g Hg) as H ; match type of H with _ = ?b =>
        transitivity b ; auto end end) ; (* rewrite is not working for some reason *)
        clear Hg ; rewrite/tpcases //1=.
    all: move: {Heq0} n_notmapped => /negP ? /1=.
    + by rewrite t'_Vn_unified/1=.
    + by rewrite t'_Vn_unifiable/1=.
    + by [].
Qed.

Definition unifies v s : Prop := all (fun c => termsubst v c.1 = termsubst v c.2) s.

Lemma unifies_def : unifies = (fun _268411 : nat -> term => fun _268412 : seq (prod term term) => @ALL (prod term term) (@ε ((prod term term) -> Prop) (fun f : (prod term term) -> Prop => forall s : term, forall t : term, @eq Prop (f (@pair term term s t)) ((termsubst _268411 s) = (termsubst _268411 t)))) _268412).
Proof.
  funext=> v l ; rewrite/unifies -/(ALL _ _) ; f_equal => /=.
  by align_ε ; [reflexivity | move=> * /f` -[*]].
Qed.

Inductive is_None (A : Type) : option A -> Prop :=
  is_None_def : is_None None.

Arguments is_None : clear implicits.

Definition THE {_211969 : Type'} : (option _211969) -> _211969 := @ε ((prod nat (prod nat nat)) -> (option _211969) -> _211969) (fun THE' : (prod nat (prod nat nat)) -> (option _211969) -> _211969 => forall _274433 : prod nat (prod nat nat), forall x : _211969, (THE' _274433 (@Some _211969 x)) = x) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))).

Definition the {A : Type'} (x : option A) :=
  match x with None => THE None | Some a => a end.

Lemma THE_def {_211969 : Type'} : (@the _211969) = (@ε ((prod nat (prod nat nat)) -> (option _211969) -> _211969) (fun THE' : (prod nat (prod nat nat)) -> (option _211969) -> _211969 => forall _274433 : prod nat (prod nat nat), forall x : _211969, (THE' _274433 (@Some _211969 x)) = x) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof. by partial_align (is_None _211969). Qed.

Definition unifier s := foldr valmod V (SOLVE nil s).

Lemma unifier_def : unifier = (fun _274434 : seq (prod nat term) => @LET (seq (prod nat term)) (nat -> term) (fun sol : seq (prod nat term) => @LET_END (nat -> term) (@ITLIST (prod nat term) (nat -> term) (@valmod term nat) sol V)) (SOLVE (@nil (prod nat term)) _274434)).
Proof. reflexivity. Qed.

Definition Unifies subst E := forall f f' : form,
  IN f E /\ IN f' E -> formsubst subst f = formsubst subst f'.

Lemma Unifies_def : Unifies = (fun _275904 : nat -> term => fun _275905 : form -> Prop => Logic.all (fun p : form => Logic.all (fun q : form => ((@IN form p _275905) /\ (@IN form q _275905)) -> eq (formsubst _275904 p) (formsubst _275904 q)))).
Proof. reflexivity. Qed.

Definition mgu : (form -> Prop) -> nat -> term := fun _276282 : form -> Prop => @ε (nat -> term) (fun i : nat -> term => (Unifies i _276282) /\ (forall j : nat -> term, (Unifies j _276282) -> forall p : form, (qfree p) -> (formsubst j p) = (formsubst j (formsubst i p)))).

Lemma mgu_def : mgu = (fun _276282 : form -> Prop => @ε (nat -> term) (fun i : nat -> term => (Unifies i _276282) /\ (Logic.all (fun j : nat -> term => (Unifies j _276282) -> Logic.all (fun p : form => (qfree p) -> eq (formsubst j p) (formsubst j (formsubst i p))))))).
Proof. reflexivity. Qed.

Definition ismgu E subst :=
  Unifies subst E /\
  (forall subst' : nat -> term, Unifies subst' E ->
  exists subst'' : nat -> term, termsubst subst' = termsubst subst'' \o termsubst subst).

Lemma ismgu_def : ismgu = (fun _276290 : form -> Prop => fun _276291 : nat -> term => (Unifies _276291 _276290) /\ (Logic.all (fun j : nat -> term => (Unifies j _276290) -> ex (fun k : nat -> term => eq (termsubst j) (@o term term term (termsubst k) (termsubst _276291)))))).
Proof. reflexivity. Qed.

Definition renaming (subst : nat -> term) :=
  exists subst' : nat -> term, forall t,
  (termsubst subst' (termsubst subst t)) = t /\
  (termsubst subst (termsubst subst' t)) = t.

Lemma renaming_def : renaming = (fun _276319 : nat -> term => exists j : nat -> term, ((@o term term term (termsubst j) (termsubst _276319)) = (@Datatypes.id term)) /\ ((@o term term term (termsubst _276319) (termsubst j)) = (@Datatypes.id term))).
Proof.
  ext=> subst [subst' H] ; exists subst'.
  - split ; ext ; apply H.
  - by move: H ; rewrite/o/comp/Datatypes.id => -[/[gen] ? /[gen]].
Qed.

(*****************************************************************************)
(* Logic/resolution.ml *)
(*****************************************************************************)

Definition atom f := if f is Atom _ _ then True else False.

Lemma atom_def : atom = (@ε ((prod nat (prod nat (prod nat nat))) -> form -> Prop) (fun atom' : (prod nat (prod nat (prod nat nat))) -> form -> Prop => forall _276403 : prod nat (prod nat (prod nat nat)), ((atom' _276403 FFalse) = False) /\ ((forall p : nat, forall l : seq term, (atom' _276403 (Atom p l)) = True) /\ ((forall q : form, forall r : form, (atom' _276403 (FImp q r)) = False) /\ (forall x : nat, forall q : form, (atom' _276403 (FAll x q)) = False)))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))))))).
Proof. by total_align. Qed.

(* negatomic formulae *)
Definition literal f :=
  match f with
  | Atom _ _ | FImp (Atom _ _) FFalse => True
  | _ => False end.

Lemma literal_def : literal = (fun _276404 : form => (atom _276404) \/ (exists q : form, (atom q) /\ (_276404 = (Not q)))).
Proof.
  ext.
  - by case ; auto ; case => // n s [] // ; right ; exists (Atom n s).
  - by move=> f [| [f' []]] ; [elim:f | elim: f'] ; move=> // ? ? _ ->.
Qed.

(* finite set of negatomic formulae *)
Definition clause c := finite_set c /\ c `<=` literal.

Lemma clause_def : clause = (fun _276409 : form -> Prop => (@finite_set form _276409) /\ (forall p : form, (@IN form p _276409) -> literal p)).
Proof. by rewrite/3=. Qed.

Inductive negative : form -> Prop := negative_intro : forall f, negative (Not f).

#[global]
Hint Constructors negative : core.

Lemma negative_def : negative = (fun _276554 : form => exists q : form, _276554 = (Not q)).
Proof.
  by ext => [f [] | f [f' ->]] ; eauto.
Qed.

Inductive positive : form -> Prop :=
  | positive_FFalse : positive FFalse
  | positive_Atom : forall n l, positive (Atom n l)
  | positive_FImp : forall f f', f' <> FFalse -> positive (FImp f f')
  | positive_FAll : forall n f, positive (FAll n f).

#[global]
Hint Constructors positive : core.

Lemma positive_def : positive = (fun _276559 : form => ~ (negative _276559)).
Proof.
  ext => f H.
  by inversion 1 ; inversion H ; subst f ; inversion H0 ; try injection H3.
  by destruct f ; auto ; destruct f2 ; only 1 : contradiction H ; constructor.
Qed.

Definition FNot f := match f with FImp f' FFalse => f' | _ => Not f end.

Lemma FNot_def : FNot = (fun _276564 : form => @COND form (negative _276564) (@ε form (fun q : form => (Not q) = _276564)) (Not _276564)).
Proof.
  ext => f ; if_intro => [{f}[f]|H] ; first by align_ε => // ? _ [=].
  by move:f H => [] // ? [] // H ; contradiction H.
Qed.

Definition resolve f cl cl' := cl `\ f `|` cl' `\ (FNot f).

Lemma resolve_def : resolve = (fun _276622 : form => fun _276623 : form -> Prop => fun _276624 : form -> Prop => @setU form (@DELETE form _276623 _276622) (@DELETE form _276624 (FNot _276622))).
Proof. reflexivity. Qed.

Inductive presproof (hyps : set (set form)) : set form -> Prop :=
  | presproof_assumption : forall cl, hyps cl -> presproof hyps cl
  | presproof_resolve : forall f cl cl', presproof hyps cl ->
                        presproof hyps cl' -> cl f -> cl' (FNot f) ->
                        presproof hyps (resolve f cl cl').

Lemma presproof_def : presproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall presproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists p : form, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a' = (resolve p cl1 cl2)) /\ ((presproof' cl1) /\ ((presproof' cl2) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2)))))) -> presproof' a') -> presproof' a).
Proof. rewrite/3= ; ind_align. Qed.

Definition interp cl := foldr FOr FFalse [seq of cl].

Lemma interp_def : interp = (fun _276649 : form -> Prop => @ITLIST form form FOr (@seq_of_set form _276649) FFalse).
Proof. reflexivity. Qed.

Definition instance_of cl cl' := (exists subst, cl = formsubst subst @` cl').

Lemma instance_of_def : instance_of = (fun _282937 : form -> Prop => fun _282938 : form -> Prop => ex (fun i : nat -> term => eq _282937 (@IMAGE form form (formsubst i) _282938))).
Proof. reflexivity. Qed.

Definition FVS cl := UNIONS (free_variables @` cl).

Lemma FVS_def : FVS = (fun _282949 : form -> Prop => @UNIONS nat (@GSPEC (nat -> Prop) (fun GEN_PVAR_527 : nat -> Prop => exists p : form, @SETSPEC (nat -> Prop) GEN_PVAR_527 (@IN form p _282949) (free_variables p)))).
Proof. by move=> /f` * /3=. Qed.

Definition rename : (form -> Prop) -> (nat -> Prop) -> nat -> term := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (form -> Prop) -> (nat -> Prop) -> nat -> term) (fun i : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (form -> Prop) -> (nat -> Prop) -> nat -> term => forall _285948 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), forall cl : form -> Prop, forall s : nat -> Prop, ((@finite_set nat s) /\ (clause cl)) -> (renaming (i _285948 cl s)) /\ ((@setI nat (FVS (@IMAGE form form (formsubst (i _285948 cl s)) cl)) s) = (@set0 nat))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0))))))))))))).

Lemma rename_def : rename = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (form -> Prop) -> (nat -> Prop) -> nat -> term) (fun i : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (form -> Prop) -> (nat -> Prop) -> nat -> term => Logic.all (fun _285948 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))) => Logic.all (fun cl : form -> Prop => Logic.all (fun s : nat -> Prop => ((@finite_set nat s) /\ (clause cl)) -> (renaming (i _285948 cl s)) /\ (eq (@setI nat (FVS (@IMAGE form form (formsubst (i _285948 cl s)) cl)) s) (@set0 nat)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))))))))).
Proof. reflexivity. Qed.

Inductive resproof (hyps : set (set form)) : set form -> Prop :=
  | resproof_assumption : forall cl, hyps cl -> resproof hyps cl
  | resproof_rm_opposable :
      forall cl1 cl2 cl2' ps1 ps2 subst, resproof hyps cl1 -> resproof hyps cl2 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` FNot @` ps2)) ->
      mgu (ps1 `|` FNot @` ps2) = subst ->
      resproof hyps ([set formsubst subst x | x in (cl1 `\` ps1 `|` cl2' `\` ps2)]).

Lemma resproof_def : resproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall resproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : nat -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((resproof' cl1) /\ ((resproof' cl2) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : nat -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_533 : form => exists p : form, @SETSPEC form GEN_PVAR_533 (@IN form p ps2) (FNot p))))) /\ ((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_534 : form => exists p : form, @SETSPEC form GEN_PVAR_534 (@IN form p ps2) (FNot p))))) = i))))))))))) -> resproof' a') -> resproof' a).
Proof.
  rewrite/3= ; ind_align.
  - breakgoal by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE.
  - apply resproof_rm_opposable with (cl2 := x1) ; auto.
    1,2 : rewrite -[fun x => exists p, [set x' | x4 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x4 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H7,H8.
    by exists x6. by [].
Qed.

Definition isaresolvent cl c := match c with (cl1,cl2) =>
  let y := (formsubst (rename cl2 (FVS cl1))) @` cl2 in
  exists ps1 ps2 : form -> Prop, subset ps1 cl1 /\ subset ps2 y /\
  ps1 <> set0 /\ ps2 <> set0 /\
  (exists subst : nat -> term, Unifies subst (ps1 `|` (FNot @` ps2))) /\
  cl = formsubst (mgu (ps1 `|` FNot @` ps2)) @` (cl1 `\` ps1 `|` y `\` ps2) end.

Lemma isaresolvent_def : isaresolvent = (fun _289554 : form -> Prop => fun _289555 : prod (form -> Prop) (form -> Prop) => @LET (form -> Prop) Prop (fun cl2' : form -> Prop => @LET_END Prop (exists ps1 : form -> Prop, exists ps2 : form -> Prop, (@subset form ps1 (@fst (form -> Prop) (form -> Prop) _289555)) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i : nat -> term, Unifies i (@setU form ps1 (@GSPEC form (fun GEN_PVAR_540 : form => exists p : form, @SETSPEC form GEN_PVAR_540 (@IN form p ps2) (FNot p))))) /\ (@LET (nat -> term) Prop (fun i : nat -> term => @LET_END Prop (_289554 = (@IMAGE form form (formsubst i) (@setU form (@setD form (@fst (form -> Prop) (form -> Prop) _289555) ps1) (@setD form cl2' ps2))))) (mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_541 : form => exists p : form, @SETSPEC form GEN_PVAR_541 (@IN form p ps2) (FNot p)))))))))))) (@IMAGE form form (formsubst (rename (@snd (form -> Prop) (form -> Prop) _289555) (FVS (@fst (form -> Prop) (form -> Prop) _289555)))) (@snd (form -> Prop) (form -> Prop) _289555))).
Proof.
  by ext => cl [cl1 cl2] [ps1 [ps2 H]] ; exist ps1 ps2 ; move: H => /3= H ;
    full_destruct ; repeat split ; eauto.
Qed.

(*****************************************************************************)
(* Logic/given.ml *)
(*****************************************************************************)

Lemma FIRSTN_def {_216234 : Type'} : (@take _216234) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> (seq _216234) -> seq _216234) (fun FIRSTN' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> (seq _216234) -> seq _216234 => forall _289585 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall l : seq _216234, (FIRSTN' _289585 (NUMERAL 0) l) = (@nil _216234)) /\ (forall n : nat, forall l : seq _216234, (FIRSTN' _289585 (S n) l) = (@COND (seq _216234) (l = (@nil _216234)) (@nil _216234) (@cons _216234 (@HD _216234 l) (FIRSTN' _289585 n (@TL _216234 l)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof.
  by total_align => [[] | ? []] // * ; if_seq.
Qed.

Definition tautologous cl := (exists f : form, cl f /\ cl (FNot f)).

Lemma tautologous_def : tautologous = (fun _290199 : form -> Prop => exists p : form, (@IN form p _290199) /\ (@IN form (FNot p) _290199)).
Proof. by rewrite/3=. Qed.

Definition subsumes cl cl' := exists subst, formsubst subst @` cl `<=` cl'.

Lemma subsumes_def : subsumes = (fun _290204 : form -> Prop => fun _290205 : form -> Prop => ex (fun i : nat -> term => @subset form (@IMAGE form form (formsubst i) _290204) _290205)).
Proof. reflexivity. Qed.

Definition SUBSUMES (s s' : set (set form)) := forall cl', s' cl' -> exists cl, s cl /\ subsumes cl cl'.

Lemma SUBSUMES_def : SUBSUMES = (fun _290276 : (form -> Prop) -> Prop => fun _290277 : (form -> Prop) -> Prop => forall cl' : form -> Prop, (@IN (form -> Prop) cl' _290277) -> exists cl : form -> Prop, (@IN (form -> Prop) cl _290276) /\ (subsumes cl cl')).
Proof. by rewrite/3=. Qed.

Definition allresolvents (s s' : set (set form)) cl :=
  (exists c1 c2, s c1 /\ s' c2 /\ isaresolvent cl (c1, c2)).

Lemma allresolvents_def : allresolvents = (fun _290388 : (form -> Prop) -> Prop => fun _290389 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_542 : form -> Prop => exists c : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_542 (exists c1 : form -> Prop, exists c2 : form -> Prop, (@IN (form -> Prop) c1 _290388) /\ ((@IN (form -> Prop) c2 _290389) /\ (isaresolvent c (@pair (form -> Prop) (form -> Prop) c1 c2)))) c)).
Proof. by move=> /f` * /3=. Qed.

Definition allntresolvents s s' cl := allresolvents s s' cl /\ ~ tautologous cl.

Lemma allntresolvents_def : allntresolvents = (fun _290400 : (form -> Prop) -> Prop => fun _290401 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_543 : form -> Prop => exists r : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_543 ((@IN (form -> Prop) r (allresolvents _290400 _290401)) /\ (~ (tautologous r))) r)).
Proof. by extall ; rewrite/3=. Qed.

Definition resolvents cl (l : seq (set form)) := [seq of allresolvents [set cl] [set` l]].

Lemma resolvents_def : resolvents = (fun _315994 : form -> Prop => fun _315995 : seq (form -> Prop) => @seq_of_set (form -> Prop) (allresolvents (@INSERT (form -> Prop) _315994 (@set0 (form -> Prop))) (@set_of_seq (form -> Prop) _315995))).
Proof. by extall ; rewrite/3=. Qed.

Fixpoint replace (cl : form -> Prop) l :=
  match l with
  | nil => cl::nil
  | cl'::l' => if subsumes cl cl' then cl::l' else cl'::(replace cl l') end.

Lemma replace_def : replace = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (form -> Prop) -> (seq (form -> Prop)) -> seq (form -> Prop)) (fun replace' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (form -> Prop) -> (seq (form -> Prop)) -> seq (form -> Prop) => forall _316246 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), (forall cl : form -> Prop, (replace' _316246 cl (@nil (form -> Prop))) = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (forall c : form -> Prop, forall cl : form -> Prop, forall cls : seq (form -> Prop), (replace' _316246 cl (@cons (form -> Prop) c cls)) = (@COND (seq (form -> Prop)) (subsumes cl c) (@cons (form -> Prop) cl cls) (@cons (form -> Prop) c (replace' _316246 cl cls))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0))))))))))))))).
Proof. by total_align. Qed.

Definition incorporate cl cl' s :=
  if tautologous cl' \/ has (fun cl0 : form -> Prop => subsumes cl0 cl') (cl :: s)
    then s else replace cl' s.

Lemma incorporate_def : incorporate =(fun _316633 : form -> Prop => fun _316634 : form -> Prop => fun _316635 : seq (form -> Prop) => @COND (seq (form -> Prop)) ((tautologous _316634) \/ (@EX (form -> Prop) (fun c : form -> Prop => subsumes c _316634) (@cons (form -> Prop) _316633 _316635))) _316635 (replace _316634 _316635)).
Proof. reflexivity. Qed.

Definition insert {A : Type'} (a : A) s := if a \in s then s else a :: s.

Lemma insert_def {_218810 : Type'} :  (@insert _218810) = (fun _316826 : _218810 => fun _316827 : seq _218810 => @COND (seq _218810) (@MEM _218810 _316826 _316827) _316827 (@cons _218810 _316826 _316827)).
Proof. by funext=> * ; rewrite/MEM/COND asboolb. Qed.

Definition step c :=
  match snd c with
  | nil => c
  | a::s => (insert a (fst c), foldr (incorporate a) s (resolvents a (a :: (fst c)))) end.

Lemma step_def : step = (fun _316838 : prod (seq (form -> Prop)) (seq (form -> Prop)) => @COND (prod (seq (form -> Prop)) (seq (form -> Prop))) ((@snd (seq (form -> Prop)) (seq (form -> Prop)) _316838) = (@nil (form -> Prop))) (@pair (seq (form -> Prop)) (seq (form -> Prop)) (@fst (seq (form -> Prop)) (seq (form -> Prop)) _316838) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _316838)) (@LET (seq (form -> Prop)) (prod (seq (form -> Prop)) (seq (form -> Prop))) (fun new : seq (form -> Prop) => @LET_END (prod (seq (form -> Prop)) (seq (form -> Prop))) (@pair (seq (form -> Prop)) (seq (form -> Prop)) (@insert (form -> Prop) (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _316838)) (@fst (seq (form -> Prop)) (seq (form -> Prop)) _316838)) (@ITLIST (form -> Prop) (seq (form -> Prop)) (incorporate (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _316838))) new (@TL (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _316838))))) (resolvents (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _316838)) (@cons (form -> Prop) (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _316838)) (@fst (seq (form -> Prop)) (seq (form -> Prop)) _316838))))).
Proof.
  by ext => [[? s]] * ;  if_seq ; destruct s.
Qed.

Fixpoint given n (p : seq (set form) * seq (set form)) :=
  if n is k.+1 then step (given k p) else p.

Lemma given_def : given = (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> nat -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> prod (seq (form -> Prop)) (seq (form -> Prop))) (fun given' : (prod nat (prod nat (prod nat (prod nat nat)))) -> nat -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> prod (seq (form -> Prop)) (seq (form -> Prop)) => forall _316850 : prod nat (prod nat (prod nat (prod nat nat))), (forall p : prod (seq (form -> Prop)) (seq (form -> Prop)), (given' _316850 (NUMERAL 0) p) = p) /\ (forall n : nat, forall p : prod (seq (form -> Prop)) (seq (form -> Prop)), (given' _316850 (S n) p) = (step (given' _316850 n p)))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0))))))))))))).
Proof. by total_align. Qed.

Definition Used init n := [set` (given n init).1].
Definition Unused init n := [set` (given n init).2].

Lemma Used_def : Used = (fun _316851 : prod (seq (form -> Prop)) (seq (form -> Prop)) => fun _316852 : nat => @set_of_seq (form -> Prop) (@fst (seq (form -> Prop)) (seq (form -> Prop)) (given _316852 _316851))).
Proof. reflexivity. Qed.
Lemma Unused_def : Unused = (fun _316863 : prod (seq (form -> Prop)) (seq (form -> Prop)) => fun _316864 : nat => @set_of_seq (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) (given _316864 _316863))).
Proof. reflexivity. Qed.

Fixpoint Sub init n : set (set form) := if n is k.+1
  then if (given k init).2 is a::_ then a |` (Sub init k) else Sub init k
  else set0.

Lemma Sub_def : Sub = (@ε ((prod nat (prod nat nat)) -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> nat -> (form -> Prop) -> Prop) (fun Sub' : (prod nat (prod nat nat)) -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> nat -> (form -> Prop) -> Prop => forall _316881 : prod nat (prod nat nat), (forall init : prod (seq (form -> Prop)) (seq (form -> Prop)), (Sub' _316881 init (NUMERAL 0)) = (@set0 (form -> Prop))) /\ (forall init : prod (seq (form -> Prop)) (seq (form -> Prop)), forall n : nat, (Sub' _316881 init (S n)) = (@COND ((form -> Prop) -> Prop) ((@snd (seq (form -> Prop)) (seq (form -> Prop)) (given n init)) = (@nil (form -> Prop))) (Sub' _316881 init n) (@INSERT (form -> Prop) (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) (given n init))) (Sub' _316881 init n))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0))))))))))).
Proof.
  by total_align => //= init k ; if_seq ; case: (given k init).2.
Qed.

Fixpoint break init n := if n is k.+1
  then let k' := break init k in k' + size (given k' init).2
  else size init.2.

Lemma break_def : break = (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> nat -> nat) (fun break' : (prod nat (prod nat (prod nat (prod nat nat)))) -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> nat -> nat => forall _328646 : prod nat (prod nat (prod nat (prod nat nat))), (forall init : prod (seq (form -> Prop)) (seq (form -> Prop)), (break' _328646 init (NUMERAL 0)) = (@size (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) (given (NUMERAL 0) init)))) /\ (forall n : nat, forall init : prod (seq (form -> Prop)) (seq (form -> Prop)), (break' _328646 init (S n)) = (addn (break' _328646 init n) (@size (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) (given (break' _328646 init n) init)))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0))))))))))))).
Proof. by total_align. Qed.

Definition level init n := Sub init (break init n).

Lemma level_def : level = (fun _328647 : prod (seq (form -> Prop)) (seq (form -> Prop)) => fun _328648 : nat => Sub _328647 (break _328647 _328648)).
Proof. reflexivity. Qed.

(*****************************************************************************)
(* Logic/linear.ml *)
(*****************************************************************************)

Inductive ppresproof : set (set form) -> set form -> Prop :=
  | ppresproof_assumption : forall cl, clause cl -> ppresproof [set cl] cl
  | ppresproof_resolve : forall f hyps hyps' cl cl', ppresproof hyps cl ->
                        ppresproof hyps' cl' -> cl f -> cl' (FNot f) ->
                        ppresproof (hyps `|` hyps') (resolve f cl cl').

Lemma ppresproof_def : ppresproof = (fun a0 : (form -> Prop) -> Prop => fun a1 : form -> Prop => forall ppresproof' : ((form -> Prop) -> Prop) -> (form -> Prop) -> Prop, (forall a0' : (form -> Prop) -> Prop, forall a1' : form -> Prop, (((a0' = (@INSERT (form -> Prop) a1' (@set0 (form -> Prop)))) /\ (clause a1')) \/ (exists p : form, exists asm1 : (form -> Prop) -> Prop, exists asm2 : (form -> Prop) -> Prop, exists c1 : form -> Prop, exists c2 : form -> Prop, (a0' = (@setU (form -> Prop) asm1 asm2)) /\ ((a1' = (resolve p c1 c2)) /\ ((ppresproof' asm1 c1) /\ ((ppresproof' asm2 c2) /\ ((@IN form p c1) /\ (@IN form (FNot p) c2))))))) -> ppresproof' a0' a1') -> ppresproof' a0 a1).
Proof.
  by rewrite/3= ; ind_align ; rewrite/3= ; first left ; last apply ppresproof_assumption.
Qed.

Inductive lpresproof (hyps : set (set form)) : seq (set form) -> Prop :=
  | lpresproof_assumption : forall cl, hyps cl -> lpresproof hyps ([:: cl])
  | lpresproof_resolve : forall f cl cl' s, lpresproof hyps (cl::s) ->
                        (hyps cl' \/ cl' \in s) -> cl f -> cl' (FNot f) ->
                        lpresproof hyps ((resolve f cl cl')::cl::s).

Lemma lpresproof_def : lpresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : seq (form -> Prop) => forall lpresproof' : (seq (form -> Prop)) -> Prop, (forall a' : seq (form -> Prop), ((exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (@IN (form -> Prop) cl hyps')) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists lis : seq (form -> Prop), exists p : form, (a' = (@cons (form -> Prop) (resolve p c1 c2) (@cons (form -> Prop) c1 lis))) /\ ((lpresproof' (@cons (form -> Prop) c1 lis)) /\ (((@IN (form -> Prop) c2 hyps') \/ (@MEM (form -> Prop) c2 lis)) /\ ((@IN form p c1) /\ (@IN form (FNot p) c2)))))) -> lpresproof' a') -> lpresproof' a).
Proof. rewrite/3= ; ind_align. Qed.

Fixpoint suffix {A : Type} (s s' : seq A) :=
  match s' with
  | nil => s = nil
  | _::s''  => s = s' \/ suffix s s'' end.

Lemma suffix_def {_224872 : Type'} : (@suffix _224872) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq _224872) -> (seq _224872) -> Prop) (fun suffix' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq _224872) -> (seq _224872) -> Prop => forall _374747 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall lis : seq _224872, (suffix' _374747 lis (@nil _224872)) = (lis = (@nil _224872))) /\ (forall s : _224872, forall lis : seq _224872, forall cs : seq _224872, (suffix' _374747 lis (@cons _224872 s cs)) = ((lis = (@cons _224872 s cs)) \/ (suffix' _374747 lis cs)))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))))))))).
Proof. by total_align. Qed.

Inductive lresproof (hyps : set (set form)) : seq (set form) -> Prop :=
  | lresproof_assumption : forall cl, hyps cl -> lresproof hyps (cl::nil)
  | lresproof_resolve : forall cl0 cl cl' s, lresproof hyps (cl::s) ->
                        (hyps cl' \/ cl' \in s) -> isaresolvent cl0 (cl,cl') ->
                        lresproof hyps (cl0::cl::s).

Lemma lresproof_def : lresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : seq (form -> Prop) => forall lresproof' : (seq (form -> Prop)) -> Prop, (forall a' : seq (form -> Prop), ((exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (@IN (form -> Prop) cl hyps')) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists lis : seq (form -> Prop), exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@cons (form -> Prop) c1 lis))) /\ ((lresproof' (@cons (form -> Prop) c1 lis)) /\ (((@IN (form -> Prop) c2 hyps') \/ (@MEM (form -> Prop) c2 lis)) /\ (isaresolvent cl (@pair (form -> Prop) (form -> Prop) c1 c2)))))) -> lresproof' a') -> lresproof' a).
Proof. rewrite/3= ; ind_align. Qed.

(*****************************************************************************)
(* Logic/support.ml *)
(*****************************************************************************)

Inductive npresproof (hyps : set (set form)) : set form -> nat -> Prop :=
  | npresproof_assumption : forall cl, hyps cl -> npresproof hyps cl 1
  | npresproof_resolve : forall f cl cl' n n', npresproof hyps cl n ->
                        npresproof hyps cl' n' -> cl f -> cl' (FNot f) ->
                        npresproof hyps (resolve f cl cl') (S (n+n')).

Lemma npresproof_def : npresproof = (fun hyps' : (form -> Prop) -> Prop => fun a0 : form -> Prop => fun a1 : nat => forall npresproof' : (form -> Prop) -> nat -> Prop, (forall a0' : form -> Prop, forall a1' : nat, (((a1' = (NUMERAL (BIT1 0))) /\ (@IN (form -> Prop) a0' hyps')) \/ (exists p : form, exists n1 : nat, exists n2 : nat, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a0' = (resolve p cl1 cl2)) /\ ((a1' = (addn n1 (addn n2 (NUMERAL (BIT1 0))))) /\ ((npresproof' cl1 n1) /\ ((npresproof' cl2 n2) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2))))))) -> npresproof' a0' a1') -> npresproof' a0 a1).
Proof.
  rewrite/2=/3= ; ind_align.
  - breakgoal by rewrite addn1 addnS.
  - by rewrite addn1 addnS ; apply npresproof_resolve.
Qed.

Inductive psresproof (hyps sos : set (set form)) : Prop -> set form -> Prop :=
  | psresproof_assumption : forall cl, hyps cl -> ~ tautologous cl ->
                            psresproof hyps sos (sos cl) cl
  | psresproof_resolve : forall f cl cl' P P', psresproof hyps sos P cl ->
                        psresproof hyps sos P' cl' -> cl f -> cl' (FNot f) ->
                        P \/ P' -> ~ tautologous (resolve f cl cl') ->
                        psresproof hyps sos True (resolve f cl cl').

Lemma psresproof_def : psresproof = (fun hyps' : (form -> Prop) -> Prop => fun sos : (form -> Prop) -> Prop => fun a0 : Prop => fun a1 : form -> Prop => forall psresproof' : Prop -> (form -> Prop) -> Prop, (forall a0' : Prop, forall a1' : form -> Prop, (((a0' = (@IN (form -> Prop) a1' sos)) /\ ((@IN (form -> Prop) a1' hyps') /\ (~ (tautologous a1')))) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists s1 : Prop, exists s2 : Prop, exists p : form, (a0' = True) /\ ((a1' = (resolve p c1 c2)) /\ ((psresproof' s1 c1) /\ ((psresproof' s2 c2) /\ ((@IN form p c1) /\ ((@IN form (FNot p) c2) /\ ((s1 \/ s2) /\ (~ (tautologous (resolve p c1 c2))))))))))) -> psresproof' a0' a1') -> psresproof' a0 a1).
Proof. rewrite/3= ; ind_align. Qed.

Inductive spresproof (hyps sos : set (set form)) : set form -> Prop :=
  | spresproof_assumption : forall cl, hyps cl -> sos cl ->
                            ~ tautologous cl -> spresproof hyps sos cl
  | spresproof_resolve1 : forall f cl cl', spresproof hyps sos cl ->
                        spresproof hyps sos cl' -> cl f ->
                        cl' (FNot f) -> ~ tautologous (resolve f cl cl') ->
                        spresproof hyps sos (resolve f cl cl')
  | spresproof_resolve2 : forall f cl cl', spresproof hyps sos cl ->
                        hyps cl' -> cl f ->
                        cl' (FNot f) -> ~ tautologous (resolve f cl cl') ->
                        spresproof hyps sos (resolve f cl cl').

Lemma spresproof_def : spresproof = (fun hyps' : (form -> Prop) -> Prop => fun sos : (form -> Prop) -> Prop => fun a : form -> Prop => forall spresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, (((@IN (form -> Prop) a' hyps') /\ ((@IN (form -> Prop) a' sos) /\ (~ (tautologous a')))) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists p : form, (a' = (resolve p c1 c2)) /\ ((spresproof' c1) /\ (((spresproof' c2) \/ (@IN (form -> Prop) c2 hyps')) /\ ((@IN form p c1) /\ ((@IN form (FNot p) c2) /\ (~ (tautologous (resolve p c1 c2))))))))) -> spresproof' a') -> spresproof' a).
Proof. rewrite/3= ; ind_align. Qed.

Inductive sresproof (hyps sos : set (set form)) : set form -> Prop :=
  | sresproof_assumption : forall cl, hyps cl -> sos cl ->
    ~ tautologous cl -> sresproof hyps sos cl
  | sresproof_rm_opposable1 :
      forall cl1 cl2 cl2' ps1 ps2 subst, sresproof hyps sos cl1 -> sresproof hyps sos cl2 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      ~ tautologous (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)) ->
      sresproof hyps sos (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2))
  | sresproof_rm_opposable2 :
      forall cl1 cl2 cl2' ps1 ps2 subst, sresproof hyps sos cl1 -> hyps cl2 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      ~ tautologous (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)) ->
      sresproof hyps sos (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)).

Lemma sresproof_def : sresproof = (fun hyps' : (form -> Prop) -> Prop => fun sos : (form -> Prop) -> Prop => fun a : form -> Prop => forall sresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, (((@IN (form -> Prop) a' hyps') /\ ((@IN (form -> Prop) a' sos) /\ (~ (tautologous a')))) \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : nat -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((sresproof' cl1) /\ (((sresproof' cl2) \/ (@IN (form -> Prop) cl2 hyps')) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : nat -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_589 : form => exists p : form, @SETSPEC form GEN_PVAR_589 (@IN form p ps2) (FNot p))))) /\ (((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_590 : form => exists p : form, @SETSPEC form GEN_PVAR_590 (@IN form p ps2) (FNot p))))) = i) /\ (~ (tautologous (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))))))))))))))) -> sresproof' a') -> sresproof' a).
Proof.
  rewrite/3= ; ind_align.
  1,2 : by right ; destruct H6 ; repeat eexists ; eauto ; by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE ; eauto.
  1,2 : rewrite -[fun x => exists p, [set x' | x5 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x5 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H7,H8 ; econstructor ; by eauto.
Qed.

(*****************************************************************************)
(* Logic/positive.ml *)
(*****************************************************************************)

Definition allpositive cl := cl `<=` positive.

Lemma allpositive_def : allpositive = (fun _460164 : form -> Prop => forall p : form, (@IN form p _460164) -> positive p).
Proof. by rewrite/3=. Qed.

Inductive pposresproof (hyps : set (set form)) : set form -> Prop :=
  | pposresproof_assumption : forall cl, hyps cl -> pposresproof hyps cl
  | pposresproof_resolve1 : forall f cl cl', pposresproof hyps cl ->
                        pposresproof hyps cl' -> allpositive cl ->
                        cl f -> cl' (FNot f) ->
                        pposresproof hyps (resolve f cl cl')
  | pposresproof_resolve2 : forall f cl cl', pposresproof hyps cl ->
                        pposresproof hyps cl' -> allpositive cl' ->
                        cl f -> cl' (FNot f) ->
                        pposresproof hyps (resolve f cl cl').

Lemma pposresproof_def : pposresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall pposresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists p : form, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a' = (resolve p cl1 cl2)) /\ ((pposresproof' cl1) /\ ((pposresproof' cl2) /\ (((allpositive cl1) \/ (allpositive cl2)) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2))))))) -> pposresproof' a') -> pposresproof' a).
Proof. rewrite/3= ; ind_align. Qed.

Inductive psemresproof (TrueVar : set form) (hyps : set (set form)) : set form -> Prop :=
  | psemresproof_assumption : forall cl, hyps cl -> psemresproof TrueVar hyps cl
  | psemresproof_resolve1 : forall f cl cl', psemresproof TrueVar hyps cl ->
                        psemresproof TrueVar hyps cl' ->
                        ~pholds TrueVar (interp cl) ->
                        cl f -> cl' (FNot f) ->
                        psemresproof TrueVar hyps (resolve f cl cl')
  | psemresproof_resolve2 : forall f cl cl', psemresproof TrueVar hyps cl ->
                        psemresproof TrueVar hyps cl' ->
                        ~pholds TrueVar (interp cl') ->
                        cl f -> cl' (FNot f) ->
                        psemresproof TrueVar hyps (resolve f cl cl').

Lemma psemresproof_def : psemresproof = (fun v : form -> Prop => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall psemresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists p : form, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a' = (resolve p cl1 cl2)) /\ ((psemresproof' cl1) /\ ((psemresproof' cl2) /\ (((~ (pholds v (interp cl1))) \/ (~ (pholds v (interp cl2)))) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2))))))) -> psemresproof' a') -> psemresproof' a).
Proof. rewrite/3= ; ind_align. Qed.

Definition propflip TrueVar f := if negative f <-> pholds TrueVar f then f else FNot f.

Lemma propflip_def : propflip = (fun _467005 : form -> Prop => fun _467006 : form => @COND form ((negative _467006) = (pholds _467005 _467006)) _467006 (FNot _467006)).
Proof.
  rewrite/COND/propflip.
  apply (f_equal (fun P TrueVar f => if `[< P TrueVar f >] then f else FNot f)).
  by ext => * ; blindrewrite ; firstorder.
Qed.


Inductive posresproof (hyps : set (set form)) : set form -> Prop :=
  | posresproof_assumption : forall cl, hyps cl -> posresproof hyps cl
  | posresproof_rm_opposable1 :
      forall cl1 cl2 cl2' ps1 ps2 subst, posresproof hyps cl1 ->
      posresproof hyps cl2 -> allpositive cl1 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      posresproof hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2))
  | posresproof_rm_opposable2 :
      forall cl1 cl2 cl2' ps1 ps2 subst, posresproof hyps cl1 ->
      posresproof hyps cl2 -> allpositive cl2 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      posresproof hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)).

Lemma posresproof_def : posresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall posresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : nat -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((posresproof' cl1) /\ ((posresproof' cl2) /\ (((allpositive cl1) \/ (allpositive cl2)) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : nat -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_622 : form => exists p : form, @SETSPEC form GEN_PVAR_622 (@IN form p ps2) (FNot p))))) /\ ((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_623 : form => exists p : form, @SETSPEC form GEN_PVAR_623 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> posresproof' a') -> posresproof' a).
Proof.
  rewrite/3= ; ind_align.
  1,2 : right ; full_destruct ; repeat eexists ; eauto ; by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE ; eauto.
  1,2 : rewrite -[fun x => exists p, [set x' | x4 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x4 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H8,H9 ; econstructor ; by eauto.
Qed.

Inductive semresproof {A : Type'} (M : Structure A) 
  (hyps : set (set form)) : set form -> Prop :=
  | semresproof_assumption : forall cl, hyps cl -> semresproof M hyps cl
  | semresproof_rm_opposable1 :
      forall cl1 cl2 cl2' ps1 ps2 subst, semresproof M hyps cl1 ->
      semresproof M hyps cl2 -> (~ forall v, holds M v (interp cl1)) ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      semresproof M hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2))
  | semresproof_rm_opposable2 :
      forall cl1 cl2 cl2' ps1 ps2 subst, semresproof M hyps cl1 ->
      semresproof M hyps cl2 -> (~ forall v, holds M v (interp cl2)) ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      semresproof M hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)).

Lemma semresproof_def {A : Type'} : (@semresproof A) = (fun M : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : nat -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((semresproof' cl1) /\ ((semresproof' cl2) /\ (((~ (forall v : nat -> A, @holds A M v (interp cl1))) \/ (~ (forall v : nat -> A, @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : nat -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_629 : form => exists p : form, @SETSPEC form GEN_PVAR_629 (@IN form p ps2) (FNot p))))) /\ ((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_630 : form => exists p : form, @SETSPEC form GEN_PVAR_630 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof' a') -> semresproof' a).
Proof.
  ext 2 => M hyps ; rewrite/3= ; ind_align.
  1,2 : right ; full_destruct ; repeat eexists ; eauto ; by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE ; eauto.
  1,2 : rewrite -[fun x => exists p, [set x' | x3 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x3 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H8,H9 ; econstructor ; by eauto.
Qed.

Inductive semresproof2 {A : Type'} (M : Structure A) 
  (hyps : set (set form)) : set form -> Prop :=
  | semresproof2_assumption : forall cl, hyps cl -> semresproof2 M hyps cl
  | semresproof2_rm_opposable1 :
      forall cl1 cl2 cl2' ps1 ps2 subst,
      semresproof2 M hyps cl1 -> semresproof2 M hyps cl2 ->
      (~forall v, valuation M v -> holds M v (interp cl1)) ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` FNot @` ps2)) ->
      mgu (ps1 `|` FNot @` ps2) = subst ->
      semresproof2 M hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2))
  | semresproof2_rm_opposable2 :
      forall cl1 cl2 cl2' ps1 ps2 subst,
      semresproof2 M hyps cl1 -> semresproof2 M hyps cl2 ->
      (~forall v, valuation M v -> holds M v (interp cl2)) ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` FNot @` ps2)) ->
      mgu (ps1 `|` FNot @` ps2) = subst ->
      semresproof2 M hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)).

Lemma semresproof2_def {A : Type'} : (@semresproof2 A) = (fun M : prod (A -> Prop) (prod (nat -> (seq A) -> A) (nat -> (seq A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof2' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : nat -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((semresproof2' cl1) /\ ((semresproof2' cl2) /\ (((~ (forall v : nat -> A, (@valuation A M v) -> @holds A M v (interp cl1))) \/ (~ (forall v : nat -> A, (@valuation A M v) -> @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : nat -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_636 : form => exists p : form, @SETSPEC form GEN_PVAR_636 (@IN form p ps2) (FNot p))))) /\ ((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_637 : form => exists p : form, @SETSPEC form GEN_PVAR_637 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof2' a') -> semresproof2' a).
Proof.
  ext 2 => M hyps ; rewrite/3= ; ind_align.
  1,2 : right ; full_destruct ; repeat eexists ; eauto ; by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE ; eauto.
  1,2 : rewrite -[fun x => exists p, [set x' | x3 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x3 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H8,H9 ; econstructor ; by eauto.
Qed.

(*****************************************************************************)
(* Logic/givensem.ml *)
(*****************************************************************************)

Definition isaresolvent_sem (M : Structure nat) cl (c : set form * set form) :=
  let (cl1,cl2) := c in isaresolvent cl c /\
  (~(forall v, holds M v (interp cl1)) \/ ~forall v, holds M v (interp cl2)).

Lemma isaresolvent_sem_def : isaresolvent_sem = (fun _533128 : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)) => fun _533129 : form -> Prop => fun _533130 : prod (form -> Prop) (form -> Prop) => (isaresolvent _533129 (@pair (form -> Prop) (form -> Prop) (@fst (form -> Prop) (form -> Prop) _533130) (@snd (form -> Prop) (form -> Prop) _533130))) /\ ((~ (forall v : nat -> nat, @holds nat _533128 v (interp (@fst (form -> Prop) (form -> Prop) _533130)))) \/ (~ (forall v : nat -> nat, @holds nat _533128 v (interp (@snd (form -> Prop) (form -> Prop) _533130)))))).
Proof. by funext=> + + []. Qed.

Definition allresolvents_sem M s s' :=
  fun cl => (exists c1 c2, s c1 /\ s' c2 /\ isaresolvent_sem M cl (c1, c2)).

Lemma allresolvents_sem_def : allresolvents_sem = (fun _533155 : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)) => fun _533156 : (form -> Prop) -> Prop => fun _533157 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_648 : form -> Prop => exists c : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_648 (exists c1 : form -> Prop, exists c2 : form -> Prop, (@IN (form -> Prop) c1 _533156) /\ ((@IN (form -> Prop) c2 _533157) /\ (isaresolvent_sem _533155 c (@pair (form -> Prop) (form -> Prop) c1 c2)))) c)).
Proof. by extall ; rewrite/3=. Qed.

Definition allntresolvents_sem M s s' cl :=
  allresolvents_sem M s s' cl /\ ~ tautologous cl.

Lemma allntresolvents_sem_def : allntresolvents_sem = (fun _533176 : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)) => fun _533177 : (form -> Prop) -> Prop => fun _533178 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_649 : form -> Prop => exists r : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_649 ((@IN (form -> Prop) r (allresolvents_sem _533176 _533177 _533178)) /\ (~ (tautologous r))) r)).
Proof. by extall ; rewrite/3=. Qed.

Definition resolvents_sem M cl (l : seq (set form)) :=
  [seq of allresolvents_sem M [set cl] [set` l]].

Lemma resolvents_sem_def : resolvents_sem = (fun _533232 : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)) => fun _533233 : form -> Prop => fun _533234 : seq (form -> Prop) => @seq_of_set (form -> Prop) (allresolvents_sem _533232 (@INSERT (form -> Prop) _533233 (@set0 (form -> Prop))) (@set_of_seq (form -> Prop) _533234))).
Proof. by extall ; rewrite/3=. Qed.

Definition step_sem M c :=
  match c with
  | (_,nil) => c
  | (s,a::s') => (insert a s,
    foldr (incorporate a) s' (resolvents_sem M a (a :: s))) end.

Lemma step_sem_def : step_sem = (fun _533275 : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)) => fun _533276 : prod (seq (form -> Prop)) (seq (form -> Prop)) => @COND (prod (seq (form -> Prop)) (seq (form -> Prop))) ((@snd (seq (form -> Prop)) (seq (form -> Prop)) _533276) = (@nil (form -> Prop))) (@pair (seq (form -> Prop)) (seq (form -> Prop)) (@fst (seq (form -> Prop)) (seq (form -> Prop)) _533276) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _533276)) (@Basics.apply (seq (form -> Prop)) (prod (seq (form -> Prop)) (seq (form -> Prop))) (fun new : seq (form -> Prop) => @Datatypes.id (prod (seq (form -> Prop)) (seq (form -> Prop))) (@pair (seq (form -> Prop)) (seq (form -> Prop)) (@insert (form -> Prop) (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _533276)) (@fst (seq (form -> Prop)) (seq (form -> Prop)) _533276)) (@ITLIST (form -> Prop) (seq (form -> Prop)) (incorporate (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _533276))) new (@TL (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _533276))))) (resolvents_sem _533275 (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _533276)) (@cons (form -> Prop) (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) _533276)) (@fst (seq (form -> Prop)) (seq (form -> Prop)) _533276))))).
Proof.
  by funext => ? [? s] ; if_seq ; case s.
Qed.

Fixpoint given_sem M n p :=
  match n with
  | O => p
  | S n => step_sem M (given_sem M n p) end.

Lemma given_sem_def : given_sem = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop))) -> nat -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> prod (seq (form -> Prop)) (seq (form -> Prop))) (fun given_sem' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop))) -> nat -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> prod (seq (form -> Prop)) (seq (form -> Prop)) => forall _533299 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), (forall M : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)), forall p : prod (seq (form -> Prop)) (seq (form -> Prop)), (given_sem' _533299 M (NUMERAL 0) p) = p) /\ (forall M : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)), forall n : nat, forall p : prod (seq (form -> Prop)) (seq (form -> Prop)), (given_sem' _533299 M (S n) p) = (step_sem M (given_sem' _533299 M n p)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0))))))))))))))))).
Proof. by total_align. Qed.

Definition Used_SEM M init n := let (s,_) := given_sem M n init in [set` s].
Definition Unused_SEM M init n := let (_,s) := given_sem M n init in [set` s].

Lemma Used_SEM_def : Used_SEM = (fun _533300 : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)) => fun _533301 : prod (seq (form -> Prop)) (seq (form -> Prop)) => fun _533302 : nat => @set_of_seq (form -> Prop) (@fst (seq (form -> Prop)) (seq (form -> Prop)) (given_sem _533300 _533302 _533301))).
Proof.
  by funext => M init n ; rewrite/Used_SEM ;case (given_sem M n init).
Qed.

Lemma Unused_SEM_def : Unused_SEM = (fun _533321 : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)) => fun _533322 : prod (seq (form -> Prop)) (seq (form -> Prop)) => fun _533323 : nat => @set_of_seq (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) (given_sem _533321 _533323 _533322))).
Proof.
  by funext => M init n ; rewrite/Unused_SEM ;case (given_sem M n init).
Qed.

Fixpoint Sub_SEM M init n := if n is k.+1
  then if (given_sem M k init).2 is a::_ then a |` (Sub_SEM M init k)
    else Sub_SEM M init k
  else set0.

Lemma Sub_SEM_def : Sub_SEM = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop))) -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> nat -> (form -> Prop) -> Prop) (fun Sub_SEM' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop))) -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> nat -> (form -> Prop) -> Prop => forall _533349 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), (forall M : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)), forall init : prod (seq (form -> Prop)) (seq (form -> Prop)), (Sub_SEM' _533349 M init (NUMERAL 0)) = (@set0 (form -> Prop))) /\ (forall M : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)), forall init : prod (seq (form -> Prop)) (seq (form -> Prop)), forall n : nat, (Sub_SEM' _533349 M init (S n)) = (@COND ((form -> Prop) -> Prop) ((@snd (seq (form -> Prop)) (seq (form -> Prop)) (given_sem M n init)) = (@nil (form -> Prop))) (Sub_SEM' _533349 M init n) (@INSERT (form -> Prop) (@HD (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) (given_sem M n init))) (Sub_SEM' _533349 M init n))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))))))).
Proof.
  by total_align => //= M init k ; if_seq ; case: (given_sem M k init).2.
Qed.

Fixpoint break_sem M (init : seq (set form) * seq (set form)) n := if n is k.+1
  then let k' := break_sem M init k in k' + size (given_sem M k' init).2
  else size init.2.

Lemma break_sem_def : break_sem = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop))) -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> nat -> nat) (fun break_sem' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> (prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop))) -> (prod (seq (form -> Prop)) (seq (form -> Prop))) -> nat -> nat => forall _544384 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), (forall M : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)), forall init : prod (seq (form -> Prop)) (seq (form -> Prop)), (break_sem' _544384 M init (NUMERAL 0)) = (@size (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) (given_sem M (NUMERAL 0) init)))) /\ (forall M : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)), forall n : nat, forall init : prod (seq (form -> Prop)) (seq (form -> Prop)), (break_sem' _544384 M init (S n)) = (addn (break_sem' _544384 M init n) (@size (form -> Prop) (@snd (seq (form -> Prop)) (seq (form -> Prop)) (given_sem M (break_sem' _544384 M init n) init)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0))))))))))))))))).
Proof. by total_align. Qed.

Definition level_sem M init n := Sub_SEM M init (break_sem M init n).

Lemma level_sem_def : level_sem = (fun _544385 : prod (nat -> Prop) (prod (nat -> (seq nat) -> nat) (nat -> (seq nat) -> Prop)) => fun _544386 : prod (seq (form -> Prop)) (seq (form -> Prop)) => fun _544387 : nat => Sub_SEM _544385 _544386 (break_sem _544385 _544386 _544387)).
Proof. reflexivity. Qed.

(*****************************************************************************)
(* Logic/prolog.ml *)
(*****************************************************************************)

Definition definite cl := clause cl /\ #|` fset_set (cl `&` positive) | = 1%nat.

Lemma definite_def : definite = (fun _545149 : form -> Prop => (clause _545149) /\ ((@CARD form (@GSPEC form (fun GEN_PVAR_652 : form => exists p : form, @SETSPEC form GEN_PVAR_652 ((@IN form p _545149) /\ (positive p)) p))) = (NUMERAL (BIT1 0)))).
Proof.
  rewrite/definite/clause/CARD INTER_def => /` cl [[fincl +]] /3= /=.
  1,2 : by (if_triv by exact: finite_setIl) => + ->.
Qed.

Definition horn cl := clause cl /\ (#|` fset_set (cl `&` positive) | <= 1)%nat.

Lemma horn_def : horn = (fun _545154 : form -> Prop => (clause _545154) /\ (leqn (@CARD form (@GSPEC form (fun GEN_PVAR_653 : form => exists p : form, @SETSPEC form GEN_PVAR_653 ((@IN form p _545154) /\ (positive p)) p))) (NUMERAL (BIT1 0)))).
Proof.
  rewrite/horn/clause/CARD INTER_def.
  by ext => cl [[fincl +] +] ; if_triv by rewrite/3= ; exact: finite_setIl.
Qed.

Definition falsify f cl := if definite cl then cl else f |` cl.

Lemma falsify_def : falsify = (fun _545159 : form => fun _545160 : form -> Prop => @COND (form -> Prop) (definite _545160) _545160 (@INSERT form _545159 _545160)).
Proof. reflexivity. Qed.

Definition minmodel E := (herbase (functions E),
  (Fn,
  fun n l => forall M, Dom M = herbase (functions E) /\ 
    Fun M = Fn /\ satisfies M E -> Pred M n l)).

Lemma minmodel_def : minmodel = (fun _546187 : form -> Prop => @pair (term -> Prop) (prod (nat -> (seq term) -> term) (nat -> (seq term) -> Prop)) (herbase (functions _546187)) (@pair (nat -> (seq term) -> term) (nat -> (seq term) -> Prop) Fn (fun p : nat => fun zs : seq term => forall H : prod (term -> Prop) (prod (nat -> (seq term) -> term) (nat -> (seq term) -> Prop)), (((@Dom term H) = (herbase (functions _546187))) /\ (((@Fun term H) = Fn) /\ (@satisfies term H _546187))) -> @Pred term H p zs))).
Proof. reflexivity. Qed.

Definition breakhorn cl := if definite cl
  then let p := ε (fun p : form => cl p /\ positive p) in
    (map FNot [seq of cl `\  p], p)
  else (map FNot (seq_of_set cl), FFalse).

Lemma breakhorn_def : breakhorn = (fun _546245 : form -> Prop => @COND (prod (seq form) form) (definite _546245) (@LET form (prod (seq form) form) (fun p : form => @LET_END (prod (seq form) form) (@pair (seq form) form (@List.map form form FNot (@seq_of_set form (@DELETE form _546245 p))) p)) (@ε form (fun p : form => (@IN form p _546245) /\ (positive p)))) (@pair (seq form) form (@List.map form form FNot (@seq_of_set form _546245)) FFalse)).
Proof. by rewrite/3=. Qed.

Definition hypotheses cl := fst (breakhorn cl).
Definition conclusion cl := snd (breakhorn cl).

Lemma hypotheses_def : hypotheses = (fun _546250 : form -> Prop => @fst (seq form) form (breakhorn _546250)).
Proof. reflexivity. Qed.
Lemma conclusion_def : conclusion = (fun _546250 : form -> Prop => @snd (seq form) form (breakhorn _546250)).
Proof. reflexivity. Qed.

Lemma all2E : List.Forall2 = @all2.
Proof.
  ext => A B P s s'.
  - elim => // a b {}s {}s' /asboolP /= -> _ ; exact.
  - elim: s s' => [| a s IHs] [| b s'] //= /andP [/asboolP + /IHs].
    exact: List.Forall2_cons.
Qed.

Lemma all2E_gen A B (P : A -> B -> Prop) (s : seq A) (s' : seq B) :
 all2 P s s' = List.Forall2 P s s' :> Prop.
Proof. by move:all2E => /[gen] ->. Qed.

Unset Elimination Schemes.
Inductive gbackchain (S : set (set form)) : nat -> form -> Prop :=
| gbackchain_rule0 : forall cl v s, S cl ->
  (forall n, herbase (functions (interp @` S)) (v n)) ->
  List.Forall2 (gbackchain S) s (map (formsubst v) (hypotheses cl)) ->
  gbackchain S (\sum_(i <- s) i).+1 (formsubst v (conclusion cl)).

Lemma gbackchain_rule (S : set (set form)) cl v s : S cl ->
  (forall n, herbase (functions (interp @` S)) (v n)) ->
  all2 (gbackchain S) s (map (formsubst v) (hypotheses cl)) ->
  gbackchain S (\sum_(i <- s) i).+1 (formsubst v (conclusion cl)).
Proof. rewrite all2E_gen ; exact: gbackchain_rule0. Qed.

Fixpoint gbackchain_ind0 (S : set (set form))
  (P : nat -> form -> Prop)
  (H : forall cl v s, S cl ->
    (forall n : nat, herbase (functions (interp @` S)) (v n)) ->
    List.Forall2 P s (map (formsubst v) (hypotheses cl)) ->
    P (\sum_(i <- s) i).+1 (formsubst v (conclusion cl)))
  (n : nat) (f : form) (H0 : gbackchain S n f) : P n f :=
  match H0 in gbackchain _ n1 f1 return P n1 f1
  with gbackchain_rule0 cl v l H1 H2 H3 => H cl v l H1 H2
    (List.Forall2_ind (List.Forall2 P)
      (List.Forall2_nil _) (fun _ _ _ _ H4 H5 H6 =>
        List.Forall2_cons _ _ (gbackchain_ind0 H H4) H6) H3) end.

Lemma gbackchain_ind (S : set (set form))
  (P : nat -> form -> Prop)
  (H : forall cl v s, S cl ->
    (forall n : nat, herbase (functions (interp @` S)) (v n)) ->
    all2 P s (map (formsubst v) (hypotheses cl)) ->
    P (\sum_(i <- s) i).+1 (formsubst v (conclusion cl)))
  (n : nat) (f : form) (H0 : gbackchain S n f) : P n f.
Proof.
  by apply (@gbackchain_ind0 S) ; first rewrite all2E.
Qed.

Register Scheme gbackchain_ind as ind_nodep for gbackchain.

Lemma foldr_addn_S n s : foldr addn n.+1 s = (foldr addn n s).+1.
Proof. by elim:s => //= ? ? -> ; rewrite addnS. Qed.

Lemma gbackchain_def : gbackchain = (fun s : (form -> Prop) -> Prop => fun a0 : nat => fun a1 : form => forall gbackchain' : nat -> form -> Prop, (forall a0' : nat, forall a1' : form, (exists cl : form -> Prop, exists i : nat -> term, exists ns : seq nat, (a0' = (@ITLIST nat nat addn ns (NUMERAL (BIT1 0)))) /\ ((a1' = (formsubst i (conclusion cl))) /\ ((@IN (form -> Prop) cl s) /\ ((forall x : nat, @IN term (i x) (herbase (functions (@IMAGE (form -> Prop) form interp s)))) /\ (@ALL2 nat form gbackchain' ns (@List.map form form (formsubst i) (hypotheses cl))))))) -> gbackchain' a0' a1') -> gbackchain' a0 a1).
Proof.
  rewrite/3= ; ind_align.
  - by exist cl v s ; split ; first rewrite -foldrE -foldr_addn_S.
  - rewrite/ITLIST foldr_addn_S /2= foldrE ; exact:gbackchain_rule.
Qed.

Definition iminmodel E :=
  (terms (functions E),
   (Fn,
     fun n l => forall M, Dom M = terms (functions E) /\ Fun M = Fn /\ 
     (forall v f, IN f E /\ valuation M v -> holds M v f) ->
     Pred M n l)).

Lemma iminmodel_def : iminmodel = (fun _549309 : form -> Prop => @pair (term -> Prop) (prod (nat -> (seq term) -> term) (nat -> (seq term) -> Prop)) (terms (functions _549309)) (@pair (nat -> (seq term) -> term) (nat -> (seq term) -> Prop) Fn (fun p : nat => fun zs : seq term => forall C : prod (term -> Prop) (prod (nat -> (seq term) -> term) (nat -> (seq term) -> Prop)), (((@Dom term C) = (terms (functions _549309))) /\ (((@Fun term C) = Fn) /\ (forall v : nat -> term, forall p' : form, ((@IN form p' _549309) /\ (@valuation term C v)) -> @holds term C v p')) -> @Pred term C p zs)))).
Proof. reflexivity. Qed.

Inductive ibackchain (S : set (set form)) : nat -> form -> Prop :=
| ibackchain_rule0 : forall cl v s, S cl ->
  (forall n, terms (functions (interp @` S)) (v n)) ->
  List.Forall2 (ibackchain S) s (map (formsubst v) (hypotheses cl)) ->
  ibackchain S (\sum_(i <- s) i).+1 (formsubst v (conclusion cl)).

Lemma ibackchain_rule (S : set (set form)) cl v s : S cl ->
  (forall n, terms (functions (interp @` S)) (v n)) ->
  all2 (ibackchain S) s (map (formsubst v) (hypotheses cl)) ->
  ibackchain S (\sum_(i <- s) i).+1 (formsubst v (conclusion cl)).
Proof. rewrite all2E_gen ; exact: ibackchain_rule0. Qed.

Fixpoint ibackchain_ind0 (S : set (set form))
  (P : nat -> form -> Prop)
  (H : forall cl v s, S cl ->
    (forall n : nat, terms (functions (interp @` S)) (v n)) ->
    List.Forall2 P s (map (formsubst v) (hypotheses cl)) ->
    P (\sum_(i <- s) i).+1 (formsubst v (conclusion cl)))
  (n : nat) (f : form) (H0 : ibackchain S n f) : P n f :=
  match H0 in ibackchain _ n1 f1 return P n1 f1
  with ibackchain_rule0 cl v l H1 H2 H3 => H cl v l H1 H2
    (List.Forall2_ind (List.Forall2 P)
      (List.Forall2_nil _) (fun _ _ _ _ H4 H5 H6 =>
        List.Forall2_cons _ _ (ibackchain_ind0 H H4) H6) H3) end.

Lemma ibackchain_ind (S : set (set form))
  (P : nat -> form -> Prop)
  (H : forall cl v s, S cl ->
    (forall n : nat, terms (functions (interp @` S)) (v n)) ->
    all2 P s (map (formsubst v) (hypotheses cl)) ->
    P (\sum_(i <- s) i).+1 (formsubst v (conclusion cl)))
  (n : nat) (f : form) (H0 : ibackchain S n f) : P n f.
Proof.
  by apply (@ibackchain_ind0 S) ; first rewrite all2E.
Qed.

Register Scheme ibackchain_ind as ind_nodep for ibackchain.

Lemma ibackchain_def : ibackchain = (fun s : (form -> Prop) -> Prop => fun a0 : nat => fun a1 : form => forall ibackchain' : nat -> form -> Prop, (forall a0' : nat, forall a1' : form, (exists cl : form -> Prop, exists i : nat -> term, exists ns : seq nat, (a0' = (@ITLIST nat nat addn ns (NUMERAL (BIT1 0)))) /\ ((a1' = (formsubst i (conclusion cl))) /\ ((@IN (form -> Prop) cl s) /\ ((forall x : nat, @IN term (i x) (terms (functions (@IMAGE (form -> Prop) form interp s)))) /\ (@ALL2 nat form ibackchain' ns (@List.map form form (formsubst i) (hypotheses cl))))))) -> ibackchain' a0' a1') -> ibackchain' a0 a1).
Proof.
  rewrite/3= ; ind_align.
  - by exist cl v s ; split ; first rewrite -foldrE -foldr_addn_S.
  - rewrite/ITLIST foldr_addn_S /2= foldrE ; exact:ibackchain_rule.
Qed.

(*****************************************************************************)
(* Logic/Birkhoff.ml *)
(*****************************************************************************)


Inductive provable (S : set form) : form -> Prop :=
| pr_assume : forall t t', S (FEq t t') -> provable S (FEq t t')
| pr_FEq_refl : forall t, provable S (FEq t t)
| pr_FEq_sym : forall t t', provable S (FEq t t') -> provable S (FEq t' t)
| pr_FEq_trans : forall t t' t'', provable S (FEq t t') -> provable S (FEq t' t'') ->
                 provable S (FEq t t'')
| pr_FEq_fun_compat0 : forall n s s', List.Forall2 (fun t t' => provable S (FEq t t')) s s' ->
               provable S (FEq (Fn n s) (Fn n s'))
| pr_formsubst : forall t t' v, provable S (FEq t t') -> provable S (formsubst v (FEq t t')).

Lemma pr_FEq_fun_compat (S : set form) n s s' :
  all2 (fun t t' => provable S (FEq t t')) s s' ->
    provable S (FEq (Fn n s) (Fn n s')).
Proof. rewrite all2E_gen ; exact: pr_FEq_fun_compat0. Qed.

Scheme provable_ind0 := Minimality for provable Sort Prop.

Fixpoint provable_ind1 (S : set form) (P : form -> Prop)
  H0 H1 H2 H3
  (H4 : forall n s s', List.Forall2 (fun t t' => P (FEq t t')) s s' ->
               P (FEq (Fn n s) (Fn n s')))
  H5 (f : form) (H6 : provable S f) : P f :=
  provable_ind0 H0 H1 H2 H3
    (fun n s s' H' => H4 n s s' (List.Forall2_ind (List.Forall2 (fun t t' => P (FEq t t')))
      (List.Forall2_nil _) (fun f0 f'0 s0 s'0 H00 H10 H20 => List.Forall2_cons _ _
        (@provable_ind1 S P H0 H1 H2 H3 H4 H5 _ H00) H20) H')) H5 H6.

Lemma provable_ind (S : set form) (P : form -> Prop) :
  (forall t t', S (FEq t t') -> P (FEq t t')) ->
  (forall t, P (FEq t t)) ->
  (forall t t', provable S (FEq t t') -> P (FEq t t') -> P (FEq t' t)) ->
  (forall t t' t'', provable S (FEq t t') -> P (FEq t t') ->
    provable S (FEq t' t'') -> P (FEq t' t'') -> P (FEq t t'')) ->
  (forall n s s', all2 (fun t t' => P (FEq t t')) s s' ->
    P (FEq (Fn n s) (Fn n s'))) ->
  (forall t t' v, provable S (FEq t t') -> P (FEq t t') ->
    P (formsubst v (FEq t t'))) ->
  forall f, provable S f -> P f.
Proof. move:provable_ind1 ; rewrite all2E ; exact. Qed.

Register Scheme provable_ind as ind_nodep for provable.

Lemma vdash_def : provable = (fun E : form -> Prop => fun a : form => forall vdash' : form -> Prop, (forall a' : form, ((exists s : term, exists t : term, (a' = (FEq s t)) /\ (@IN form (FEq s t) E)) \/ ((exists t : term, a' = (FEq t t)) \/ ((exists s : term, exists t : term, (a' = (FEq t s)) /\ (vdash' (FEq s t))) \/ ((exists s : term, exists t : term, exists u : term, (a' = (FEq s u)) /\ ((vdash' (FEq s t)) /\ (vdash' (FEq t u)))) \/ ((exists f : nat, exists a'' : seq term, exists b : seq term, (a' = (FEq (Fn f a'') (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash' (FEq l r)) a'' b)) \/ (exists s : term, exists t : term, exists i : nat -> term, (a' = (formsubst i (FEq s t))) /\ (vdash' (FEq s t)))))))) -> vdash' a') -> vdash' a).
Proof.
  rewrite/3= ; ind_align.
  exact: pr_FEq_fun_compat.
Qed.

Inductive wcprovable (S : set form) : form -> Prop :=
| wcpr_assume : forall t t' v, S (FEq t t') -> wcprovable S (formsubst v (FEq t t'))
| wcpr_FEq_refl : forall t, wcprovable S (FEq t t)
| wcpr_FEq_sym : forall t t' v, S (FEq t t') -> wcprovable S (formsubst v (FEq t' t))
| wcpr_FEq_trans : forall t t' t'', wcprovable S (FEq t t') -> wcprovable S (FEq t' t'') ->
                 wcprovable S (FEq t t'')
| wcpr_FEq_fun_compat0 : forall n s s', List.Forall2 (fun t t' => wcprovable S (FEq t t')) s s' ->
               wcprovable S (FEq (Fn n s) (Fn n s')).

Lemma wcpr_FEq_fun_compat (S : set form) n s s' :
  all2 (fun t t' => wcprovable S (FEq t t')) s s' ->
    wcprovable S (FEq (Fn n s) (Fn n s')).
Proof. rewrite all2E_gen ; exact: wcpr_FEq_fun_compat0. Qed.

Scheme wcprovable_ind0 := Minimality for wcprovable Sort Prop.

Fixpoint wcprovable_ind1 (S : set form) (P : form -> Prop)
  H0 H1 H2 H3
  (H4 : forall n s s', List.Forall2 (fun t t' => P (FEq t t')) s s' ->
               P (FEq (Fn n s) (Fn n s')))
  (f : form) (H5 : wcprovable S f) : P f :=
  @wcprovable_ind0 S P H0 H1 H2 H3
    (fun n s s' H' => H4 n s s' (List.Forall2_ind (List.Forall2 (fun t t' => P (FEq t t')))
      (List.Forall2_nil _) (fun f0 f'0 l0 l'0 H00 H10 H20 => List.Forall2_cons _ _
        (@wcprovable_ind1 S P H0 H1 H2 H3 H4 _ H00) H20) H')) f H5.

Lemma wcprovable_ind (S : set form) (P : form -> Prop) :
  (forall t t' v, S (FEq t t') -> P (formsubst v (FEq t t'))) ->
  (forall t, P (FEq t t)) ->
  (forall t t' v, S (FEq t t') -> P (formsubst v (FEq t' t))) ->
  (forall t t' t'', wcprovable S (FEq t t') -> P (FEq t t') ->
    wcprovable S (FEq t' t'') -> P (FEq t' t'') -> P (FEq t t'')) ->
  (forall n s s', all2 (fun t t' : term => P (FEq t t')) s s' ->
    P (FEq (Fn n s) (Fn n s'))) ->
  forall f, wcprovable S f -> P f.
Proof.  move:wcprovable_ind1 ; rewrite all2E ; exact. Qed.

Register Scheme wcprovable_ind as ind_nodep for wcprovable.

Lemma vdash2_def : wcprovable = (fun E : form -> Prop => fun a : form => forall vdash2' : form -> Prop, (forall a' : form, ((exists s : term, exists t : term, exists i : nat -> term, (a' = (formsubst i (FEq s t))) /\ (@IN form (FEq s t) E)) \/ ((exists s : term, exists t : term, exists i : nat -> term, (a' = (formsubst i (FEq t s))) /\ (@IN form (FEq s t) E)) \/ ((exists t : term, a' = (FEq t t)) \/ ((exists s : term, exists t : term, exists u : term, (a' = (FEq s u)) /\ ((vdash2' (FEq s t)) /\ (vdash2' (FEq t u)))) \/ (exists f : nat, exists a'' : seq term, exists b : seq term, (a' = (FEq (Fn f a'') (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash2' (FEq l r)) a'' b)))))) -> vdash2' a') -> vdash2' a).
Proof.
  rewrite/3= ; ind_align.
  exact: wcpr_FEq_fun_compat.
Qed.

Set Elimination Schemes.
Inductive aprovable (S : set form) : form -> Prop :=
| apr_assume : forall t t' v, S (FEq t t') -> aprovable S (formsubst v (FEq t t'))
| apr_FEq_sym : forall t t' v, S (FEq t t')  -> aprovable S (formsubst v (FEq t' t)).

Lemma vdash2_axiom_def : aprovable = (fun E : form -> Prop => fun a : form => forall vdash2_axiom' : form -> Prop, (forall a' : form, ((exists s : term, exists t : term, exists i : nat -> term, (a' = (formsubst i (FEq s t))) /\ (@IN form (FEq s t) E)) \/ (exists s : term, exists t : term, exists i : nat -> term, (a' = (formsubst i (FEq t s))) /\ (@IN form (FEq s t) E))) -> vdash2_axiom' a') -> vdash2_axiom' a).
Proof. rewrite/3= ; ind_align. Qed.

Unset Elimination Schemes.
Inductive cprovable (S : set form) : form -> Prop :=
| cpr_FEq_refl : forall t, cprovable S (FEq t t)
| cpr_prac : forall t t', provable_achain S (FEq t t') -> cprovable S (FEq t t')
| cpr_prcc : forall t t', provable_cchain S (FEq t t') -> cprovable S (FEq t t')
with provable_achain (S : set form) : form -> Prop :=
| prac_apr : forall t t', aprovable S (FEq t t') -> provable_achain S (FEq t t')
| prac_trans : forall t t' t'', aprovable S (FEq t t') -> cprovable S (FEq t' t'') ->
               provable_achain S (FEq t t'')
with provable_cchain (S : set form) : form -> Prop :=
| prcc_prc : forall t t', provable_cong S (FEq t t') -> provable_cchain S (FEq t t')
| prcc_trans : forall t t' t'', provable_cong S (FEq t t') -> provable_achain S (FEq t' t'') ->
               provable_cchain S (FEq t t'')
with provable_cong (S : set form) : form -> Prop :=
| prc_fun_compat0 : forall n s s', List.Forall2 (fun t t' => cprovable S (FEq t t')) s s' ->
                   provable_cong S (FEq (Fn n s) (Fn n s')).
Set Elimination Schemes.

Lemma prc_fun_compat (S : set form) n s s' :
  all2 (fun t t' => cprovable S (FEq t t')) s s' ->
    provable_cong S (FEq (Fn n s) (Fn n s')).
Proof. rewrite all2E_gen ; exact: prc_fun_compat0. Qed.

Unset Implicit Arguments.
Section cprovable_ind0.

Variables
  (S : set form)
  (P P0 P1 P2 : form -> Prop)
  (H0 : forall t, P (FEq t t))
  (H1 : forall t t', provable_achain S (FEq t t') -> P0 (FEq t t') -> P (FEq t t'))
  (H2 : forall t t', provable_cchain S (FEq t t') -> P1 (FEq t t') -> P (FEq t t'))
  (H3 : forall t t', aprovable S (FEq t t') -> P0 (FEq t t'))
  (H4 : forall t t' t'', aprovable S (FEq t t') -> cprovable S (FEq t' t'') ->
    P (FEq t' t'') -> P0 (FEq t t''))
  (H5 : forall t t', provable_cong S (FEq t t') -> P2 (FEq t t') -> P1 (FEq t t'))
  (H6 : forall t t' t'', provable_cong S (FEq t t') -> P2 (FEq t t') ->
    provable_achain S (FEq t' t'') -> P0 (FEq t' t'') -> P1 (FEq t t''))
  (H7 : forall n s s', List.Forall2 (fun t t' : term => P (FEq t t')) s s' -> P2 (FEq (Fn n s) (Fn n s'))).

Fixpoint cprovable_ind0 f (H' : cprovable S f) : P f :=
  match H' in cprovable _ f return P f with
  | cpr_FEq_refl t => H0 t
  | cpr_prac t t' Hac => H1 t t' Hac (provable_achain_ind0 (FEq t t') Hac)
  | cpr_prcc t t' Hcc => H2 t t' Hcc (provable_cchain_ind0 (FEq t t') Hcc) end
with provable_achain_ind0 f (Hac : provable_achain S f ): P0 f :=
  match Hac in provable_achain _ f return P0 f with
  | prac_apr t t' Ha => H3 t t' Ha
  | prac_trans t t' t'' Ha H' => H4 t t' t'' Ha H' (cprovable_ind0 (FEq t' t'') H') end
with provable_cchain_ind0 f (Hcc : provable_cchain S f) : P1 f :=
  match Hcc in provable_cchain _ f return P1 f with
  | prcc_prc t t' Hc => H5 t t' Hc (provable_cong_ind0 (FEq t t') Hc)
  | prcc_trans t t' t'' Hc Hac => H6 t t' t'' Hc (provable_cong_ind0 (FEq t t') Hc)
    Hac (provable_achain_ind0 (FEq t' t'') Hac) end
with provable_cong_ind0 f (Hc : provable_cong S f) : P2 f :=
  match Hc in provable_cong _ f return P2 f with
  | prc_fun_compat0 n s s' HF2' => H7 n s s'
    (List.Forall2_ind (List.Forall2 (fun t t' => P (FEq t t')))
      (List.Forall2_nil _) (fun _ _ _ _ H00 _ H20 => List.Forall2_cons _ _
        (cprovable_ind0 _ H00) H20) HF2') end.

End cprovable_ind0.

Section cprovable_ind.

Variables
  (S : set form)
  (P P0 P1 P2 : form -> Prop)
  (H0 : forall t, P (FEq t t))
  (H1 : forall t t', provable_achain S (FEq t t') -> P0 (FEq t t') -> P (FEq t t'))
  (H2 : forall t t', provable_cchain S (FEq t t') -> P1 (FEq t t') -> P (FEq t t'))
  (H3 : forall t t', aprovable S (FEq t t') -> P0 (FEq t t'))
  (H4 : forall t t' t'', aprovable S (FEq t t') -> cprovable S (FEq t' t'') ->
    P (FEq t' t'') -> P0 (FEq t t''))
  (H5 : forall t t', provable_cong S (FEq t t') -> P2 (FEq t t') -> P1 (FEq t t'))
  (H6 : forall t t' t'', provable_cong S (FEq t t') -> P2 (FEq t t') ->
    provable_achain S (FEq t' t'') -> P0 (FEq t' t'') -> P1 (FEq t t''))
  (H7 : forall n s s', all2 (fun t t' : term => P (FEq t t')) s s' -> P2 (FEq (Fn n s) (Fn n s'))).

Local Ltac from prev :=
  refine (prev _ _ _ _ _ H0 H1 H2 H3 H4 H5 H6 _ _) ; rewrite all2E ; exact H7.

Lemma cprovable_ind f : cprovable S f -> P f.
Proof. from cprovable_ind0. Qed.
Lemma provable_achain_ind f : provable_achain S f -> P0 f.
Proof. from provable_achain_ind0. Qed.
Lemma provable_cchain_ind f : provable_cchain S f -> P1 f.
Proof. from provable_cchain_ind0. Qed.
Lemma provable_cong_ind f : provable_cong S f -> P2 f.
Proof. from provable_cong_ind0. Qed.

End cprovable_ind.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Register Scheme cprovable_ind as ind_nodep for cprovable.
Register Scheme provable_achain_ind as ind_nodep for provable_achain.
Register Scheme provable_cchain_ind as ind_nodep for provable_cchain.
Register Scheme provable_cong_ind as ind_nodep for provable_cong.

Ltac provable_align induction_principle :=
  let s := fresh in
  let H := fresh in
  let Pac := fresh in
  let Pcc := fresh in
  let Pc := fresh in
  let P := fresh in
  let H' := fresh in
  funext => s ? ; apply prop_ext ; intro H ;
  [ intros Pac Pcc Pc P H' ; apply (induction_principle s P Pac Pcc Pc) ; auto ;
    clear H ; intros ; apply H' ; breakgoal
  | apply (H (provable_achain s) (provable_cchain s) (provable_cong s) (cprovable s)) ;
    clear ; repeat split ; intros f H ; full_destruct ;
    blindrewrite ; try (by constructor) ; try exact: prc_fun_compat ;
    apply: prac_trans || apply: prcc_trans ; eassumption ].

Lemma vdash3_def : cprovable = (fun E : form -> Prop => fun a3 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1) /\ ((forall a2 : form, (exists f : nat, exists a : seq term, exists b : seq term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2) /\ (forall a3' : form, (exists s : term, exists t : term, (a3' = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3')))) -> vdash3' a3).
Proof. provable_align cprovable_ind. Qed.

Lemma vdash2_achain_def : provable_achain = (fun E : form -> Prop => fun a0 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0' : form, ((exists s : term, exists t : term, (a0' = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0' = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0') /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1) /\ ((forall a2 : form, (exists f : nat, exists a : seq term, exists b : seq term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3)))) -> vdash2_achain' a0).
Proof. provable_align provable_achain_ind. Qed.

Lemma vdash2_cchain_def : provable_cchain = (fun E : form -> Prop => fun a1 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0) /\ ((forall a1' : form, ((exists s : term, exists t : term, (a1' = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1' = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1') /\ ((forall a2 : form, (exists f : nat, exists a : seq term, exists b : seq term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3)))) -> vdash2_cchain' a1).
Proof. provable_align provable_cchain_ind. Qed.

Lemma vdash2_cong_def : provable_cong = (fun E : form -> Prop => fun a2 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1) /\ ((forall a2' : form, (exists f : nat, exists a : seq term, exists b : seq term, (a2' = (FEq (Fn f a) (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2') /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3)))) -> vdash2_cong' a2).
Proof. provable_align provable_cong_ind. Qed.

Fixpoint subterms t : term -> Prop :=
  match t with
  | V _ => [set t]
  | Fn _ l => t |` (seq_Union (map subterms l)) end.

Lemma subterms_def : subterms = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> term -> term -> Prop) (fun subterms' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> term -> term -> Prop => forall _553739 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall x : nat, (subterms' _553739 (V x)) = (@INSERT term (V x) (@set0 term))) /\ (forall f : nat, forall args : seq term, (subterms' _553739 (Fn f args)) = (@INSERT term (Fn f args) (@seq_Union term (@List.map term (term -> Prop) (subterms' _553739) args))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))).
Proof. by term_align => * /3=. Qed.

Inductive notatom : form -> Prop :=
| notatom_FFalse : notatom FFalse
| notatom_FImp : forall f f', notatom (FImp f f')
| notatom_FAll : forall n f, notatom (FAll n f).

Definition SUBTERMSA : form -> term -> Prop := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> form -> term -> Prop) (fun subtermsa' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> form -> term -> Prop => forall _553741 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), forall P : nat, forall args : seq term, (subtermsa' _553741 (Atom P args)) = (@seq_Union term (@List.map term (term -> Prop) subterms args))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))))))))))).

Definition subtermsa f : term -> Prop :=
  match f with Atom _ l => seq_Union (map subterms l) | _ => SUBTERMSA f end.

Lemma subtermsa_def : subtermsa = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> form -> term -> Prop) (fun subtermsa' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> form -> term -> Prop => forall _553741 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), forall P : nat, forall args : seq term, (subtermsa' _553741 (Atom P args)) = (@seq_Union term (@List.map term (term -> Prop) subterms args))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0))))))))))))))))).
Proof. by partial_align notatom. Qed.

Definition subtermss s := UNIONS (subtermsa @` s).

Lemma subtermss_def : subtermss = (fun _553742 : form -> Prop => @UNIONS term (@GSPEC (term -> Prop) (fun GEN_PVAR_664 : term -> Prop => exists p : form, @SETSPEC (term -> Prop) GEN_PVAR_664 (@IN form p _553742) (subtermsa p)))).
Proof. by move=> /f` * /3=. Qed.

Definition esubterms s t t' := subtermss (FEq t t' |` [set f | exists v, (formsubst v @` s) f]).

Lemma esubterms_def : esubterms = (fun _553747 : form -> Prop => fun _553748 : term => fun _553749 : term => subtermss (@INSERT form (FEq _553748 _553749) (@GSPEC form (fun GEN_PVAR_665 : form => exists i : nat -> term, exists p : form, @SETSPEC form GEN_PVAR_665 (@IN form p _553747) (formsubst i p))))).
Proof.
  move=> /f` * ; rewrite/3=/esubterms.
  by repeat f_equal ; ext => [? /= [? []] | ? /= [? [? []]]] ; eauto.
Qed.

Unset Elimination Schemes.
Inductive scprovable (S : set form) : form -> Prop :=
| scpr_FEq_refl : forall t, scprovable S (FEq t t)
| scpr_prsac : forall t t', provable_sachain S (FEq t t') -> scprovable S (FEq t t')
| scpr_prscc : forall t t', provable_scchain S (FEq t t') -> scprovable S (FEq t t')
with provable_sachain (S : set form) : form -> Prop :=
| prsac_apr : forall t t', aprovable S (FEq t t') -> provable_sachain S (FEq t t')
| prsac_trans : forall t t' t'', aprovable S (FEq t t') -> scprovable S (FEq t' t'') ->
                esubterms S t t'' t' -> provable_sachain S (FEq t t'')
with provable_scchain (S : set form) : form -> Prop :=
| prscc_prsc : forall t t', provable_scong S (FEq t t') -> provable_scchain S (FEq t t')
| prscc_trans : forall t t' t'', provable_scong S (FEq t t') -> provable_sachain S (FEq t' t'') ->
                esubterms S t t'' t' -> provable_scchain S (FEq t t'')
with provable_scong (S : set form) : form -> Prop :=
| prsc_fun_compat0 : forall n s s', List.Forall2 (fun t t' => scprovable S (FEq t t')) s s' ->
                   provable_scong S (FEq (Fn n s) (Fn n s')).
Set Elimination Schemes.

Lemma prsc_fun_compat (S : set form) n s s' :
  all2 (fun t t' => scprovable S (FEq t t')) s s' ->
    provable_scong S (FEq (Fn n s) (Fn n s')).
Proof. rewrite all2E_gen ; exact: prsc_fun_compat0. Qed.

Unset Implicit Arguments.
Section scprovable_ind0.

Variables
  (S : set form)
  (P P0 P1 P2 : form -> Prop)
  (H0 : forall t, P (FEq t t))
  (H1 : forall t t', provable_sachain S (FEq t t') -> P0 (FEq t t') -> P (FEq t t'))
  (H2 : forall t t', provable_scchain S (FEq t t') -> P1 (FEq t t') -> P (FEq t t'))
  (H3 : forall t t', aprovable S (FEq t t') -> P0 (FEq t t'))
  (H4 : forall t t' t'', aprovable S (FEq t t') -> scprovable S (FEq t' t'') ->
    P (FEq t' t'') -> esubterms S t t'' t' -> P0 (FEq t t''))
  (H5 : forall t t', provable_scong S (FEq t t') -> P2 (FEq t t') -> P1 (FEq t t'))
  (H6 : forall t t' t'', provable_scong S (FEq t t') -> P2 (FEq t t') ->
    provable_sachain S (FEq t' t'') -> P0 (FEq t' t'') -> esubterms S t t'' t' ->
    P1 (FEq t t''))
  (H7 : forall n s s', List.Forall2 (fun t t' : term => P (FEq t t')) s s' -> P2 (FEq (Fn n s) (Fn n s'))).

Fixpoint scprovable_ind0 f (H' : scprovable S f) : P f :=
  match H' in scprovable _ f return P f with
  | scpr_FEq_refl t => H0 t
  | scpr_prsac t t' Hac => H1 t t' Hac (provable_sachain_ind0 (FEq t t') Hac)
  | scpr_prscc t t' Hcc => H2 t t' Hcc (provable_scchain_ind0 (FEq t t') Hcc) end
with provable_sachain_ind0 f (Hac : provable_sachain S f ): P0 f :=
  match Hac in provable_sachain _ f return P0 f with
  | prsac_apr t t' Ha => H3 t t' Ha
  | prsac_trans t t' t'' Ha H' Hsubs => H4 t t' t'' Ha H' (scprovable_ind0 (FEq t' t'') H') Hsubs end
with provable_scchain_ind0 f (Hcc : provable_scchain S f) : P1 f :=
  match Hcc in provable_scchain _ f return P1 f with
  | prscc_prsc t t' Hc => H5 t t' Hc (provable_scong_ind0 (FEq t t') Hc)
  | prscc_trans t t' t'' Hc Hac Hsubs => H6 t t' t'' Hc (provable_scong_ind0 (FEq t t') Hc)
    Hac (provable_sachain_ind0 (FEq t' t'') Hac) Hsubs end
with provable_scong_ind0 f (Hc : provable_scong _ f) : P2 f :=
  match Hc in provable_scong _ f return P2 f with
  | prsc_fun_compat0 n l l' HF2' => H7 n l l'
    (List.Forall2_ind (List.Forall2 (fun t t' => P (FEq t t')))
      (List.Forall2_nil _) (fun _ _ _ _ H00 _ H20 => List.Forall2_cons _ _
        (scprovable_ind0 _ H00) H20) HF2') end.

End scprovable_ind0.

Section scprovable_ind.
Variables
  (S : set form)
  (P P0 P1 P2 : form -> Prop)
  (H0 : forall t, P (FEq t t))
  (H1 : forall t t', provable_sachain S (FEq t t') -> P0 (FEq t t') -> P (FEq t t'))
  (H2 : forall t t', provable_scchain S (FEq t t') -> P1 (FEq t t') -> P (FEq t t'))
  (H3 : forall t t', aprovable S (FEq t t') -> P0 (FEq t t'))
  (H4 : forall t t' t'', aprovable S (FEq t t') -> scprovable S (FEq t' t'') ->
    P (FEq t' t'') -> esubterms S t t'' t' -> P0 (FEq t t''))
  (H5 : forall t t', provable_scong S (FEq t t') -> P2 (FEq t t') -> P1 (FEq t t'))
  (H6 : forall t t' t'', provable_scong S (FEq t t') -> P2 (FEq t t') ->
    provable_sachain S (FEq t' t'') -> P0 (FEq t' t'') -> esubterms S t t'' t' ->
    P1 (FEq t t''))
  (H7 : forall n l l', all2 (fun t t' : term => P (FEq t t')) l l' -> P2 (FEq (Fn n l) (Fn n l'))).

Local Ltac from prev :=
  refine (prev _ _ _ _ _ H0 H1 H2 H3 H4 H5 H6 _ _) ; rewrite all2E ; exact H7.

Lemma scprovable_ind f : scprovable S f -> P f.
Proof. from scprovable_ind0. Qed.
Lemma provable_sachain_ind f : provable_sachain S f -> P0 f.
Proof. from provable_sachain_ind0. Qed.
Lemma provable_scchain_ind f : provable_scchain S f -> P1 f.
Proof. from provable_scchain_ind0. Qed.
Lemma provable_scong_ind f : provable_scong S f -> P2 f.
Proof. from provable_scong_ind0. Qed.

End scprovable_ind.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Register Scheme scprovable_ind as ind_nodep for scprovable.
Register Scheme provable_sachain_ind as ind_nodep for provable_sachain.
Register Scheme provable_scchain_ind as ind_nodep for provable_scchain.
Register Scheme provable_scong_ind as ind_nodep for provable_scong.

Ltac sprovable_align induction_principle :=
  let s := fresh in
  let H := fresh in
  let Pac := fresh in
  let Pcc := fresh in
  let Pc := fresh in
  let P := fresh in
  let H' := fresh in
  funext => s ? ; apply prop_ext ; intro H ;
  [ intros Pac Pcc Pc P H' ; apply (induction_principle s P Pac Pcc Pc) ; auto ;
    clear H ; intros ; apply H' ; breakgoal
  | apply (H (provable_sachain s) (provable_scchain s) (provable_scong s) (scprovable s)) ;
    clear ; repeat split ; intros f H ; full_destruct ;
    blindrewrite ; try (by constructor) ; try exact: prsc_fun_compat ;
    apply: prsac_trans || apply: prscc_trans ; eassumption ].

Lemma vdash4_def : scprovable = (fun E : form -> Prop => fun a3 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1) /\ ((forall a2 : form, (exists f : nat, exists a : seq term, exists b : seq term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2) /\ (forall a3' : form, (exists s : term, exists t : term, (a3' = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3')))) -> vdash4' a3).
Proof. sprovable_align scprovable_ind. Qed.

Lemma vdash2_sachain_def : provable_sachain = (fun E : form -> Prop => fun a0 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0' : form, ((exists s : term, exists t : term, (a0' = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0' = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0') /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1) /\ ((forall a2 : form, (exists f : nat, exists a : seq term, exists b : seq term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3)))) -> vdash2_sachain' a0).
Proof. sprovable_align provable_sachain_ind. Qed.

Lemma vdash2_scchain_def : provable_scchain = (fun E : form -> Prop => fun a1 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0) /\ ((forall a1' : form, ((exists s : term, exists t : term, (a1' = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1' = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1') /\ ((forall a2 : form, (exists f : nat, exists a : seq term, exists b : seq term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3)))) -> vdash2_scchain' a1).
Proof. sprovable_align provable_scchain_ind. Qed.

Lemma vdash2_scong_def : provable_scong = (fun E : form -> Prop => fun a2 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1) /\ ((forall a2' : form, (exists f : nat, exists a : seq term, exists b : seq term, (a2' = (FEq (Fn f a) (Fn f b))) /\ (@ALL2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2') /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3)))) -> vdash2_scong' a2).
Proof. sprovable_align provable_scong_ind. Qed.

Definition Eqclause_Func (c : nat * nat) := let (n,m) := c in
  let l := Varpairs m in
  [set` (FEq (Fn n (map fst l)) (Fn n (map snd l)) ::
   map (fun c' => Not (FEq (fst c') (snd c'))) l)].

Lemma Eqclause_Func_def : Eqclause_Func = (fun _554544 : prod nat nat => @set_of_seq form (@cons form (FEq (Fn (@fst nat nat _554544) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd nat nat _554544)))) (Fn (@fst nat nat _554544) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd nat nat _554544))))) (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (Not (FEq s t)))) (Varpairs (@snd nat nat _554544))))).
Proof.
  apply funext ; case=> n m ; rewrite/Eqclause_Func/set_of_seq /=.
  match goal with | |- [set` (?a::map _ ?s)] = _ =>
    apply (f_equal (fun f => [set` (a :: map f s)])) end.
  by align_ε => // ? H H' ; ext ; case => t t' ; rewrite H H'.
Qed.

Definition Eqclause_Pred (c : nat * nat) := let (n,m) := c in
  let s := Varpairs m in
  [set` Atom n (map snd s) :: Not (Atom n (map fst s)) ::
     map (fun c' => Not (FEq (fst c') (snd c'))) s].

Lemma Eqclause_Pred_def : Eqclause_Pred = (fun _554553 : prod nat nat => @set_of_seq form (@cons form (Atom (@fst nat nat _554553) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd nat nat _554553)))) (@cons form (Not (Atom (@fst nat nat _554553) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd nat nat _554553))))) (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (Not (FEq s t)))) (Varpairs (@snd nat nat _554553)))))).
Proof.
  apply funext ; case=> n m ; rewrite/Eqclause_Func/set_of_seq /=.
  match goal with | |- [set` (?a::?b::map _ ?s)] = _ =>
    apply (f_equal (fun f => [set` (a :: b :: map f s)])) end.
  by align_ε => // ? H H' ; ext ; case => t t' ; rewrite H H'.
Qed.

Definition Eqclauses (L : set (nat * nat) * set (nat * nat)) :=
  let (s,s') := L in [set FEq (V 0) (V 0)] |` (
    [set Not (FEq (V 0) (V 1)) ; Not (FEq (V 2) (V 1)) ; FEq (V 0) (V 2)] |` (
      Eqclause_Func @` s `|` Eqclause_Pred @` s' )).

Lemma Eqclauses_def : Eqclauses = (fun _554562 : prod ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) => @INSERT (form -> Prop) (@INSERT form (FEq (V (NUMERAL 0)) (V (NUMERAL 0))) (@set0 form)) (@INSERT (form -> Prop) (@INSERT form (Not (FEq (V (NUMERAL 0)) (V (NUMERAL (BIT1 0))))) (@INSERT form (Not (FEq (V (NUMERAL (BIT0 (BIT1 0)))) (V (NUMERAL (BIT1 0))))) (@INSERT form (FEq (V (NUMERAL 0)) (V (NUMERAL (BIT0 (BIT1 0))))) (@set0 form)))) (@setU (form -> Prop) (@GSPEC (form -> Prop) (fun GEN_PVAR_666 : form -> Prop => exists fa : prod nat nat, @SETSPEC (form -> Prop) GEN_PVAR_666 (@IN (prod nat nat) fa (@fst ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) _554562)) (Eqclause_Func fa))) (@GSPEC (form -> Prop) (fun GEN_PVAR_667 : form -> Prop => exists pa : prod nat nat, @SETSPEC (form -> Prop) GEN_PVAR_667 (@IN (prod nat nat) pa (@snd ((prod nat nat) -> Prop) ((prod nat nat) -> Prop) _554562)) (Eqclause_Pred pa)))))).
Proof.
  by apply funext ; case => n m ; rewrite/3= ; rewrite/Eqclauses ?setUA.
Qed.

Definition Eqaxiom_Pred_imp c := uclose
  (FImp (foldr FAnd FTrue (map (fun c => FEq (fst c) (snd c)) (Varpairs (snd c))))
     (FImp (Atom (fst c) (map fst (Varpairs (snd c)))) (Atom (fst c) (map snd (Varpairs (snd c)))))).

Lemma Eqaxiom_Pred_imp_def : Eqaxiom_Pred_imp = (fun _554616 : prod nat nat => uclose (FImp (@ITLIST form form FAnd (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (FEq s t))) (Varpairs (@snd nat nat _554616))) FTrue) (FImp (Atom (@fst nat nat _554616) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd nat nat _554616)))) (Atom (@fst nat nat _554616) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd nat nat _554616))))))).
Proof.
  have <- : (fun c => FEq (fst c) (snd c)) =
    ε (fun f => forall s t, f (s,t) = FEq s t) ; last by [].
  by align_ε => // func' H H' ; ext ; case => * ; rewrite H H'.
Qed.

(*****************************************************************************)
(* Logic/trs.ml *)
(*****************************************************************************)

(* term rewritings *)
Inductive TRS (rw_rules : term * term -> Prop) : term -> term -> Prop :=
| TRS_subst : forall v t t', rw_rules (t,t') ->
  TRS rw_rules (termsubst v t) (termsubst v t')
| TRS_rec : forall t t' n s s', TRS rw_rules t t' ->
  TRS rw_rules (Fn n (s++t::s')) (Fn n (s++t'::s')).

Lemma TRS_def : TRS = (fun rws : (prod term term) -> Prop => fun a0 : term => fun a1 : term => forall TRS' : term -> term -> Prop, (forall a0' : term, forall a1' : term, ((exists i : nat -> term, exists l : term, exists r : term, (a0' = (termsubst i l)) /\ ((a1' = (termsubst i r)) /\ (@IN (prod term term) (@pair term term l r) rws))) \/ (exists s : term, exists t : term, exists f : nat, exists largs : seq term, exists rargs : seq term, (a0' = (Fn f (@app term largs (@cons term s rargs)))) /\ ((a1' = (Fn f (@app term largs (@cons term t rargs)))) /\ (TRS' s t)))) -> TRS' a0' a1') -> TRS' a0 a1).
Proof. rewrite/3= ; ind_align. Qed.

(*****************************************************************************)
(* Logic/lpo.ml *)
(*****************************************************************************)

Definition NONWF A (R : A -> A -> Prop) (x : A) := ~Acc R x.

Lemma NONWF_def {A : Type'} :  (@NONWF A) = (fun _563585 : A -> A -> Prop => fun _563586 : A => ex (fun s : nat -> A => (eq (s (NUMERAL 0)) _563586) /\ (forall n : nat, _563585 (s (S n)) (s n)))).
Proof.
  ext=> R x.
  - intro NWFx. set (NONWFseq := fix NONWFseq n := if n is k.+1
    then ε (fun y => NONWF R y /\ R y (NONWFseq k)) else x).
    exists NONWFseq ; split => // n.
    have IG: forall n, NONWF R (NONWFseq n) -> NONWF R (NONWFseq n.+1) /\
      R (NONWFseq n.+1) (NONWFseq n).
    { move=> {}n NWFn /= ; ε_spec ; last by [].
      apply/not_notP/forallNP => H ; apply/NWFn/Acc_intro=> y.
      move: (H y) ; rewrite/NONWF not_andE ; tauto. }
    have: NONWF R (NONWFseq n) /\ R (NONWFseq n.+1) (NONWFseq n) ; last tauto.
    elim: n => [|n [NWFn _]] ; first by split ; last apply IG.
    by have ?: NONWF R (NONWFseq n.+1) ; [apply IG | split ; last apply IG].
  - case=> + + H ; elim:H =>{}x _ IHx s [s0x schain].
    by apply: (IHx (s 1) _ (s \o S)) ; [rewrite -s0x | split => /=].
Qed.

Fixpoint termsize t :=
  match t with
  | V _ => 1
  | Fn _ s => foldr addn 1 (map termsize s) end.

Lemma termsize_def : termsize = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> term -> nat) (fun termsize' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> term -> nat => forall _564457 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall x : nat, (termsize' _564457 (V x)) = (NUMERAL (BIT1 0))) /\ (forall f : nat, forall args : seq term, (termsize' _564457 (Fn f args)) = (@ITLIST nat nat addn (@List.map term nat (termsize' _564457) args) (NUMERAL (BIT1 0))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))))))))))).
Proof. by term_align. Qed.

Inductive LEXi A (R : A -> A -> Prop) : seq A -> seq A -> Prop :=
| LEX_R : forall x s x' s', R x x' -> size s = size s' -> LEXi R (x::s) (x'::s')
| LEX_eq : forall x s s', LEXi R s s' -> LEXi R (x::s) (x::s').

Lemma LEXi_size A (R : A -> A -> Prop) s s' :
  LEXi R s s' -> size s = size s'.
Proof.
  by induction 1 => /= ; f_equal.
Qed.

Fixpoint LEX A (R : A -> A -> Prop) (s s' : seq A) := match s, s' with
| a::s, a'::s' => if R a a' then size s = size s' else a = a' /\ LEX R s s'
| _,_ => False end.

Lemma LEXE : LEX = LEXi.
Proof.
  ext=> A R.
  - elim=> // a s IHs [] //= a' s' /c`.
    + exact: LEX_R.
    + move=> _ [-> /IHs] ; exact: LEX_eq.
  - move=> s s' ; elim {s s'}=> [* | a s s' LEXss' IHLEX] /= //1= /c` _.
    + exact (LEXi_size LEXss').
    + by [].
Qed.

Lemma LEX_def {_250280 : Type'} : (@LEX _250280) = (@ε ((prod nat (prod nat nat)) -> (_250280 -> _250280 -> Prop) -> (seq _250280) -> (seq _250280) -> Prop) (fun LEX' : (prod nat (prod nat nat)) -> (_250280 -> _250280 -> Prop) -> (seq _250280) -> (seq _250280) -> Prop => forall _564465 : prod nat (prod nat nat), (forall lt2' : _250280 -> _250280 -> Prop, forall l : seq _250280, (LEX' _564465 lt2' (@nil _250280) l) = False) /\ (forall h : _250280, forall lt2' : _250280 -> _250280 -> Prop, forall t : seq _250280, forall l : seq _250280, (LEX' _564465 lt2' (@cons _250280 h t) l) = (@COND Prop (l = (@nil _250280)) False (@COND Prop (lt2' h (@HD _250280 l)) ((@size _250280 t) = (@size _250280 (@TL _250280 l))) ((h = (@HD _250280 l)) /\ (LEX' _564465 lt2' t (@TL _250280 l))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof. by total_align => // ? ? ? [] * ; if_seq. Qed.

Inductive subterm : term -> term -> Prop :=
| subterm_refl : forall t, subterm t t
| subterm_rec : forall t t' n s, subterm t t' -> MEM t' s -> subterm t (Fn n s).

Lemma subterm_def : subterm = (fun a0 : term => fun a1 : term => forall subterm' : term -> term -> Prop, (forall a0' : term, forall a1' : term, ((a1' = a0') \/ (exists a : term, exists f : nat, exists args : seq term, (a1' = (Fn f args)) /\ ((subterm' a0' a) /\ (@MEM term a args)))) -> subterm' a0' a1') -> subterm' a0 a1).
Proof. ind_align. Qed.

Definition psubterm t t' := (subterm t t' /\ t <> t').

Lemma psubterm_def : psubterm = (fun _567009 : term => fun _567010 : term => (subterm _567009 _567010) /\ (~ (eq _567009 _567010))).
Proof. reflexivity. Qed.

Lemma allE : List.Forall = @all.
Proof.
  ext => A P s.
  - elim => // a {}s' /asboolP /= -> _ ; exact.
  - elim: s => [| a s IHs] //= /andP [/asboolP + /IHs].
    exact: List.Forall_cons.
Qed.

Lemma allE_gen A (P : A -> Prop) (s : seq A) :
 all P s = List.Forall P s :> Prop.
Proof. by move:allE => /[gen] ->. Qed.

Unset Elimination Schemes.
Inductive lpo : term -> term -> Prop :=
| lpo_free : forall n t, free_variables_term t n -> t <> V n -> lpo (V n) t
| lpo_psubterm1 : forall n (s : seq term) n' (s' : seq term) (t : term), MEM t s' -> lpo (Fn n s) t ->
      lpo (Fn n s) (Fn n' s')
| lpo_psubterm2 : forall n (s : seq term) n' (s' : seq term) (t : term), MEM t s' -> t = Fn n s ->
      lpo (Fn n s) (Fn n' s')
| lpo_Fn_smaller0 : forall n (s : seq term) n' (s' : seq term),
      n' > n \/ (n' = n /\ size s' > size s) ->
      List.Forall (fun t => lpo t (Fn n' s')) s -> lpo (Fn n s) (Fn n' s')
| lpo_LEX0 : forall n (s s' : seq term), List.Forall (fun t => lpo t (Fn n s')) s ->
      LEXi lpo s s' -> lpo (Fn n s) (Fn n s').
Set Elimination Schemes.

Lemma lpo_Fn_smaller : forall n (s : seq term) n' (s' : seq term),
      n' > n \/ (n' = n /\ size s' > size s) ->
      all (fun t => lpo t (Fn n' s')) s -> lpo (Fn n s) (Fn n' s').
Proof.
 move=> ???? ; rewrite allE_gen ; exact: lpo_Fn_smaller0.
Qed.

Lemma lpo_LEX : forall n (s s' : seq term), all (fun t => lpo t (Fn n s')) s ->
      LEX lpo s s' -> lpo (Fn n s) (Fn n s').
Proof.
  move=> ??? ; rewrite allE_gen LEXE ; exact: lpo_LEX0.
Qed.

Scheme lpo_ind0 := Minimality for lpo Sort Prop.

Fixpoint lpo_ind1 P H0 H1 H2
  (H3 : forall n (s : seq term) n' (s' : seq term), n' > n \/ (n' = n /\ size s' > size s) ->
    List.Forall (fun t : term => P t (Fn n' s')) s -> P (Fn n s) (Fn n' s'))
  (H4 : forall n (s s' : seq term), List.Forall (fun t : term => P t (Fn n s')) s -> LEXi lpo s s' ->
    LEXi P s s' -> P (Fn n s) (Fn n s'))
  t t' (H5 : lpo t t') : P t t' :=
  @lpo_ind0 P H0 H1 H2
    (fun n s n' s' H0' H1' => H3 n s n' s' H0' (ListDef.Forall_ind (List.Forall (fun t => P t (Fn n' s')))
      (List.Forall_nil _)
      (fun t0 s0 H00 _ H10 => List.Forall_cons _ (@lpo_ind1 P H0 H1 H2 H3 H4 _ _ H00) H10) H1'))
    (fun n s s' H0' H1' => H4 n s s' (ListDef.Forall_ind (List.Forall (fun t => P t (Fn n s')))
      (List.Forall_nil _)
      (fun t0 s0 H00 _ H10 => List.Forall_cons _ (@lpo_ind1 P H0 H1 H2 H3 H4 _ _ H00) H10) H0')
      H1'
      (@LEXi_ind _ _ (LEXi P)
        (fun t0 l0 t0' s0' H00 H10 => @LEX_R _ P t0 l0 t0' s0' 
          (@lpo_ind1 P H0 H1 H2 H3 H4 _ _ H00) H10)
        (fun t0 s0 s0' _ H00 => @LEX_eq _ P t0 s0 s0' H00) s s' H1')) t t' H5.

Lemma lpo_ind (P : term -> term -> Prop) :
       (forall (n : nat) (t : term), free_variables_term t n -> t <> V n -> P (V n) t) ->
       (forall (n : nat) (s : seq term) (n' : nat) (s' : seq term) (t : term),
        MEM t s' -> lpo (Fn n s) t -> P (Fn n s) t -> P (Fn n s) (Fn n' s')) ->
       (forall (n : nat) (s : seq term) (n' : nat) (s' : seq term) (t : term),
        MEM t s' -> t = Fn n s -> P (Fn n s) (Fn n' s')) ->
       (forall (n : nat) (s : seq term) (n' : nat) (s' : seq term),
        n < n' \/ n' = n /\ size s < size s' ->
        all (P^~ (Fn n' s')) s -> P (Fn n s) (Fn n' s')) ->
       (forall (n : nat) (s s' : seq term),
        all (P^~ (Fn n s')) s -> LEX lpo s s' -> LEX P s s' -> P (Fn n s) (Fn n s')) ->
       forall t t' : term, lpo t t' -> P t t'.
Proof. move: lpo_ind1 ; rewrite LEXE allE ; exact. Qed.

Register Scheme lpo_ind as ind_nodep for lpo.

Lemma lpo_def : lpo = (fun a0 : term => fun a1 : term => forall lt2' : term -> term -> Prop, (forall a0' : term, forall a1' : term, ((exists x : nat, (a0' = (V x)) /\ ((@IN nat x (free_variables_term a1')) /\ (~ (a1' = (V x))))) \/ ((exists fs : nat, exists sargs : seq term, exists ft : nat, exists targs : seq term, exists si : term, (a0' = (Fn ft targs)) /\ ((a1' = (Fn fs sargs)) /\ ((@MEM term si sargs) /\ ((lt2' (Fn ft targs) si) \/ (si = (Fn ft targs)))))) \/ ((exists fs : nat, exists ft : nat, exists sargs : seq term, exists targs : seq term, (a0' = (Fn ft targs)) /\ ((a1' = (Fn fs sargs)) /\ (((gtn fs ft) \/ ((fs = ft) /\ (gtn (@size term sargs) (@size term targs)))) /\ (@ALL term (fun ti : term => lt2' ti (Fn fs sargs)) targs)))) \/ (exists f : nat, exists sargs : seq term, exists targs : seq term, (a0' = (Fn f targs)) /\ ((a1' = (Fn f sargs)) /\ ((@ALL term (fun ti : term => lt2' ti (Fn f sargs)) targs) /\ (@LEX term lt2' targs sargs))))))) -> lt2' a0' a1') -> lt2' a0 a1).
Proof.
  rewrite/ALL/gtn ; ind_align.
  1,2 : by subst ; apply: lpo_Fn_smaller ; auto.
  exact: lpo_LEX.
Qed.