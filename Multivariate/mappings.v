From HB Require Import structures.
From Stdlib Require Import Reals.Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype finmap bigop finset monoid order ssralg.
From mathcomp Require Import ssrnum matrix sesquilinear interval ssrint boolp.
From mathcomp Require Import cardinality filter topology matrix_topology.
From mathcomp Require Import normedtype Rstruct_topology.
Import Order Order.TTheory GRing Num.Theory.
Require Export HOLLight.HOL.mappings.
From HOLLight Require Import morepointedtypes HOL.theorems.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(*****************************************************************************)
(* Library.Frag.frag (free Abelian group) *)
(*****************************************************************************)

Definition is_frag {A:Type'} (f:A -> int) := @finite_set A (@GSPEC A (fun GEN_PVAR_709 : A => exists x : A, @SETSPEC A GEN_PVAR_709 (~ ((f x) = (int_of_nat (NUMERAL O)))) x)).

Lemma is_frag0 (A:Type') : @is_frag A (fun=>0).
Proof.
  rewrite/is_frag/3=; have ->: (fun=>0%Z<>int_of_nat 0) = @set0 A ; last by [].
  by ext => x [].
Qed.

Definition frag A := subtype (is_frag0 A).

Definition mk_frag : forall {A : Type'}, (A -> int) -> frag A := fun A => mk (is_frag0 A).

Definition dest_frag : forall {A : Type'}, (frag A) -> A -> int := fun A => dest (is_frag0 A).

Lemma axiom_41 : forall {A : Type'} (a : frag A), (@mk_frag A (@dest_frag A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_42 : forall {A : Type'} (r : A -> int), ((fun f : A -> int => @finite_set A (@GSPEC A (fun GEN_PVAR_709 : A => exists x : A, @SETSPEC A GEN_PVAR_709 (~ ((f x) = (int_of_nat (NUMERAL O)))) x))) r) = ((@dest_frag A (@mk_frag A r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Library.grouptheory.group *)
(*****************************************************************************)

Definition Grp (A:Type') := prod (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))).
Definition Gcar {A:Type'} (G: Grp A) := fst G.
Definition G0 {A:Type'} (G:Grp A) := fst (snd G).
Definition Gop {A:Type'} (G:Grp A) := snd (snd (snd G)).
Definition Ginv {A:Type'} (G:Grp A) := fst (snd (snd G)).

Definition is_group {A:Type'} (r:Grp A) := IN (G0 r) (Gcar r)
/\ ((forall x, IN x (Gcar r) -> IN (Ginv r x) (Gcar r))
/\ ((forall x y, (IN x (Gcar r) /\ (IN y (Gcar r))) -> IN (Gop r x y) (Gcar r))
/\ ((forall x y z, (IN x (Gcar r) /\ (IN y (Gcar r) /\ IN z (Gcar r))) ->
Gop r x (Gop r y z) = Gop r (Gop r x y) z)
/\ ((forall x, IN x (Gcar r) -> (Gop r (G0 r) x = x) /\ (Gop r x (G0 r) = x))
/\ (forall x, IN x (Gcar r) -> (Gop r (Ginv r x) x = G0 r) /\ (Gop r x (Ginv r x) = G0 r)))))).

Class hol_Group (A : Type') := {
  gcar :> set A ;
  g0 : A ;
  g0_gcar : gcar g0 ;
  gop : A -> A -> A ;
  gop_gcar : forall x y, gcar x -> gcar y -> gcar (gop x y) ;
  ginv : A -> A ;
  ginv_gcar : forall x, gcar x -> gcar (ginv x) ;
  gop_assoc : forall x y z, gcar x -> gcar y -> gcar z -> gop x (gop y z) = gop (gop x y) z ;
  gop_0_l : forall x, gcar x -> gop g0 x = x ;
  gop_0_r : forall x, gcar x -> gop x g0 = x ;
  ginv_gop_l : forall x, gcar x -> gop (ginv x) x = g0 ;
  ginv_gop_r : forall x, gcar x -> gop x (ginv x) = g0 }.

Instance triv_group (A : Type') : hol_Group A.
Proof. 
  by exists [set point] point (fun _ _ => point) (fun=> point).
Defined.

HB.instance Definition _ (A : Type') := is_Type' (triv_group A).

Definition group_operations {A : Type'} (G : hol_Group A) : Grp A :=
  (gcar , (g0 , (ginv , gop))).

Definition group {A : Type'} := finv (@group_operations A).

Lemma axiom_43 : forall {A : Type'} (a : hol_Group A), (@group A (@group_operations A a)) = a.
Proof. _mk_dest_record. Qed.

Lemma axiom_44 : forall {A : Type'} (r : Grp A), is_group r = (group_operations (group r) = r).
Proof.
  _dest_mk_record by rewrite/3=.
  record_exists {| gcar := Gcar r ; g0 := G0 r ; ginv := Ginv r ; gop := Gop r |} ;
  move=>* ; match goal with Hyp : _ |- _ => by apply Hyp end.
Qed.

Lemma group_carrier_def {A : Type'} : (@gcar A) = (fun g : hol_Group A => @fst (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))) (@group_operations A g)).
Proof. by []. Qed.

Lemma group_id_def {A : Type'} : (@g0 A) = (fun g : hol_Group A => @fst A (prod (A -> A) (A -> A -> A)) (@snd (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))) (@group_operations A g))).
Proof. by []. Qed.

Lemma group_inv_def {A : Type'} : (@ginv A) = (fun g : hol_Group A => @fst (A -> A) (A -> A -> A) (@snd A (prod (A -> A) (A -> A -> A)) (@snd (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))) (@group_operations A g)))).
Proof. by []. Qed.

Lemma group_mul_def {A : Type'} : (@gop A) = (fun g : hol_Group A => @snd (A -> A) (A -> A -> A) (@snd A (prod (A -> A) (A -> A -> A)) (@snd (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))) (@group_operations A g)))).
Proof. by []. Qed.

(*****************************************************************************)
(* Library.Matroids.matroid *)
(*****************************************************************************)

Definition is_matroid {A:Type'} m := (forall s : A -> Prop, (@subset A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> @subset A (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s) (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((forall s : A -> Prop, (@subset A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> @subset A s (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) /\ ((forall s : A -> Prop, forall t : A -> Prop, ((@subset A s t) /\ (@subset A t (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m))) -> @subset A (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s) (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m t)) /\ ((forall s : A -> Prop, (@subset A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) = (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) /\ ((forall s : A -> Prop, forall x : A, ((@subset A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ (@IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s))) -> exists s' : A -> Prop, (@finite_set A s') /\ ((@subset A s' s) /\ (@IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s')))) /\ (forall s : A -> Prop, forall x : A, forall y : A, ((@subset A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((@IN A x (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((@IN A y (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@INSERT A x s))) /\ (~ (@IN A y (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)))))) -> @IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@INSERT A y s))))))).

Class Matroid (A : Type') := {
  mat_set :> set A ;
  mat_span : set A -> set A ;
  mat_span_mat_set : forall s, s `<=` mat_set -> mat_span s `<=` mat_set ;
  mat_span_subset : forall s, s `<=` mat_set -> s `<=` mat_span s ;
  mat_span_increasing : forall s s', s' `<=` mat_set -> s `<=` s' ->
    mat_span s `<=` mat_span s' ;
  mat_span_stationary : forall s, s `<=` mat_set ->
    mat_span (mat_span s) = mat_span s ;
  mat_span_finitary_gen : forall s x, s `<=` mat_set -> mat_span s x ->
    exists s', finite_set s' /\ s' `<=` s /\ mat_span s' x ;
  mat_span_setU1_sym : forall s x y, s `<=` mat_set -> mat_set x ->
    mat_span (x |` s) y -> ~ mat_span s y ->  mat_span (y |` s) x }.

Instance triv_matroid (A : Type') : Matroid A.
Proof.
  by exists set0 id ; firstorder.
Defined.

HB.instance Definition _ A := is_Type' (triv_matroid A).

Definition dest_matroid {A : Type'} (M : Matroid A) := (mat_set,mat_span).

Definition matroid {A : Type'} := finv (@dest_matroid A).

Lemma axiom_45 : forall {A : Type'} (a : Matroid A), (@matroid A (@dest_matroid A a)) = a.
Proof. _mk_dest_record. Qed.

Lemma axiom_46 : forall {A : Type'} (r : prod (A -> Prop) ((A -> Prop) -> A -> Prop)), (is_matroid r) = ((@dest_matroid A (@matroid A r)) = r).
Proof.
  _dest_mk_record by rewrite/3= with dest_matroid.
  record_exists {| mat_set := fst r ; mat_span := snd r |}.
Qed.

Lemma matroid_set_def {A : Type'} : (@mat_set A) = (fun m : Matroid A => @fst (A -> Prop) ((A -> Prop) -> A -> Prop) (@dest_matroid A m)).
Proof. by []. Qed.

Lemma matroid_span_def {A : Type'} : (@mat_span A) = (fun m : Matroid A => @snd (A -> Prop) ((A -> Prop) -> A -> Prop) (@dest_matroid A m)).
Proof. by []. Qed.

(*****************************************************************************)
(* topology from Multivariate/metric.ml *)
(*****************************************************************************)

Definition istopology {A : Type'} : ((A -> Prop) -> Prop) -> Prop :=
  fun U => (IN set0 U)
        /\ ((forall s t, ((IN s U) /\ (IN t U)) -> IN (setI s t) U)
           /\ (forall k, subset k U -> IN (UNIONS k) U)).

Class Topology (A : Type') := {
  open_in :> set A -> Prop ;
  open_set0 : open_in set0 ;
  open_setI : forall s s', open_in s -> open_in s' -> open_in (setI s s') ;
  open_UNIONS : forall S, S `<=` open_in ->
    open_in [set a | (exists s, S s /\ s a)] }.

Instance discrete_topology A : Topology A.
Proof.
  by exists [set: set A].
Defined.

HB.instance Definition _ A := is_Type' (discrete_topology A).

Definition topology {A} := finv (@open_in A).

Lemma axiom_47 : forall {A : Type'} (a : Topology A), (@topology A (@open_in A a)) = a.
Proof. _mk_dest_record. Qed.

Lemma axiom_48 : forall {A : Type'} (r : (A -> Prop) -> Prop), ((fun t : (A -> Prop) -> Prop => @istopology A t) r) = ((@open_in A (@topology A r)) = r).
Proof.
  _dest_mk_record by rewrite/3=. record_exists {| open_in := r |}.
  - by rewrite bigcupE in H1 ; and_arrow.
  - by rewrite bigcupE ; and_arrow.
Qed.

(*****************************************************************************)
(* Multivariate.Metric.net *)
(*****************************************************************************)

Definition is_net {A:Type'} (g: prod ((A -> Prop) -> Prop) (A -> Prop)) :=
  forall s t, ((IN s (fst g)) /\ (IN t (fst g))) -> IN (setI s t) (fst g).

Lemma is_net_def {A:Type'} g : is_net g = forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s (@fst ((A -> Prop) -> Prop) (A -> Prop) g)) /\ (@IN (A -> Prop) t (@fst ((A -> Prop) -> Prop) (A -> Prop) g))) -> @IN (A -> Prop) (@setI A s t) (@fst ((A -> Prop) -> Prop) (A -> Prop) g).
Proof. reflexivity. Qed.

Class net (A : Type') := {
  net_filter :> set A -> Prop ;
  net_limits : set A ;
  net_setI : forall s s', net_filter s ->
    net_filter s' -> net_filter (s `&` s') }.

Instance triv_net A : net A.
Proof.
  exists set0. exact set0. auto.
Defined.

HB.instance Definition _ A := is_Type' (triv_net A).

Definition dest_net {A} (n : net A) := (net_filter,net_limits).

Definition mk_net {A} := finv (@dest_net A).

Lemma axiom_49 : forall {A : Type'} (a : net A), (@mk_net A (@dest_net A a)) = a.
Proof. _mk_dest_record. Qed.

Lemma axiom_50 : forall {A : Type'} (r : prod ((A -> Prop) -> Prop) (A -> Prop)), is_net r = ((@dest_net A (@mk_net A r)) = r).
Proof.
  _dest_mk_record by rewrite/3= with dest_net.
  record_exists {| net_filter := fst r ; net_limits := snd r |}.
Qed.

Lemma netfilter_def {A : Type'} : (@net_filter A) = (fun _757793 : net A => @fst ((A -> Prop) -> Prop) (A -> Prop) (@dest_net A _757793)).
Proof. by []. Qed.

Lemma netlimits_def {A : Type'} : (@net_limits A) = (fun _757798 : net A => @snd ((A -> Prop) -> Prop) (A -> Prop) (@dest_net A _757798)).
Proof. by []. Qed.

(*****************************************************************************)
(* Multivariate.Metric.metric *)
(*****************************************************************************)

Definition MS (A:Type') := prod (A -> Prop) ((prod A A) -> R).

Definition Mcar {A:Type'} : MS A -> A -> Prop := fst.
Definition Mdist {A:Type'} : MS A -> prod A A -> R := snd.

Definition is_metric_space {A : Type'} : MS A -> Prop :=
  fun M => (forall x y, ((IN x (Mcar M)) /\ (IN y (Mcar M))) ->
                ler (R_of_nat (NUMERAL O)) (Mdist M (@pair A A x y)))
        /\ ((forall x y, ((IN x (Mcar M)) /\ (IN y (Mcar M))) ->
                   ((Mdist M (pair x y)) = (R_of_nat (NUMERAL O))) = (x = y))
           /\ ((forall x y, ((IN x (Mcar M)) /\ (IN y (Mcar M))) ->
                      (Mdist M (pair x y)) = (Mdist M (pair y x)))
              /\ (forall x y z, ((IN x (Mcar M)) /\ ((IN y (Mcar M)) /\ (IN z (Mcar M)))) ->
                          ler (Mdist M (pair x z)) (addr (Mdist M (pair x y)) (Mdist M (pair y z)))))).

Open Scope ring_scope.

Class Metric (A : Type') := {
  mcar :> set A ;
  mdist : A -> A -> R ;
  mdist_pos : forall x y, mcar x -> mcar y -> 0 <= mdist x y ;
  mdist_sym : forall x y, mcar x -> mcar y -> mdist x y = mdist y x ;
  mdist_refl : forall x y, mcar x -> mcar y -> mdist x y = 0 <-> x = y ;
  mdist_tri : forall z x y, mcar x -> mcar y -> mcar z ->
    mdist x y <= mdist x z + mdist z y }.

Instance triv_metric A : Metric A.
Proof.
  by exists set0 (fun _ _ => 0).
Defined.

HB.instance Definition _ A := is_Type' (triv_metric A).

Definition mdist_pair (A : Type') M := uncurry (@mdist A M).

Definition dest_metric {A} (M : Metric A) :=
  (mcar, mdist_pair M).

Definition metric {A} := finv (@dest_metric A).

Lemma axiom_51 : forall {A : Type'} (a : Metric A), (@metric A (@dest_metric A a)) = a.
Proof.
  finv_inv_l => /= instance1 instance2 eq.
  destruct instance1,instance2.
  rewrite/dest_metric/mdist_pair in eq. simpl in eq.
  revert_keep eq. case: eq => -> /[gen] mdisteq0.
  have -> : mdist0 = mdist1 by ext=> x y ; exact: (mdisteq0 (x,y)).
  clear => * ; f_equal ; exact: Prop_irrelevance.
Qed.

Lemma axiom_52 : forall {A : Type'} (r : prod (A -> Prop) ((prod A A) -> R)), ((fun m : prod (A -> Prop) ((prod A A) -> R) => @is_metric_space A m) r) = ((@dest_metric A (@metric A r)) = r).
Proof.
  _dest_mk_record by rewrite/3= with dest_metric.
  record_exists {| mcar := Mcar r ; mdist x y := Mdist r (x,y) |}.
  - by move=>* ; rewrite H0.
  - by destruct r ; unfold dest_metric ; f_equal => /` -[].
  - by move=> * /` ? ; full_destruct ; apply mdist_refl0.
Qed.

Lemma mspace_def {A : Type'} : (@mcar A) = (fun _759924 : Metric A => @fst (A -> Prop) ((prod A A) -> R) (@dest_metric A _759924)).
Proof. by []. Qed.

Lemma mdist_def {A : Type'} : (@mdist_pair A) = (fun _759929 : Metric A => @snd (A -> Prop) ((prod A A) -> R) (@dest_metric A _759929)).
Proof. by []. Qed.

(*****************************************************************************)
(* Multivariate.Clifford.multivector *)
(*****************************************************************************)

Definition is_multivector (A:Type') (s: set nat) := subset s (dotdot 1 (dimindex (@setT A))).

Lemma is_multivector0 (A:Type') : is_multivector A (fun n => n = 1).
Proof.
  move=> _ -> ; apply/andP ; split ; [ by [] | exact:dimindex_gt0 ].
Qed.

Definition Multivector (A:Type') := subtype (is_multivector0 A).

Definition mk_multivector : forall {N' : Type'}, (nat -> Prop) -> Multivector N' := fun A => mk (is_multivector0 A). 

Definition dest_multivector : forall {N' : Type'}, (Multivector N') -> nat -> Prop := fun A => dest (is_multivector0 A).

Lemma axiom_53 : forall {N' : Type'} (a : Multivector N'), (@mk_multivector N' (@dest_multivector N' a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_54 : forall {N' : Type'} (r : nat -> Prop), ((fun s : nat -> Prop => @subset nat s (dotdot (NUMERAL (BIT1 O)) (@dimindex N' (@setT N')))) r) = ((@dest_multivector N' (@mk_multivector N' r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Alignments towards convergence of sums *)
(*****************************************************************************)

Definition lambda {A B : Type'} (s : nat -> A) : cart A B :=
  \row_i s i.+1.

Lemma rowE A n (v v' : 'rV[A]_n) : (forall k (coordk : (k < n)%N),
  v ord0 (Ordinal coordk) = v' ord0 (Ordinal coordk)) -> v = v'.
Proof.
  by move=> ? ; apply/rowP => -[].
Qed.

Notation "[ 'rowE' ]" := ltac:(apply: rowE).

Lemma lambda_def {A B : Type'} : (@lambda A B) = (fun _94688 : nat -> A => @ε (cart A B) (fun f : cart A B => forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94688 i))).
Proof.
  ext=> s ; rewrite/leqn/2= ; align_ε.
  - by case => [|n] [// _ coordn1] ; rewrite/dollar coordE mxE.
  - move=> v rocq_val hol_val /[rowE] i coordi ; rewrite -2!coordE (pred_Sn i).
    by rewrite -/(dollar v i.+1) hol_val -?rocq_val.
Qed.

Definition from (n : nat) : set nat := `[n,+oo[.

Lemma from_def : from = (fun _273385 : nat => @GSPEC nat (fun GEN_PVAR_641 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_641 (leqn _273385 m) m)).
Proof.
  by funext=> n /3= k ; rewrite/from/leqn/= in_itv /= Bool.andb_true_r.
Qed.

Definition eventually (A : Type') (s : set A) (n : net A) :=
  (n : set_system A) = set0 \/ exists s0, n s0 /\ (s0 `\` net_limits) `<=` s.

Lemma eventually_def {A : Type'} : (@eventually A) = (fun _757911 : A -> Prop => fun _757912 : net A => ((@net_filter A _757912) = (@set0 (A -> Prop))) \/ (exists u : A -> Prop, (@IN (A -> Prop) u (@net_filter A _757912)) /\ (forall x : A, (@IN A x (@setD A u (@net_limits A _757912))) -> _757911 x))).
Proof. by funext=> * /3=. Qed.

Lemma from_setI_closed : forall s s' : set nat,
  range from s -> range from s' -> range from (s `&` s').
Proof.
  move=> _ _ [n _ <-] [n' _ <-] ; exists (maxn n n') => // ; symmetry.
  rewrite/from/maxn ; case ltnP=> ? ; [apply: setIidr | apply: setIidl].
  1,2: move=> ? ; rewrite/= 2!in_itv /= 2!Bool.andb_true_r. 
  - exact/le_trans/ltW.
  - exact: le_trans.
Qed.

Definition sequentially : net nat := {|
  net_limits := set0 ;
  net_setI := from_setI_closed |}.

Lemma sequentially_def : sequentially = (@mk_net nat (@pair ((nat -> Prop) -> Prop) (nat -> Prop) (@GSPEC (nat -> Prop) (fun GEN_PVAR_1595 : nat -> Prop => exists n : nat, @SETSPEC (nat -> Prop) GEN_PVAR_1595 (@IN nat n (@setT nat)) (from n))) (@set0 nat))).
Proof. rewrite/3= ; constr_align (@axiom_49 nat). Qed.

(* Useful for the alignment of vector operations *)
Lemma map2_lambda (A B C n : Type') (f : A -> B -> C)
  (v : cart A n) (v' : cart B n) :
  map2_mx f v v' = lambda (fun k => f (dollar v k) (dollar v' k)).
Proof.
  by move/[rowE] => * ; rewrite/dollar 2!mxE -pred_Sn 2!coordE.
Qed.

Definition vector_sub n (v v' : cart R n) := v - v'.

Lemma vector_sub_def {N' : Type'} : (@vector_sub N') = (fun _1113090 : cart R N' => fun _1113091 : cart R N' => @lambda R N' (fun i : nat => subr (@dollar R N' _1113090 i) (@dollar R N' _1113091 i))).
Proof.
  ext=> * ; apply/matrixP ; rewrite/vector_sub/add/=/addmx map2_lambda /lambda.
  case=> i coordi [j coordj] ; rewrite/lambda/dollar 2!mxE -pred_Sn 3!coordE.
  by rewrite/opp/=/oppmx/map_mx mxE.
Qed.

Definition row_dot (R : fieldType) n : 'rV[R]_n -> 'rV[R]_n -> R :=
  form idfun 1%R.

Lemma row_dotE (R : fieldType) n (v v' : 'rV[R]_n) :
  row_dot v v' = \sum_i v ord0 i * v' ord0 i.
Proof.
  rewrite/row_dot/form mulmx1 /mulmx mxE map_mx_id // ; f_equal => /= /` i.
  by f_equal ; rewrite mxE.
Qed.

Definition dot (n : Type') (v v': cart R n) : R := row_dot v v'.

(* Not sure what's supposed to be best to define it hence belast_rowE *)
Definition belast_row A n (v : 'rV[A]_n.+1) : 'rV[A]_n := col' (Ordinal (leqnn _)) v.

Lemma belast_rowE A n (v : 'rV[A]_n.+1) :
  belast_row v = \row_(i < n) (v ord0 (widen_ord (leqnSn _) i)).
Proof.
  apply/rowP => -[i coordi] ; rewrite 2!mxE ; f_equal.
  rewrite/lift/widen_ord ; apply: val_inj.
  by rewrite/bump/= -{3}(add0n i) ; f_equal ; move: coordi ; case leqP.
Qed.

Lemma hol_sum_condE n (s : set nat) (f : nat -> R) :
  sum (s `&` dotdot 1 n) f = \sum_(i < n | s i.+1) f i.+1.
Proof.
  elim: n => [|n IHn].
  - rewrite/setI big_ord0 ; apply: thm_SUM_EQ_0 => /3= /= n [_].
    by rewrite leqn0=> /andP [/[swap] /eqP ->].
  - rewrite thm_NUMSEG_REC // setIC thm_INSERT_INTER=> /c` [sn | nsn].
    + have [_ ->] := @thm_SUM_CLAUSES nat nat.
      2: { apply: finite_setIl ; exact: thm_FINITE_NUMSEG. }
      if_triv by rewrite/3=/setI/= ltnn => -[].
      rewrite big_mkcond big_ord_recr -big_mkcond /= addrC setIC IHn.
      by move:sn=> /3= ? /1=.
    + rewrite big_mkcond big_ord_recr -big_mkcond /= setIC IHn.
      by move: nsn => /3= ? /1= ; rewrite addr0.
Qed.

Lemma hol_sum_ordE n (f : nat -> R) : sum (dotdot 1 n) f = \sum_(i < n) f i.+1.
Proof.
  by rewrite -(setTI (dotdot 1 n)) hol_sum_condE /= asboolT.
Qed.

Lemma hol_sum_natE n m (f : nat -> R) :
  sum (dotdot n m) f = \sum_(n <= i < m.+1) f i.
Proof.
  elim: m n f => [|m IHm] n f.
  - case:n => [|n] ; first by rewrite thm_SUM_SING_NUMSEG big_nat1_id addr0.
    by rewrite big_geq ?thm_SUM_TRIV_NUMSEG.
  - have [_ ->] := thm_SUM_CLAUSES_NUMSEG f => /c` ; rewrite/leqn.
    + by move=> ? ; rewrite big_nat_recr ?IHm.
    + rewrite thm_NOT_LE=> ltmn ; rewrite big_geq // thm_SUM_TRIV_NUMSEG //.
      by apply: (leq_trans _ ltmn) ; rewrite ltnS leqnSn.
Qed.

Lemma hol_sum_nat_condE n m (s : set nat) (f : nat -> R) :
  sum (s `&` dotdot n m) f = \sum_(n <= i < m.+1 | s i) f i.
Proof.
  by rewrite big_mkcond/= -hol_sum_natE -thm_SUM_RESTRICT_SET /3= setIC.
Qed.

Lemma dot_def {N' : Type'} : (@dot N') = (fun _1113124 : cart R N' => fun _1113125 : cart R N' => @sum nat (dotdot (NUMERAL (BIT1 O)) (@dimindex N' (@setT N'))) (fun i : nat => mulr (@dollar R N' _1113124 i) (@dollar R N' _1113125 i))).
Proof.
  ext=> v v' ; rewrite/dot row_dotE hol_sum_ordE ; f_equal=> /= /` -[i coordi].
  by f_equal ; rewrite/dollar 2?coordE.
Qed.

Definition row_norm (R : rcfType) n (v : 'rV[R]_n) : R := Num.sqrt (row_dot v v).

Definition vector_norm (n : Type') (v : cart R n) : R := @row_norm R _ v.

Lemma row_square_ge0 (R : realFieldType) n (v : 'rV[R]_n) : 0 <= row_dot v v.
Proof.
  rewrite row_dotE ; apply: Num.Theory.sumr_ge0 => /= i _.
  exact: Num.Theory.sqr_ge0.
Qed.

Lemma vector_norm_def {_586104 : Type'} : (@vector_norm _586104) = (fun _1113880 : cart R _586104 => hol_sqrt (@dot _586104 _1113880 _1113880)).
Proof.
  by ext=> v ; rewrite/vector_norm/row_norm/hol_sqrt/dot row_square_ge0.
Qed.

Definition row_distance (R : rcfType) n (v v' : 'rV[R]_n) := row_norm (v-v').

Definition distance n : prod (cart R n) (cart R n) -> R :=
  uncurry (@row_distance R _).

Lemma distance_def {_586129 : Type'} : (@distance _586129) = (fun _1113885 : prod (cart R _586129) (cart R _586129) => @vector_norm _586129 (@vector_sub _586129 (@fst (cart R _586129) (cart R _586129) _1113885) (@snd (cart R _586129) (cart R _586129) _1113885))).
Proof. by ext ; case. Qed.

Definition row_sum (A : Type') n (s : set A) (f : A -> 'rV[R]_n) : 'rV_n :=
  \row_i sum s (fun x => (f x) ord0 i).

Definition vsum (A n : Type') : (A -> Prop) -> (A -> cart R n) -> cart R n :=
  row_sum (n := _).

Lemma vsum_def {A N' : Type'} : (@vsum A N') = (fun s : A -> Prop => fun f : A -> cart R N' => @lambda R N' (fun i : nat => @sum A s (fun x : A => @dollar R N' (f x) i))).
Proof.
  rewrite/vsum/row_sum/lambda/dollar => /` * /= ; f_equal => /` ? [] *.
  by f_equal => /` * ; rewrite coordE.
Qed.

Definition FImp (n A : Type') (f : A -> cart R n) l (n : net A) :=
  (forall e : R, 0 < e -> eventually (fun x => row_distance (f x) l < e) n).

Lemma FImp_def {_708096 _708101 : Type'} : (@FImp _708096 _708101) = (fun _1218977 : _708101 -> cart R _708096 => fun _1218978 : cart R _708096 => fun _1218979 : net _708101 => forall e : R, (ltr (R_of_nat (NUMERAL O)) e) -> @eventually _708101 (fun x : _708101 => ltr (@distance _708096 (@pair (cart R _708096) (cart R _708096) (_1218977 x) _1218978)) e) _1218979).
Proof. by []. Qed.

Lemma row_sum_condE n k (s : set nat) (f : nat -> 'rV[R]_n) :
  row_sum (s `&` dotdot 0 k) f = \sum_(i < k.+1 | s i) f i.
Proof.
  apply/rowP => -[i coordi] ; rewrite/row_sum summxE mxE hol_sum_nat_condE.
  by rewrite big_mkord ord1.
Qed.

Lemma row_square0 R n : @row_dot R n 0 0 = 0.
Proof.
  by rewrite row_dotE big1 // => * ; rewrite mxE mulr0.
Qed.

Definition sums n (u : nat -> cart R n) (l : cart R n) (s : set nat) :=
  \sum_(i < n.+1 | s i) u i @[n --> \oo] --> l.

Lemma max_square (R : realDomainType) (x y : R) :
  max (x ^+ 2) (y ^+ 2) = max `|x| `|y| ^+ 2.
Proof.
  rewrite/exp/iterop/= maxr_pMr ; last by case (ltP `|x|).
  rewrite -2![_ * _]/(_^+ 2) -(ger0_norm (sqr_ge0 x)) -(ger0_norm (sqr_ge0 y)).
  rewrite 2!normrX/exp/iterop/= ; case (ltP `|x|)=>[ltxy|gexy] ; rewrite/max.
  - rewrite ltr_pM2l ?ltr_pM ?ltxy // ; exact: (le_lt_trans _ ltxy).
  - by rewrite 2!ltNge ler_pM ?ler_wpM2l.
Qed.

Lemma bigmax_square A (R : realDomainType) (r : seq A) (F : A -> R) :
  \big[Def.max/0]_(x <- r) F x ^+ 2 = (\big[Def.max/0]_(x <- r) `|F x|) ^+ 2.
Proof.
  elim:r=>[|a r IHr] ; first by rewrite/exp/= 2!big_nil mulr0.
  rewrite 2!big_cons IHr max_square ; do 2 f_equal.
  apply:ger0_norm ; exact: bigmax_ge_id.
Qed.

Lemma row_norm_le_mx_norm (R : rcfType) n (v : 'rV[R]_n) :
  row_norm v <= Num.sqrt n%:R * `|v|.
Proof.
  rewrite/row_norm -normr_id -sqrtr_sqr -sqrtrM ; last by [].
  rewrite ler_sqrt ; last (apply:mulr_ge0 ; [by [] | exact:mulr_ge0]).
  rewrite/Num.norm/= mx_normrE -bigmax_square row_dotE.
  match goal with |- is_true (_ <= _ * ?x) => set (maxv2 := x) end.
  apply: (le_trans (y:= \sum_(i < n) maxv2)).
  { apply: ler_sum=> /= i _ ; exact: (le_bigmax _ _ (ord0, i)). }
  rewrite sumr_const mulr_natl.
  match goal with |- is_true (?x <= ?y) => have -> // : x = y end.
  f_equal ; exact: card_ord.
Qed.

Lemma injectiveE A B (f : A -> B) : injective f ->
  forall x y, (f x = f y) = (x = y).
Proof. move=> injf * /` ; [exact: injf | by move=>->]. Qed.

Lemma lift0_surj n (k : 'I_n.+1) :
  k <> ord0 -> exists k0 : 'I_n, k = lift ord0 k0.
Proof.
  case:k=> -[? []|m /[dup]] ; [exact: val_inj | rewrite{1} ltnS => ltmn ? ?].
  by exists (Ordinal ltmn) ; apply: ord_inj ;  rewrite lift0.
Qed.

Lemma mx_norm_le_row_norm (R : rcfType) n (v : 'rV[R]_n) :
  `|v| <= row_norm v.
Proof.
  rewrite/row_norm -normr_id -sqrtr_sqr ler_sqrt ; last exact: row_square_ge0.
  rewrite/Num.norm/exp/iterop/= ; case (EM (mx_norm v == 0)).
  - by move/eqP/mx_norm_eq0 => -> ; rewrite mx_norm0 row_square0 mulr0.
  - move/negP/mx_norm_neq0 => -[[j i] ->] /= ; rewrite row_dotE {j}ord1.
    rewrite-[X in X <= _]/(_ ^+ 2) -normrX ger0_norm ; last exact: sqr_ge0.
    have ->: v ord0 i ^+ 2 = \sum_(k < n) (if k = i then v ord0 i ^+ 2 else 0).
    + elim: n v i => [|n IHn] v i.
      { by rewrite/exp/iterop/= thinmx0 big_ord0 mxE mul0r. }
      rewrite big_ord_recl /= ; if_intro.
      * move=> <-. rewrite big1 ?addr0 // => k.
        by have -> : `[< lift ord0 k = ord0 >] = false by rewrite asboolF.
      * rewrite sym add0r => /lift0_surj [{}i ->].
        rewrite-{1}(mxE Datatypes.tt (fun (i : 'I_1) j => v i (lift ord0 j))).
        by rewrite IHn mxE ; f_equal => /` ? ; rewrite (injectiveE lift_inj).
    + apply: ler_sum=> /= k _ /c` [->|?] ; [by [] | exact: sqr_ge0].
Qed.

Lemma sums_def {n0 : Type'} : (@sums n0) = (fun _1333473 : nat -> cart R n0 => fun _1333474 : cart R n0 => fun _1333475 : nat -> Prop => @FImp n0 nat (fun n : nat => @vsum nat n0 (@setI nat _1333475 (dotdot (NUMERAL O) n)) _1333473) _1333474 sequentially).
Proof.
  rewrite/sums/cart/vsum/FImp/row_distance; remember (dimindex [set: n0]) as n.
  case: n Heqn => []; first by have := dimindex_gt0 [set:n0] => /[swap] <-.
  rewrite/eventually=> {n0}n _ /` u l s.
  - move/cvgrPdist_le=> /= cvgul e pos_e ; right.
    have /[spec] [|[N _ incl]] := cvgul ((e / 2) / Num.sqrt n.+1%:R).
    { apply:divr_gt0 ; [exact:divr_gt0 | by rewrite sqrtr_gt0]. }
    exists [set n | leq N n] ; split.
    + by exists N => // ; rewrite from_def /3=.
    + rewrite setD0 ; apply: {incl}(subset_trans incl).
      move=> k nearl ; rewrite row_sum_condE.
      apply: (le_lt_trans (row_norm_le_mx_norm _)).
      rewrite -(@mulrK _ (Num.sqrt n.+1%:R) _ e).
      * rewrite -mulrA mulrCA ltr_pM2l ; last by rewrite sqrtr_gt0.
        rewrite -opprB normrN ; apply: (le_lt_trans nearl).
        by rewrite mulrAC ltr_pdivrMr ?ltr_pMr ?ltr1n ?divr_gt0 ?sqrtr_gt0.
      * by rewrite unitfE sqrtr_eq0 -real_ltNge.
  - move=> cvgul ; apply/cvgrPdist_le => /= e pos_e.
    case (cvgul e pos_e) => [contra |[Ns [[N _ {Ns}<-]] /= incl]].
    + by contradict contra; apply/eqP; rewrite set0P; exist (from 0) 0.
    + exists N => // ; rewrite setD0 from_def /3= in incl.
      apply: {incl}(subset_trans incl) => k nearl.
      rewrite -opprB normrN -row_sum_condE /3=.
      apply: (le_trans (mx_norm_le_row_norm _)).
      by move:nearl ; case: ltgtP.
Qed.

