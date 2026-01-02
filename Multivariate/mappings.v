(*
From HB Require Import structures.
From Stdlib Require Import List Reals.Reals Lra Permutation.
From Equations Require Import Equations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun order ssralg ssrnum matrix.
From mathcomp Require Import interval ssrint intdiv archimedean finmap.
From mathcomp Require Import interval_inference all_classical topology.
From mathcomp Require Import normedtype reals Rstruct_topology derive realfun.
Import preorder.Order Order.TTheory GRing GRing.Theory Num.Theory Logic.
*)
From HB Require Import structures.
From Stdlib Require Import Reals.Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice.
From mathcomp Require Import fintype order ssralg ssrnum matrix interval.
From mathcomp Require Import ssrint cardinality Rstruct_topology.
From HOLLight.HOL Require Export mappings.

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

Class Group (A : Type') := {
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

Instance triv_group (A : Type') : Group A.
Proof. 
  by exists [set point] point (fun _ _ => point) (fun=> point).
Defined.

HB.instance Definition _ (A : Type') := is_Type' (triv_group A).

Definition group_operations {A : Type'} (G : Group A) : Grp A :=
  (gcar , (g0 , (ginv , gop))).

Definition group {A : Type'} := finv (@group_operations A).

Lemma axiom_43 : forall {A : Type'} (a : Group A), (@group A (@group_operations A a)) = a.
Proof. _mk_dest_record. Qed.

Lemma axiom_44 : forall {A : Type'} (r : Grp A), is_group r = (group_operations (group r) = r).
Proof.
  _dest_mk_record by rewrite/3=.
  record_exists {| gcar := Gcar r ; g0 := G0 r ; ginv := Ginv r ; gop := Gop r |} ;
  move=>* ; match goal with Hyp : _ |- _ => by apply Hyp end.
Qed.

Lemma group_carrier_def {A : Type'} : (@gcar A) = (fun g : Group A => @fst (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))) (@group_operations A g)).
Proof. by []. Qed.

Lemma group_id_def {A : Type'} : (@g0 A) = (fun g : Group A => @fst A (prod (A -> A) (A -> A -> A)) (@snd (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))) (@group_operations A g))).
Proof. by []. Qed.

Lemma group_inv_def {A : Type'} : (@ginv A) = (fun g : Group A => @fst (A -> A) (A -> A -> A) (@snd A (prod (A -> A) (A -> A -> A)) (@snd (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))) (@group_operations A g)))).
Proof. by []. Qed.

Lemma group_mul_def {A : Type'} : (@gop A) = (fun g : Group A => @snd (A -> A) (A -> A -> A) (@snd A (prod (A -> A) (A -> A -> A)) (@snd (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))) (@group_operations A g)))).
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

Print UNIONS.
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
  - move=> S ; have -> : [set a | (exists s : set A, S s /\ s a)] =
      [set a | (exists s : set A, s \in S /\ a \in s)] ; last by and_arrow.
    by f_equal => /` a [s Hs] ; exists s ; move:Hs ; rewrite 2!in_setE.
  - move=> S ; have <- : [set a | (exists s : set A, S s /\ s a)] =
      [set a | (exists s : set A, s \in S /\ a \in s)] ; last by and_arrow.
    by f_equal => /` a [s Hs] ; exists s ; move:Hs ; rewrite 2!in_setE.
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

Definition dest_metric {A} (M : Metric A) :=
  (mcar, fun (c : A * A) => let (x,y) := c in mdist x y).

Definition metric {A} := finv (@dest_metric A).

Lemma axiom_51 : forall {A : Type'} (a : Metric A), (@metric A (@dest_metric A a)) = a.
Proof.
  finv_inv_l => /= instance1 instance2 eq.
  destruct instance1,instance2.
  unfold dest_metric in eq. simpl in eq.
  revert_keep eq. case: eq => -> /[gen] mdisteq0.
  have -> : mdist0 = mdist1 by ext=> x y ; exact: (mdisteq0 (x,y)).
  clearall => * ; f_equal ; exact: proof_irrelevance.
Qed.

Lemma axiom_52 : forall {A : Type'} (r : prod (A -> Prop) ((prod A A) -> R)), ((fun m : prod (A -> Prop) ((prod A A) -> R) => @is_metric_space A m) r) = ((@dest_metric A (@metric A r)) = r).
Proof.
  _dest_mk_record by rewrite/3= with dest_metric.
  record_exists {| mcar := Mcar r ; mdist x y := Mdist r (x,y) |}.
  - by move=>* ; rewrite H0.
  - by destruct r ; unfold dest_metric ; f_equal => /` -[].
  - by move=> * /` ? ; full_destruct ; apply mdist_refl0.
Qed.

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

Definition count_vector (n : nat) := \matrix_(_ < 1, j < n) j.+1.

Definition lambda {A B : Type'} (s : nat -> A) : cart A B :=
  map_mx s (count_vector _).

Lemma lambda_def {A B : Type'} : (@lambda A B) = (fun _94688 : nat -> A => @ε (cart A B) (fun f : cart A B => forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94688 i))).
Proof.
  ext=> s ; rewrite/leqn/2= ; align_ε.
  - by case => [|n] [// _ coordn1] ; rewrite/dollar coordE 2!mxE.
  - move=> v rocq_val hol_val; apply/matrixP => i [j coordj]; rewrite {i}ord1.
    by rewrite -2!coordE (pred_Sn j) -/(dollar v j.+1) hol_val -?rocq_val.
Qed.

Definition from (n : nat) : set nat := `[n,+oo[.

Lemma from_def : from = (fun _273385 : nat => @GSPEC nat (fun GEN_PVAR_641 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_641 (leqn _273385 m) m)).
Proof.
  by funext=> n /3= k ; rewrite/from/leqn/= in_itv /= Bool.andb_true_r.
Qed.

Locate eventually. Print filter.eventually.
Definition eventually {A : Type'} : (A -> Prop) -> (net A) -> Prop := fun _757911 : A -> Prop => fun _757912 : net A => ((@net_filter A _757912) = (@set0 (A -> Prop))) \/ (exists u : A -> Prop, (@IN (A -> Prop) u (@net_filter A _757912)) /\ (forall x : A, (@IN A x (@setD A u (@net_limits A _757912))) -> _757911 x)).
Lemma eventually_def {A : Type'} : (@eventually A) = (fun _757911 : A -> Prop => fun _757912 : net A => ((@net_filter A _757912) = (@set0 (A -> Prop))) \/ (exists u : A -> Prop, (@IN (A -> Prop) u (@net_filter A _757912)) /\ (forall x : A, (@IN A x (@setD A u (@net_limits A _757912))) -> _757911 x))).
Proof. funext=> s n.  Qed.



























