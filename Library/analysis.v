From Stdlib Require Import Reals.Reals.
From Equations Require Import Equations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice.
From mathcomp Require Import order ssralg interval_inference ssrnum boolp.
From mathcomp Require Import classical_sets reals topology.
From mathcomp Require Import pseudometric_normed_Zmodule normed_module derive.
From mathcomp Require Import realfun Rstruct_topology.
Import preorder.Order Order.TTheory Num.Theory GRing.Theory.
Require Export HOLLight.HOL.mappings.
From HB Require Import structures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(*****************************************************************************)
(* Topologies *)
(*****************************************************************************)

(* HOL Light redefines some minimal set theory, for some reason. *)

Lemma re_Union_def {A : Type'} : (@UNIONS A) = (fun _114591 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114591 s) /\ (s x)).
Proof. by rewrite UNIONS_def => /f` * /3=. Qed.

Lemma re_union_def {A : Type'} : (@setU A) = (fun _114510 : A -> Prop => fun _114511 : A -> Prop => fun x : A => (_114510 x) \/ (_114511 x)).
Proof. exact (REFL (@setU A)). Qed.

Lemma re_intersect_def {A : Type'} : (@setI A) = (fun _114522 : A -> Prop => fun _114523 : A -> Prop => fun x : A => (_114522 x) /\ (_114523 x)).
Proof. exact (REFL (@setI A)). Qed.

Lemma re_null_def {A : Type'} : (@set0 A) = (fun x : A => False).
Proof. exact (REFL (@set0 A)). Qed.

Lemma re_universe_def {A : Type'} : (@setT A) = (fun x : A => True).
Proof. exact (REFL (@setT A)). Qed.

Lemma re_subset_def {A : Type'} : (@subset A) = (fun _114534 : A -> Prop => fun _114535 : A -> Prop => forall x : A, (_114534 x) -> _114535 x).
Proof. exact (REFL (@subset A)). Qed.

Lemma re_compl_def {A : Type'} : (@setC A) = (fun _114546 : A -> Prop => fun x : A => ~ (_114546 x)).
Proof. exact (REFL (@setC A)). Qed.

Definition istopology {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _114555 : (A -> Prop) -> Prop => (_114555 (@set0 A)) /\ ((_114555 (@setT A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114555 a) /\ (_114555 b)) -> _114555 (@setI A a b)) /\ (forall P : (A -> Prop) -> Prop, (@subset (A -> Prop) P _114555) -> _114555 (@UNIONS A P)))).
Lemma istopology_def {A : Type'} : (@istopology A) = (fun _114555 : (A -> Prop) -> Prop => (_114555 (@set0 A)) /\ ((_114555 (@setT A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114555 a) /\ (_114555 b)) -> _114555 (@setI A a b)) /\ (forall P : (A -> Prop) -> Prop, (@subset (A -> Prop) P _114555) -> _114555 (@UNIONS A P))))).
Proof. exact (REFL (@istopology A)). Qed.

Record Topology (A : Type') := {
  opens : set (set A) ;
  opens_empty : opens set0;
  opens_full : opens setT;
  opens_I : forall s s', opens s -> opens s' -> opens (s `&` s');
  opens_U : forall S, S `<=` opens -> opens (\bigcup_(s in S) s) }.

Definition discrete_Topology A : Topology A.
Proof.
  by exists setT.
Defined.

HB.instance Definition _ A := is_Type' (discrete_Topology A).

Definition topology {A : Type'} : ((A -> Prop) -> Prop) -> Topology A :=
  finv (@opens A).

Lemma _mk_dest_Topology : forall {A : Type'} (a : Topology A), (@topology A (@opens A a)) = a.
Proof.
  _mk_dest_record.
Qed.

Lemma _dest_mk_Topology : forall {A : Type'} (r : (A -> Prop) -> Prop), ((fun t : (A -> Prop) -> Prop => @istopology A t) r) = ((@opens A (@topology A r)) = r).
Proof.
  _dest_mk_record. record_exists {| opens := r |}.
Qed.

Definition toTopology (T : ptopologicalType) : Topology T.
Proof.
  exists open.
  - exact open0.
  - exact openT.
  - exact openI.
  - move=> S Sopen. by apply bigcup_open.
Defined.

Definition neigh {A : Type'} : (Topology A) -> (prod (A -> Prop) A) -> Prop := fun T : Topology A => fun c : prod (A -> Prop) A => exists P : A -> Prop, (@opens A T P) /\ ((@subset A P (@fst (A -> Prop) A c)) /\ (P (@snd (A -> Prop) A c))).
Lemma neigh_def {A : Type'} : (@neigh A) = (fun T : Topology A => fun c : prod (A -> Prop) A => exists P : A -> Prop, (@opens A T P) /\ ((@subset A P (@fst (A -> Prop) A c)) /\ (P (@snd (A -> Prop) A c)))).
Proof. exact (REFL (@neigh A)). Qed.

Lemma neigh_align (T : ptopologicalType) : forall x s, nbhs x s = neigh (toTopology T) (s,x).
Proof.
  move=> x s ; rewrite nbhsE/neigh/open_nbhs mksetE exists2E.
  ext => [[s' [[open_s' s'_x] s'_s]] | [s' [open_s' [s'_x s'_s]]]] ; exists s' ; repeat split => //.
Qed.

Definition tends {A B : Type'} : (B -> A) -> A -> (prod (Topology A) (B -> B -> Prop)) -> Prop :=
  fun f : B -> A => fun l : A => fun c : prod (Topology A) (B -> B -> Prop) =>
  let T := fst c in let R := snd c in
   forall N' : A -> Prop, neigh T (N',l) -> exists n : B, R n n /\ forall m : B, R m n -> N' (f m).
Lemma tends_def {A B : Type'} : (@tends A B) = (fun f : B -> A => fun l : A => fun c : prod (Topology A) (B -> B -> Prop) => forall N' : A -> Prop, (@neigh A (@fst (Topology A) (B -> B -> Prop) c) (@pair (A -> Prop) A N' l)) -> exists n : B, (@snd (Topology A) (B -> B -> Prop) c n n) /\ (forall m : B, (@snd (Topology A) (B -> B -> Prop) c m n) -> N' (f m))).
Proof. exact (REFL (@tends A B)). Qed.

(*****************************************************************************)
(* Metric spaces *)
(*****************************************************************************)
(* Difference with Rocq : Base is an argument instead of a projection *)

Unset Implicit Arguments.
Open Scope ring_scope.
Definition discrete_metric A (c : A * A) : R := if (fst c=snd c) then 0 else 1.

Lemma discr_pos A : forall x y : A, discrete_metric A (x,y) >= 0.
Proof. by rewrite/discrete_metric => * /c`. Qed.

Lemma discr_sym A : forall x y : A, discrete_metric A (x,y) = discrete_metric A (y,x).
Proof.
  by rewrite/discrete_metric/= => * /c` [-> | +] /c` // => ->.
Qed.

Lemma discr_refl A : forall x y, discrete_metric A (x,y) = 0 <-> x = y.
Proof.
  rewrite/discrete_metric => * /c` //= ; split=> contra ; contradict contra.
  - by rewrite eqP** oner_eq0.
  - by [].
Qed.

Lemma discr_tri A : forall x y z,
  discrete_metric A (x,y) <= discrete_metric A (x,z) + discrete_metric A (z,y).
Proof.
  rewrite/discrete_metric => * /c`+/c`+/c` ;
    rewrite /= ?addr0 ?add0r // -?[1+1]/(2%:R).
  - by move=> -> ->.
  - by rewrite ler1n.
Qed.

Set Implicit Arguments.

Record Metric (A : Type) := { mdist : prod A A -> R;
    mdist_pos : forall x y : A, mdist (x,y) >= 0;
    mdist_sym : forall x y : A, mdist (x,y) = mdist (y,x);
    mdist_refl : forall x y : A, mdist (x,y) = 0 <-> x = y;
    mdist_tri : forall x y z : A, mdist (x,y) <= mdist (x,z) + mdist (z,y) }.

Definition discrete (A : Type) :=
  {| mdist := discrete_metric A;
     mdist_pos := discr_pos A;
     mdist_sym := discr_sym A;
     mdist_refl := discr_refl A;
     mdist_tri := discr_tri A |}.

HB.instance Definition _ (A : Type) := is_Type' (discrete A).

Definition metric {A : Type'} := finv (@mdist A).

Lemma _mk_dest_Metric : forall {A : Type'} (a : Metric A), (@metric A (@mdist A a)) = a.
Proof.
  _mk_dest_record.
Qed.

Definition ismet {A : Type'} : (prod A A -> R) -> Prop := fun d =>
  (forall x y, d (x,y) = 0 <-> x = y) /\
  forall x y z : A, d (y,z) <= d (x,y) + d (x,z).

Lemma ismet_def {A : Type'} : (@ismet A) = (fun _114640 : (prod A A) -> R => (forall x : A, forall y : A, ((_114640 (@pair A A x y)) = (R_of_nat (NUMERAL 0))) = (x = y)) /\ (forall x : A, forall y : A, forall z : A, ler (_114640 (@pair A A y z)) (addr (_114640 (@pair A A x y)) (_114640 (@pair A A x z))))).
Proof.
  rewrite/ismet=> /1` d ; f_equal => /` H *.
  - apply propext ; exact:H.
  - by rewrite H.
Qed.

Ltac d0 d x := (* automatically replaces all bound instances of d (x,x) with 0 assuming
                  mdist_refl is in the context. *)
  replace (d (x,x)) with (0%mcR : R) in * ; [ idtac
  | lazymatch goal with H : forall x y, d (x,y) = 0%R <-> x=y |- 0%R = d (x,x) =>
      symmetry ; now apply H end].

Lemma _dest_mk_Metric : forall {A : Type'} (r : (prod A A) -> R), ((fun m : (prod A A) -> R => @ismet A m) r) = ((@mdist A (@metric A r)) = r).
Proof.
  _dest_mk_record.
  - have r_sym : forall x y, r (x,y) = r (y,x).
    { move=> x y ; have := H0 y x y ; have := H0 x y x ; d0 r y ; d0 r x.
      by rewrite 2!addr0 => sym1 sym2 ; apply le_anti ; rewrite sym1 sym2. }
    record_exists {| mdist := r |} => [x y | x y z].
    + by have:= H0 x y y ; d0 r y ; rewrite -mulr2n pmulrn_lge0.
    + by have := H0 z x y ; rewrite (r_sym z x) (r_sym z y).
  - by move=> x y ? ; rewrite (mdist_sym0 x y).
Qed.

Definition mtop {A : Type'} : (Metric A) -> Topology A := fun _114835 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (ltr (R_of_nat (NUMERAL O)) e) /\ (forall y : A, (ltr (@mdist A _114835 (@pair A A x y)) e) -> S' y)).
Lemma mtop_def {A : Type'} : (@mtop A) = (fun _114835 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (ltr (R_of_nat (NUMERAL O)) e) /\ (forall y : A, (ltr (@mdist A _114835 (@pair A A x y)) e) -> S' y))).
Proof. exact (REFL (@mtop A)). Qed.

Definition mr1 : Metric R := metric (fun c : R*R => let (x,y) := c in `|y-x|).
Lemma mr1_def : mr1 = (@metric R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @eq R (f (@pair R R x y)) (normr (subr y x))))).
Proof.
  rewrite/mr1 ; f_equal ; align_ε.
  - by [].
  - by move=> d _ d_def // ; funext => -[].
Qed.

Lemma _dest_mk_Metric_if : forall {A : Type'} (r : (prod A A) -> R), ismet r -> mdist (metric r) = r.
Proof.  by move=> A r ; rewrite _dest_mk_Metric. Qed.

Lemma ismet_rdist : ismet (fun c : R*R => let (x,y) := c in `|y-x|).
Proof.
  unfold ismet. split.
  - by move=> x y ; rewrite eqP** normr_eq0 subr_eq0 eqP** eq_sym.
  - move => x y z ; rewrite (distrC z x).
    by rewrite (le_trans _ (ler_normD _ _)) // [in leRHS]addrA subrK distrC.
Qed.

Lemma mdist_mr1_align : mdist mr1 = (fun c : R*R => let (x,y) := c in `|y-x|).
Proof. exact (_dest_mk_Metric_if ismet_rdist). Qed.

Lemma mtop_mr1_align : mtop mr1 = (toTopology R).
Proof.
  rewrite/mtop mdist_mr1_align -(_mk_dest_Topology (toTopology R)) ; f_equal => /=.
  ext => s /= open_s.
  - rewrite openE /= => r /open_s [e [pos_e sr]].
    by exists e => //= ; rewrite/ball_=> y /= rey ; apply sr ; rewrite distrC.
  - move=> r sr. have [/= e e0 rs] := @normed_module.open_subball R^o R^o _ _ open_s sr.
    exists (e/2)%mcR. have e20 : (0 < e / 2)%mcR by rewrite divr_gt0.
    split => // r' rr' ; apply: (rs _ _ e20) => /=.
    + by rewrite sub0r normrN gtr0_norm // gtr_pMr // invf_lt1 // ltr1n.
    + by rewrite distrC in rr'.
Qed.

Import numFieldNormedType.Exports.
Definition tends_num_real (x : nat -> R) (l : R) := x @ \oo --> l.

Lemma tends_num_real_def : tends_num_real = (fun _115068 : nat -> R => fun _115069 : R => @tends R nat _115068 _115069 (@pair (Topology R) (nat -> nat -> Prop) (@mtop R mr1) geqn)).
Proof.
  rewrite /tends_num_real mtop_mr1_align /tends /=.
  ext => x l.
  - move/(@cvgrPdist_le R R^o) => /= cvgxl U.
    rewrite -neigh_align => -[e /= e_pos incl_ball_U].
    have e20 : (0 < e/2)%mcR by rewrite divr_gt0.
    have:= (cvgxl (e/2)%R e20) => -[M _ incl_inter_ball] ; exists M.
    split ; [exact:leqnn | move=> n leqMn ; apply incl_ball_U].
    rewrite ball_normE ; apply: (closed_ball_subset e20).
    + by rewrite ltr_pdivrMr // ; rewrite ltr_pMr ; first rewrite ltr1n.
    + by rewrite (closed_ballE _ e20) ; apply (incl_inter_ball n).
  - move=> cvgxl ; apply/(@cvgrPdist_le R R^o) => /= e pos_e.
    pose B := closed_ball_ Num.Def.normr l e. have := cvgxl B.
    rewrite -neigh_align. have : nbhs l B.
    + apply/(@nbhs_closedballP _ R^o).
      exists (PosNum pos_e). by rewrite closed_ballE.
    + move => /[swap]/[apply]. case => M [_ MBx]. near=> n.
      by apply: MBx ; near: n ; exists M.
  Unshelve. by end_near.
Qed.

Definition tendsto {A : Type'} : (prod (Metric A) A) -> A -> A -> Prop := fun _114977 : prod (Metric A) A => fun _114978 : A => fun _114979 : A => (ltr (R_of_nat (NUMERAL O)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978))) /\ (ler (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114979))).
Lemma tendsto_def {A : Type'} : (@tendsto A) = (fun _114977 : prod (Metric A) A => fun _114978 : A => fun _114979 : A => (ltr (R_of_nat (NUMERAL O)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978))) /\ (ler (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114979)))).
Proof. exact (REFL (@tendsto A)). Qed.

(* represents lim(x (!=)--> x0) f(x) = l *)
Definition tends_real_real (f : R -> R) (l x0 : R) := f @ x0^' --> l.

Lemma tends_real_real_def : tends_real_real = (fun _115511 : R -> R => fun _115512 : R => fun _115513 : R => @tends R R _115511 _115512 (@pair (Topology R) (R -> R -> Prop) (@mtop R mr1) (@tendsto R (@pair (Metric R) R mr1 _115513)))).
Proof.
  rewrite/tends_real_real/tendsto/tends/ltr/ler/NUMERAL/R_of_nat.
  rewrite mtop_mr1_align /= mdist_mr1_align => /` f l x0.
  - move/(@cvgrPdist_le R R^o) => /= cvg_f_x0_l U.
    rewrite -neigh_align => -[/= e e_pos incl_ball_U].
    have pos_e2 : 0 < e/2 by rewrite divr_gt0.
    have:= cvg_f_x0_l (e/2) pos_e2 => -[/= d pos_d incl_inter_ball].
    exists (x0 + d/2). replace ((x0 + d/2) - x0) with (d/2).
    split. split ; last exact: le_refl.
    + by rewrite normr_gt0;apply lt0r_neq0;rewrite divr_gt0.
    + move=> x ; rewrite ?coqRE => -[neq_x_x0 ball_x0_d2_x].
      apply incl_ball_U ; rewrite ball_normE ; apply: (closed_ball_subset pos_e2).
      * by rewrite ltr_pdivrMr // ; rewrite ltr_pMr ; first rewrite ltr1n.
      * rewrite (closed_ballE _ pos_e2) ; apply incl_inter_ball.
        { rewrite/= distrC ; apply: (le_lt_trans ball_x0_d2_x).
          by rewrite gtr0_norm ?divr_gt0 // ltr_pdivrMr // ltr_pMr // ltr1n. }
        { rewrite -negP**-eqP** => eq_x_x0. move: neq_x_x0.
          replace `|x - x0|%mcR with (@Algebra.zero R^o).
          by rewrite lt_irreflexive. rewrite -(@normr0 _ R^o).
          f_equal. by rewrite eq_x_x0 -RminusE Rminus_diag. }
    + by rewrite addrAC subrr add0r.
  - move=> cvgf_x0_l ; apply/(@cvgrPdist_le R R^o) => /= e pos_e.
    pose B := closed_ball_ Num.Def.normr l e.
    have := cvgf_x0_l B. rewrite -neigh_align => /[spec].
    + apply/(@nbhs_closedballP _ R^o).
      exists (PosNum pos_e). by rewrite closed_ballE.
    + case => cx0  [[neq_cx0_x0 _] cx0Bx0]. near=> n.
      apply: cx0Bx0. near: n.
      exists (`|cx0 - x0|) => //= x near_x_x0 neq_x_x0. split.
      * by rewrite normr_gt0 subr_eq0.
      * by move: near_x_x0 ; rewrite/ball_/= distrC lt_le_def ; case/andP.
  Unshelve. by end_near.
Qed.

Definition diffl (f : R -> R) (y x : R) :=
  @derivable _ R^o R^o f x 1 /\ @derive1 R^o R^o f x = y.

Lemma diffl_def : diffl = (fun _115541 : R -> R => fun _115542 : R => fun _115543 : R => tends_real_real (fun h : R => divr (subr (_115541 (addr _115543 h)) (_115541 _115543)) h) _115542 (R_of_nat (NUMERAL O))).
Proof.
  rewrite/R_of_nat/diffl/derive1/derivable/tends_real_real/=. funext => f y x.
  under eq_fun; first (move=> h; rewrite (scaler1 h) [(_ *: _)%mcR]mulrC (addrC h) ; over).
  under [in X in _ /\ X]eq_fun; first (move=> h; rewrite [(_ *: _)%mcR]mulrC (addrC h) ; over).
  ext => [[H1 H2]|H].
  - by apply: cvg_toP.
- split.
  + by apply: cvgP H.
  + by apply/cvg_lim.
Qed.

Lemma cvg_dnbhs_at_right (f : R -> R) (p : R) (l : R) :
  f x @[x --> p^'] --> l ->
  f x @[x --> p^'+] --> l.
Proof.
apply: cvg_trans; apply: cvg_app.
by apply: within_subset => r ?; rewrite gt_eqF.
Qed.

Lemma cvg_dnbhs_at_left (f : R -> R) (p : R) (l : R) :
  f x @[x --> p^'] --> l ->
  f x @[x --> p^'-] --> l.
Proof.
apply: cvg_trans; apply: cvg_app.
by apply: within_subset => r ?; rewrite lt_eqF.
Qed.

Definition contl (f : R -> R) (x : R) := {for x, continuous f}.

Lemma contl_def : contl = (fun _115562 : R -> R => fun _115563 : R => tends_real_real (fun h : R => _115562 (addr _115563 h)) (_115562 _115563) (R_of_nat (NUMERAL O))).
Proof.
  rewrite/contl/addr => /f` f x /=. rewrite (@continuous_shift _ R^o R^o).
  under [in X in _ = X]eq_fun do (rewrite addrC).
  rewrite/tends_real_real/continuous_at/=.
  rewrite -[in X in _ --> X](add0r x).
  transitivity (f (x0 + x)%mcR @[x0 --> (0%mcR)^'-] --> f (0+x)%mcR /\
    f (x0 + x)%mcR @[x0 --> (0%mcR)^'+] --> f (0+x)%mcR).
  - apply propext. apply iff_sym. exact: left_right_continuousP.
  - ext => [[contfxl contfxr]|contfx].
    + exact: cvg_at_right_left_dnbhs.
    + split ; [exact: cvg_dnbhs_at_left | exact: cvg_dnbhs_at_right].
Qed.

Definition differentiable (f : R -> R) (x : R) := @derivable _ R^o R^o f x 1.
Lemma differentiable_def : differentiable = (fun _115574 : R -> R => fun _115575 : R => exists l : R, diffl _115574 l _115575).
Proof.
  rewrite/differentiable/diffl/derivable/=. ext => f x.
  - by move=> ? ; exists (@derive1 R^o R^o f x).
  - by move=>[?[]].
Qed.