Require Import Stdlib.Reals.Reals mathcomp.boot.ssrnat mathcomp.boot.div mathcomp.boot.seq mathcomp.algebra.ssrint mathcomp.algebra.intdiv mathcomp.classical.classical_sets mathcomp.classical.cardinality mathcomp.analysis_stdlib.Rstruct_topology HOLLight.HOL.mappings.
Require Import HOLLight.HOL.terms.
Axiom thm_T_DEF : True = ((fun p : Prop => p) = (fun p : Prop => p)).
Axiom thm_AND_DEF : and = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True)).
Axiom thm_IMP_DEF : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).
Axiom thm_FORALL_DEF : forall {A : Type'}, (@Logic.all A) = (fun P : A -> Prop => P = (fun x : A => True)).
Axiom thm_EXISTS_DEF : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q).
Axiom thm_OR_DEF : or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r).
Axiom thm_F_DEF : False = (forall p : Prop, p).
Axiom thm_NOT_DEF : not = (fun p : Prop => p -> False).
Axiom thm_EXISTS_UNIQUE_DEF : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Axiom thm__FALSITY_ : _FALSITY_ = False.
Axiom thm_EQ_REFL : forall {A : Type'}, forall x : A, x = x.
Axiom thm_REFL_CLAUSE : forall {A : Type'}, forall x : A, (x = x) = True.
Axiom thm_EQ_SYM : forall {A : Type'}, forall x : A, forall y : A, (x = y) -> y = x.
Axiom thm_EQ_SYM_EQ : forall {A : Type'}, forall x : A, forall y : A, (x = y) = (y = x).
Axiom thm_EQ_TRANS : forall {A : Type'}, forall x : A, forall y : A, forall z : A, ((x = y) /\ (y = z)) -> x = z.
Axiom thm_BETA_THM : forall {A B : Type'}, forall f : A -> B, forall y : A, ((fun x : A => f x) y) = (f y).
Axiom thm_ABS_SIMP : forall {A B : Type'}, forall t1 : A, forall t2 : B, ((fun x : B => t1) t2) = t1.
Axiom thm_CONJ_ASSOC : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 /\ (t2 /\ t3)) = ((t1 /\ t2) /\ t3).
Axiom thm_CONJ_SYM : forall t1 : Prop, forall t2 : Prop, (t1 /\ t2) = (t2 /\ t1).
Axiom thm_CONJ_ACI : forall (r : Prop) (p : Prop) (q : Prop), ((p /\ q) = (q /\ p)) /\ ((((p /\ q) /\ r) = (p /\ (q /\ r))) /\ (((p /\ (q /\ r)) = (q /\ (p /\ r))) /\ (((p /\ p) = p) /\ ((p /\ (p /\ q)) = (p /\ q))))).
Axiom thm_DISJ_ASSOC : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 \/ (t2 \/ t3)) = ((t1 \/ t2) \/ t3).
Axiom thm_DISJ_SYM : forall t1 : Prop, forall t2 : Prop, (t1 \/ t2) = (t2 \/ t1).
Axiom thm_DISJ_ACI : forall (r : Prop) (p : Prop) (q : Prop), ((p \/ q) = (q \/ p)) /\ ((((p \/ q) \/ r) = (p \/ (q \/ r))) /\ (((p \/ (q \/ r)) = (q \/ (p \/ r))) /\ (((p \/ p) = p) /\ ((p \/ (p \/ q)) = (p \/ q))))).
Axiom thm_IMP_CONJ : forall (p : Prop) (q : Prop) (r : Prop), ((p /\ q) -> r) = (p -> q -> r).
Axiom thm_IMP_CONJ_ALT : forall (q : Prop) (p : Prop) (r : Prop), ((p /\ q) -> r) = (q -> p -> r).
Axiom thm_LEFT_OR_DISTRIB : forall p : Prop, forall q : Prop, forall r : Prop, (p /\ (q \/ r)) = ((p /\ q) \/ (p /\ r)).
Axiom thm_RIGHT_OR_DISTRIB : forall p : Prop, forall q : Prop, forall r : Prop, ((p \/ q) /\ r) = ((p /\ r) \/ (q /\ r)).
Axiom thm_FORALL_SIMP : forall {A : Type'}, forall t : Prop, (forall x : A, t) = t.
Axiom thm_EXISTS_SIMP : forall {A : Type'}, forall t : Prop, (exists x : A, t) = t.
Axiom thm_EQ_CLAUSES : forall t : Prop, ((True = t) = t) /\ (((t = True) = t) /\ (((False = t) = (~ t)) /\ ((t = False) = (~ t)))).
Axiom thm_NOT_CLAUSES_WEAK : ((~ True) = False) /\ ((~ False) = True).
Axiom thm_AND_CLAUSES : forall t : Prop, ((True /\ t) = t) /\ (((t /\ True) = t) /\ (((False /\ t) = False) /\ (((t /\ False) = False) /\ ((t /\ t) = t)))).
Axiom thm_OR_CLAUSES : forall t : Prop, ((True \/ t) = True) /\ (((t \/ True) = True) /\ (((False \/ t) = t) /\ (((t \/ False) = t) /\ ((t \/ t) = t)))).
Axiom thm_IMP_CLAUSES : forall t : Prop, ((True -> t) = t) /\ (((t -> True) = True) /\ (((False -> t) = True) /\ (((t -> t) = True) /\ ((t -> False) = (~ t))))).
Axiom thm_EXISTS_UNIQUE_THM : forall {A : Type'}, forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = ((exists x : A, P x) /\ (forall x : A, forall x' : A, ((P x) /\ (P x')) -> x = x')).
Axiom thm_EXISTS_REFL : forall {A : Type'}, forall a : A, exists x : A, x = a.
Axiom thm_EXISTS_UNIQUE_REFL : forall {A : Type'}, forall a : A, @ex1 A (fun x : A => x = a).
Axiom thm_UNWIND_THM1 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (exists x : A, (a = x) /\ (P x)) = (P a).
Axiom thm_UNWIND_THM2 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (exists x : A, (x = a) /\ (P x)) = (P a).
Axiom thm_FORALL_UNWIND_THM2 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (forall x : A, (x = a) -> P x) = (P a).
Axiom thm_FORALL_UNWIND_THM1 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (forall x : A, (a = x) -> P x) = (P a).
Axiom thm_SWAP_FORALL_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, forall y : B, P x y) = (forall y : B, forall x : A, P x y).
Axiom thm_SWAP_EXISTS_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (exists x : A, exists y : B, P x y) = (exists y : B, exists x : A, P x y).
Axiom thm_FORALL_AND_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, (forall x : A, (P x) /\ (Q x)) = ((forall x : A, P x) /\ (forall x : A, Q x)).
Axiom thm_AND_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, ((forall x : A, P x) /\ (forall x : A, Q x)) = (forall x : A, (P x) /\ (Q x)).
Axiom thm_LEFT_AND_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) /\ Q) = (forall x : A, (P x) /\ Q).
Axiom thm_RIGHT_AND_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P /\ (forall x : A, Q x)) = (forall x : A, P /\ (Q x)).
Axiom thm_EXISTS_OR_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, (exists x : A, (P x) \/ (Q x)) = ((exists x : A, P x) \/ (exists x : A, Q x)).
Axiom thm_OR_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, ((exists x : A, P x) \/ (exists x : A, Q x)) = (exists x : A, (P x) \/ (Q x)).
Axiom thm_LEFT_OR_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) \/ Q) = (exists x : A, (P x) \/ Q).
Axiom thm_RIGHT_OR_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P \/ (exists x : A, Q x)) = (exists x : A, P \/ (Q x)).
Axiom thm_LEFT_EXISTS_AND_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (exists x : A, (P x) /\ Q) = ((exists x : A, P x) /\ Q).
Axiom thm_RIGHT_EXISTS_AND_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (exists x : A, P /\ (Q x)) = (P /\ (exists x : A, Q x)).
Axiom thm_TRIV_EXISTS_AND_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (exists x : A, P /\ Q) = ((exists x : A, P) /\ (exists x : A, Q)).
Axiom thm_LEFT_AND_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) /\ Q) = (exists x : A, (P x) /\ Q).
Axiom thm_RIGHT_AND_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P /\ (exists x : A, Q x)) = (exists x : A, P /\ (Q x)).
Axiom thm_TRIV_AND_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, ((exists x : A, P) /\ (exists x : A, Q)) = (exists x : A, P /\ Q).
Axiom thm_TRIV_FORALL_OR_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (forall x : A, P \/ Q) = ((forall x : A, P) \/ (forall x : A, Q)).
Axiom thm_TRIV_OR_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, ((forall x : A, P) \/ (forall x : A, Q)) = (forall x : A, P \/ Q).
Axiom thm_RIGHT_IMP_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P -> forall x : A, Q x) = (forall x : A, P -> Q x).
Axiom thm_RIGHT_FORALL_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (forall x : A, P -> Q x) = (P -> forall x : A, Q x).
Axiom thm_LEFT_IMP_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) -> Q) = (forall x : A, (P x) -> Q).
Axiom thm_LEFT_FORALL_IMP_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (forall x : A, (P x) -> Q) = ((exists x : A, P x) -> Q).
Axiom thm_TRIV_FORALL_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (forall x : A, P -> Q) = ((exists x : A, P) -> forall x : A, Q).
Axiom thm_TRIV_EXISTS_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (exists x : A, P -> Q) = ((forall x : A, P) -> exists x : A, Q).
Axiom thm_MONO_FORALL : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), (forall x : A, (P x) -> Q x) -> (forall x : A, P x) -> forall x : A, Q x.
Axiom thm_MONO_EXISTS : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), (forall x : A, (P x) -> Q x) -> (exists x : A, P x) -> exists x : A, Q x.
Axiom thm_WLOG_RELATION : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (P x y) -> P y x) /\ ((forall x : A, forall y : A, (R' x y) \/ (R' y x)) /\ (forall x : A, forall y : A, (R' x y) -> P x y))) -> forall x : A, forall y : A, P x y.
Axiom thm_EXISTS_UNIQUE_ALT : forall {A : Type'}, forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = (exists x : A, forall y : A, (P y) = (x = y)).
Axiom thm_EXISTS_UNIQUE : forall {A : Type'}, forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = (exists x : A, (P x) /\ (forall y : A, (P y) -> y = x)).
Axiom thm_ETA_AX : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Axiom thm_EQ_EXT : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, (forall x : A, (f x) = (g x)) -> f = g.
Axiom thm_FUN_EQ_THM : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, (f = g) = (forall x : A, (f x) = (g x)).
Axiom thm_SELECT_AX : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Axiom thm_EXISTS_THM : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => P (@ε A P)).
Axiom thm_SELECT_REFL : forall {A : Type'}, forall x : A, (@ε A (fun y : A => y = x)) = x.
Axiom thm_SELECT_UNIQUE : forall {A : Type'}, forall P : A -> Prop, forall x : A, (forall y : A, (P y) = (y = x)) -> (@ε A P) = x.
Axiom thm_EXCLUDED_MIDDLE : forall t : Prop, t \/ (~ t).
Axiom thm_BOOL_CASES_AX : forall t : Prop, (t = True) \/ (t = False).
Axiom thm_DE_MORGAN_THM : forall t1 : Prop, forall t2 : Prop, ((~ (t1 /\ t2)) = ((~ t1) \/ (~ t2))) /\ ((~ (t1 \/ t2)) = ((~ t1) /\ (~ t2))).
Axiom thm_NOT_CLAUSES : (forall t : Prop, (~ (~ t)) = t) /\ (((~ True) = False) /\ ((~ False) = True)).
Axiom thm_NOT_IMP : forall t1 : Prop, forall t2 : Prop, (~ (t1 -> t2)) = (t1 /\ (~ t2)).
Axiom thm_CONTRAPOS_THM : forall t1 : Prop, forall t2 : Prop, ((~ t1) -> ~ t2) = (t2 -> t1).
Axiom thm_NOT_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, (~ (exists x : A, P x)) = (forall x : A, ~ (P x)).
Axiom thm_EXISTS_NOT_THM : forall {A : Type'}, forall P : A -> Prop, (exists x : A, ~ (P x)) = (~ (forall x : A, P x)).
Axiom thm_NOT_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, (~ (forall x : A, P x)) = (exists x : A, ~ (P x)).
Axiom thm_FORALL_NOT_THM : forall {A : Type'}, forall P : A -> Prop, (forall x : A, ~ (P x)) = (~ (exists x : A, P x)).
Axiom thm_FORALL_BOOL_THM : forall (P : Prop -> Prop), (forall b : Prop, P b) = ((P True) /\ (P False)).
Axiom thm_EXISTS_BOOL_THM : forall (P : Prop -> Prop), (exists b : Prop, P b) = ((P True) \/ (P False)).
Axiom thm_LEFT_FORALL_OR_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (forall x : A, (P x) \/ Q) = ((forall x : A, P x) \/ Q).
Axiom thm_RIGHT_FORALL_OR_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (forall x : A, P \/ (Q x)) = (P \/ (forall x : A, Q x)).
Axiom thm_LEFT_OR_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) \/ Q) = (forall x : A, (P x) \/ Q).
Axiom thm_RIGHT_OR_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P \/ (forall x : A, Q x)) = (forall x : A, P \/ (Q x)).
Axiom thm_LEFT_IMP_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) -> Q) = (exists x : A, (P x) -> Q).
Axiom thm_LEFT_EXISTS_IMP_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (exists x : A, (P x) -> Q) = ((forall x : A, P x) -> Q).
Axiom thm_RIGHT_IMP_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P -> exists x : A, Q x) = (exists x : A, P -> Q x).
Axiom thm_RIGHT_EXISTS_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (exists x : A, P -> Q x) = (P -> exists x : A, Q x).
Axiom thm_COND_DEF : forall {A : Type'}, (@COND A) = (fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))).
Axiom thm_COND_CLAUSES : forall {A : Type'}, forall t1 : A, forall t2 : A, ((@COND A True t1 t2) = t1) /\ ((@COND A False t1 t2) = t2).
Axiom thm_COND_EXPAND : forall b : Prop, forall t1 : Prop, forall t2 : Prop, (@COND Prop b t1 t2) = (((~ b) \/ t1) /\ (b \/ t2)).
Axiom thm_COND_ID : forall {A : Type'}, forall b : Prop, forall t : A, (@COND A b t t) = t.
Axiom thm_COND_RAND : forall {A B : Type'}, forall b : Prop, forall f : A -> B, forall x : A, forall y : A, (f (@COND A b x y)) = (@COND B b (f x) (f y)).
Axiom thm_COND_RATOR : forall {A B : Type'}, forall b : Prop, forall f : A -> B, forall g : A -> B, forall x : A, (@COND (A -> B) b f g x) = (@COND B b (f x) (g x)).
Axiom thm_COND_ABS : forall {A B : Type'}, forall b : Prop, forall f : A -> B, forall g : A -> B, (fun x : A => @COND B b (f x) (g x)) = (@COND (A -> B) b f g).
Axiom thm_COND_SWAP : forall {A : Type'}, forall p : Prop, forall x : A, forall y : A, (@COND A (~ p) x y) = (@COND A p y x).
Axiom thm_MONO_COND : forall (A : Prop) (C : Prop) (b : Prop) (B : Prop) (D : Prop), ((A -> B) /\ (C -> D)) -> (@COND Prop b A C) -> @COND Prop b B D.
Axiom thm_COND_ELIM_THM : forall {A : Type'} (x : A) (c : Prop) (P : A -> Prop) (y : A), (P (@COND A c x y)) = ((c -> P x) /\ ((~ c) -> P y)).
Axiom thm_SKOLEM_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, exists y : B, P x y) = (exists y : A -> B, forall x : A, P x (y x)).
Axiom thm_SKOLEM_THM_GEN : forall {A B : Type'}, forall P : A -> Prop, forall R' : A -> B -> Prop, (forall x : A, (P x) -> exists y : B, R' x y) = (exists f : A -> B, forall x : A, (P x) -> R' x (f x)).
Axiom thm_UNIQUE_SKOLEM_ALT : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, @ex1 B (fun y : B => P x y)) = (exists f : A -> B, forall x : A, forall y : B, (P x y) = ((f x) = y)).
Axiom thm_UNIQUE_SKOLEM_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, @ex1 B (fun y : B => P x y)) = (@ex1 (A -> B) (fun f : A -> B => forall x : A, P x (f x))).
Axiom thm_bool_INDUCT : forall P : Prop -> Prop, ((P False) /\ (P True)) -> forall x : Prop, P x.
Axiom thm_bool_RECURSION : forall {A : Type'}, forall a : A, forall b : A, exists f : Prop -> A, ((f False) = a) /\ ((f True) = b).
Axiom thm_o_DEF : forall {A B C : Type'}, forall f : B -> C, forall g : A -> B, (@o A B C f g) = (fun x : A => f (g x)).
Axiom thm_I_DEF : forall {A : Type'}, (@I A) = (fun x : A => x).
Axiom thm_o_THM : forall {A B C : Type'}, forall f : B -> C, forall g : A -> B, forall x : A, (@o A B C f g x) = (f (g x)).
Axiom thm_o_ASSOC : forall {A B C D : Type'}, forall f : C -> D, forall g : B -> C, forall h : A -> B, (@o A C D f (@o A B C g h)) = (@o A B D (@o B C D f g) h).
Axiom thm_I_THM : forall {A : Type'}, forall x : A, (@I A x) = x.
Axiom thm_I_O_ID : forall {A B : Type'}, forall f : A -> B, ((@o A B B (@I B) f) = f) /\ ((@o A A B f (@I A)) = f).
Axiom thm_EXISTS_ONE_REP : exists b : Prop, b.
Axiom thm_one_DEF : tt = (@ε unit (fun x : unit => True)).
Axiom thm_one : forall v : unit, v = tt.
Axiom thm_one_axiom : forall {A : Type'}, forall f : A -> unit, forall g : A -> unit, f = g.
Axiom thm_one_INDUCT : forall P : unit -> Prop, (P tt) -> forall x : unit, P x.
Axiom thm_one_RECURSION : forall {A : Type'}, forall e : A, exists fn : unit -> A, (fn tt) = e.
Axiom thm_one_Axiom : forall {A : Type'}, forall e : A, @ex1 (unit -> A) (fun fn : unit -> A => (fn tt) = e).
Axiom thm_FORALL_ONE_THM : forall (P : unit -> Prop), (forall x : unit, P x) = (P tt).
Axiom thm_EXISTS_ONE_THM : forall (P : unit -> Prop), (exists x : unit, P x) = (P tt).
Axiom thm_ETA_ONE : forall {A : Type'}, forall f : unit -> A, (fun x : unit => f tt) = f.
Axiom thm_LET_DEF : forall {A B : Type'}, forall f : A -> B, forall x : A, (@LET A B f x) = (f x).
Axiom thm_LET_END_DEF : forall {A : Type'}, forall t : A, (@LET_END A t) = t.
Axiom thm_GABS_DEF : forall {A : Type'}, forall P : A -> Prop, (@GABS A P) = (@ε A P).
Axiom thm_GEQ_DEF : forall {A : Type'}, forall a : A, forall b : A, (@eq A a b) = (a = b).
Axiom thm__SEQPATTERN : forall {A B : Type'}, (@_SEQPATTERN A B) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x)).
Axiom thm__UNGUARDED_PATTERN : _UNGUARDED_PATTERN = (fun p : Prop => fun r : Prop => p /\ r).
Axiom thm__GUARDED_PATTERN : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)).
Axiom thm__MATCH : forall {A B : Type'}, (@_MATCH A B) = (fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False))).
Axiom thm__FUNCTION : forall {A B : Type'}, (@_FUNCTION A B) = (fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False))).
Axiom thm_mk_pair_def : forall {A B : Type'}, forall x : A, forall y : B, (@mk_pair A B x y) = (fun a : A => fun b : B => (a = x) /\ (b = y)).
Axiom thm_PAIR_EXISTS_THM : forall {A B : Type'}, exists x : A -> B -> Prop, exists a : A, exists b : B, x = (@mk_pair A B a b).
Axiom thm_REP_ABS_PAIR : forall {A B : Type'}, forall x : A, forall y : B, (@REP_prod A B (@ABS_prod A B (@mk_pair A B x y))) = (@mk_pair A B x y).
Axiom thm_COMMA_DEF : forall {A B : Type'}, forall x : A, forall y : B, (@pair A B x y) = (@ABS_prod A B (@mk_pair A B x y)).
Axiom thm_FST_DEF : forall {A B : Type'}, forall p : prod A B, (@fst A B p) = (@ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Axiom thm_SND_DEF : forall {A B : Type'}, forall p : prod A B, (@snd A B p) = (@ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Axiom thm_PAIR_EQ : forall {A B : Type'}, forall x : A, forall y : B, forall a : A, forall b : B, ((@pair A B x y) = (@pair A B a b)) = ((x = a) /\ (y = b)).
Axiom thm_PAIR_SURJECTIVE : forall {A B : Type'}, forall p : prod A B, exists x : A, exists y : B, p = (@pair A B x y).
Axiom thm_FST : forall {A B : Type'}, forall x : A, forall y : B, (@fst A B (@pair A B x y)) = x.
Axiom thm_SND : forall {A B : Type'}, forall x : A, forall y : B, (@snd A B (@pair A B x y)) = y.
Axiom thm_PAIR : forall {A B : Type'}, forall x : prod A B, (@pair A B (@fst A B x) (@snd A B x)) = x.
Axiom thm_pair_INDUCT : forall {A B : Type'}, forall P : (prod A B) -> Prop, (forall x : A, forall y : B, P (@pair A B x y)) -> forall p : prod A B, P p.
Axiom thm_pair_RECURSION : forall {A B C : Type'}, forall PAIR' : A -> B -> C, exists fn : (prod A B) -> C, forall a0 : A, forall a1 : B, (fn (@pair A B a0 a1)) = (PAIR' a0 a1).
Axiom thm_CURRY_DEF : forall {A B C : Type'}, forall f : (prod A B) -> C, forall x : A, forall y : B, (@CURRY A B C f x y) = (f (@pair A B x y)).
Axiom thm_UNCURRY_DEF : forall {A B C : Type'}, forall f : A -> B -> C, forall x : A, forall y : B, (@UNCURRY A B C f (@pair A B x y)) = (f x y).
Axiom thm_PASSOC_DEF : forall {A B C D : Type'}, forall f : (prod (prod A B) C) -> D, forall x : A, forall y : B, forall z : C, (@PASSOC A B C D f (@pair A (prod B C) x (@pair B C y z))) = (f (@pair (prod A B) C (@pair A B x y) z)).
Axiom thm_FORALL_PAIR_THM : forall {A B : Type'}, forall P : (prod A B) -> Prop, (forall p : prod A B, P p) = (forall p1 : A, forall p2 : B, P (@pair A B p1 p2)).
Axiom thm_EXISTS_PAIR_THM : forall {A B : Type'}, forall P : (prod A B) -> Prop, (exists p : prod A B, P p) = (exists p1 : A, exists p2 : B, P (@pair A B p1 p2)).
Axiom thm_LAMBDA_PAIR_THM : forall {A B C : Type'}, forall t : (prod A B) -> C, (fun p : prod A B => t p) = (@GABS ((prod A B) -> C) (fun f : (prod A B) -> C => forall x : A, forall y : B, @eq C (f (@pair A B x y)) (t (@pair A B x y)))).
Axiom thm_LAMBDA_PAIR : forall {A B C : Type'}, forall f : A -> B -> C, (@GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall x : A, forall y : B, @eq C (f' (@pair A B x y)) (f x y))) = (fun p : prod A B => f (@fst A B p) (@snd A B p)).
Axiom thm_LAMBDA_TRIPLE_THM : forall {A B C D : Type'}, forall f : (prod A (prod B C)) -> D, (fun t : prod A (prod B C) => f t) = (@GABS ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, @eq D (f' (@pair A (prod B C) x (@pair B C y z))) (f (@pair A (prod B C) x (@pair B C y z))))).
Axiom thm_LAMBDA_TRIPLE : forall {A B C D : Type'}, forall f : A -> B -> C -> D, (@GABS ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, @eq D (f' (@pair A (prod B C) x (@pair B C y z))) (f x y z))) = (fun t : prod A (prod B C) => f (@fst A (prod B C) t) (@fst B C (@snd A (prod B C) t)) (@snd B C (@snd A (prod B C) t))).
Axiom thm_PAIRED_ETA_THM : forall {A B C D E : Type'}, (forall f : (prod A B) -> C, (@GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall x : A, forall y : B, @eq C (f' (@pair A B x y)) (f (@pair A B x y)))) = f) /\ ((forall f : (prod A (prod B C)) -> D, (@GABS ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, @eq D (f' (@pair A (prod B C) x (@pair B C y z))) (f (@pair A (prod B C) x (@pair B C y z))))) = f) /\ (forall f : (prod A (prod B (prod C D))) -> E, (@GABS ((prod A (prod B (prod C D))) -> E) (fun f' : (prod A (prod B (prod C D))) -> E => forall w : A, forall x : B, forall y : C, forall z : D, @eq E (f' (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))) (f (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))))) = f)).
Axiom thm_FORALL_UNCURRY : forall {A B C : Type'}, forall P : (A -> B -> C) -> Prop, (forall f : A -> B -> C, P f) = (forall f : (prod A B) -> C, P (fun a : A => fun b : B => f (@pair A B a b))).
Axiom thm_EXISTS_UNCURRY : forall {A B C : Type'}, forall P : (A -> B -> C) -> Prop, (exists f : A -> B -> C, P f) = (exists f : (prod A B) -> C, P (fun a : A => fun b : B => f (@pair A B a b))).
Axiom thm_EXISTS_CURRY : forall {A B C : Type'}, forall P : ((prod A B) -> C) -> Prop, (exists f : (prod A B) -> C, P f) = (exists f : A -> B -> C, P (@GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall a : A, forall b : B, @eq C (f' (@pair A B a b)) (f a b)))).
Axiom thm_FORALL_CURRY : forall {A B C : Type'}, forall P : ((prod A B) -> C) -> Prop, (forall f : (prod A B) -> C, P f) = (forall f : A -> B -> C, P (@GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall a : A, forall b : B, @eq C (f' (@pair A B a b)) (f a b)))).
Axiom thm_FORALL_UNPAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, forall y : B, P x y) = (forall z : prod A B, P (@fst A B z) (@snd A B z)).
Axiom thm_EXISTS_UNPAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (exists x : A, exists y : B, P x y) = (exists z : prod A B, P (@fst A B z) (@snd A B z)).
Axiom thm_FORALL_PAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> prod B C) -> Prop, (forall f : A -> prod B C, P f) = (forall g : A -> B, forall h : A -> C, P (fun a : A => @pair B C (g a) (h a))).
Axiom thm_EXISTS_PAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> prod B C) -> Prop, (exists f : A -> prod B C, P f) = (exists g : A -> B, exists h : A -> C, P (fun a : A => @pair B C (g a) (h a))).
Axiom thm_FORALL_UNPAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> B) -> (A -> C) -> Prop, (forall f : A -> B, forall g : A -> C, P f g) = (forall h : A -> prod B C, P (@o A (prod B C) B (@fst B C) h) (@o A (prod B C) C (@snd B C) h)).
Axiom thm_EXISTS_UNPAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> B) -> (A -> C) -> Prop, (exists f : A -> B, exists g : A -> C, P f g) = (exists h : A -> prod B C, P (@o A (prod B C) B (@fst B C) h) (@o A (prod B C) C (@snd B C) h)).
Axiom thm_EXISTS_SWAP_FUN_THM : forall {A B C : Type'}, forall P : (A -> B -> C) -> Prop, (exists f : A -> B -> C, P f) = (exists f : B -> A -> C, P (fun a : A => fun b : B => f b a)).
Axiom thm_FORALL_PAIRED_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (Logic.all (@GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))) = (forall x : A, forall y : B, P x y).
Axiom thm_EXISTS_PAIRED_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (ex (@GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))) = (exists x : A, exists y : B, P x y).
Axiom thm_FORALL_TRIPLED_THM : forall {A B C : Type'}, forall P : A -> B -> C -> Prop, (Logic.all (@GABS ((prod A (prod B C)) -> Prop) (fun f : (prod A (prod B C)) -> Prop => forall x : A, forall y : B, forall z : C, @eq Prop (f (@pair A (prod B C) x (@pair B C y z))) (P x y z)))) = (forall x : A, forall y : B, forall z : C, P x y z).
Axiom thm_EXISTS_TRIPLED_THM : forall {A B C : Type'}, forall P : A -> B -> C -> Prop, (ex (@GABS ((prod A (prod B C)) -> Prop) (fun f : (prod A (prod B C)) -> Prop => forall x : A, forall y : B, forall z : C, @eq Prop (f (@pair A (prod B C) x (@pair B C y z))) (P x y z)))) = (exists x : A, exists y : B, exists z : C, P x y z).
Axiom thm_CHOICE_UNPAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (@ε (prod A B) (@GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))) = (@ε (prod A B) (fun p : prod A B => P (@fst A B p) (@snd A B p))).
Axiom thm_CHOICE_PAIRED_THM : forall {A B : Type'}, forall P : A -> B -> Prop, forall Q : (prod A B) -> Prop, ((exists x : A, exists y : B, P x y) /\ (forall x : A, forall y : B, (P x y) -> Q (@pair A B x y))) -> Q (@ε (prod A B) (@GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))).
Axiom thm_ONE_ONE : forall {A B : Type'}, forall f : A -> B, (@ONE_ONE A B f) = (forall x1 : A, forall x2 : A, ((f x1) = (f x2)) -> x1 = x2).
Axiom thm_ONTO : forall {A B : Type'}, forall f : A -> B, (@ONTO A B f) = (forall y : B, exists x : A, y = (f x)).
Axiom thm_INFINITY_AX : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Axiom thm_IND_SUC_0_EXISTS : exists f : ind -> ind, exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)).
Axiom thm_NUM_REP_RULES : (NUM_REP IND_0) /\ (forall i : ind, (NUM_REP i) -> NUM_REP (IND_SUC i)).
Axiom thm_NUM_REP_CASES : forall a : ind, (NUM_REP a) = ((a = IND_0) \/ (exists i : ind, (a = (IND_SUC i)) /\ (NUM_REP i))).
Axiom thm_NUM_REP_INDUCT : forall NUM_REP' : ind -> Prop, ((NUM_REP' IND_0) /\ (forall i : ind, (NUM_REP' i) -> NUM_REP' (IND_SUC i))) -> forall a : ind, (NUM_REP a) -> NUM_REP' a.
Axiom thm_ZERO_DEF : O = (mk_num IND_0).
Axiom thm_SUC_DEF : forall n : nat, (S n) = (mk_num (IND_SUC (dest_num n))).
Axiom thm_SUC_INJ : forall m : nat, forall n : nat, ((S m) = (S n)) = (m = n).
Axiom thm_NOT_SUC : forall n : nat, ~ ((S n) = (NUMERAL O)).
Axiom thm_num_INDUCTION : forall P : nat -> Prop, ((P (NUMERAL O)) /\ (forall n : nat, (P n) -> P (S n))) -> forall n : nat, P n.
Axiom thm_num_Axiom : forall {A : Type'}, forall e : A, forall f : A -> nat -> A, @ex1 (nat -> A) (fun fn : nat -> A => ((fn (NUMERAL O)) = e) /\ (forall n : nat, (fn (S n)) = (f (fn n) n))).
Axiom thm_num_CASES : forall m : nat, (m = (NUMERAL O)) \/ (exists n : nat, m = (S n)).
Axiom thm_PRE : ((predn (NUMERAL O)) = (NUMERAL O)) /\ (forall n : nat, (predn (S n)) = n).
Axiom thm_ADD : (forall n : nat, (addn (NUMERAL O) n) = n) /\ (forall m : nat, forall n : nat, (addn (S m) n) = (S (addn m n))).
Axiom thm_ADD_0 : forall m : nat, (addn m (NUMERAL O)) = m.
Axiom thm_ADD_SUC : forall m : nat, forall n : nat, (addn m (S n)) = (S (addn m n)).
Axiom thm_ADD_CLAUSES : (forall n : nat, (addn (NUMERAL O) n) = n) /\ ((forall m : nat, (addn m (NUMERAL O)) = m) /\ ((forall m : nat, forall n : nat, (addn (S m) n) = (S (addn m n))) /\ (forall m : nat, forall n : nat, (addn m (S n)) = (S (addn m n))))).
Axiom thm_ADD_SYM : forall m : nat, forall n : nat, (addn m n) = (addn n m).
Axiom thm_ADD_ASSOC : forall m : nat, forall n : nat, forall p : nat, (addn m (addn n p)) = (addn (addn m n) p).
Axiom thm_ADD_AC : forall (n : nat) (m : nat) (p : nat), ((addn m n) = (addn n m)) /\ (((addn (addn m n) p) = (addn m (addn n p))) /\ ((addn m (addn n p)) = (addn n (addn m p)))).
Axiom thm_ADD_EQ_0 : forall m : nat, forall n : nat, ((addn m n) = (NUMERAL O)) = ((m = (NUMERAL O)) /\ (n = (NUMERAL O))).
Axiom thm_EQ_ADD_LCANCEL : forall m : nat, forall n : nat, forall p : nat, ((addn m n) = (addn m p)) = (n = p).
Axiom thm_EQ_ADD_RCANCEL : forall m : nat, forall n : nat, forall p : nat, ((addn m p) = (addn n p)) = (m = n).
Axiom thm_EQ_ADD_LCANCEL_0 : forall m : nat, forall n : nat, ((addn m n) = m) = (n = (NUMERAL O)).
Axiom thm_EQ_ADD_RCANCEL_0 : forall m : nat, forall n : nat, ((addn m n) = n) = (m = (NUMERAL O)).
Axiom thm_BIT0 : forall n : nat, (BIT0 n) = (addn n n).
Axiom thm_BIT1 : forall n : nat, (BIT1 n) = (S (addn n n)).
Axiom thm_BIT0_THM : forall n : nat, (NUMERAL (BIT0 n)) = (addn (NUMERAL n) (NUMERAL n)).
Axiom thm_BIT1_THM : forall n : nat, (NUMERAL (BIT1 n)) = (S (addn (NUMERAL n) (NUMERAL n))).
Axiom thm_ONE : (NUMERAL (BIT1 O)) = (S (NUMERAL O)).
Axiom thm_TWO : (NUMERAL (BIT0 (BIT1 O))) = (S (NUMERAL (BIT1 O))).
Axiom thm_ADD1 : forall m : nat, (S m) = (addn m (NUMERAL (BIT1 O))).
Axiom thm_MULT : (forall n : nat, (muln (NUMERAL O) n) = (NUMERAL O)) /\ (forall m : nat, forall n : nat, (muln (S m) n) = (addn (muln m n) n)).
Axiom thm_MULT_0 : forall m : nat, (muln m (NUMERAL O)) = (NUMERAL O).
Axiom thm_MULT_SUC : forall m : nat, forall n : nat, (muln m (S n)) = (addn m (muln m n)).
Axiom thm_MULT_CLAUSES : (forall n : nat, (muln (NUMERAL O) n) = (NUMERAL O)) /\ ((forall m : nat, (muln m (NUMERAL O)) = (NUMERAL O)) /\ ((forall n : nat, (muln (NUMERAL (BIT1 O)) n) = n) /\ ((forall m : nat, (muln m (NUMERAL (BIT1 O))) = m) /\ ((forall m : nat, forall n : nat, (muln (S m) n) = (addn (muln m n) n)) /\ (forall m : nat, forall n : nat, (muln m (S n)) = (addn m (muln m n))))))).
Axiom thm_MULT_SYM : forall m : nat, forall n : nat, (muln m n) = (muln n m).
Axiom thm_LEFT_ADD_DISTRIB : forall m : nat, forall n : nat, forall p : nat, (muln m (addn n p)) = (addn (muln m n) (muln m p)).
Axiom thm_RIGHT_ADD_DISTRIB : forall m : nat, forall n : nat, forall p : nat, (muln (addn m n) p) = (addn (muln m p) (muln n p)).
Axiom thm_MULT_ASSOC : forall m : nat, forall n : nat, forall p : nat, (muln m (muln n p)) = (muln (muln m n) p).
Axiom thm_MULT_AC : forall (n : nat) (m : nat) (p : nat), ((muln m n) = (muln n m)) /\ (((muln (muln m n) p) = (muln m (muln n p))) /\ ((muln m (muln n p)) = (muln n (muln m p)))).
Axiom thm_MULT_EQ_0 : forall m : nat, forall n : nat, ((muln m n) = (NUMERAL O)) = ((m = (NUMERAL O)) \/ (n = (NUMERAL O))).
Axiom thm_EQ_MULT_LCANCEL : forall m : nat, forall n : nat, forall p : nat, ((muln m n) = (muln m p)) = ((m = (NUMERAL O)) \/ (n = p)).
Axiom thm_EQ_MULT_RCANCEL : forall m : nat, forall n : nat, forall p : nat, ((muln m p) = (muln n p)) = ((m = n) \/ (p = (NUMERAL O))).
Axiom thm_MULT_2 : forall n : nat, (muln (NUMERAL (BIT0 (BIT1 O))) n) = (addn n n).
Axiom thm_MULT_EQ_1 : forall m : nat, forall n : nat, ((muln m n) = (NUMERAL (BIT1 O))) = ((m = (NUMERAL (BIT1 O))) /\ (n = (NUMERAL (BIT1 O)))).
Axiom thm_EXP : (forall m : nat, (expn m (NUMERAL O)) = (NUMERAL (BIT1 O))) /\ (forall m : nat, forall n : nat, (expn m (S n)) = (muln m (expn m n))).
Axiom thm_EXP_EQ_0 : forall m : nat, forall n : nat, ((expn m n) = (NUMERAL O)) = ((m = (NUMERAL O)) /\ (~ (n = (NUMERAL O)))).
Axiom thm_EXP_EQ_1 : forall x : nat, forall n : nat, ((expn x n) = (NUMERAL (BIT1 O))) = ((x = (NUMERAL (BIT1 O))) \/ (n = (NUMERAL O))).
Axiom thm_EXP_ZERO : forall n : nat, (expn (NUMERAL O) n) = (@COND nat (n = (NUMERAL O)) (NUMERAL (BIT1 O)) (NUMERAL O)).
Axiom thm_EXP_ADD : forall m : nat, forall n : nat, forall p : nat, (expn m (addn n p)) = (muln (expn m n) (expn m p)).
Axiom thm_EXP_ONE : forall n : nat, (expn (NUMERAL (BIT1 O)) n) = (NUMERAL (BIT1 O)).
Axiom thm_EXP_1 : forall n : nat, (expn n (NUMERAL (BIT1 O))) = n.
Axiom thm_EXP_2 : forall n : nat, (expn n (NUMERAL (BIT0 (BIT1 O)))) = (muln n n).
Axiom thm_MULT_EXP : forall p : nat, forall m : nat, forall n : nat, (expn (muln m n) p) = (muln (expn m p) (expn n p)).
Axiom thm_EXP_MULT : forall m : nat, forall n : nat, forall p : nat, (expn m (muln n p)) = (expn (expn m n) p).
Axiom thm_EXP_EXP : forall x : nat, forall m : nat, forall n : nat, (expn (expn x m) n) = (expn x (muln m n)).
Axiom thm_LE : (forall m : nat, (leqn m (NUMERAL O)) = (m = (NUMERAL O))) /\ (forall m : nat, forall n : nat, (leqn m (S n)) = ((m = (S n)) \/ (leqn m n))).
Axiom thm_LT : (forall m : nat, (ltn m (NUMERAL O)) = False) /\ (forall m : nat, forall n : nat, (ltn m (S n)) = ((m = n) \/ (ltn m n))).
Axiom thm_GE : forall n : nat, forall m : nat, (geqn m n) = (leqn n m).
Axiom thm_GT : forall n : nat, forall m : nat, (gtn m n) = (ltn n m).
Axiom thm_MAX : forall m : nat, forall n : nat, (maxn m n) = (@COND nat (leqn m n) n m).
Axiom thm_MIN : forall m : nat, forall n : nat, (minn m n) = (@COND nat (leqn m n) m n).
Axiom thm_LE_SUC_LT : forall m : nat, forall n : nat, (leqn (S m) n) = (ltn m n).
Axiom thm_LT_SUC_LE : forall m : nat, forall n : nat, (ltn m (S n)) = (leqn m n).
Axiom thm_LE_SUC : forall m : nat, forall n : nat, (leqn (S m) (S n)) = (leqn m n).
Axiom thm_LT_SUC : forall m : nat, forall n : nat, (ltn (S m) (S n)) = (ltn m n).
Axiom thm_LE_0 : forall n : nat, leqn (NUMERAL O) n.
Axiom thm_LT_0 : forall n : nat, ltn (NUMERAL O) (S n).
Axiom thm_LE_REFL : forall n : nat, leqn n n.
Axiom thm_LT_REFL : forall n : nat, ~ (ltn n n).
Axiom thm_LT_IMP_NE : forall m : nat, forall n : nat, (ltn m n) -> ~ (m = n).
Axiom thm_LE_ANTISYM : forall m : nat, forall n : nat, ((leqn m n) /\ (leqn n m)) = (m = n).
Axiom thm_LT_ANTISYM : forall m : nat, forall n : nat, ~ ((ltn m n) /\ (ltn n m)).
Axiom thm_LET_ANTISYM : forall m : nat, forall n : nat, ~ ((leqn m n) /\ (ltn n m)).
Axiom thm_LTE_ANTISYM : forall m : nat, forall n : nat, ~ ((ltn m n) /\ (leqn n m)).
Axiom thm_LE_TRANS : forall m : nat, forall n : nat, forall p : nat, ((leqn m n) /\ (leqn n p)) -> leqn m p.
Axiom thm_LT_TRANS : forall m : nat, forall n : nat, forall p : nat, ((ltn m n) /\ (ltn n p)) -> ltn m p.
Axiom thm_LET_TRANS : forall m : nat, forall n : nat, forall p : nat, ((leqn m n) /\ (ltn n p)) -> ltn m p.
Axiom thm_LTE_TRANS : forall m : nat, forall n : nat, forall p : nat, ((ltn m n) /\ (leqn n p)) -> ltn m p.
Axiom thm_LE_CASES : forall m : nat, forall n : nat, (leqn m n) \/ (leqn n m).
Axiom thm_LT_CASES : forall m : nat, forall n : nat, (ltn m n) \/ ((ltn n m) \/ (m = n)).
Axiom thm_LET_CASES : forall m : nat, forall n : nat, (leqn m n) \/ (ltn n m).
Axiom thm_LTE_CASES : forall m : nat, forall n : nat, (ltn m n) \/ (leqn n m).
Axiom thm_LE_LT : forall m : nat, forall n : nat, (leqn m n) = ((ltn m n) \/ (m = n)).
Axiom thm_LT_LE : forall m : nat, forall n : nat, (ltn m n) = ((leqn m n) /\ (~ (m = n))).
Axiom thm_NOT_LE : forall m : nat, forall n : nat, (~ (leqn m n)) = (ltn n m).
Axiom thm_NOT_LT : forall m : nat, forall n : nat, (~ (ltn m n)) = (leqn n m).
Axiom thm_LT_IMP_LE : forall m : nat, forall n : nat, (ltn m n) -> leqn m n.
Axiom thm_EQ_IMP_LE : forall m : nat, forall n : nat, (m = n) -> leqn m n.
Axiom thm_LT_NZ : forall n : nat, (ltn (NUMERAL O) n) = (~ (n = (NUMERAL O))).
Axiom thm_LE_1 : (forall n : nat, (~ (n = (NUMERAL O))) -> ltn (NUMERAL O) n) /\ ((forall n : nat, (~ (n = (NUMERAL O))) -> leqn (NUMERAL (BIT1 O)) n) /\ ((forall n : nat, (ltn (NUMERAL O) n) -> ~ (n = (NUMERAL O))) /\ ((forall n : nat, (ltn (NUMERAL O) n) -> leqn (NUMERAL (BIT1 O)) n) /\ ((forall n : nat, (leqn (NUMERAL (BIT1 O)) n) -> ltn (NUMERAL O) n) /\ (forall n : nat, (leqn (NUMERAL (BIT1 O)) n) -> ~ (n = (NUMERAL O))))))).
Axiom thm_LE_EXISTS : forall m : nat, forall n : nat, (leqn m n) = (exists d : nat, n = (addn m d)).
Axiom thm_LT_EXISTS : forall m : nat, forall n : nat, (ltn m n) = (exists d : nat, n = (addn m (S d))).
Axiom thm_LE_ADD : forall m : nat, forall n : nat, leqn m (addn m n).
Axiom thm_LE_ADDR : forall m : nat, forall n : nat, leqn n (addn m n).
Axiom thm_LT_ADD : forall m : nat, forall n : nat, (ltn m (addn m n)) = (ltn (NUMERAL O) n).
Axiom thm_LT_ADDR : forall m : nat, forall n : nat, (ltn n (addn m n)) = (ltn (NUMERAL O) m).
Axiom thm_LE_ADD_LCANCEL : forall m : nat, forall n : nat, forall p : nat, (leqn (addn m n) (addn m p)) = (leqn n p).
Axiom thm_LE_ADD_RCANCEL : forall m : nat, forall n : nat, forall p : nat, (leqn (addn m p) (addn n p)) = (leqn m n).
Axiom thm_LT_ADD_LCANCEL : forall m : nat, forall n : nat, forall p : nat, (ltn (addn m n) (addn m p)) = (ltn n p).
Axiom thm_LT_ADD_RCANCEL : forall m : nat, forall n : nat, forall p : nat, (ltn (addn m p) (addn n p)) = (ltn m n).
Axiom thm_LE_ADD2 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, ((leqn m p) /\ (leqn n q)) -> leqn (addn m n) (addn p q).
Axiom thm_LET_ADD2 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, ((leqn m p) /\ (ltn n q)) -> ltn (addn m n) (addn p q).
Axiom thm_LTE_ADD2 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, ((ltn m p) /\ (leqn n q)) -> ltn (addn m n) (addn p q).
Axiom thm_LT_ADD2 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, ((ltn m p) /\ (ltn n q)) -> ltn (addn m n) (addn p q).
Axiom thm_LT_MULT : forall m : nat, forall n : nat, (ltn (NUMERAL O) (muln m n)) = ((ltn (NUMERAL O) m) /\ (ltn (NUMERAL O) n)).
Axiom thm_LE_MULT2 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, ((leqn m n) /\ (leqn p q)) -> leqn (muln m p) (muln n q).
Axiom thm_LT_LMULT : forall m : nat, forall n : nat, forall p : nat, ((~ (m = (NUMERAL O))) /\ (ltn n p)) -> ltn (muln m n) (muln m p).
Axiom thm_LE_MULT_LCANCEL : forall m : nat, forall n : nat, forall p : nat, (leqn (muln m n) (muln m p)) = ((m = (NUMERAL O)) \/ (leqn n p)).
Axiom thm_LE_MULT_RCANCEL : forall m : nat, forall n : nat, forall p : nat, (leqn (muln m p) (muln n p)) = ((leqn m n) \/ (p = (NUMERAL O))).
Axiom thm_LT_MULT_LCANCEL : forall m : nat, forall n : nat, forall p : nat, (ltn (muln m n) (muln m p)) = ((~ (m = (NUMERAL O))) /\ (ltn n p)).
Axiom thm_LT_MULT_RCANCEL : forall m : nat, forall n : nat, forall p : nat, (ltn (muln m p) (muln n p)) = ((ltn m n) /\ (~ (p = (NUMERAL O)))).
Axiom thm_LT_MULT2 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, ((ltn m n) /\ (ltn p q)) -> ltn (muln m p) (muln n q).
Axiom thm_LE_SQUARE_REFL : forall n : nat, leqn n (muln n n).
Axiom thm_LT_POW2_REFL : forall n : nat, ltn n (expn (NUMERAL (BIT0 (BIT1 O))) n).
Axiom thm_WLOG_LE : forall (P : nat -> nat -> Prop), ((forall m : nat, forall n : nat, (P m n) = (P n m)) /\ (forall m : nat, forall n : nat, (leqn m n) -> P m n)) -> forall m : nat, forall n : nat, P m n.
Axiom thm_WLOG_LT : forall (P : nat -> nat -> Prop), ((forall m : nat, P m m) /\ ((forall m : nat, forall n : nat, (P m n) = (P n m)) /\ (forall m : nat, forall n : nat, (ltn m n) -> P m n))) -> forall m : nat, forall y : nat, P m y.
Axiom thm_WLOG_LE_3 : forall P : nat -> nat -> nat -> Prop, ((forall x : nat, forall y : nat, forall z : nat, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : nat, forall y : nat, forall z : nat, ((leqn x y) /\ (leqn y z)) -> P x y z)) -> forall x : nat, forall y : nat, forall z : nat, P x y z.
Axiom thm_num_WF : forall P : nat -> Prop, (forall n : nat, (forall m : nat, (ltn m n) -> P m) -> P n) -> forall n : nat, P n.
Axiom thm_num_WOP : forall P : nat -> Prop, (exists n : nat, P n) = (exists n : nat, (P n) /\ (forall m : nat, (ltn m n) -> ~ (P m))).
Axiom thm_num_MAX : forall P : nat -> Prop, ((exists x : nat, P x) /\ (exists M : nat, forall x : nat, (P x) -> leqn x M)) = (exists m : nat, (P m) /\ (forall x : nat, (P x) -> leqn x m)).
Axiom thm_LE_INDUCT : forall P : nat -> nat -> Prop, ((forall m : nat, P m m) /\ (forall m : nat, forall n : nat, ((leqn m n) /\ (P m n)) -> P m (S n))) -> forall m : nat, forall n : nat, (leqn m n) -> P m n.
Axiom thm_num_INDUCTION_DOWN : forall P : nat -> Prop, forall m : nat, ((forall n : nat, (leqn m n) -> P n) /\ (forall n : nat, ((ltn n m) /\ (P (addn n (NUMERAL (BIT1 O))))) -> P n)) -> forall n : nat, P n.
Axiom thm_EVEN : ((even (NUMERAL O)) = True) /\ (forall n : nat, (even (S n)) = (~ (even n))).
Axiom thm_ODD : ((oddn (NUMERAL O)) = False) /\ (forall n : nat, (oddn (S n)) = (~ (oddn n))).
Axiom thm_NOT_EVEN : forall n : nat, (~ (even n)) = (oddn n).
Axiom thm_NOT_ODD : forall n : nat, (~ (oddn n)) = (even n).
Axiom thm_EVEN_OR_ODD : forall n : nat, (even n) \/ (oddn n).
Axiom thm_EVEN_AND_ODD : forall n : nat, ~ ((even n) /\ (oddn n)).
Axiom thm_EVEN_ADD : forall m : nat, forall n : nat, (even (addn m n)) = ((even m) = (even n)).
Axiom thm_EVEN_MULT : forall m : nat, forall n : nat, (even (muln m n)) = ((even m) \/ (even n)).
Axiom thm_EVEN_EXP : forall m : nat, forall n : nat, (even (expn m n)) = ((even m) /\ (~ (n = (NUMERAL O)))).
Axiom thm_ODD_ADD : forall m : nat, forall n : nat, (oddn (addn m n)) = (~ ((oddn m) = (oddn n))).
Axiom thm_ODD_MULT : forall m : nat, forall n : nat, (oddn (muln m n)) = ((oddn m) /\ (oddn n)).
Axiom thm_ODD_EXP : forall m : nat, forall n : nat, (oddn (expn m n)) = ((oddn m) \/ (n = (NUMERAL O))).
Axiom thm_EVEN_DOUBLE : forall n : nat, even (muln (NUMERAL (BIT0 (BIT1 O))) n).
Axiom thm_ODD_DOUBLE : forall n : nat, oddn (S (muln (NUMERAL (BIT0 (BIT1 O))) n)).
Axiom thm_EVEN_EXISTS_LEMMA : forall n : nat, ((even n) -> exists m : nat, n = (muln (NUMERAL (BIT0 (BIT1 O))) m)) /\ ((~ (even n)) -> exists m : nat, n = (S (muln (NUMERAL (BIT0 (BIT1 O))) m))).
Axiom thm_EVEN_EXISTS : forall n : nat, (even n) = (exists m : nat, n = (muln (NUMERAL (BIT0 (BIT1 O))) m)).
Axiom thm_ODD_EXISTS : forall n : nat, (oddn n) = (exists m : nat, n = (S (muln (NUMERAL (BIT0 (BIT1 O))) m))).
Axiom thm_EVEN_ODD_DECOMPOSITION : forall n : nat, (exists k : nat, exists m : nat, (oddn m) /\ (n = (muln (expn (NUMERAL (BIT0 (BIT1 O))) k) m))) = (~ (n = (NUMERAL O))).
Axiom thm_SUB : (forall m : nat, (subn m (NUMERAL O)) = m) /\ (forall m : nat, forall n : nat, (subn m (S n)) = (predn (subn m n))).
Axiom thm_SUB_0 : forall m : nat, ((subn (NUMERAL O) m) = (NUMERAL O)) /\ ((subn m (NUMERAL O)) = m).
Axiom thm_SUB_PRESUC : forall m : nat, forall n : nat, (predn (subn (S m) n)) = (subn m n).
Axiom thm_SUB_SUC : forall m : nat, forall n : nat, (subn (S m) (S n)) = (subn m n).
Axiom thm_SUB_REFL : forall n : nat, (subn n n) = (NUMERAL O).
Axiom thm_ADD_SUB : forall m : nat, forall n : nat, (subn (addn m n) n) = m.
Axiom thm_ADD_SUB2 : forall m : nat, forall n : nat, (subn (addn m n) m) = n.
Axiom thm_SUB_EQ_0 : forall m : nat, forall n : nat, ((subn m n) = (NUMERAL O)) = (leqn m n).
Axiom thm_ADD_SUBR2 : forall m : nat, forall n : nat, (subn m (addn m n)) = (NUMERAL O).
Axiom thm_ADD_SUBR : forall m : nat, forall n : nat, (subn n (addn m n)) = (NUMERAL O).
Axiom thm_SUB_ADD : forall m : nat, forall n : nat, (leqn n m) -> (addn (subn m n) n) = m.
Axiom thm_SUB_ADD_LCANCEL : forall m : nat, forall n : nat, forall p : nat, (subn (addn m n) (addn m p)) = (subn n p).
Axiom thm_SUB_ADD_RCANCEL : forall m : nat, forall n : nat, forall p : nat, (subn (addn m p) (addn n p)) = (subn m n).
Axiom thm_LEFT_SUB_DISTRIB : forall m : nat, forall n : nat, forall p : nat, (muln m (subn n p)) = (subn (muln m n) (muln m p)).
Axiom thm_RIGHT_SUB_DISTRIB : forall m : nat, forall n : nat, forall p : nat, (muln (subn m n) p) = (subn (muln m p) (muln n p)).
Axiom thm_SUC_SUB1 : forall n : nat, (subn (S n) (NUMERAL (BIT1 O))) = n.
Axiom thm_EVEN_SUB : forall m : nat, forall n : nat, (even (subn m n)) = ((leqn m n) \/ ((even m) = (even n))).
Axiom thm_ODD_SUB : forall m : nat, forall n : nat, (oddn (subn m n)) = ((ltn n m) /\ (~ ((oddn m) = (oddn n)))).
Axiom thm_FACT : ((factorial (NUMERAL O)) = (NUMERAL (BIT1 O))) /\ (forall n : nat, (factorial (S n)) = (muln (S n) (factorial n))).
Axiom thm_FACT_LT : forall n : nat, ltn (NUMERAL O) (factorial n).
Axiom thm_FACT_LE : forall n : nat, leqn (NUMERAL (BIT1 O)) (factorial n).
Axiom thm_FACT_NZ : forall n : nat, ~ ((factorial n) = (NUMERAL O)).
Axiom thm_FACT_MONO : forall m : nat, forall n : nat, (leqn m n) -> leqn (factorial m) (factorial n).
Axiom thm_EXP_LT_0 : forall n : nat, forall x : nat, (ltn (NUMERAL O) (expn x n)) = ((~ (x = (NUMERAL O))) \/ (n = (NUMERAL O))).
Axiom thm_LT_EXP : forall x : nat, forall m : nat, forall n : nat, (ltn (expn x m) (expn x n)) = (((leqn (NUMERAL (BIT0 (BIT1 O))) x) /\ (ltn m n)) \/ ((x = (NUMERAL O)) /\ ((~ (m = (NUMERAL O))) /\ (n = (NUMERAL O))))).
Axiom thm_LE_EXP : forall x : nat, forall m : nat, forall n : nat, (leqn (expn x m) (expn x n)) = (@COND Prop (x = (NUMERAL O)) ((m = (NUMERAL O)) -> n = (NUMERAL O)) ((x = (NUMERAL (BIT1 O))) \/ (leqn m n))).
Axiom thm_EQ_EXP : forall x : nat, forall m : nat, forall n : nat, ((expn x m) = (expn x n)) = (@COND Prop (x = (NUMERAL O)) ((m = (NUMERAL O)) = (n = (NUMERAL O))) ((x = (NUMERAL (BIT1 O))) \/ (m = n))).
Axiom thm_EXP_MONO_LE_IMP : forall x : nat, forall y : nat, forall n : nat, (leqn x y) -> leqn (expn x n) (expn y n).
Axiom thm_EXP_MONO_LT_IMP : forall x : nat, forall y : nat, forall n : nat, ((ltn x y) /\ (~ (n = (NUMERAL O)))) -> ltn (expn x n) (expn y n).
Axiom thm_EXP_MONO_LE : forall x : nat, forall y : nat, forall n : nat, (leqn (expn x n) (expn y n)) = ((leqn x y) \/ (n = (NUMERAL O))).
Axiom thm_EXP_MONO_LT : forall x : nat, forall y : nat, forall n : nat, (ltn (expn x n) (expn y n)) = ((ltn x y) /\ (~ (n = (NUMERAL O)))).
Axiom thm_EXP_MONO_EQ : forall x : nat, forall y : nat, forall n : nat, ((expn x n) = (expn y n)) = ((x = y) \/ (n = (NUMERAL O))).
Axiom thm_DIVMOD_EXIST : forall m : nat, forall n : nat, (~ (n = (NUMERAL O))) -> exists q : nat, exists r : nat, (m = (addn (muln q n) r)) /\ (ltn r n).
Axiom thm_DIVMOD_EXIST_0 : forall m : nat, forall n : nat, exists q : nat, exists r : nat, @COND Prop (n = (NUMERAL O)) ((q = (NUMERAL O)) /\ (r = m)) ((m = (addn (muln q n) r)) /\ (ltn r n)).
Axiom thm_DIVISION : forall m : nat, forall n : nat, (~ (n = (NUMERAL O))) -> (m = (addn (muln (divn m n) n) (modn m n))) /\ (ltn (modn m n) n).
Axiom thm_DIV_ZERO : forall n : nat, (divn n (NUMERAL O)) = (NUMERAL O).
Axiom thm_MOD_ZERO : forall n : nat, (modn n (NUMERAL O)) = n.
Axiom thm_DIVISION_SIMP : (forall m : nat, forall n : nat, (addn (muln (divn m n) n) (modn m n)) = m) /\ (forall m : nat, forall n : nat, (addn (muln n (divn m n)) (modn m n)) = m).
Axiom thm_EQ_DIVMOD : forall p : nat, forall m : nat, forall n : nat, (((divn m p) = (divn n p)) /\ ((modn m p) = (modn n p))) = (m = n).
Axiom thm_MOD_LT_EQ : forall m : nat, forall n : nat, (ltn (modn m n) n) = (~ (n = (NUMERAL O))).
Axiom thm_MOD_LT_EQ_LT : forall m : nat, forall n : nat, (ltn (modn m n) n) = (ltn (NUMERAL O) n).
Axiom thm_DIVMOD_UNIQ_LEMMA : forall m : nat, forall n : nat, forall q1 : nat, forall r1 : nat, forall q2 : nat, forall r2 : nat, (((m = (addn (muln q1 n) r1)) /\ (ltn r1 n)) /\ ((m = (addn (muln q2 n) r2)) /\ (ltn r2 n))) -> (q1 = q2) /\ (r1 = r2).
Axiom thm_DIVMOD_UNIQ : forall m : nat, forall n : nat, forall q : nat, forall r : nat, ((m = (addn (muln q n) r)) /\ (ltn r n)) -> ((divn m n) = q) /\ ((modn m n) = r).
Axiom thm_MOD_UNIQ : forall m : nat, forall n : nat, forall q : nat, forall r : nat, ((m = (addn (muln q n) r)) /\ (ltn r n)) -> (modn m n) = r.
Axiom thm_DIV_UNIQ : forall m : nat, forall n : nat, forall q : nat, forall r : nat, ((m = (addn (muln q n) r)) /\ (ltn r n)) -> (divn m n) = q.
Axiom thm_MOD_0 : forall n : nat, (modn (NUMERAL O) n) = (NUMERAL O).
Axiom thm_DIV_0 : forall n : nat, (divn (NUMERAL O) n) = (NUMERAL O).
Axiom thm_MOD_MULT : forall m : nat, forall n : nat, (modn (muln m n) m) = (NUMERAL O).
Axiom thm_DIV_MULT : forall m : nat, forall n : nat, (~ (m = (NUMERAL O))) -> (divn (muln m n) m) = n.
Axiom thm_MOD_LT : forall m : nat, forall n : nat, (ltn m n) -> (modn m n) = m.
Axiom thm_MOD_EQ_SELF : forall m : nat, forall n : nat, ((modn m n) = m) = ((n = (NUMERAL O)) \/ (ltn m n)).
Axiom thm_MOD_CASES : forall n : nat, forall p : nat, (ltn n (muln (NUMERAL (BIT0 (BIT1 O))) p)) -> (modn n p) = (@COND nat (ltn n p) n (subn n p)).
Axiom thm_MOD_ADD_CASES : forall m : nat, forall n : nat, forall p : nat, ((ltn m p) /\ (ltn n p)) -> (modn (addn m n) p) = (@COND nat (ltn (addn m n) p) (addn m n) (subn (addn m n) p)).
Axiom thm_MOD_EQ : forall m : nat, forall n : nat, forall p : nat, forall q : nat, (m = (addn n (muln q p))) -> (modn m p) = (modn n p).
Axiom thm_DIV_LE : forall m : nat, forall n : nat, leqn (divn m n) m.
Axiom thm_DIV_MUL_LE : forall m : nat, forall n : nat, leqn (muln n (divn m n)) m.
Axiom thm_MOD_LE_TWICE : forall m : nat, forall n : nat, ((ltn (NUMERAL O) m) /\ (leqn m n)) -> leqn (muln (NUMERAL (BIT0 (BIT1 O))) (modn n m)) n.
Axiom thm_MOD_1 : forall n : nat, (modn n (NUMERAL (BIT1 O))) = (NUMERAL O).
Axiom thm_DIV_1 : forall n : nat, (divn n (NUMERAL (BIT1 O))) = n.
Axiom thm_DIV_LT : forall m : nat, forall n : nat, (ltn m n) -> (divn m n) = (NUMERAL O).
Axiom thm_MOD_MOD : forall m : nat, forall n : nat, forall p : nat, (modn (modn m (muln n p)) n) = (modn m n).
Axiom thm_MOD_MOD_REFL : forall m : nat, forall n : nat, (modn (modn m n) n) = (modn m n).
Axiom thm_MOD_MOD_LE : forall m : nat, forall n : nat, forall p : nat, ((~ (n = (NUMERAL O))) /\ (leqn n p)) -> (modn (modn m n) p) = (modn m n).
Axiom thm_MOD_EVEN_2 : forall m : nat, forall n : nat, (even n) -> (modn (modn m n) (NUMERAL (BIT0 (BIT1 O)))) = (modn m (NUMERAL (BIT0 (BIT1 O)))).
Axiom thm_DIV_MULT2 : forall m : nat, forall n : nat, forall p : nat, (~ (m = (NUMERAL O))) -> (divn (muln m n) (muln m p)) = (divn n p).
Axiom thm_MOD_MULT2 : forall m : nat, forall n : nat, forall p : nat, (modn (muln m n) (muln m p)) = (muln m (modn n p)).
Axiom thm_MOD_EXISTS : forall m : nat, forall n : nat, (exists q : nat, m = (muln n q)) = (@COND Prop (n = (NUMERAL O)) (m = (NUMERAL O)) ((modn m n) = (NUMERAL O))).
Axiom thm_LE_RDIV_EQ : forall a : nat, forall b : nat, forall n : nat, (~ (a = (NUMERAL O))) -> (leqn n (divn b a)) = (leqn (muln a n) b).
Axiom thm_RDIV_LT_EQ : forall a : nat, forall b : nat, forall n : nat, (~ (a = (NUMERAL O))) -> (ltn (divn b a) n) = (ltn b (muln a n)).
Axiom thm_LE_LDIV_EQ : forall a : nat, forall b : nat, forall n : nat, (~ (a = (NUMERAL O))) -> (leqn (divn b a) n) = (ltn b (muln a (addn n (NUMERAL (BIT1 O))))).
Axiom thm_LDIV_LT_EQ : forall a : nat, forall b : nat, forall n : nat, (~ (a = (NUMERAL O))) -> (ltn n (divn b a)) = (leqn (muln a (addn n (NUMERAL (BIT1 O)))) b).
Axiom thm_LE_LDIV : forall a : nat, forall b : nat, forall n : nat, ((~ (a = (NUMERAL O))) /\ (leqn b (muln a n))) -> leqn (divn b a) n.
Axiom thm_DIV_MONO : forall m : nat, forall n : nat, forall p : nat, (leqn m n) -> leqn (divn m p) (divn n p).
Axiom thm_DIV_MONO_LT : forall m : nat, forall n : nat, forall p : nat, ((~ (p = (NUMERAL O))) /\ (leqn (addn m p) n)) -> ltn (divn m p) (divn n p).
Axiom thm_DIV_EQ_0 : forall m : nat, forall n : nat, (~ (n = (NUMERAL O))) -> ((divn m n) = (NUMERAL O)) = (ltn m n).
Axiom thm_MOD_DIV_EQ_0 : forall m : nat, forall n : nat, (~ (n = (NUMERAL O))) -> (divn (modn m n) n) = (NUMERAL O).
Axiom thm_MOD_EQ_0 : forall m : nat, forall n : nat, ((modn m n) = (NUMERAL O)) = (exists q : nat, m = (muln q n)).
Axiom thm_DIV_EQ_SELF : forall m : nat, forall n : nat, ((divn m n) = m) = ((m = (NUMERAL O)) \/ (n = (NUMERAL (BIT1 O)))).
Axiom thm_MOD_REFL : forall n : nat, (modn n n) = (NUMERAL O).
Axiom thm_EVEN_MOD : forall n : nat, (even n) = ((modn n (NUMERAL (BIT0 (BIT1 O)))) = (NUMERAL O)).
Axiom thm_ODD_MOD : forall n : nat, (oddn n) = ((modn n (NUMERAL (BIT0 (BIT1 O)))) = (NUMERAL (BIT1 O))).
Axiom thm_MOD_2_CASES : forall n : nat, (modn n (NUMERAL (BIT0 (BIT1 O)))) = (@COND nat (even n) (NUMERAL O) (NUMERAL (BIT1 O))).
Axiom thm_EVEN_MOD_EVEN : forall m : nat, forall n : nat, (even n) -> (even (modn m n)) = (even m).
Axiom thm_ODD_MOD_EVEN : forall m : nat, forall n : nat, (even n) -> (oddn (modn m n)) = (oddn m).
Axiom thm_HALF_DOUBLE : (forall n : nat, (divn (muln (NUMERAL (BIT0 (BIT1 O))) n) (NUMERAL (BIT0 (BIT1 O)))) = n) /\ (forall n : nat, (divn (muln n (NUMERAL (BIT0 (BIT1 O)))) (NUMERAL (BIT0 (BIT1 O)))) = n).
Axiom thm_DOUBLE_HALF : (forall n : nat, (even n) -> (muln (NUMERAL (BIT0 (BIT1 O))) (divn n (NUMERAL (BIT0 (BIT1 O))))) = n) /\ (forall n : nat, (even n) -> (muln (divn n (NUMERAL (BIT0 (BIT1 O)))) (NUMERAL (BIT0 (BIT1 O)))) = n).
Axiom thm_MOD_MULT_RMOD : forall m : nat, forall n : nat, forall p : nat, (modn (muln m (modn p n)) n) = (modn (muln m p) n).
Axiom thm_MOD_MULT_LMOD : forall m : nat, forall n : nat, forall p : nat, (modn (muln (modn m n) p) n) = (modn (muln m p) n).
Axiom thm_MOD_MULT_MOD2 : forall m : nat, forall n : nat, forall p : nat, (modn (muln (modn m n) (modn p n)) n) = (modn (muln m p) n).
Axiom thm_MOD_EXP_MOD : forall m : nat, forall n : nat, forall p : nat, (modn (expn (modn m n) p) n) = (modn (expn m p) n).
Axiom thm_MOD_MULT_ADD : (forall m : nat, forall n : nat, forall p : nat, (modn (addn (muln m n) p) n) = (modn p n)) /\ ((forall m : nat, forall n : nat, forall p : nat, (modn (addn (muln n m) p) n) = (modn p n)) /\ ((forall m : nat, forall n : nat, forall p : nat, (modn (addn p (muln m n)) n) = (modn p n)) /\ (forall m : nat, forall n : nat, forall p : nat, (modn (addn p (muln n m)) n) = (modn p n)))).
Axiom thm_DIV_MULT_ADD : (forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL O))) -> (divn (addn (muln a n) b) n) = (addn a (divn b n))) /\ ((forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL O))) -> (divn (addn (muln n a) b) n) = (addn a (divn b n))) /\ ((forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL O))) -> (divn (addn b (muln a n)) n) = (addn (divn b n) a)) /\ (forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL O))) -> (divn (addn b (muln n a)) n) = (addn (divn b n) a)))).
Axiom thm_MOD_ADD_MOD : forall a : nat, forall b : nat, forall n : nat, (modn (addn (modn a n) (modn b n)) n) = (modn (addn a b) n).
Axiom thm_DIV_ADD_MOD : forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL O))) -> ((modn (addn a b) n) = (addn (modn a n) (modn b n))) = ((divn (addn a b) n) = (addn (divn a n) (divn b n))).
Axiom thm_MOD_ADD_EQ_EQ : forall n : nat, forall x : nat, forall y : nat, ((modn (addn x y) n) = (addn (modn x n) (modn y n))) = ((n = (NUMERAL O)) \/ (ltn (addn (modn x n) (modn y n)) n)).
Axiom thm_DIV_ADD_EQ_EQ : forall n : nat, forall x : nat, forall y : nat, ((divn (addn x y) n) = (addn (divn x n) (divn y n))) = ((n = (NUMERAL O)) \/ (ltn (addn (modn x n) (modn y n)) n)).
Axiom thm_DIV_ADD_EQ : forall n : nat, forall x : nat, forall y : nat, (ltn (addn (modn x n) (modn y n)) n) -> (divn (addn x y) n) = (addn (divn x n) (divn y n)).
Axiom thm_MOD_ADD_EQ : forall n : nat, forall x : nat, forall y : nat, (ltn (addn (modn x n) (modn y n)) n) -> (modn (addn x y) n) = (addn (modn x n) (modn y n)).
Axiom thm_DIV_REFL : forall n : nat, (~ (n = (NUMERAL O))) -> (divn n n) = (NUMERAL (BIT1 O)).
Axiom thm_MOD_LE : forall m : nat, forall n : nat, leqn (modn m n) m.
Axiom thm_DIV_MONO2 : forall m : nat, forall n : nat, forall p : nat, ((~ (p = (NUMERAL O))) /\ (leqn p m)) -> leqn (divn n m) (divn n p).
Axiom thm_DIV_LE_EXCLUSION : forall a : nat, forall b : nat, forall c : nat, forall d : nat, ((~ (b = (NUMERAL O))) /\ (ltn (muln b c) (muln (addn a (NUMERAL (BIT1 O))) d))) -> leqn (divn c d) (divn a b).
Axiom thm_DIV_EQ_EXCLUSION : forall a : nat, forall b : nat, forall c : nat, forall d : nat, ((ltn (muln b c) (muln (addn a (NUMERAL (BIT1 O))) d)) /\ (ltn (muln a d) (muln (addn c (NUMERAL (BIT1 O))) b))) -> (divn a b) = (divn c d).
Axiom thm_MULT_DIV_LE : forall m : nat, forall n : nat, forall p : nat, leqn (muln m (divn n p)) (divn (muln m n) p).
Axiom thm_DIV_DIV : forall m : nat, forall n : nat, forall p : nat, (divn (divn m n) p) = (divn m (muln n p)).
Axiom thm_DIV_MOD : forall m : nat, forall n : nat, forall p : nat, (modn (divn m n) p) = (divn (modn m (muln n p)) n).
Axiom thm_MOD_MULT_MOD : forall m : nat, forall n : nat, forall p : nat, (modn m (muln n p)) = (addn (muln n (modn (divn m n) p)) (modn m n)).
Axiom thm_MOD_MOD_EXP_MIN : forall x : nat, forall p : nat, forall m : nat, forall n : nat, (modn (modn x (expn p m)) (expn p n)) = (modn x (expn p (minn m n))).
Axiom thm_MOD_EXP : forall m : nat, forall n : nat, forall p : nat, (~ (m = (NUMERAL O))) -> (modn (expn m n) (expn m p)) = (@COND nat ((leqn p n) \/ (m = (NUMERAL (BIT1 O)))) (NUMERAL O) (expn m n)).
Axiom thm_DIV_EXP : forall m : nat, forall n : nat, forall p : nat, (~ (m = (NUMERAL O))) -> (divn (expn m n) (expn m p)) = (@COND nat (leqn p n) (expn m (subn n p)) (@COND nat (m = (NUMERAL (BIT1 O))) (NUMERAL (BIT1 O)) (NUMERAL O))).
Axiom thm_FORALL_LT_MOD_THM : forall P : nat -> Prop, forall n : nat, (forall a : nat, (ltn a n) -> P a) = ((n = (NUMERAL O)) \/ (forall a : nat, P (modn a n))).
Axiom thm_FORALL_MOD_THM : forall P : nat -> Prop, forall n : nat, (~ (n = (NUMERAL O))) -> (forall a : nat, P (modn a n)) = (forall a : nat, (ltn a n) -> P a).
Axiom thm_EXISTS_LT_MOD_THM : forall P : nat -> Prop, forall n : nat, (exists a : nat, (ltn a n) /\ (P a)) = ((~ (n = (NUMERAL O))) /\ (exists a : nat, P (modn a n))).
Axiom thm_EXISTS_MOD_THM : forall P : nat -> Prop, forall n : nat, (~ (n = (NUMERAL O))) -> (exists a : nat, P (modn a n)) = (exists a : nat, (ltn a n) /\ (P a)).
Axiom thm_PRE_ELIM_THM : forall (n : nat) (P : nat -> Prop), (P (predn n)) = (forall m : nat, ((n = (S m)) \/ ((m = (NUMERAL O)) /\ (n = (NUMERAL O)))) -> P m).
Axiom thm_SUB_ELIM_THM : forall (a : nat) (b : nat) (P : nat -> Prop), (P (subn a b)) = (forall d : nat, ((a = (addn b d)) \/ ((ltn a b) /\ (d = (NUMERAL O)))) -> P d).
Axiom thm_DIVMOD_ELIM_THM : forall (m : nat) (n : nat) (P : nat -> nat -> Prop), (P (divn m n) (modn m n)) = (forall q : nat, forall r : nat, (((n = (NUMERAL O)) /\ ((q = (NUMERAL O)) /\ (r = m))) \/ ((m = (addn (muln q n) r)) /\ (ltn r n))) -> P q r).
Axiom thm_minimal : forall P : nat -> Prop, (minimal P) = (@ε nat (fun n : nat => (P n) /\ (forall m : nat, (ltn m n) -> ~ (P m)))).
Axiom thm_MINIMAL : forall P : nat -> Prop, (exists n : nat, P n) = ((P (minimal P)) /\ (forall m : nat, (ltn m (minimal P)) -> ~ (P m))).
Axiom thm_MINIMAL_UNIQUE : forall P : nat -> Prop, forall n : nat, ((P n) /\ (forall m : nat, (ltn m n) -> ~ (P m))) -> (minimal P) = n.
Axiom thm_LE_MINIMAL : forall P : nat -> Prop, forall n : nat, (exists r : nat, P r) -> (leqn n (minimal P)) = (forall i : nat, (P i) -> leqn n i).
Axiom thm_MINIMAL_LE : forall P : nat -> Prop, forall n : nat, (exists r : nat, P r) -> (leqn (minimal P) n) = (exists i : nat, (leqn i n) /\ (P i)).
Axiom thm_MINIMAL_UBOUND : forall P : nat -> Prop, forall n : nat, (P n) -> leqn (minimal P) n.
Axiom thm_MINIMAL_LBOUND : forall P : nat -> Prop, forall n : nat, ((exists r : nat, P r) /\ (forall m : nat, (ltn m n) -> ~ (P m))) -> leqn n (minimal P).
Axiom thm_MINIMAL_MONO : forall P : nat -> Prop, forall Q : nat -> Prop, ((exists n : nat, P n) /\ (forall n : nat, (P n) -> Q n)) -> leqn (minimal Q) (minimal P).
Axiom thm_TRANSITIVE_STEPWISE_LT_EQ : forall R' : nat -> nat -> Prop, (forall x : nat, forall y : nat, forall z : nat, ((R' x y) /\ (R' y z)) -> R' x z) -> (forall m : nat, forall n : nat, (ltn m n) -> R' m n) = (forall n : nat, R' n (S n)).
Axiom thm_TRANSITIVE_STEPWISE_LT : forall R' : nat -> nat -> Prop, ((forall x : nat, forall y : nat, forall z : nat, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall n : nat, R' n (S n))) -> forall m : nat, forall n : nat, (ltn m n) -> R' m n.
Axiom thm_TRANSITIVE_STEPWISE_LE_EQ : forall R' : nat -> nat -> Prop, ((forall x : nat, R' x x) /\ (forall x : nat, forall y : nat, forall z : nat, ((R' x y) /\ (R' y z)) -> R' x z)) -> (forall m : nat, forall n : nat, (leqn m n) -> R' m n) = (forall n : nat, R' n (S n)).
Axiom thm_TRANSITIVE_STEPWISE_LE : forall R' : nat -> nat -> Prop, ((forall x : nat, R' x x) /\ ((forall x : nat, forall y : nat, forall z : nat, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall n : nat, R' n (S n)))) -> forall m : nat, forall n : nat, (leqn m n) -> R' m n.
Axiom thm_DEPENDENT_CHOICE_FIXED : forall {A : Type'}, forall P : nat -> A -> Prop, forall R' : nat -> A -> A -> Prop, forall a : A, ((P (NUMERAL O) a) /\ (forall n : nat, forall x : A, (P n x) -> exists y : A, (P (S n) y) /\ (R' n x y))) -> exists f : nat -> A, ((f (NUMERAL O)) = a) /\ ((forall n : nat, P n (f n)) /\ (forall n : nat, R' n (f n) (f (S n)))).
Axiom thm_DEPENDENT_CHOICE : forall {A : Type'}, forall P : nat -> A -> Prop, forall R' : nat -> A -> A -> Prop, ((exists a : A, P (NUMERAL O) a) /\ (forall n : nat, forall x : A, (P n x) -> exists y : A, (P (S n) y) /\ (R' n x y))) -> exists f : nat -> A, (forall n : nat, P n (f n)) /\ (forall n : nat, R' n (f n) (f (S n))).
Axiom thm_WF : forall {A : Type'}, forall lt2 : A -> A -> Prop, (@well_founded A lt2) = (forall P : A -> Prop, (exists x : A, P x) -> exists x : A, (P x) /\ (forall y : A, (lt2 y x) -> ~ (P y))).
Axiom thm_WF_EQ : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = (forall P : A -> Prop, (exists x : A, P x) = (exists x : A, (P x) /\ (forall y : A, (lt2 y x) -> ~ (P y)))).
Axiom thm_WF_IND : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = (forall P : A -> Prop, (forall x : A, (forall y : A, (lt2 y x) -> P y) -> P x) -> forall x : A, P x).
Axiom thm_WF_DCHAIN : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = (~ (exists s : nat -> A, forall n : nat, lt2 (s (S n)) (s n))).
Axiom thm_WF_DHAIN_TRANSITIVE : forall {A : Type'}, forall lt2 : A -> A -> Prop, (forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z) -> (@well_founded A lt2) = (~ (exists s : nat -> A, forall i : nat, forall j : nat, (ltn i j) -> lt2 (s j) (s i))).
Axiom thm_WF_UREC : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> forall f : A -> B, forall g : A -> B, ((forall x : A, (f x) = (H f x)) /\ (forall x : A, (g x) = (H g x))) -> f = g.
Axiom thm_WF_UREC_WF : forall {A : Type'} (lt2 : A -> A -> Prop), (forall H : (A -> Prop) -> A -> Prop, (forall f : A -> Prop, forall g : A -> Prop, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> forall f : A -> Prop, forall g : A -> Prop, ((forall x : A, (f x) = (H f x)) /\ (forall x : A, (g x) = (H g x))) -> f = g) -> @well_founded A lt2.
Axiom thm_WF_REC_INVARIANT : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, forall S' : A -> B -> Prop, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> ((f z) = (g z)) /\ (S' z (f z))) -> ((H f x) = (H g x)) /\ (S' x (H f x))) -> exists f : A -> B, forall x : A, (f x) = (H f x).
Axiom thm_WF_REC : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> exists f : A -> B, forall x : A, (f x) = (H f x).
Axiom thm_WF_REC_WF : forall {A : Type'} (lt2 : A -> A -> Prop), (forall H : (A -> nat) -> A -> nat, (forall f : A -> nat, forall g : A -> nat, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> exists f : A -> nat, forall x : A, (f x) = (H f x)) -> @well_founded A lt2.
Axiom thm_WF_EREC : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> @ex1 (A -> B) (fun f : A -> B => forall x : A, (f x) = (H f x)).
Axiom thm_WF_REC_EXISTS : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall P : (A -> B) -> A -> B -> Prop, ((forall f : A -> B, forall g : A -> B, forall x : A, forall y : B, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (P f x y) = (P g x y)) /\ (forall f : A -> B, forall x : A, (forall z : A, (lt2 z x) -> P f z (f z)) -> exists y : B, P f x y)) -> exists f : A -> B, forall x : A, P f x (f x).
Axiom thm_WF_SUBSET : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall lt3 : A -> A -> Prop, ((forall x : A, forall y : A, (lt2 x y) -> lt3 x y) /\ (@well_founded A lt3)) -> @well_founded A lt2.
Axiom thm_WF_RESTRICT : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall P : A -> Prop, (@well_founded A lt2) -> @well_founded A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (lt2 x y))).
Axiom thm_WF_MEASURE_GEN : forall {A B : Type'}, forall lt2 : B -> B -> Prop, forall m : A -> B, (@well_founded B lt2) -> @well_founded A (fun x : A => fun x' : A => lt2 (m x) (m x')).
Axiom thm_WF_LEX_DEPENDENT : forall {A B : Type'}, forall R' : A -> A -> Prop, forall S' : A -> B -> B -> Prop, ((@well_founded A R') /\ (forall a : A, @well_founded B (S' a))) -> @well_founded (prod A B) (@GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall r1 : A, forall s1 : B, @eq ((prod A B) -> Prop) (f (@pair A B r1 s1)) (@GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall r2 : A, forall s2 : B, @eq Prop (f' (@pair A B r2 s2)) ((R' r1 r2) \/ ((r1 = r2) /\ (S' r1 s1 s2))))))).
Axiom thm_WF_LEX : forall {A B : Type'}, forall R' : A -> A -> Prop, forall S' : B -> B -> Prop, ((@well_founded A R') /\ (@well_founded B S')) -> @well_founded (prod A B) (@GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall r1 : A, forall s1 : B, @eq ((prod A B) -> Prop) (f (@pair A B r1 s1)) (@GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall r2 : A, forall s2 : B, @eq Prop (f' (@pair A B r2 s2)) ((R' r1 r2) \/ ((r1 = r2) /\ (S' s1 s2))))))).
Axiom thm_WF_POINTWISE : forall {A B : Type'} (lt2 : A -> A -> Prop) (lt3 : B -> B -> Prop), ((@well_founded A lt2) /\ (@well_founded B lt3)) -> @well_founded (prod A B) (@GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall x1 : A, forall y1 : B, @eq ((prod A B) -> Prop) (f (@pair A B x1 y1)) (@GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall x2 : A, forall y2 : B, @eq Prop (f' (@pair A B x2 y2)) ((lt2 x1 x2) /\ (lt3 y1 y2)))))).
Axiom thm_WF_num : @well_founded nat ltn.
Axiom thm_WF_REC_num : forall {A : Type'}, forall H : (nat -> A) -> nat -> A, (forall f : nat -> A, forall g : nat -> A, forall n : nat, (forall m : nat, (ltn m n) -> (f m) = (g m)) -> (H f n) = (H g n)) -> exists f : nat -> A, forall n : nat, (f n) = (H f n).
Axiom thm_MEASURE : forall {A : Type'}, forall m : A -> nat, (@MEASURE A m) = (fun x : A => fun y : A => ltn (m x) (m y)).
Axiom thm_WF_MEASURE : forall {A : Type'}, forall m : A -> nat, @well_founded A (@MEASURE A m).
Axiom thm_MEASURE_LE : forall {A : Type'} (a : A) (b : A), forall m : A -> nat, (forall y : A, (@MEASURE A m y a) -> @MEASURE A m y b) = (leqn (m a) (m b)).
Axiom thm_WF_ANTISYM : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall x : A, forall y : A, (@well_founded A lt2) -> ~ ((lt2 x y) /\ (lt2 y x)).
Axiom thm_WF_REFL : forall {A : Type'} (lt2 : A -> A -> Prop), forall x : A, (@well_founded A lt2) -> ~ (lt2 x x).
Axiom thm_WF_FALSE : forall {A : Type'}, @well_founded A (fun x : A => fun y : A => False).
Axiom thm_MINIMAL_BAD_SEQUENCE : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall bad : (nat -> A) -> Prop, ((@well_founded A lt2) /\ ((forall x : nat -> A, (~ (bad x)) -> exists n : nat, forall y : nat -> A, (forall k : nat, (ltn k n) -> (y k) = (x k)) -> ~ (bad y)) /\ (exists x : nat -> A, bad x))) -> exists y : nat -> A, (bad y) /\ (forall z : nat -> A, forall n : nat, ((bad z) /\ (forall k : nat, (ltn k n) -> (z k) = (y k))) -> ~ (lt2 (z n) (y n))).
Axiom thm_WF_REC_TAIL : forall {A B : Type'}, forall P : A -> Prop, forall g : A -> A, forall h : A -> B, exists f : A -> B, forall x : A, (f x) = (@COND B (P x) (f (g x)) (h x)).
Axiom thm_WF_REC_TAIL_GENERAL : forall {A B : Type'} (lt2 : A -> A -> Prop), forall P : (A -> B) -> A -> Prop, forall G : (A -> B) -> A -> A, forall H : (A -> B) -> A -> B, ((@well_founded A lt2) /\ ((forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> ((P f x) = (P g x)) /\ (((G f x) = (G g x)) /\ ((H f x) = (H g x)))) /\ ((forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) /\ (forall f : A -> B, forall x : A, forall y : A, ((P f x) /\ (lt2 y (G f x))) -> lt2 y x)))) -> exists f : A -> B, forall x : A, (f x) = (@COND B (P f x) (f (G f x)) (H f x)).
Axiom thm_ARITH_ZERO : ((NUMERAL (NUMERAL O)) = (NUMERAL O)) /\ ((BIT0 O) = O).
Axiom thm_BIT0_0 : (BIT0 (NUMERAL O)) = (NUMERAL O).
Axiom thm_BIT1_0 : (BIT1 (NUMERAL O)) = (NUMERAL (BIT1 O)).
Axiom thm_ARITH_SUC : (forall n : nat, (S (NUMERAL n)) = (NUMERAL (S n))) /\ (((S O) = (BIT1 O)) /\ ((forall n : nat, (S (BIT0 n)) = (BIT1 n)) /\ (forall n : nat, (S (BIT1 n)) = (BIT0 (S n))))).
Axiom thm_ARITH_PRE : (forall n : nat, (predn (NUMERAL n)) = (NUMERAL (predn n))) /\ (((predn O) = O) /\ ((forall n : nat, (predn (BIT0 n)) = (@COND nat (n = O) O (BIT1 (predn n)))) /\ (forall n : nat, (predn (BIT1 n)) = (BIT0 n)))).
Axiom thm_ARITH_ADD : (forall m : nat, forall n : nat, (addn (NUMERAL m) (NUMERAL n)) = (NUMERAL (addn m n))) /\ (((addn O O) = O) /\ ((forall n : nat, (addn O (BIT0 n)) = (BIT0 n)) /\ ((forall n : nat, (addn O (BIT1 n)) = (BIT1 n)) /\ ((forall n : nat, (addn (BIT0 n) O) = (BIT0 n)) /\ ((forall n : nat, (addn (BIT1 n) O) = (BIT1 n)) /\ ((forall m : nat, forall n : nat, (addn (BIT0 m) (BIT0 n)) = (BIT0 (addn m n))) /\ ((forall m : nat, forall n : nat, (addn (BIT0 m) (BIT1 n)) = (BIT1 (addn m n))) /\ ((forall m : nat, forall n : nat, (addn (BIT1 m) (BIT0 n)) = (BIT1 (addn m n))) /\ (forall m : nat, forall n : nat, (addn (BIT1 m) (BIT1 n)) = (BIT0 (S (addn m n)))))))))))).
Axiom thm_ARITH_MULT : (forall m : nat, forall n : nat, (muln (NUMERAL m) (NUMERAL n)) = (NUMERAL (muln m n))) /\ (((muln O O) = O) /\ ((forall n : nat, (muln O (BIT0 n)) = O) /\ ((forall n : nat, (muln O (BIT1 n)) = O) /\ ((forall n : nat, (muln (BIT0 n) O) = O) /\ ((forall n : nat, (muln (BIT1 n) O) = O) /\ ((forall m : nat, forall n : nat, (muln (BIT0 m) (BIT0 n)) = (BIT0 (BIT0 (muln m n)))) /\ ((forall m : nat, forall n : nat, (muln (BIT0 m) (BIT1 n)) = (addn (BIT0 m) (BIT0 (BIT0 (muln m n))))) /\ ((forall m : nat, forall n : nat, (muln (BIT1 m) (BIT0 n)) = (addn (BIT0 n) (BIT0 (BIT0 (muln m n))))) /\ (forall m : nat, forall n : nat, (muln (BIT1 m) (BIT1 n)) = (addn (BIT1 m) (addn (BIT0 n) (BIT0 (BIT0 (muln m n)))))))))))))).
Axiom thm_ARITH_EXP : (forall m : nat, forall n : nat, (expn (NUMERAL m) (NUMERAL n)) = (NUMERAL (expn m n))) /\ (((expn O O) = (BIT1 O)) /\ ((forall m : nat, (expn (BIT0 m) O) = (BIT1 O)) /\ ((forall m : nat, (expn (BIT1 m) O) = (BIT1 O)) /\ ((forall n : nat, (expn O (BIT0 n)) = (muln (expn O n) (expn O n))) /\ ((forall m : nat, forall n : nat, (expn (BIT0 m) (BIT0 n)) = (muln (expn (BIT0 m) n) (expn (BIT0 m) n))) /\ ((forall m : nat, forall n : nat, (expn (BIT1 m) (BIT0 n)) = (muln (expn (BIT1 m) n) (expn (BIT1 m) n))) /\ ((forall n : nat, (expn O (BIT1 n)) = O) /\ ((forall m : nat, forall n : nat, (expn (BIT0 m) (BIT1 n)) = (muln (BIT0 m) (muln (expn (BIT0 m) n) (expn (BIT0 m) n)))) /\ (forall m : nat, forall n : nat, (expn (BIT1 m) (BIT1 n)) = (muln (BIT1 m) (muln (expn (BIT1 m) n) (expn (BIT1 m) n)))))))))))).
Axiom thm_ARITH_EVEN : (forall n : nat, (even (NUMERAL n)) = (even n)) /\ (((even O) = True) /\ ((forall n : nat, (even (BIT0 n)) = True) /\ (forall n : nat, (even (BIT1 n)) = False))).
Axiom thm_ARITH_ODD : (forall n : nat, (oddn (NUMERAL n)) = (oddn n)) /\ (((oddn O) = False) /\ ((forall n : nat, (oddn (BIT0 n)) = False) /\ (forall n : nat, (oddn (BIT1 n)) = True))).
Axiom thm_ARITH_LE : (forall m : nat, forall n : nat, (leqn (NUMERAL m) (NUMERAL n)) = (leqn m n)) /\ (((leqn O O) = True) /\ ((forall n : nat, (leqn (BIT0 n) O) = (leqn n O)) /\ ((forall n : nat, (leqn (BIT1 n) O) = False) /\ ((forall n : nat, (leqn O (BIT0 n)) = True) /\ ((forall n : nat, (leqn O (BIT1 n)) = True) /\ ((forall m : nat, forall n : nat, (leqn (BIT0 m) (BIT0 n)) = (leqn m n)) /\ ((forall m : nat, forall n : nat, (leqn (BIT0 m) (BIT1 n)) = (leqn m n)) /\ ((forall m : nat, forall n : nat, (leqn (BIT1 m) (BIT0 n)) = (ltn m n)) /\ (forall m : nat, forall n : nat, (leqn (BIT1 m) (BIT1 n)) = (leqn m n)))))))))).
Axiom thm_ARITH_LT : (forall m : nat, forall n : nat, (ltn (NUMERAL m) (NUMERAL n)) = (ltn m n)) /\ (((ltn O O) = False) /\ ((forall n : nat, (ltn (BIT0 n) O) = False) /\ ((forall n : nat, (ltn (BIT1 n) O) = False) /\ ((forall n : nat, (ltn O (BIT0 n)) = (ltn O n)) /\ ((forall n : nat, (ltn O (BIT1 n)) = True) /\ ((forall m : nat, forall n : nat, (ltn (BIT0 m) (BIT0 n)) = (ltn m n)) /\ ((forall m : nat, forall n : nat, (ltn (BIT0 m) (BIT1 n)) = (leqn m n)) /\ ((forall m : nat, forall n : nat, (ltn (BIT1 m) (BIT0 n)) = (ltn m n)) /\ (forall m : nat, forall n : nat, (ltn (BIT1 m) (BIT1 n)) = (ltn m n)))))))))).
Axiom thm_ARITH_EQ : (forall m : nat, forall n : nat, ((NUMERAL m) = (NUMERAL n)) = (m = n)) /\ (((O = O) = True) /\ ((forall n : nat, ((BIT0 n) = O) = (n = O)) /\ ((forall n : nat, ((BIT1 n) = O) = False) /\ ((forall n : nat, (O = (BIT0 n)) = (O = n)) /\ ((forall n : nat, (O = (BIT1 n)) = False) /\ ((forall m : nat, forall n : nat, ((BIT0 m) = (BIT0 n)) = (m = n)) /\ ((forall m : nat, forall n : nat, ((BIT0 m) = (BIT1 n)) = False) /\ ((forall m : nat, forall n : nat, ((BIT1 m) = (BIT0 n)) = False) /\ (forall m : nat, forall n : nat, ((BIT1 m) = (BIT1 n)) = (m = n)))))))))).
Axiom thm_ARITH_SUB : (forall m : nat, forall n : nat, (subn (NUMERAL m) (NUMERAL n)) = (NUMERAL (subn m n))) /\ (((subn O O) = O) /\ ((forall n : nat, (subn O (BIT0 n)) = O) /\ ((forall n : nat, (subn O (BIT1 n)) = O) /\ ((forall n : nat, (subn (BIT0 n) O) = (BIT0 n)) /\ ((forall n : nat, (subn (BIT1 n) O) = (BIT1 n)) /\ ((forall m : nat, forall n : nat, (subn (BIT0 m) (BIT0 n)) = (BIT0 (subn m n))) /\ ((forall m : nat, forall n : nat, (subn (BIT0 m) (BIT1 n)) = (predn (BIT0 (subn m n)))) /\ ((forall m : nat, forall n : nat, (subn (BIT1 m) (BIT0 n)) = (@COND nat (leqn n m) (BIT1 (subn m n)) O)) /\ (forall m : nat, forall n : nat, (subn (BIT1 m) (BIT1 n)) = (BIT0 (subn m n))))))))))).
Axiom thm_EXP_2_NE_0 : forall n : nat, ~ ((expn (NUMERAL (BIT0 (BIT1 O))) n) = (NUMERAL O)).
Axiom thm_INJ_INVERSE2 : forall {A B C : Type'}, forall P : A -> B -> C, (forall x1 : A, forall y1 : B, forall x2 : A, forall y2 : B, ((P x1 y1) = (P x2 y2)) = ((x1 = x2) /\ (y1 = y2))) -> exists X : C -> A, exists Y : C -> B, forall x : A, forall y : B, ((X (P x y)) = x) /\ ((Y (P x y)) = y).
Axiom thm_NUMPAIR : forall x : nat, forall y : nat, (NUMPAIR x y) = (muln (expn (NUMERAL (BIT0 (BIT1 O))) x) (addn (muln (NUMERAL (BIT0 (BIT1 O))) y) (NUMERAL (BIT1 O)))).
Axiom thm_NUMPAIR_INJ_LEMMA : forall x1 : nat, forall y1 : nat, forall x2 : nat, forall y2 : nat, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) -> x1 = x2.
Axiom thm_NUMPAIR_INJ : forall x1 : nat, forall y1 : nat, forall x2 : nat, forall y2 : nat, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((x1 = x2) /\ (y1 = y2)).
Axiom thm_NUMSUM : forall b : Prop, forall x : nat, (NUMSUM b x) = (@COND nat b (S (muln (NUMERAL (BIT0 (BIT1 O))) x)) (muln (NUMERAL (BIT0 (BIT1 O))) x)).
Axiom thm_NUMSUM_INJ : forall b1 : Prop, forall x1 : nat, forall b2 : Prop, forall x2 : nat, ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = ((b1 = b2) /\ (x1 = x2)).
Axiom thm_INJN : forall {A : Type'}, forall m : nat, (@INJN A m) = (fun n : nat => fun a : A => n = m).
Axiom thm_INJN_INJ : forall {A : Type'}, forall n1 : nat, forall n2 : nat, ((@INJN A n1) = (@INJN A n2)) = (n1 = n2).
Axiom thm_INJA : forall {A : Type'}, forall a : A, (@INJA A a) = (fun n : nat => fun b : A => b = a).
Axiom thm_INJA_INJ : forall {A : Type'}, forall a1 : A, forall a2 : A, ((@INJA A a1) = (@INJA A a2)) = (a1 = a2).
Axiom thm_INJF : forall {A : Type'}, forall f : nat -> nat -> A -> Prop, (@INJF A f) = (fun n : nat => f (NUMFST n) (NUMSND n)).
Axiom thm_INJF_INJ : forall {A : Type'}, forall f1 : nat -> nat -> A -> Prop, forall f2 : nat -> nat -> A -> Prop, ((@INJF A f1) = (@INJF A f2)) = (f1 = f2).
Axiom thm_INJP : forall {A : Type'}, forall f1 : nat -> A -> Prop, forall f2 : nat -> A -> Prop, (@INJP A f1 f2) = (fun n : nat => fun a : A => @COND Prop (NUMLEFT n) (f1 (NUMRIGHT n) a) (f2 (NUMRIGHT n) a)).
Axiom thm_INJP_INJ : forall {A : Type'}, forall f1 : nat -> A -> Prop, forall f1' : nat -> A -> Prop, forall f2 : nat -> A -> Prop, forall f2' : nat -> A -> Prop, ((@INJP A f1 f2) = (@INJP A f1' f2')) = ((f1 = f1') /\ (f2 = f2')).
Axiom thm_ZCONSTR : forall {A : Type'}, forall c : nat, forall i : A, forall r : nat -> nat -> A -> Prop, (@ZCONSTR A c i r) = (@INJP A (@INJN A (S c)) (@INJP A (@INJA A i) (@INJF A r))).
Axiom thm_ZBOT : forall {A : Type'}, (@ZBOT A) = (@INJP A (@INJN A (NUMERAL O)) (@ε (nat -> A -> Prop) (fun z : nat -> A -> Prop => True))).
Axiom thm_ZCONSTR_ZBOT : forall {A : Type'}, forall c : nat, forall i : A, forall r : nat -> nat -> A -> Prop, ~ ((@ZCONSTR A c i r) = (@ZBOT A)).
Axiom thm_ZRECSPACE_RULES : forall {A : Type'}, (@ZRECSPACE A (@ZBOT A)) /\ (forall c : nat, forall i : A, forall r : nat -> nat -> A -> Prop, (forall n : nat, @ZRECSPACE A (r n)) -> @ZRECSPACE A (@ZCONSTR A c i r)).
Axiom thm_ZRECSPACE_CASES : forall {A : Type'}, forall a : nat -> A -> Prop, (@ZRECSPACE A a) = ((a = (@ZBOT A)) \/ (exists c : nat, exists i : A, exists r : nat -> nat -> A -> Prop, (a = (@ZCONSTR A c i r)) /\ (forall n : nat, @ZRECSPACE A (r n)))).
Axiom thm_ZRECSPACE_INDUCT : forall {A : Type'}, forall ZRECSPACE' : (nat -> A -> Prop) -> Prop, ((ZRECSPACE' (@ZBOT A)) /\ (forall c : nat, forall i : A, forall r : nat -> nat -> A -> Prop, (forall n : nat, ZRECSPACE' (r n)) -> ZRECSPACE' (@ZCONSTR A c i r))) -> forall a : nat -> A -> Prop, (@ZRECSPACE A a) -> ZRECSPACE' a.
Axiom thm_BOTTOM : forall {A : Type'}, (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
Axiom thm_CONSTR : forall {A : Type'}, forall c : nat, forall i : A, forall r : nat -> recspace A, (@CONSTR A c i r) = (@_mk_rec A (@ZCONSTR A c i (fun n : nat => @_dest_rec A (r n)))).
Axiom thm_MK_REC_INJ : forall {A : Type'}, forall x : nat -> A -> Prop, forall y : nat -> A -> Prop, ((@_mk_rec A x) = (@_mk_rec A y)) -> ((@ZRECSPACE A x) /\ (@ZRECSPACE A y)) -> x = y.
Axiom thm_DEST_REC_INJ : forall {A : Type'}, forall x : recspace A, forall y : recspace A, ((@_dest_rec A x) = (@_dest_rec A y)) = (x = y).
Axiom thm_CONSTR_BOT : forall {A : Type'}, forall c : nat, forall i : A, forall r : nat -> recspace A, ~ ((@CONSTR A c i r) = (@BOTTOM A)).
Axiom thm_CONSTR_INJ : forall {A : Type'}, forall c1 : nat, forall i1 : A, forall r1 : nat -> recspace A, forall c2 : nat, forall i2 : A, forall r2 : nat -> recspace A, ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = ((c1 = c2) /\ ((i1 = i2) /\ (r1 = r2))).
Axiom thm_CONSTR_IND : forall {A : Type'}, forall P : (recspace A) -> Prop, ((P (@BOTTOM A)) /\ (forall c : nat, forall i : A, forall r : nat -> recspace A, (forall n : nat, P (r n)) -> P (@CONSTR A c i r))) -> forall x : recspace A, P x.
Axiom thm_CONSTR_REC : forall {A B : Type'}, forall Fn : nat -> A -> (nat -> recspace A) -> (nat -> B) -> B, exists f : (recspace A) -> B, forall c : nat, forall i : A, forall r : nat -> recspace A, (f (@CONSTR A c i r)) = (Fn c i r (fun n : nat => f (r n))).
Axiom thm_FCONS : forall {A : Type'}, (forall a : A, forall f : nat -> A, (@FCONS A a f (NUMERAL O)) = a) /\ (forall a : A, forall f : nat -> A, forall n : nat, (@FCONS A a f (S n)) = (f n)).
Axiom thm_FCONS_UNDO : forall {A : Type'}, forall f : nat -> A, f = (@FCONS A (f (NUMERAL O)) (@o nat nat A f S)).
Axiom thm_FNIL : forall {A : Type'}, forall n : nat, (@FNIL A n) = (@ε A (fun x : A => True)).
Axiom thm_sum_INDUCT : forall {A B : Type'}, forall P : (Datatypes.sum A B) -> Prop, ((forall a : A, P (@inl A B a)) /\ (forall a : B, P (@inr A B a))) -> forall x : Datatypes.sum A B, P x.
Axiom thm_sum_RECURSION : forall {A B Z' : Type'}, forall INL' : A -> Z', forall INR' : B -> Z', exists fn : (Datatypes.sum A B) -> Z', (forall a : A, (fn (@inl A B a)) = (INL' a)) /\ (forall a : B, (fn (@inr A B a)) = (INR' a)).
Axiom thm_OUTL : forall {A B : Type'} (x : A), (@OUTL A B (@inl A B x)) = x.
Axiom thm_OUTR : forall {A B : Type'} (y : B), (@OUTR A B (@inr A B y)) = y.
Axiom thm_option_INDUCT : forall {A : Type'}, forall P : (option A) -> Prop, ((P (@None A)) /\ (forall a : A, P (@Some A a))) -> forall x : option A, P x.
Axiom thm_option_RECURSION : forall {A Z' : Type'}, forall NONE' : Z', forall SOME' : A -> Z', exists fn : (option A) -> Z', ((fn (@None A)) = NONE') /\ (forall a : A, (fn (@Some A a)) = (SOME' a)).
Axiom thm_list_INDUCT : forall {A : Type'}, forall P : (seq A) -> Prop, ((P (@nil A)) /\ (forall a0 : A, forall a1 : seq A, (P a1) -> P (@cons A a0 a1))) -> forall x : seq A, P x.
Axiom thm_list_RECURSION : forall {A Z' : Type'}, forall NIL' : Z', forall CONS' : A -> (seq A) -> Z' -> Z', exists fn : (seq A) -> Z', ((fn (@nil A)) = NIL') /\ (forall a0 : A, forall a1 : seq A, (fn (@cons A a0 a1)) = (CONS' a0 a1 (fn a1))).
Axiom thm_FORALL_OPTION_THM : forall {A : Type'}, forall P : (option A) -> Prop, (forall x : option A, P x) = ((P (@None A)) /\ (forall a : A, P (@Some A a))).
Axiom thm_EXISTS_OPTION_THM : forall {A : Type'}, forall P : (option A) -> Prop, (exists x : option A, P x) = ((P (@None A)) \/ (exists a : A, P (@Some A a))).
Axiom thm_option_DISTINCT : forall {A : Type'}, forall a : A, ~ ((@Some A a) = (@None A)).
Axiom thm_option_INJ : forall {A : Type'}, forall a : A, forall b : A, ((@Some A a) = (@Some A b)) = (a = b).
Axiom thm_ISO : forall {A B : Type'}, forall g : B -> A, forall f : A -> B, (@cancel2 A B f g) = ((forall x : B, (f (g x)) = x) /\ (forall y : A, (g (f y)) = y)).
Axiom thm_ISO_REFL : forall {A : Type'}, @cancel2 A A (fun x : A => x) (fun x : A => x).
Axiom thm_ISO_FUN : forall {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A'), ((@cancel2 A A' f f') /\ (@cancel2 B B' g g')) -> @cancel2 (A -> B) (A' -> B') (fun h : A -> B => fun a' : A' => g (h (f' a'))) (fun h : A' -> B' => fun a : A => g' (h (f a))).
Axiom thm_ISO_USAGE : forall {A B : Type'} (g : B -> A) (f : A -> B), (@cancel2 A B f g) -> (forall P : A -> Prop, (forall x : A, P x) = (forall x : B, P (g x))) /\ ((forall P : A -> Prop, (exists x : A, P x) = (exists x : B, P (g x))) /\ (forall a : A, forall b : B, (a = (g b)) = ((f a) = b))).
Axiom thm_HD : forall {A : Type'} (t : seq A) (h : A), (@HD A (@cons A h t)) = h.
Axiom thm_TL : forall {A : Type'} (h : A) (t : seq A), (@TL A (@cons A h t)) = t.
Axiom thm_APPEND : forall {A : Type'}, (forall l : seq A, (@cat A (@nil A) l) = l) /\ (forall h : A, forall t : seq A, forall l : seq A, (@cat A (@cons A h t) l) = (@cons A h (@cat A t l))).
Axiom thm_REVERSE : forall {A : Type'} (l : seq A) (x : A), ((@rev A (@nil A)) = (@nil A)) /\ ((@rev A (@cons A x l)) = (@cat A (@rev A l) (@cons A x (@nil A)))).
Axiom thm_LENGTH : forall {A : Type'}, ((@size A (@nil A)) = (NUMERAL O)) /\ (forall h : A, forall t : seq A, (@size A (@cons A h t)) = (S (@size A t))).
Axiom thm_MAP : forall {A B : Type'}, (forall f : A -> B, (@map A B f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : seq A, (@map A B f (@cons A h t)) = (@cons B (f h) (@map A B f t))).
Axiom thm_LAST : forall {A : Type'} (h : A) (t : seq A), (@LAST A (@cons A h t)) = (@COND A (t = (@nil A)) h (@LAST A t)).
Axiom thm_BUTLAST : forall {A : Type'} (h : A) (t : seq A), ((@BUTLAST A (@nil A)) = (@nil A)) /\ ((@BUTLAST A (@cons A h t)) = (@COND (seq A) (t = (@nil A)) (@nil A) (@cons A h (@BUTLAST A t)))).
Axiom thm_REPLICATE : forall {A : Type'} (n : nat) (x : A), ((@nseq A (NUMERAL O) x) = (@nil A)) /\ ((@nseq A (S n) x) = (@cons A x (@nseq A n x))).
Axiom thm_NULL : forall {A : Type'} (h : A) (t : seq A), ((@NULL A (@nil A)) = True) /\ ((@NULL A (@cons A h t)) = False).
Axiom thm_ALL : forall {A : Type'} (h : A) (P : A -> Prop) (t : seq A), ((@ALL A P (@nil A)) = True) /\ ((@ALL A P (@cons A h t)) = ((P h) /\ (@ALL A P t))).
Axiom thm_EX : forall {A : Type'} (h : A) (P : A -> Prop) (t : seq A), ((@EX A P (@nil A)) = False) /\ ((@EX A P (@cons A h t)) = ((P h) \/ (@EX A P t))).
Axiom thm_ITLIST : forall {A B : Type'} (h : A) (f : A -> B -> B) (t : seq A) (b : B), ((@ITLIST A B f (@nil A) b) = b) /\ ((@ITLIST A B f (@cons A h t) b) = (f h (@ITLIST A B f t b))).
Axiom thm_MEM : forall {A : Type'} (h : A) (x : A) (t : seq A), ((@MEM A x (@nil A)) = False) /\ ((@MEM A x (@cons A h t)) = ((x = h) \/ (@MEM A x t))).
Axiom thm_ALL2_DEF : forall {A B : Type'} (h1' : A) (P : A -> B -> Prop) (t1 : seq A) (l2 : seq B), ((@ALL2 A B P (@nil A) l2) = (l2 = (@nil B))) /\ ((@ALL2 A B P (@cons A h1' t1) l2) = (@COND Prop (l2 = (@nil B)) False ((P h1' (@HD B l2)) /\ (@ALL2 A B P t1 (@TL B l2))))).
Axiom thm_ALL2 : forall {A B : Type'} (h1' : A) (h2' : B) (P : A -> B -> Prop) (t1 : seq A) (t2 : seq B), ((@ALL2 A B P (@nil A) (@nil B)) = True) /\ (((@ALL2 A B P (@cons A h1' t1) (@nil B)) = False) /\ (((@ALL2 A B P (@nil A) (@cons B h2' t2)) = False) /\ ((@ALL2 A B P (@cons A h1' t1) (@cons B h2' t2)) = ((P h1' h2') /\ (@ALL2 A B P t1 t2))))).
Axiom thm_MAP2_DEF : forall {A B C : Type'} (h1' : A) (f : A -> B -> C) (t1 : seq A) (l : seq B), ((@MAP2 A B C f (@nil A) l) = (@nil C)) /\ ((@MAP2 A B C f (@cons A h1' t1) l) = (@cons C (f h1' (@HD B l)) (@MAP2 A B C f t1 (@TL B l)))).
Axiom thm_MAP2 : forall {A B C : Type'} (h1' : A) (h2' : B) (f : A -> B -> C) (t1 : seq A) (t2 : seq B), ((@MAP2 A B C f (@nil A) (@nil B)) = (@nil C)) /\ ((@MAP2 A B C f (@cons A h1' t1) (@cons B h2' t2)) = (@cons C (f h1' h2') (@MAP2 A B C f t1 t2))).
Axiom thm_EL : forall {A : Type'} (n : nat) (l : seq A), ((@EL A (NUMERAL O) l) = (@HD A l)) /\ ((@EL A (S n) l) = (@EL A n (@TL A l))).
Axiom thm_FILTER : forall {A : Type'} (h : A) (P : A -> Prop) (t : seq A), ((@FILTER A P (@nil A)) = (@nil A)) /\ ((@FILTER A P (@cons A h t)) = (@COND (seq A) (P h) (@cons A h (@FILTER A P t)) (@FILTER A P t))).
Axiom thm_ASSOC : forall {A B : Type'} (h : prod A B) (a : A) (t : seq (prod A B)), (@ASSOC A B a (@cons (prod A B) h t)) = (@COND B ((@fst A B h) = a) (@snd A B h) (@ASSOC A B a t)).
Axiom thm_ITLIST2_DEF : forall {A B C : Type'} (h1' : A) (f : A -> B -> C -> C) (t1 : seq A) (l2 : seq B) (b : C), ((@ITLIST2 A B C f (@nil A) l2 b) = b) /\ ((@ITLIST2 A B C f (@cons A h1' t1) l2 b) = (f h1' (@HD B l2) (@ITLIST2 A B C f t1 (@TL B l2) b))).
Axiom thm_ITLIST2 : forall {A B C : Type'} (h1' : A) (h2' : B) (f : A -> B -> C -> C) (t1 : seq A) (t2 : seq B) (b : C), ((@ITLIST2 A B C f (@nil A) (@nil B) b) = b) /\ ((@ITLIST2 A B C f (@cons A h1' t1) (@cons B h2' t2) b) = (f h1' h2' (@ITLIST2 A B C f t1 t2 b))).
Axiom thm_ZIP_DEF : forall {A B : Type'} (h1' : A) (t1 : seq A) (l2 : seq B), ((@ZIP A B (@nil A) l2) = (@nil (prod A B))) /\ ((@ZIP A B (@cons A h1' t1) l2) = (@cons (prod A B) (@pair A B h1' (@HD B l2)) (@ZIP A B t1 (@TL B l2)))).
Axiom thm_ZIP : forall {A B : Type'} (h1' : A) (h2' : B) (t1 : seq A) (t2 : seq B), ((@ZIP A B (@nil A) (@nil B)) = (@nil (prod A B))) /\ ((@ZIP A B (@cons A h1' t1) (@cons B h2' t2)) = (@cons (prod A B) (@pair A B h1' h2') (@ZIP A B t1 t2))).
Axiom thm_ALLPAIRS : forall {A B : Type'} (h : A) (f : A -> B -> Prop) (t : seq A) (l : seq B), ((@ALLPAIRS A B f (@nil A) l) = True) /\ ((@ALLPAIRS A B f (@cons A h t) l) = ((@ALL B (f h) l) /\ (@ALLPAIRS A B f t l))).
Axiom thm_PAIRWISE : forall {A : Type'} (h : A) (r : A -> A -> Prop) (t : seq A), ((@PAIRWISE A r (@nil A)) = True) /\ ((@PAIRWISE A r (@cons A h t)) = ((@ALL A (r h) t) /\ (@PAIRWISE A r t))).
Axiom thm_list_of_seq : forall {A : Type'} (s : nat -> A) (n : nat), ((@mkseq A s (NUMERAL O)) = (@nil A)) /\ ((@mkseq A s (S n)) = (@cat A (@mkseq A s n) (@cons A (s n) (@nil A)))).
Axiom thm_NOT_CONS_NIL : forall {A : Type'}, forall h : A, forall t : seq A, ~ ((@cons A h t) = (@nil A)).
Axiom thm_LAST_CLAUSES : forall {A : Type'} (h : A) (k : A) (t : seq A), ((@LAST A (@cons A h (@nil A))) = h) /\ ((@LAST A (@cons A h (@cons A k t))) = (@LAST A (@cons A k t))).
Axiom thm_APPEND_NIL : forall {A : Type'}, forall l : seq A, (@cat A l (@nil A)) = l.
Axiom thm_APPEND_ASSOC : forall {A : Type'}, forall l : seq A, forall m : seq A, forall n : seq A, (@cat A l (@cat A m n)) = (@cat A (@cat A l m) n).
Axiom thm_REVERSE_APPEND : forall {A : Type'}, forall l : seq A, forall m : seq A, (@rev A (@cat A l m)) = (@cat A (@rev A m) (@rev A l)).
Axiom thm_REVERSE_REVERSE : forall {A : Type'}, forall l : seq A, (@rev A (@rev A l)) = l.
Axiom thm_REVERSE_EQ_EMPTY : forall {A : Type'}, forall l : seq A, ((@rev A l) = (@nil A)) = (l = (@nil A)).
Axiom thm_CONS_11 : forall {A : Type'}, forall h1' : A, forall h2' : A, forall t1 : seq A, forall t2 : seq A, ((@cons A h1' t1) = (@cons A h2' t2)) = ((h1' = h2') /\ (t1 = t2)).
Axiom thm_list_CASES : forall {A : Type'}, forall l : seq A, (l = (@nil A)) \/ (exists h : A, exists t : seq A, l = (@cons A h t)).
Axiom thm_LIST_EQ : forall {A : Type'}, forall l1 : seq A, forall l2 : seq A, (l1 = l2) = (((@size A l1) = (@size A l2)) /\ (forall n : nat, (ltn n (@size A l2)) -> (@EL A n l1) = (@EL A n l2))).
Axiom thm_LENGTH_APPEND : forall {A : Type'}, forall l : seq A, forall m : seq A, (@size A (@cat A l m)) = (addn (@size A l) (@size A m)).
Axiom thm_MAP_APPEND : forall {A B : Type'}, forall f : A -> B, forall l1 : seq A, forall l2 : seq A, (@map A B f (@cat A l1 l2)) = (@cat B (@map A B f l1) (@map A B f l2)).
Axiom thm_LENGTH_MAP : forall {A B : Type'}, forall l : seq A, forall f : A -> B, (@size B (@map A B f l)) = (@size A l).
Axiom thm_LENGTH_EQ_NIL : forall {A : Type'}, forall l : seq A, ((@size A l) = (NUMERAL O)) = (l = (@nil A)).
Axiom thm_LENGTH_EQ_CONS : forall {A : Type'}, forall l : seq A, forall n : nat, ((@size A l) = (S n)) = (exists h : A, exists t : seq A, (l = (@cons A h t)) /\ ((@size A t) = n)).
Axiom thm_LENGTH_REVERSE : forall {A : Type'}, forall l : seq A, (@size A (@rev A l)) = (@size A l).
Axiom thm_MAP_o : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall l : seq A, (@map A C (@o A B C g f) l) = (@map B C g (@map A B f l)).
Axiom thm_MAP_EQ : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, forall l : seq A, (@ALL A (fun x : A => (f x) = (g x)) l) -> (@map A B f l) = (@map A B g l).
Axiom thm_ALL_IMP : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : seq A, ((forall x : A, ((@MEM A x l) /\ (P x)) -> Q x) /\ (@ALL A P l)) -> @ALL A Q l.
Axiom thm_NOT_EX : forall {A : Type'}, forall P : A -> Prop, forall l : seq A, (~ (@EX A P l)) = (@ALL A (fun x : A => ~ (P x)) l).
Axiom thm_NOT_ALL : forall {A : Type'}, forall P : A -> Prop, forall l : seq A, (~ (@ALL A P l)) = (@EX A (fun x : A => ~ (P x)) l).
Axiom thm_ALL_MAP : forall {A B : Type'}, forall P : B -> Prop, forall f : A -> B, forall l : seq A, (@ALL B P (@map A B f l)) = (@ALL A (@o A B Prop P f) l).
Axiom thm_ALL_EQ : forall {A : Type'} (R' : A -> Prop) (P : A -> Prop) (Q : A -> Prop), forall l : seq A, ((@ALL A R' l) /\ (forall x : A, (R' x) -> (P x) = (Q x))) -> (@ALL A P l) = (@ALL A Q l).
Axiom thm_ALL_T : forall {A : Type'}, forall l : seq A, @ALL A (fun x : A => True) l.
Axiom thm_MAP_EQ_ALL2 : forall {A B : Type'}, forall f : A -> B, forall l : seq A, forall m : seq A, (@ALL2 A A (fun x : A => fun y : A => (f x) = (f y)) l m) -> (@map A B f l) = (@map A B f m).
Axiom thm_ALL2_MAP : forall {A B : Type'}, forall P : B -> A -> Prop, forall f : A -> B, forall l : seq A, (@ALL2 B A P (@map A B f l) l) = (@ALL A (fun a : A => P (f a) a) l).
Axiom thm_MAP_EQ_DEGEN : forall {A : Type'}, forall l : seq A, forall f : A -> A, (@ALL A (fun x : A => (f x) = x) l) -> (@map A A f l) = l.
Axiom thm_ALL2_AND_RIGHT : forall {A B : Type'}, forall l : seq A, forall m : seq B, forall P : A -> Prop, forall Q : A -> B -> Prop, (@ALL2 A B (fun x : A => fun y : B => (P x) /\ (Q x y)) l m) = ((@ALL A P l) /\ (@ALL2 A B Q l m)).
Axiom thm_ITLIST_APPEND : forall {A B : Type'}, forall f : A -> B -> B, forall a : B, forall l1 : seq A, forall l2 : seq A, (@ITLIST A B f (@cat A l1 l2) a) = (@ITLIST A B f l1 (@ITLIST A B f l2 a)).
Axiom thm_ITLIST_EXTRA : forall {A B : Type'} (a : A) (b : B), forall f : A -> B -> B, forall l : seq A, (@ITLIST A B f (@cat A l (@cons A a (@nil A))) b) = (@ITLIST A B f l (f a b)).
Axiom thm_ALL_MP : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : seq A, ((@ALL A (fun x : A => (P x) -> Q x) l) /\ (@ALL A P l)) -> @ALL A Q l.
Axiom thm_AND_ALL : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), forall l : seq A, ((@ALL A P l) /\ (@ALL A Q l)) = (@ALL A (fun x : A => (P x) /\ (Q x)) l).
Axiom thm_EX_IMP : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : seq A, ((forall x : A, ((@MEM A x l) /\ (P x)) -> Q x) /\ (@EX A P l)) -> @EX A Q l.
Axiom thm_ALL_MEM : forall {A : Type'}, forall P : A -> Prop, forall l : seq A, (forall x : A, (@MEM A x l) -> P x) = (@ALL A P l).
Axiom thm_LENGTH_REPLICATE : forall {A : Type'}, forall n : nat, forall x : A, (@size A (@nseq A n x)) = n.
Axiom thm_MEM_REPLICATE : forall {A : Type'}, forall n : nat, forall x : A, forall y : A, (@MEM A x (@nseq A n y)) = ((x = y) /\ (~ (n = (NUMERAL O)))).
Axiom thm_EX_MAP : forall {A B : Type'}, forall P : B -> Prop, forall f : A -> B, forall l : seq A, (@EX B P (@map A B f l)) = (@EX A (@o A B Prop P f) l).
Axiom thm_EXISTS_EX : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : seq B, (exists x : A, @EX B (P x) l) = (@EX B (fun s : B => exists x : A, P x s) l).
Axiom thm_FORALL_ALL : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : seq B, (forall x : A, @ALL B (P x) l) = (@ALL B (fun s : B => forall x : A, P x s) l).
Axiom thm_MEM_APPEND : forall {A : Type'}, forall x : A, forall l1 : seq A, forall l2 : seq A, (@MEM A x (@cat A l1 l2)) = ((@MEM A x l1) \/ (@MEM A x l2)).
Axiom thm_MEM_MAP : forall {A B : Type'}, forall f : A -> B, forall y : B, forall l : seq A, (@MEM B y (@map A B f l)) = (exists x : A, (@MEM A x l) /\ (y = (f x))).
Axiom thm_FILTER_APPEND : forall {A : Type'}, forall P : A -> Prop, forall l1 : seq A, forall l2 : seq A, (@FILTER A P (@cat A l1 l2)) = (@cat A (@FILTER A P l1) (@FILTER A P l2)).
Axiom thm_FILTER_MAP : forall {A B : Type'}, forall P : B -> Prop, forall f : A -> B, forall l : seq A, (@FILTER B P (@map A B f l)) = (@map A B f (@FILTER A (@o A B Prop P f) l)).
Axiom thm_MEM_FILTER : forall {A : Type'}, forall P : A -> Prop, forall l : seq A, forall x : A, (@MEM A x (@FILTER A P l)) = ((P x) /\ (@MEM A x l)).
Axiom thm_LENGTH_FILTER : forall {A : Type'}, forall P : A -> Prop, forall l : seq A, leqn (@size A (@FILTER A P l)) (@size A l).
Axiom thm_EX_MEM : forall {A : Type'}, forall P : A -> Prop, forall l : seq A, (exists x : A, (P x) /\ (@MEM A x l)) = (@EX A P l).
Axiom thm_MAP_FST_ZIP : forall {A B : Type'}, forall l1 : seq A, forall l2 : seq B, ((@size A l1) = (@size B l2)) -> (@map (prod A B) A (@fst A B) (@ZIP A B l1 l2)) = l1.
Axiom thm_MAP_SND_ZIP : forall {A B : Type'}, forall l1 : seq A, forall l2 : seq B, ((@size A l1) = (@size B l2)) -> (@map (prod A B) B (@snd A B) (@ZIP A B l1 l2)) = l2.
Axiom thm_LENGTH_ZIP : forall {A B : Type'}, forall l1 : seq A, forall l2 : seq B, ((@size A l1) = (@size B l2)) -> (@size (prod A B) (@ZIP A B l1 l2)) = (@size B l2).
Axiom thm_MEM_ASSOC : forall {A B : Type'}, forall l : seq (prod A B), forall x : A, (@MEM (prod A B) (@pair A B x (@ASSOC A B x l)) l) = (@MEM A x (@map (prod A B) A (@fst A B) l)).
Axiom thm_ALL_APPEND : forall {A : Type'}, forall P : A -> Prop, forall l1 : seq A, forall l2 : seq A, (@ALL A P (@cat A l1 l2)) = ((@ALL A P l1) /\ (@ALL A P l2)).
Axiom thm_MEM_EL : forall {A : Type'}, forall l : seq A, forall n : nat, (ltn n (@size A l)) -> @MEM A (@EL A n l) l.
Axiom thm_MEM_EXISTS_EL : forall {A : Type'}, forall l : seq A, forall x : A, (@MEM A x l) = (exists i : nat, (ltn i (@size A l)) /\ (x = (@EL A i l))).
Axiom thm_ALL_EL : forall {A : Type'}, forall P : A -> Prop, forall l : seq A, (forall i : nat, (ltn i (@size A l)) -> P (@EL A i l)) = (@ALL A P l).
Axiom thm_ALL2_MAP2 : forall {A B C D : Type'} (P : B -> D -> Prop), forall f : A -> B, forall g : C -> D, forall l : seq A, forall m : seq C, (@ALL2 B D P (@map A B f l) (@map C D g m)) = (@ALL2 A C (fun x : A => fun y : C => P (f x) (g y)) l m).
Axiom thm_AND_ALL2 : forall {A B : Type'}, forall P : A -> B -> Prop, forall Q : A -> B -> Prop, forall l : seq A, forall m : seq B, ((@ALL2 A B P l m) /\ (@ALL2 A B Q l m)) = (@ALL2 A B (fun x : A => fun y : B => (P x y) /\ (Q x y)) l m).
Axiom thm_ALLPAIRS_SYM : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : seq A, forall m : seq B, (@ALLPAIRS A B P l m) = (@ALLPAIRS B A (fun x : B => fun y : A => P y x) m l).
Axiom thm_ALLPAIRS_MEM : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : seq A, forall m : seq B, (forall x : A, forall y : B, ((@MEM A x l) /\ (@MEM B y m)) -> P x y) = (@ALLPAIRS A B P l m).
Axiom thm_ALLPAIRS_MAP : forall {A B C D : Type'}, forall P : B -> D -> Prop, forall f : A -> B, forall g : C -> D, forall l : seq A, forall m : seq C, (@ALLPAIRS B D P (@map A B f l) (@map C D g m)) = (@ALLPAIRS A C (fun x : A => fun y : C => P (f x) (g y)) l m).
Axiom thm_ALLPAIRS_EQ : forall {A B : Type'} (R' : A -> B -> Prop) (R'' : A -> B -> Prop), forall l : seq A, forall m : seq B, forall P : A -> Prop, forall Q : B -> Prop, ((@ALL A P l) /\ ((@ALL B Q m) /\ (forall p : A, forall q : B, ((P p) /\ (Q q)) -> (R' p q) = (R'' p q)))) -> (@ALLPAIRS A B R' l m) = (@ALLPAIRS A B R'' l m).
Axiom thm_ALL2_ALL : forall {A : Type'}, forall P : A -> A -> Prop, forall l : seq A, (@ALL2 A A P l l) = (@ALL A (fun x : A => P x x) l).
Axiom thm_APPEND_EQ_NIL : forall {A : Type'}, forall l : seq A, forall m : seq A, ((@cat A l m) = (@nil A)) = ((l = (@nil A)) /\ (m = (@nil A))).
Axiom thm_APPEND_LCANCEL : forall {A : Type'}, forall l1 : seq A, forall l2 : seq A, forall l3 : seq A, ((@cat A l1 l2) = (@cat A l1 l3)) = (l2 = l3).
Axiom thm_APPEND_RCANCEL : forall {A : Type'}, forall l1 : seq A, forall l2 : seq A, forall l3 : seq A, ((@cat A l1 l3) = (@cat A l2 l3)) = (l1 = l2).
Axiom thm_LENGTH_MAP2 : forall {A B C : Type'}, forall f : A -> B -> C, forall l : seq A, forall m : seq B, ((@size A l) = (@size B m)) -> (@size C (@MAP2 A B C f l m)) = (@size B m).
Axiom thm_EL_MAP2 : forall {A B C : Type'}, forall f : A -> B -> C, forall l : seq A, forall m : seq B, forall k : nat, ((ltn k (@size A l)) /\ (ltn k (@size B m))) -> (@EL C k (@MAP2 A B C f l m)) = (f (@EL A k l) (@EL B k m)).
Axiom thm_MAP_EQ_NIL : forall {A B : Type'}, forall f : A -> B, forall l : seq A, ((@map A B f l) = (@nil B)) = (l = (@nil A)).
Axiom thm_INJECTIVE_MAP : forall {A B : Type'}, forall f : A -> B, (forall l : seq A, forall m : seq A, ((@map A B f l) = (@map A B f m)) -> l = m) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
Axiom thm_SURJECTIVE_MAP : forall {A B : Type'}, forall f : A -> B, (forall m : seq B, exists l : seq A, (@map A B f l) = m) = (forall y : B, exists x : A, (f x) = y).
Axiom thm_MAP_ID : forall {A : Type'}, forall l : seq A, (@map A A (fun x : A => x) l) = l.
Axiom thm_MAP_I : forall {A : Type'}, (@map A A (@I A)) = (@I (seq A)).
Axiom thm_BUTLAST_CLAUSES : forall {A : Type'}, ((@BUTLAST A (@nil A)) = (@nil A)) /\ ((forall a : A, (@BUTLAST A (@cons A a (@nil A))) = (@nil A)) /\ (forall a : A, forall h : A, forall t : seq A, (@BUTLAST A (@cons A a (@cons A h t))) = (@cons A a (@BUTLAST A (@cons A h t))))).
Axiom thm_BUTLAST_APPEND : forall {A : Type'}, forall l : seq A, forall m : seq A, (@BUTLAST A (@cat A l m)) = (@COND (seq A) (m = (@nil A)) (@BUTLAST A l) (@cat A l (@BUTLAST A m))).
Axiom thm_APPEND_BUTLAST_LAST : forall {A : Type'}, forall l : seq A, (~ (l = (@nil A))) -> (@cat A (@BUTLAST A l) (@cons A (@LAST A l) (@nil A))) = l.
Axiom thm_LAST_APPEND : forall {A : Type'}, forall p : seq A, forall q : seq A, (@LAST A (@cat A p q)) = (@COND A (q = (@nil A)) (@LAST A p) (@LAST A q)).
Axiom thm_LENGTH_TL : forall {A : Type'}, forall l : seq A, (~ (l = (@nil A))) -> (@size A (@TL A l)) = (subn (@size A l) (NUMERAL (BIT1 O))).
Axiom thm_LAST_REVERSE : forall {A : Type'}, forall l : seq A, (~ (l = (@nil A))) -> (@LAST A (@rev A l)) = (@HD A l).
Axiom thm_HD_REVERSE : forall {A : Type'}, forall l : seq A, (~ (l = (@nil A))) -> (@HD A (@rev A l)) = (@LAST A l).
Axiom thm_EL_APPEND : forall {A : Type'}, forall k : nat, forall l : seq A, forall m : seq A, (@EL A k (@cat A l m)) = (@COND A (ltn k (@size A l)) (@EL A k l) (@EL A (subn k (@size A l)) m)).
Axiom thm_EL_TL : forall {A : Type'} (l : seq A), forall n : nat, (@EL A n (@TL A l)) = (@EL A (addn n (NUMERAL (BIT1 O))) l).
Axiom thm_EL_CONS : forall {A : Type'}, forall n : nat, forall h : A, forall t : seq A, (@EL A n (@cons A h t)) = (@COND A (n = (NUMERAL O)) h (@EL A (subn n (NUMERAL (BIT1 O))) t)).
Axiom thm_LAST_EL : forall {A : Type'}, forall l : seq A, (~ (l = (@nil A))) -> (@LAST A l) = (@EL A (subn (@size A l) (NUMERAL (BIT1 O))) l).
Axiom thm_HD_APPEND : forall {A : Type'}, forall l : seq A, forall m : seq A, (@HD A (@cat A l m)) = (@COND A (l = (@nil A)) (@HD A m) (@HD A l)).
Axiom thm_CONS_HD_TL : forall {A : Type'}, forall l : seq A, (~ (l = (@nil A))) -> l = (@cons A (@HD A l) (@TL A l)).
Axiom thm_EL_MAP : forall {A B : Type'}, forall f : A -> B, forall n : nat, forall l : seq A, (ltn n (@size A l)) -> (@EL B n (@map A B f l)) = (f (@EL A n l)).
Axiom thm_MAP_REVERSE : forall {A B : Type'}, forall f : A -> B, forall l : seq A, (@rev B (@map A B f l)) = (@map A B f (@rev A l)).
Axiom thm_ALL_FILTER : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : seq A, (@ALL A P (@FILTER A Q l)) = (@ALL A (fun x : A => (Q x) -> P x) l).
Axiom thm_APPEND_SING : forall {A : Type'}, forall h : A, forall t : seq A, (@cat A (@cons A h (@nil A)) t) = (@cons A h t).
Axiom thm_MEM_APPEND_DECOMPOSE_LEFT : forall {A : Type'}, forall x : A, forall l : seq A, (@MEM A x l) = (exists l1 : seq A, exists l2 : seq A, (~ (@MEM A x l1)) /\ (l = (@cat A l1 (@cons A x l2)))).
Axiom thm_MEM_APPEND_DECOMPOSE : forall {A : Type'}, forall x : A, forall l : seq A, (@MEM A x l) = (exists l1 : seq A, exists l2 : seq A, l = (@cat A l1 (@cons A x l2))).
Axiom thm_PAIRWISE_APPEND : forall {A : Type'}, forall R' : A -> A -> Prop, forall l : seq A, forall m : seq A, (@PAIRWISE A R' (@cat A l m)) = ((@PAIRWISE A R' l) /\ ((@PAIRWISE A R' m) /\ (forall x : A, forall y : A, ((@MEM A x l) /\ (@MEM A y m)) -> R' x y))).
Axiom thm_PAIRWISE_MAP : forall {A B : Type'}, forall R' : B -> B -> Prop, forall f : A -> B, forall l : seq A, (@PAIRWISE B R' (@map A B f l)) = (@PAIRWISE A (fun x : A => fun y : A => R' (f x) (f y)) l).
Axiom thm_PAIRWISE_IMPLIES : forall {A : Type'}, forall R' : A -> A -> Prop, forall R'' : A -> A -> Prop, forall l : seq A, ((@PAIRWISE A R' l) /\ (forall x : A, forall y : A, ((@MEM A x l) /\ ((@MEM A y l) /\ (R' x y))) -> R'' x y)) -> @PAIRWISE A R'' l.
Axiom thm_PAIRWISE_TRANSITIVE : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall l : seq A, (forall x' : A, forall y' : A, forall z : A, ((R' x' y') /\ (R' y' z)) -> R' x' z) -> (@PAIRWISE A R' (@cons A x (@cons A y l))) = ((R' x y) /\ (@PAIRWISE A R' (@cons A y l))).
Axiom thm_LENGTH_LIST_OF_SEQ : forall {A : Type'}, forall s : nat -> A, forall n : nat, (@size A (@mkseq A s n)) = n.
Axiom thm_EL_LIST_OF_SEQ : forall {A : Type'}, forall s : nat -> A, forall m : nat, forall n : nat, (ltn m n) -> (@EL A m (@mkseq A s n)) = (s m).
Axiom thm_LIST_OF_SEQ_EQ_NIL : forall {A : Type'}, forall s : nat -> A, forall n : nat, ((@mkseq A s n) = (@nil A)) = (n = (NUMERAL O)).
Axiom thm_LIST_OF_SEQ_EQ_SELF : forall {A : Type'}, forall l : seq A, (@mkseq A (fun i : nat => @EL A i l) (@size A l)) = l.
Axiom thm_LENGTH_EQ_LIST_OF_SEQ : forall {A : Type'}, forall l : seq A, forall n : nat, ((@size A l) = n) = (l = (@mkseq A (fun i : nat => @EL A i l) n)).
Axiom thm_MAP_LIST_OF_SEQ : forall {A B : Type'}, forall f : nat -> A, forall g : A -> B, forall n : nat, (@map A B g (@mkseq A f n)) = (@mkseq B (@o nat A B g f) n).
Axiom thm_LIST_OF_SEQ : forall {A : Type'}, (forall f : nat -> A, (@mkseq A f (NUMERAL O)) = (@nil A)) /\ (forall f : nat -> A, forall n : nat, (@mkseq A f (S n)) = (@cons A (f (NUMERAL O)) (@mkseq A (@o nat nat A f S) n))).
Axiom thm_MONO_ALL : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop) (l : seq A), (forall x : A, (P x) -> Q x) -> (@ALL A P l) -> @ALL A Q l.
Axiom thm_MONO_ALL2 : forall {A B : Type'} (P : A -> B -> Prop) (Q : A -> B -> Prop) (l : seq A) (l' : seq B), (forall x : A, forall y : B, (P x y) -> Q x y) -> (@ALL2 A B P l l') -> @ALL2 A B Q l l'.
Axiom thm_char_INDUCT : forall P : Ascii.ascii -> Prop, (forall a0 : Prop, forall a1 : Prop, forall a2 : Prop, forall a3 : Prop, forall a4 : Prop, forall a5 : Prop, forall a6 : Prop, forall a7 : Prop, P (ASCII a0 a1 a2 a3 a4 a5 a6 a7)) -> forall x : Ascii.ascii, P x.
Axiom thm_char_RECURSION : forall {Z' : Type'}, forall f : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Z', exists fn : Ascii.ascii -> Z', forall a0 : Prop, forall a1 : Prop, forall a2 : Prop, forall a3 : Prop, forall a4 : Prop, forall a5 : Prop, forall a6 : Prop, forall a7 : Prop, (fn (ASCII a0 a1 a2 a3 a4 a5 a6 a7)) = (f a0 a1 a2 a3 a4 a5 a6 a7).
Axiom thm_dist : forall n : nat, forall m : nat, (dist (@pair nat nat m n)) = (addn (subn m n) (subn n m)).
Axiom thm_DIST_REFL : forall n : nat, (dist (@pair nat nat n n)) = (NUMERAL O).
Axiom thm_DIST_LZERO : forall n : nat, (dist (@pair nat nat (NUMERAL O) n)) = n.
Axiom thm_DIST_RZERO : forall n : nat, (dist (@pair nat nat n (NUMERAL O))) = n.
Axiom thm_DIST_SYM : forall m : nat, forall n : nat, (dist (@pair nat nat m n)) = (dist (@pair nat nat n m)).
Axiom thm_DIST_LADD : forall m : nat, forall p : nat, forall n : nat, (dist (@pair nat nat (addn m n) (addn m p))) = (dist (@pair nat nat n p)).
Axiom thm_DIST_RADD : forall m : nat, forall p : nat, forall n : nat, (dist (@pair nat nat (addn m p) (addn n p))) = (dist (@pair nat nat m n)).
Axiom thm_DIST_LADD_0 : forall m : nat, forall n : nat, (dist (@pair nat nat (addn m n) m)) = n.
Axiom thm_DIST_RADD_0 : forall m : nat, forall n : nat, (dist (@pair nat nat m (addn m n))) = n.
Axiom thm_DIST_LMUL : forall m : nat, forall n : nat, forall p : nat, (muln m (dist (@pair nat nat n p))) = (dist (@pair nat nat (muln m n) (muln m p))).
Axiom thm_DIST_RMUL : forall m : nat, forall n : nat, forall p : nat, (muln (dist (@pair nat nat m n)) p) = (dist (@pair nat nat (muln m p) (muln n p))).
Axiom thm_DIST_EQ_0 : forall m : nat, forall n : nat, ((dist (@pair nat nat m n)) = (NUMERAL O)) = (m = n).
Axiom thm_DIST_ELIM_THM : forall (y : nat) (x : nat) (P : nat -> Prop), (P (dist (@pair nat nat x y))) = (forall d : nat, ((x = (addn y d)) -> P d) /\ ((y = (addn x d)) -> P d)).
Axiom thm_DIST_TRIANGLE_LE : forall m : nat, forall n : nat, forall p : nat, forall q : nat, (leqn (addn (dist (@pair nat nat m n)) (dist (@pair nat nat n p))) q) -> leqn (dist (@pair nat nat m p)) q.
Axiom thm_DIST_TRIANGLES_LE : forall m : nat, forall n : nat, forall p : nat, forall q : nat, forall r : nat, forall s : nat, ((leqn (dist (@pair nat nat m n)) r) /\ (leqn (dist (@pair nat nat p q)) s)) -> leqn (dist (@pair nat nat m p)) (addn (dist (@pair nat nat n q)) (addn r s)).
Axiom thm_BOUNDS_LINEAR : forall A : nat, forall B : nat, forall C : nat, (forall n : nat, leqn (muln A n) (addn (muln B n) C)) = (leqn A B).
Axiom thm_BOUNDS_LINEAR_0 : forall A : nat, forall B : nat, (forall n : nat, leqn (muln A n) B) = (A = (NUMERAL O)).
Axiom thm_BOUNDS_DIVIDED : forall P : nat -> nat, (exists B : nat, forall n : nat, leqn (P n) B) = (exists A : nat, exists B : nat, forall n : nat, leqn (muln n (P n)) (addn (muln A n) B)).
Axiom thm_BOUNDS_NOTZERO : forall P : nat -> nat -> nat, forall A : nat, forall B : nat, (((P (NUMERAL O) (NUMERAL O)) = (NUMERAL O)) /\ (forall m : nat, forall n : nat, leqn (P m n) (addn (muln A (addn m n)) B))) -> exists B' : nat, forall m : nat, forall n : nat, leqn (P m n) (muln B' (addn m n)).
Axiom thm_BOUNDS_IGNORE : forall P : nat -> nat, forall Q : nat -> nat, (exists B : nat, forall i : nat, leqn (P i) (addn (Q i) B)) = (exists B : nat, exists N' : nat, forall i : nat, (leqn N' i) -> leqn (P i) (addn (Q i) B)).
Axiom thm_is_nadd : forall x : nat -> nat, (is_nadd x) = (exists B : nat, forall m : nat, forall n : nat, leqn (dist (@pair nat nat (muln m (x n)) (muln n (x m)))) (muln B (addn m n))).
Axiom thm_is_nadd_0 : is_nadd (fun n : nat => NUMERAL O).
Axiom thm_NADD_CAUCHY : forall x : nadd, exists B : nat, forall m : nat, forall n : nat, leqn (dist (@pair nat nat (muln m (dest_nadd x n)) (muln n (dest_nadd x m)))) (muln B (addn m n)).
Axiom thm_NADD_BOUND : forall x : nadd, exists A : nat, exists B : nat, forall n : nat, leqn (dest_nadd x n) (addn (muln A n) B).
Axiom thm_NADD_MULTIPLICATIVE : forall x : nadd, exists B : nat, forall m : nat, forall n : nat, leqn (dist (@pair nat nat (dest_nadd x (muln m n)) (muln m (dest_nadd x n)))) (addn (muln B m) B).
Axiom thm_NADD_ADDITIVE : forall x : nadd, exists B : nat, forall m : nat, forall n : nat, leqn (dist (@pair nat nat (dest_nadd x (addn m n)) (addn (dest_nadd x m) (dest_nadd x n)))) B.
Axiom thm_NADD_SUC : forall x : nadd, exists B : nat, forall n : nat, leqn (dist (@pair nat nat (dest_nadd x (S n)) (dest_nadd x n))) B.
Axiom thm_NADD_DIST_LEMMA : forall x : nadd, exists B : nat, forall m : nat, forall n : nat, leqn (dist (@pair nat nat (dest_nadd x (addn m n)) (dest_nadd x m))) (muln B n).
Axiom thm_NADD_DIST : forall x : nadd, exists B : nat, forall m : nat, forall n : nat, leqn (dist (@pair nat nat (dest_nadd x m) (dest_nadd x n))) (muln B (dist (@pair nat nat m n))).
Axiom thm_NADD_ALTMUL : forall x : nadd, forall y : nadd, exists A : nat, exists B : nat, forall n : nat, leqn (dist (@pair nat nat (muln n (dest_nadd x (dest_nadd y n))) (muln (dest_nadd x n) (dest_nadd y n)))) (addn (muln A n) B).
Axiom thm_nadd_eq : forall x : nadd, forall y : nadd, (nadd_eq x y) = (exists B : nat, forall n : nat, leqn (dist (@pair nat nat (dest_nadd x n) (dest_nadd y n))) B).
Axiom thm_NADD_EQ_REFL : forall x : nadd, nadd_eq x x.
Axiom thm_NADD_EQ_SYM : forall x : nadd, forall y : nadd, (nadd_eq x y) = (nadd_eq y x).
Axiom thm_NADD_EQ_TRANS : forall x : nadd, forall y : nadd, forall z : nadd, ((nadd_eq x y) /\ (nadd_eq y z)) -> nadd_eq x z.
Axiom thm_nadd_of_num : forall k : nat, (nadd_of_num k) = (mk_nadd (fun n : nat => muln k n)).
Axiom thm_NADD_OF_NUM : forall k : nat, (dest_nadd (nadd_of_num k)) = (fun n : nat => muln k n).
Axiom thm_NADD_OF_NUM_WELLDEF : forall m : nat, forall n : nat, (m = n) -> nadd_eq (nadd_of_num m) (nadd_of_num n).
Axiom thm_NADD_OF_NUM_EQ : forall m : nat, forall n : nat, (nadd_eq (nadd_of_num m) (nadd_of_num n)) = (m = n).
Axiom thm_nadd_le : forall x : nadd, forall y : nadd, (nadd_le x y) = (exists B : nat, forall n : nat, leqn (dest_nadd x n) (addn (dest_nadd y n) B)).
Axiom thm_NADD_LE_WELLDEF_LEMMA : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ ((nadd_eq y y') /\ (nadd_le x y))) -> nadd_le x' y'.
Axiom thm_NADD_LE_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> (nadd_le x y) = (nadd_le x' y').
Axiom thm_NADD_LE_REFL : forall x : nadd, nadd_le x x.
Axiom thm_NADD_LE_TRANS : forall x : nadd, forall y : nadd, forall z : nadd, ((nadd_le x y) /\ (nadd_le y z)) -> nadd_le x z.
Axiom thm_NADD_LE_ANTISYM : forall x : nadd, forall y : nadd, ((nadd_le x y) /\ (nadd_le y x)) = (nadd_eq x y).
Axiom thm_NADD_LE_TOTAL_LEMMA : forall x : nadd, forall y : nadd, (~ (nadd_le x y)) -> forall B : nat, exists n : nat, (~ (n = (NUMERAL O))) /\ (ltn (addn (dest_nadd y n) B) (dest_nadd x n)).
Axiom thm_NADD_LE_TOTAL : forall x : nadd, forall y : nadd, (nadd_le x y) \/ (nadd_le y x).
Axiom thm_NADD_ARCH : forall x : nadd, exists n : nat, nadd_le x (nadd_of_num n).
Axiom thm_NADD_OF_NUM_LE : forall m : nat, forall n : nat, (nadd_le (nadd_of_num m) (nadd_of_num n)) = (leqn m n).
Axiom thm_nadd_add : forall x : nadd, forall y : nadd, (nadd_add x y) = (mk_nadd (fun n : nat => addn (dest_nadd x n) (dest_nadd y n))).
Axiom thm_NADD_ADD : forall x : nadd, forall y : nadd, (dest_nadd (nadd_add x y)) = (fun n : nat => addn (dest_nadd x n) (dest_nadd y n)).
Axiom thm_NADD_ADD_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> nadd_eq (nadd_add x y) (nadd_add x' y').
Axiom thm_NADD_ADD_SYM : forall x : nadd, forall y : nadd, nadd_eq (nadd_add x y) (nadd_add y x).
Axiom thm_NADD_ADD_ASSOC : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_add x (nadd_add y z)) (nadd_add (nadd_add x y) z).
Axiom thm_NADD_ADD_LID : forall x : nadd, nadd_eq (nadd_add (nadd_of_num (NUMERAL O)) x) x.
Axiom thm_NADD_ADD_LCANCEL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_eq (nadd_add x y) (nadd_add x z)) -> nadd_eq y z.
Axiom thm_NADD_LE_ADD : forall x : nadd, forall y : nadd, nadd_le x (nadd_add x y).
Axiom thm_NADD_LE_EXISTS : forall x : nadd, forall y : nadd, (nadd_le x y) -> exists d : nadd, nadd_eq y (nadd_add x d).
Axiom thm_NADD_OF_NUM_ADD : forall m : nat, forall n : nat, nadd_eq (nadd_add (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (addn m n)).
Axiom thm_nadd_mul : forall x : nadd, forall y : nadd, (nadd_mul x y) = (mk_nadd (fun n : nat => dest_nadd x (dest_nadd y n))).
Axiom thm_NADD_MUL : forall x : nadd, forall y : nadd, (dest_nadd (nadd_mul x y)) = (fun n : nat => dest_nadd x (dest_nadd y n)).
Axiom thm_NADD_MUL_SYM : forall x : nadd, forall y : nadd, nadd_eq (nadd_mul x y) (nadd_mul y x).
Axiom thm_NADD_MUL_ASSOC : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul x (nadd_mul y z)) (nadd_mul (nadd_mul x y) z).
Axiom thm_NADD_MUL_LID : forall x : nadd, nadd_eq (nadd_mul (nadd_of_num (NUMERAL (BIT1 O))) x) x.
Axiom thm_NADD_LDISTRIB : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul x (nadd_add y z)) (nadd_add (nadd_mul x y) (nadd_mul x z)).
Axiom thm_NADD_MUL_WELLDEF_LEMMA : forall x : nadd, forall y : nadd, forall y' : nadd, (nadd_eq y y') -> nadd_eq (nadd_mul x y) (nadd_mul x y').
Axiom thm_NADD_MUL_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> nadd_eq (nadd_mul x y) (nadd_mul x' y').
Axiom thm_NADD_OF_NUM_MUL : forall m : nat, forall n : nat, nadd_eq (nadd_mul (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (muln m n)).
Axiom thm_NADD_LE_0 : forall x : nadd, nadd_le (nadd_of_num (NUMERAL O)) x.
Axiom thm_NADD_EQ_IMP_LE : forall x : nadd, forall y : nadd, (nadd_eq x y) -> nadd_le x y.
Axiom thm_NADD_LE_LMUL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le y z) -> nadd_le (nadd_mul x y) (nadd_mul x z).
Axiom thm_NADD_LE_RMUL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le x y) -> nadd_le (nadd_mul x z) (nadd_mul y z).
Axiom thm_NADD_LE_RADD : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le (nadd_add x z) (nadd_add y z)) = (nadd_le x y).
Axiom thm_NADD_LE_LADD : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le (nadd_add x y) (nadd_add x z)) = (nadd_le y z).
Axiom thm_NADD_RDISTRIB : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul (nadd_add x y) z) (nadd_add (nadd_mul x z) (nadd_mul y z)).
Axiom thm_NADD_ARCH_MULT : forall x : nadd, forall k : nat, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists N' : nat, nadd_le (nadd_of_num k) (nadd_mul (nadd_of_num N') x).
Axiom thm_NADD_ARCH_ZERO : forall x : nadd, forall k : nadd, (forall n : nat, nadd_le (nadd_mul (nadd_of_num n) x) k) -> nadd_eq x (nadd_of_num (NUMERAL O)).
Axiom thm_NADD_ARCH_LEMMA : forall x : nadd, forall y : nadd, forall z : nadd, (forall n : nat, nadd_le (nadd_mul (nadd_of_num n) x) (nadd_add (nadd_mul (nadd_of_num n) y) z)) -> nadd_le x y.
Axiom thm_NADD_COMPLETE : forall P : nadd -> Prop, ((exists x : nadd, P x) /\ (exists M : nadd, forall x : nadd, (P x) -> nadd_le x M)) -> exists M : nadd, (forall x : nadd, (P x) -> nadd_le x M) /\ (forall M' : nadd, (forall x : nadd, (P x) -> nadd_le x M') -> nadd_le M M').
Axiom thm_NADD_UBOUND : forall x : nadd, exists B : nat, exists N' : nat, forall n : nat, (leqn N' n) -> leqn (dest_nadd x n) (muln B n).
Axiom thm_NADD_NONZERO : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists N' : nat, forall n : nat, (leqn N' n) -> ~ ((dest_nadd x n) = (NUMERAL O)).
Axiom thm_NADD_LBOUND : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists A : nat, exists N' : nat, forall n : nat, (leqn N' n) -> leqn n (muln A (dest_nadd x n)).
Axiom thm_nadd_rinv : forall x : nadd, (nadd_rinv x) = (fun n : nat => divn (muln n n) (dest_nadd x n)).
Axiom thm_NADD_MUL_LINV_LEMMA0 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists A : nat, exists B : nat, forall n : nat, leqn (nadd_rinv x n) (addn (muln A n) B).
Axiom thm_NADD_MUL_LINV_LEMMA1 : forall x : nadd, forall n : nat, (~ ((dest_nadd x n) = (NUMERAL O))) -> leqn (dist (@pair nat nat (muln (dest_nadd x n) (nadd_rinv x n)) (muln n n))) (dest_nadd x n).
Axiom thm_NADD_MUL_LINV_LEMMA2 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists N' : nat, forall n : nat, (leqn N' n) -> leqn (dist (@pair nat nat (muln (dest_nadd x n) (nadd_rinv x n)) (muln n n))) (dest_nadd x n).
Axiom thm_NADD_MUL_LINV_LEMMA3 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists N' : nat, forall m : nat, forall n : nat, (leqn N' n) -> leqn (dist (@pair nat nat (muln m (muln (dest_nadd x m) (muln (dest_nadd x n) (nadd_rinv x n)))) (muln m (muln (dest_nadd x m) (muln n n))))) (muln m (muln (dest_nadd x m) (dest_nadd x n))).
Axiom thm_NADD_MUL_LINV_LEMMA4 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists N' : nat, forall m : nat, forall n : nat, ((leqn N' m) /\ (leqn N' n)) -> leqn (muln (muln (dest_nadd x m) (dest_nadd x n)) (dist (@pair nat nat (muln m (nadd_rinv x n)) (muln n (nadd_rinv x m))))) (addn (muln (muln m n) (dist (@pair nat nat (muln m (dest_nadd x n)) (muln n (dest_nadd x m))))) (muln (muln (dest_nadd x m) (dest_nadd x n)) (addn m n))).
Axiom thm_NADD_MUL_LINV_LEMMA5 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists B : nat, exists N' : nat, forall m : nat, forall n : nat, ((leqn N' m) /\ (leqn N' n)) -> leqn (muln (muln (dest_nadd x m) (dest_nadd x n)) (dist (@pair nat nat (muln m (nadd_rinv x n)) (muln n (nadd_rinv x m))))) (muln B (muln (muln m n) (addn m n))).
Axiom thm_NADD_MUL_LINV_LEMMA6 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists B : nat, exists N' : nat, forall m : nat, forall n : nat, ((leqn N' m) /\ (leqn N' n)) -> leqn (muln (muln m n) (dist (@pair nat nat (muln m (nadd_rinv x n)) (muln n (nadd_rinv x m))))) (muln B (muln (muln m n) (addn m n))).
Axiom thm_NADD_MUL_LINV_LEMMA7 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists B : nat, exists N' : nat, forall m : nat, forall n : nat, ((leqn N' m) /\ (leqn N' n)) -> leqn (dist (@pair nat nat (muln m (nadd_rinv x n)) (muln n (nadd_rinv x m)))) (muln B (addn m n)).
Axiom thm_NADD_MUL_LINV_LEMMA7a : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> forall N' : nat, exists A : nat, exists B : nat, forall m : nat, forall n : nat, (leqn m N') -> leqn (dist (@pair nat nat (muln m (nadd_rinv x n)) (muln n (nadd_rinv x m)))) (addn (muln A n) B).
Axiom thm_NADD_MUL_LINV_LEMMA8 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> exists B : nat, forall m : nat, forall n : nat, leqn (dist (@pair nat nat (muln m (nadd_rinv x n)) (muln n (nadd_rinv x m)))) (muln B (addn m n)).
Axiom thm_nadd_inv : forall x : nadd, (nadd_inv x) = (@COND nadd (nadd_eq x (nadd_of_num (NUMERAL O))) (nadd_of_num (NUMERAL O)) (mk_nadd (nadd_rinv x))).
Axiom thm_NADD_INV : forall x : nadd, (dest_nadd (nadd_inv x)) = (@COND (nat -> nat) (nadd_eq x (nadd_of_num (NUMERAL O))) (fun n : nat => NUMERAL O) (nadd_rinv x)).
Axiom thm_NADD_MUL_LINV : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL O)))) -> nadd_eq (nadd_mul (nadd_inv x) x) (nadd_of_num (NUMERAL (BIT1 O))).
Axiom thm_NADD_INV_0 : nadd_eq (nadd_inv (nadd_of_num (NUMERAL O))) (nadd_of_num (NUMERAL O)).
Axiom thm_NADD_INV_WELLDEF : forall x : nadd, forall y : nadd, (nadd_eq x y) -> nadd_eq (nadd_inv x) (nadd_inv y).
Axiom thm_HREAL_OF_NUM_EQ : forall m : nat, forall n : nat, ((hreal_of_num m) = (hreal_of_num n)) = (m = n).
Axiom thm_HREAL_OF_NUM_LE : forall m : nat, forall n : nat, (hreal_le (hreal_of_num m) (hreal_of_num n)) = (leqn m n).
Axiom thm_HREAL_OF_NUM_ADD : forall m : nat, forall n : nat, (hreal_add (hreal_of_num m) (hreal_of_num n)) = (hreal_of_num (addn m n)).
Axiom thm_HREAL_OF_NUM_MUL : forall m : nat, forall n : nat, (hreal_mul (hreal_of_num m) (hreal_of_num n)) = (hreal_of_num (muln m n)).
Axiom thm_HREAL_LE_REFL : forall x : hreal, hreal_le x x.
Axiom thm_HREAL_LE_TRANS : forall x : hreal, forall y : hreal, forall z : hreal, ((hreal_le x y) /\ (hreal_le y z)) -> hreal_le x z.
Axiom thm_HREAL_LE_ANTISYM : forall x : hreal, forall y : hreal, ((hreal_le x y) /\ (hreal_le y x)) = (x = y).
Axiom thm_HREAL_LE_TOTAL : forall x : hreal, forall y : hreal, (hreal_le x y) \/ (hreal_le y x).
Axiom thm_HREAL_LE_ADD : forall x : hreal, forall y : hreal, hreal_le x (hreal_add x y).
Axiom thm_HREAL_LE_EXISTS : forall x : hreal, forall y : hreal, (hreal_le x y) -> exists d : hreal, y = (hreal_add x d).
Axiom thm_HREAL_ARCH : forall x : hreal, exists n : nat, hreal_le x (hreal_of_num n).
Axiom thm_HREAL_ADD_SYM : forall x : hreal, forall y : hreal, (hreal_add x y) = (hreal_add y x).
Axiom thm_HREAL_ADD_ASSOC : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_add x (hreal_add y z)) = (hreal_add (hreal_add x y) z).
Axiom thm_HREAL_ADD_LID : forall x : hreal, (hreal_add (hreal_of_num (NUMERAL O)) x) = x.
Axiom thm_HREAL_ADD_LCANCEL : forall x : hreal, forall y : hreal, forall z : hreal, ((hreal_add x y) = (hreal_add x z)) -> y = z.
Axiom thm_HREAL_MUL_SYM : forall x : hreal, forall y : hreal, (hreal_mul x y) = (hreal_mul y x).
Axiom thm_HREAL_MUL_ASSOC : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_mul x (hreal_mul y z)) = (hreal_mul (hreal_mul x y) z).
Axiom thm_HREAL_MUL_LID : forall x : hreal, (hreal_mul (hreal_of_num (NUMERAL (BIT1 O))) x) = x.
Axiom thm_HREAL_ADD_LDISTRIB : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_mul x (hreal_add y z)) = (hreal_add (hreal_mul x y) (hreal_mul x z)).
Axiom thm_HREAL_MUL_LINV : forall x : hreal, (~ (x = (hreal_of_num (NUMERAL O)))) -> (hreal_mul (hreal_inv x) x) = (hreal_of_num (NUMERAL (BIT1 O))).
Axiom thm_HREAL_INV_0 : (hreal_inv (hreal_of_num (NUMERAL O))) = (hreal_of_num (NUMERAL O)).
Axiom thm_HREAL_LE_EXISTS_DEF : forall m : hreal, forall n : hreal, (hreal_le m n) = (exists d : hreal, n = (hreal_add m d)).
Axiom thm_HREAL_EQ_ADD_LCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, ((hreal_add m n) = (hreal_add m p)) = (n = p).
Axiom thm_HREAL_EQ_ADD_RCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, ((hreal_add m p) = (hreal_add n p)) = (m = n).
Axiom thm_HREAL_LE_ADD_LCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_le (hreal_add m n) (hreal_add m p)) = (hreal_le n p).
Axiom thm_HREAL_LE_ADD_RCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_le (hreal_add m p) (hreal_add n p)) = (hreal_le m n).
Axiom thm_HREAL_ADD_RID : forall n : hreal, (hreal_add n (hreal_of_num (NUMERAL O))) = n.
Axiom thm_HREAL_ADD_RDISTRIB : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_mul (hreal_add m n) p) = (hreal_add (hreal_mul m p) (hreal_mul n p)).
Axiom thm_HREAL_MUL_LZERO : forall m : hreal, (hreal_mul (hreal_of_num (NUMERAL O)) m) = (hreal_of_num (NUMERAL O)).
Axiom thm_HREAL_MUL_RZERO : forall m : hreal, (hreal_mul m (hreal_of_num (NUMERAL O))) = (hreal_of_num (NUMERAL O)).
Axiom thm_HREAL_ADD_AC : forall (n : hreal) (m : hreal) (p : hreal), ((hreal_add m n) = (hreal_add n m)) /\ (((hreal_add (hreal_add m n) p) = (hreal_add m (hreal_add n p))) /\ ((hreal_add m (hreal_add n p)) = (hreal_add n (hreal_add m p)))).
Axiom thm_HREAL_LE_ADD2 : forall a : hreal, forall b : hreal, forall c : hreal, forall d : hreal, ((hreal_le a b) /\ (hreal_le c d)) -> hreal_le (hreal_add a c) (hreal_add b d).
Axiom thm_HREAL_LE_MUL_RCANCEL_IMP : forall a : hreal, forall b : hreal, forall c : hreal, (hreal_le a b) -> hreal_le (hreal_mul a c) (hreal_mul b c).
Axiom thm_treal_of_num : forall n : nat, (treal_of_num n) = (@pair hreal hreal (hreal_of_num n) (hreal_of_num (NUMERAL O))).
Axiom thm_treal_neg : forall y : hreal, forall x : hreal, (treal_neg (@pair hreal hreal x y)) = (@pair hreal hreal y x).
Axiom thm_treal_add : forall x1 : hreal, forall x2 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_add (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (@pair hreal hreal (hreal_add x1 x2) (hreal_add y1 y2)).
Axiom thm_treal_mul : forall x1 : hreal, forall y2 : hreal, forall y1 : hreal, forall x2 : hreal, (treal_mul (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (@pair hreal hreal (hreal_add (hreal_mul x1 x2) (hreal_mul y1 y2)) (hreal_add (hreal_mul x1 y2) (hreal_mul y1 x2))).
Axiom thm_treal_le : forall x1 : hreal, forall y2 : hreal, forall x2 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (hreal_le (hreal_add x1 y2) (hreal_add x2 y1)).
Axiom thm_treal_inv : forall y : hreal, forall x : hreal, (treal_inv (@pair hreal hreal x y)) = (@COND (prod hreal hreal) (x = y) (@pair hreal hreal (hreal_of_num (NUMERAL O)) (hreal_of_num (NUMERAL O))) (@COND (prod hreal hreal) (hreal_le y x) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => x = (hreal_add y d)))) (hreal_of_num (NUMERAL O))) (@pair hreal hreal (hreal_of_num (NUMERAL O)) (hreal_inv (@ε hreal (fun d : hreal => y = (hreal_add x d))))))).
Axiom thm_treal_eq : forall x1 : hreal, forall y2 : hreal, forall x2 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Axiom thm_TREAL_EQ_REFL : forall x : prod hreal hreal, treal_eq x x.
Axiom thm_TREAL_EQ_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) = (treal_eq y x).
Axiom thm_TREAL_EQ_TRANS : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, ((treal_eq x y) /\ (treal_eq y z)) -> treal_eq x z.
Axiom thm_TREAL_EQ_AP : forall x : prod hreal hreal, forall y : prod hreal hreal, (x = y) -> treal_eq x y.
Axiom thm_TREAL_OF_NUM_EQ : forall m : nat, forall n : nat, (treal_eq (treal_of_num m) (treal_of_num n)) = (m = n).
Axiom thm_TREAL_OF_NUM_LE : forall m : nat, forall n : nat, (treal_le (treal_of_num m) (treal_of_num n)) = (leqn m n).
Axiom thm_TREAL_OF_NUM_ADD : forall m : nat, forall n : nat, treal_eq (treal_add (treal_of_num m) (treal_of_num n)) (treal_of_num (addn m n)).
Axiom thm_TREAL_OF_NUM_MUL : forall m : nat, forall n : nat, treal_eq (treal_mul (treal_of_num m) (treal_of_num n)) (treal_of_num (muln m n)).
Axiom thm_TREAL_ADD_SYM_EQ : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_add x y) = (treal_add y x).
Axiom thm_TREAL_MUL_SYM_EQ : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_mul x y) = (treal_mul y x).
Axiom thm_TREAL_ADD_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, treal_eq (treal_add x y) (treal_add y x).
Axiom thm_TREAL_ADD_ASSOC : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_add x (treal_add y z)) (treal_add (treal_add x y) z).
Axiom thm_TREAL_ADD_LID : forall x : prod hreal hreal, treal_eq (treal_add (treal_of_num (NUMERAL O)) x) x.
Axiom thm_TREAL_ADD_LINV : forall x : prod hreal hreal, treal_eq (treal_add (treal_neg x) x) (treal_of_num (NUMERAL O)).
Axiom thm_TREAL_MUL_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, treal_eq (treal_mul x y) (treal_mul y x).
Axiom thm_TREAL_MUL_ASSOC : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_mul x (treal_mul y z)) (treal_mul (treal_mul x y) z).
Axiom thm_TREAL_MUL_LID : forall x : prod hreal hreal, treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 O))) x) x.
Axiom thm_TREAL_ADD_LDISTRIB : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_mul x (treal_add y z)) (treal_add (treal_mul x y) (treal_mul x z)).
Axiom thm_TREAL_LE_REFL : forall x : prod hreal hreal, treal_le x x.
Axiom thm_TREAL_LE_ANTISYM : forall x : prod hreal hreal, forall y : prod hreal hreal, ((treal_le x y) /\ (treal_le y x)) = (treal_eq x y).
Axiom thm_TREAL_LE_TRANS : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, ((treal_le x y) /\ (treal_le y z)) -> treal_le x z.
Axiom thm_TREAL_LE_TOTAL : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_le x y) \/ (treal_le y x).
Axiom thm_TREAL_LE_LADD_IMP : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, (treal_le y z) -> treal_le (treal_add x y) (treal_add x z).
Axiom thm_TREAL_LE_MUL : forall x : prod hreal hreal, forall y : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL O)) x) /\ (treal_le (treal_of_num (NUMERAL O)) y)) -> treal_le (treal_of_num (NUMERAL O)) (treal_mul x y).
Axiom thm_TREAL_INV_0 : treal_eq (treal_inv (treal_of_num (NUMERAL O))) (treal_of_num (NUMERAL O)).
Axiom thm_TREAL_MUL_LINV : forall x : prod hreal hreal, (~ (treal_eq x (treal_of_num (NUMERAL O)))) -> treal_eq (treal_mul (treal_inv x) x) (treal_of_num (NUMERAL (BIT1 O))).
Axiom thm_TREAL_OF_NUM_WELLDEF : forall m : nat, forall n : nat, (m = n) -> treal_eq (treal_of_num m) (treal_of_num n).
Axiom thm_TREAL_NEG_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_neg x1) (treal_neg x2).
Axiom thm_TREAL_ADD_WELLDEFR : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_add x1 y) (treal_add x2 y).
Axiom thm_TREAL_ADD_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> treal_eq (treal_add x1 y1) (treal_add x2 y2).
Axiom thm_TREAL_MUL_WELLDEFR : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_mul x1 y) (treal_mul x2 y).
Axiom thm_TREAL_MUL_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> treal_eq (treal_mul x1 y1) (treal_mul x2 y2).
Axiom thm_TREAL_EQ_IMP_LE : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) -> treal_le x y.
Axiom thm_TREAL_LE_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> (treal_le x1 y1) = (treal_le x2 y2).
Axiom thm_TREAL_INV_WELLDEF : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) -> treal_eq (treal_inv x) (treal_inv y).
Axiom thm_REAL_ADD_SYM : forall x : R, forall y : R, (addr x y) = (addr y x).
Axiom thm_REAL_ADD_ASSOC : forall x : R, forall y : R, forall z : R, (addr x (addr y z)) = (addr (addr x y) z).
Axiom thm_REAL_ADD_LID : forall x : R, (addr (R_of_nat (NUMERAL O)) x) = x.
Axiom thm_REAL_ADD_LINV : forall x : R, (addr (oppr x) x) = (R_of_nat (NUMERAL O)).
Axiom thm_REAL_MUL_SYM : forall x : R, forall y : R, (mulr x y) = (mulr y x).
Axiom thm_REAL_MUL_ASSOC : forall x : R, forall y : R, forall z : R, (mulr x (mulr y z)) = (mulr (mulr x y) z).
Axiom thm_REAL_MUL_LID : forall x : R, (mulr (R_of_nat (NUMERAL (BIT1 O))) x) = x.
Axiom thm_REAL_ADD_LDISTRIB : forall x : R, forall y : R, forall z : R, (mulr x (addr y z)) = (addr (mulr x y) (mulr x z)).
Axiom thm_REAL_LE_REFL : forall x : R, ler x x.
Axiom thm_REAL_LE_ANTISYM : forall x : R, forall y : R, ((ler x y) /\ (ler y x)) = (x = y).
Axiom thm_REAL_LE_TRANS : forall x : R, forall y : R, forall z : R, ((ler x y) /\ (ler y z)) -> ler x z.
Axiom thm_REAL_LE_TOTAL : forall x : R, forall y : R, (ler x y) \/ (ler y x).
Axiom thm_REAL_LE_LADD_IMP : forall x : R, forall y : R, forall z : R, (ler y z) -> ler (addr x y) (addr x z).
Axiom thm_REAL_LE_MUL : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) x) /\ (ler (R_of_nat (NUMERAL O)) y)) -> ler (R_of_nat (NUMERAL O)) (mulr x y).
Axiom thm_REAL_INV_0 : (invr (R_of_nat (NUMERAL O))) = (R_of_nat (NUMERAL O)).
Axiom thm_REAL_MUL_LINV : forall x : R, (~ (x = (R_of_nat (NUMERAL O)))) -> (mulr (invr x) x) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_OF_NUM_EQ : forall m : nat, forall n : nat, ((R_of_nat m) = (R_of_nat n)) = (m = n).
Axiom thm_REAL_OF_NUM_LE : forall m : nat, forall n : nat, (ler (R_of_nat m) (R_of_nat n)) = (leqn m n).
Axiom thm_REAL_OF_NUM_ADD : forall m : nat, forall n : nat, (addr (R_of_nat m) (R_of_nat n)) = (R_of_nat (addn m n)).
Axiom thm_REAL_OF_NUM_MUL : forall m : nat, forall n : nat, (mulr (R_of_nat m) (R_of_nat n)) = (R_of_nat (muln m n)).
Axiom thm_real_sub : forall x : R, forall y : R, (subr x y) = (addr x (oppr y)).
Axiom thm_real_lt : forall y : R, forall x : R, (ltr x y) = (~ (ler y x)).
Axiom thm_real_ge : forall y : R, forall x : R, (ger x y) = (ler y x).
Axiom thm_real_gt : forall y : R, forall x : R, (gtr x y) = (ltr y x).
Axiom thm_real_abs : forall x : R, (normr x) = (@COND R (ler (R_of_nat (NUMERAL O)) x) x (oppr x)).
Axiom thm_real_pow : forall (x : R), ((expr x (NUMERAL O)) = (R_of_nat (NUMERAL (BIT1 O)))) /\ (forall n : nat, (expr x (S n)) = (mulr x (expr x n))).
Axiom thm_real_div : forall x : R, forall y : R, (divr x y) = (mulr x (invr y)).
Axiom thm_real_max : forall n : R, forall m : R, (maxr m n) = (@COND R (ler m n) n m).
Axiom thm_real_min : forall m : R, forall n : R, (minr m n) = (@COND R (ler m n) m n).
Axiom thm_REAL_HREAL_LEMMA1 : exists r : hreal -> R, (forall x : R, (ler (R_of_nat (NUMERAL O)) x) = (exists y : hreal, x = (r y))) /\ (forall y : hreal, forall z : hreal, (hreal_le y z) = (ler (r y) (r z))).
Axiom thm_REAL_HREAL_LEMMA2 : exists h : R -> hreal, exists r : hreal -> R, (forall x : hreal, (h (r x)) = x) /\ ((forall x : R, (ler (R_of_nat (NUMERAL O)) x) -> (r (h x)) = x) /\ ((forall x : hreal, ler (R_of_nat (NUMERAL O)) (r x)) /\ (forall x : hreal, forall y : hreal, (hreal_le x y) = (ler (r x) (r y))))).
Axiom thm_REAL_COMPLETE_SOMEPOS : forall P : R -> Prop, ((exists x : R, (P x) /\ (ler (R_of_nat (NUMERAL O)) x)) /\ (exists M : R, forall x : R, (P x) -> ler x M)) -> exists M : R, (forall x : R, (P x) -> ler x M) /\ (forall M' : R, (forall x : R, (P x) -> ler x M') -> ler M M').
Axiom thm_REAL_COMPLETE : forall P : R -> Prop, ((exists x : R, P x) /\ (exists M : R, forall x : R, (P x) -> ler x M)) -> exists M : R, (forall x : R, (P x) -> ler x M) /\ (forall M' : R, (forall x : R, (P x) -> ler x M') -> ler M M').
Axiom thm_REAL_ADD_AC : forall (n : R) (m : R) (p : R), ((addr m n) = (addr n m)) /\ (((addr (addr m n) p) = (addr m (addr n p))) /\ ((addr m (addr n p)) = (addr n (addr m p)))).
Axiom thm_REAL_ADD_RINV : forall x : R, (addr x (oppr x)) = (R_of_nat (NUMERAL O)).
Axiom thm_REAL_EQ_ADD_LCANCEL : forall x : R, forall y : R, forall z : R, ((addr x y) = (addr x z)) = (y = z).
Axiom thm_REAL_EQ_ADD_RCANCEL : forall x : R, forall y : R, forall z : R, ((addr x z) = (addr y z)) = (x = y).
Axiom thm_REAL_MUL_RZERO : forall x : R, (mulr x (R_of_nat (NUMERAL O))) = (R_of_nat (NUMERAL O)).
Axiom thm_REAL_MUL_LZERO : forall x : R, (mulr (R_of_nat (NUMERAL O)) x) = (R_of_nat (NUMERAL O)).
Axiom thm_REAL_NEG_NEG : forall x : R, (oppr (oppr x)) = x.
Axiom thm_REAL_MUL_RNEG : forall x : R, forall y : R, (mulr x (oppr y)) = (oppr (mulr x y)).
Axiom thm_REAL_MUL_LNEG : forall x : R, forall y : R, (mulr (oppr x) y) = (oppr (mulr x y)).
Axiom thm_REAL_NEG_ADD : forall x : R, forall y : R, (oppr (addr x y)) = (addr (oppr x) (oppr y)).
Axiom thm_REAL_ADD_RID : forall x : R, (addr x (R_of_nat (NUMERAL O))) = x.
Axiom thm_REAL_NEG_0 : (oppr (R_of_nat (NUMERAL O))) = (R_of_nat (NUMERAL O)).
Axiom thm_REAL_LE_LNEG : forall x : R, forall y : R, (ler (oppr x) y) = (ler (R_of_nat (NUMERAL O)) (addr x y)).
Axiom thm_REAL_LE_NEG2 : forall x : R, forall y : R, (ler (oppr x) (oppr y)) = (ler y x).
Axiom thm_REAL_LE_RNEG : forall x : R, forall y : R, (ler x (oppr y)) = (ler (addr x y) (R_of_nat (NUMERAL O))).
Axiom thm_REAL_OF_NUM_POW : forall x : nat, forall n : nat, (expr (R_of_nat x) n) = (R_of_nat (expn x n)).
Axiom thm_REAL_POW_NEG : forall x : R, forall n : nat, (expr (oppr x) n) = (@COND R (even n) (expr x n) (oppr (expr x n))).
Axiom thm_REAL_ABS_NUM : forall n : nat, (normr (R_of_nat n)) = (R_of_nat n).
Axiom thm_REAL_ABS_NEG : forall x : R, (normr (oppr x)) = (normr x).
Axiom thm_REAL_LTE_TOTAL : forall x : R, forall y : R, (ltr x y) \/ (ler y x).
Axiom thm_REAL_LET_TOTAL : forall x : R, forall y : R, (ler x y) \/ (ltr y x).
Axiom thm_REAL_LT_IMP_LE : forall x : R, forall y : R, (ltr x y) -> ler x y.
Axiom thm_REAL_LTE_TRANS : forall x : R, forall y : R, forall z : R, ((ltr x y) /\ (ler y z)) -> ltr x z.
Axiom thm_REAL_LET_TRANS : forall x : R, forall y : R, forall z : R, ((ler x y) /\ (ltr y z)) -> ltr x z.
Axiom thm_REAL_LT_TRANS : forall x : R, forall y : R, forall z : R, ((ltr x y) /\ (ltr y z)) -> ltr x z.
Axiom thm_REAL_LE_ADD : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) x) /\ (ler (R_of_nat (NUMERAL O)) y)) -> ler (R_of_nat (NUMERAL O)) (addr x y).
Axiom thm_REAL_LTE_ANTISYM : forall x : R, forall y : R, ~ ((ltr x y) /\ (ler y x)).
Axiom thm_REAL_SUB_LE : forall x : R, forall y : R, (ler (R_of_nat (NUMERAL O)) (subr x y)) = (ler y x).
Axiom thm_REAL_NEG_SUB : forall x : R, forall y : R, (oppr (subr x y)) = (subr y x).
Axiom thm_REAL_LE_LT : forall x : R, forall y : R, (ler x y) = ((ltr x y) \/ (x = y)).
Axiom thm_REAL_SUB_LT : forall x : R, forall y : R, (ltr (R_of_nat (NUMERAL O)) (subr x y)) = (ltr y x).
Axiom thm_REAL_NOT_LT : forall x : R, forall y : R, (~ (ltr x y)) = (ler y x).
Axiom thm_REAL_SUB_0 : forall x : R, forall y : R, ((subr x y) = (R_of_nat (NUMERAL O))) = (x = y).
Axiom thm_REAL_LT_LE : forall x : R, forall y : R, (ltr x y) = ((ler x y) /\ (~ (x = y))).
Axiom thm_REAL_LT_REFL : forall x : R, ~ (ltr x x).
Axiom thm_REAL_LTE_ADD : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ler (R_of_nat (NUMERAL O)) y)) -> ltr (R_of_nat (NUMERAL O)) (addr x y).
Axiom thm_REAL_LET_ADD : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) x) /\ (ltr (R_of_nat (NUMERAL O)) y)) -> ltr (R_of_nat (NUMERAL O)) (addr x y).
Axiom thm_REAL_LT_ADD : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr (R_of_nat (NUMERAL O)) y)) -> ltr (R_of_nat (NUMERAL O)) (addr x y).
Axiom thm_REAL_ENTIRE : forall x : R, forall y : R, ((mulr x y) = (R_of_nat (NUMERAL O))) = ((x = (R_of_nat (NUMERAL O))) \/ (y = (R_of_nat (NUMERAL O)))).
Axiom thm_REAL_LE_NEGTOTAL : forall x : R, (ler (R_of_nat (NUMERAL O)) x) \/ (ler (R_of_nat (NUMERAL O)) (oppr x)).
Axiom thm_REAL_LE_SQUARE : forall x : R, ler (R_of_nat (NUMERAL O)) (mulr x x).
Axiom thm_REAL_MUL_RID : forall x : R, (mulr x (R_of_nat (NUMERAL (BIT1 O)))) = x.
Axiom thm_REAL_POW_2 : forall x : R, (expr x (NUMERAL (BIT0 (BIT1 O)))) = (mulr x x).
Axiom thm_REAL_POLY_CLAUSES : (forall x : R, forall y : R, forall z : R, (addr x (addr y z)) = (addr (addr x y) z)) /\ ((forall x : R, forall y : R, (addr x y) = (addr y x)) /\ ((forall x : R, (addr (R_of_nat (NUMERAL O)) x) = x) /\ ((forall x : R, forall y : R, forall z : R, (mulr x (mulr y z)) = (mulr (mulr x y) z)) /\ ((forall x : R, forall y : R, (mulr x y) = (mulr y x)) /\ ((forall x : R, (mulr (R_of_nat (NUMERAL (BIT1 O))) x) = x) /\ ((forall x : R, (mulr (R_of_nat (NUMERAL O)) x) = (R_of_nat (NUMERAL O))) /\ ((forall x : R, forall y : R, forall z : R, (mulr x (addr y z)) = (addr (mulr x y) (mulr x z))) /\ ((forall x : R, (expr x (NUMERAL O)) = (R_of_nat (NUMERAL (BIT1 O)))) /\ (forall x : R, forall n : nat, (expr x (S n)) = (mulr x (expr x n))))))))))).
Axiom thm_REAL_POLY_NEG_CLAUSES : (forall x : R, (oppr x) = (mulr (oppr (R_of_nat (NUMERAL (BIT1 O)))) x)) /\ (forall x : R, forall y : R, (subr x y) = (addr x (mulr (oppr (R_of_nat (NUMERAL (BIT1 O)))) y))).
Axiom thm_REAL_POS : forall n : nat, ler (R_of_nat (NUMERAL O)) (R_of_nat n).
Axiom thm_REAL_LT_NZ : forall n : nat, (~ ((R_of_nat n) = (R_of_nat (NUMERAL O)))) = (ltr (R_of_nat (NUMERAL O)) (R_of_nat n)).
Axiom thm_REAL_POS_LT : forall n : nat, ltr (R_of_nat (NUMERAL O)) (R_of_nat (S n)).
Axiom thm_REAL_OF_NUM_LT : forall m : nat, forall n : nat, (ltr (R_of_nat m) (R_of_nat n)) = (ltn m n).
Axiom thm_REAL_OF_NUM_GE : forall m : nat, forall n : nat, (ger (R_of_nat m) (R_of_nat n)) = (geqn m n).
Axiom thm_REAL_OF_NUM_GT : forall m : nat, forall n : nat, (gtr (R_of_nat m) (R_of_nat n)) = (gtn m n).
Axiom thm_REAL_OF_NUM_MAX : forall m : nat, forall n : nat, (maxr (R_of_nat m) (R_of_nat n)) = (R_of_nat (maxn m n)).
Axiom thm_REAL_OF_NUM_MIN : forall m : nat, forall n : nat, (minr (R_of_nat m) (R_of_nat n)) = (R_of_nat (minn m n)).
Axiom thm_REAL_OF_NUM_SUC : forall n : nat, (addr (R_of_nat n) (R_of_nat (NUMERAL (BIT1 O)))) = (R_of_nat (S n)).
Axiom thm_REAL_OF_NUM_SUB : forall m : nat, forall n : nat, (leqn m n) -> (subr (R_of_nat n) (R_of_nat m)) = (R_of_nat (subn n m)).
Axiom thm_REAL_OF_NUM_SUB_CASES : forall m : nat, forall n : nat, (subr (R_of_nat m) (R_of_nat n)) = (@COND R (leqn n m) (R_of_nat (subn m n)) (oppr (R_of_nat (subn n m)))).
Axiom thm_REAL_OF_NUM_CLAUSES : (forall m : nat, forall n : nat, ((R_of_nat m) = (R_of_nat n)) = (m = n)) /\ ((forall m : nat, forall n : nat, (ger (R_of_nat m) (R_of_nat n)) = (geqn m n)) /\ ((forall m : nat, forall n : nat, (gtr (R_of_nat m) (R_of_nat n)) = (gtn m n)) /\ ((forall m : nat, forall n : nat, (ler (R_of_nat m) (R_of_nat n)) = (leqn m n)) /\ ((forall m : nat, forall n : nat, (ltr (R_of_nat m) (R_of_nat n)) = (ltn m n)) /\ ((forall m : nat, forall n : nat, (maxr (R_of_nat m) (R_of_nat n)) = (R_of_nat (maxn m n))) /\ ((forall m : nat, forall n : nat, (minr (R_of_nat m) (R_of_nat n)) = (R_of_nat (minn m n))) /\ ((forall m : nat, forall n : nat, (addr (R_of_nat m) (R_of_nat n)) = (R_of_nat (addn m n))) /\ ((forall m : nat, forall n : nat, (mulr (R_of_nat m) (R_of_nat n)) = (R_of_nat (muln m n))) /\ (forall x : nat, forall n : nat, (expr (R_of_nat x) n) = (R_of_nat (expn x n))))))))))).
Axiom thm_REAL_MUL_AC : forall (n : R) (m : R) (p : R), ((mulr m n) = (mulr n m)) /\ (((mulr (mulr m n) p) = (mulr m (mulr n p))) /\ ((mulr m (mulr n p)) = (mulr n (mulr m p)))).
Axiom thm_REAL_ADD_RDISTRIB : forall x : R, forall y : R, forall z : R, (mulr (addr x y) z) = (addr (mulr x z) (mulr y z)).
Axiom thm_REAL_LT_LADD_IMP : forall x : R, forall y : R, forall z : R, (ltr y z) -> ltr (addr x y) (addr x z).
Axiom thm_REAL_LT_MUL : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr (R_of_nat (NUMERAL O)) y)) -> ltr (R_of_nat (NUMERAL O)) (mulr x y).
Axiom thm_REAL_EQ_ADD_LCANCEL_0 : forall x : R, forall y : R, ((addr x y) = x) = (y = (R_of_nat (NUMERAL O))).
Axiom thm_REAL_EQ_ADD_RCANCEL_0 : forall x : R, forall y : R, ((addr x y) = y) = (x = (R_of_nat (NUMERAL O))).
Axiom thm_REAL_LNEG_UNIQ : forall x : R, forall y : R, ((addr x y) = (R_of_nat (NUMERAL O))) = (x = (oppr y)).
Axiom thm_REAL_RNEG_UNIQ : forall x : R, forall y : R, ((addr x y) = (R_of_nat (NUMERAL O))) = (y = (oppr x)).
Axiom thm_REAL_NEG_LMUL : forall x : R, forall y : R, (oppr (mulr x y)) = (mulr (oppr x) y).
Axiom thm_REAL_NEG_RMUL : forall x : R, forall y : R, (oppr (mulr x y)) = (mulr x (oppr y)).
Axiom thm_REAL_NEG_MUL2 : forall x : R, forall y : R, (mulr (oppr x) (oppr y)) = (mulr x y).
Axiom thm_REAL_LT_LADD : forall x : R, forall y : R, forall z : R, (ltr (addr x y) (addr x z)) = (ltr y z).
Axiom thm_REAL_LT_RADD : forall x : R, forall y : R, forall z : R, (ltr (addr x z) (addr y z)) = (ltr x y).
Axiom thm_REAL_LT_ANTISYM : forall x : R, forall y : R, ~ ((ltr x y) /\ (ltr y x)).
Axiom thm_REAL_LT_GT : forall x : R, forall y : R, (ltr x y) -> ~ (ltr y x).
Axiom thm_REAL_NOT_EQ : forall x : R, forall y : R, (~ (x = y)) = ((ltr x y) \/ (ltr y x)).
Axiom thm_REAL_NOT_LE : forall x : R, forall y : R, (~ (ler x y)) = (ltr y x).
Axiom thm_REAL_LET_ANTISYM : forall x : R, forall y : R, ~ ((ler x y) /\ (ltr y x)).
Axiom thm_REAL_NEG_LT0 : forall x : R, (ltr (oppr x) (R_of_nat (NUMERAL O))) = (ltr (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_NEG_GT0 : forall x : R, (ltr (R_of_nat (NUMERAL O)) (oppr x)) = (ltr x (R_of_nat (NUMERAL O))).
Axiom thm_REAL_NEG_LE0 : forall x : R, (ler (oppr x) (R_of_nat (NUMERAL O))) = (ler (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_NEG_GE0 : forall x : R, (ler (R_of_nat (NUMERAL O)) (oppr x)) = (ler x (R_of_nat (NUMERAL O))).
Axiom thm_REAL_LT_TOTAL : forall x : R, forall y : R, (x = y) \/ ((ltr x y) \/ (ltr y x)).
Axiom thm_REAL_LT_NEGTOTAL : forall x : R, (x = (R_of_nat (NUMERAL O))) \/ ((ltr (R_of_nat (NUMERAL O)) x) \/ (ltr (R_of_nat (NUMERAL O)) (oppr x))).
Axiom thm_REAL_LE_01 : ler (R_of_nat (NUMERAL O)) (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_LT_01 : ltr (R_of_nat (NUMERAL O)) (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_LE_LADD : forall x : R, forall y : R, forall z : R, (ler (addr x y) (addr x z)) = (ler y z).
Axiom thm_REAL_LE_RADD : forall x : R, forall y : R, forall z : R, (ler (addr x z) (addr y z)) = (ler x y).
Axiom thm_REAL_LT_ADD2 : forall w : R, forall x : R, forall y : R, forall z : R, ((ltr w x) /\ (ltr y z)) -> ltr (addr w y) (addr x z).
Axiom thm_REAL_LE_ADD2 : forall w : R, forall x : R, forall y : R, forall z : R, ((ler w x) /\ (ler y z)) -> ler (addr w y) (addr x z).
Axiom thm_REAL_LT_LNEG : forall x : R, forall y : R, (ltr (oppr x) y) = (ltr (R_of_nat (NUMERAL O)) (addr x y)).
Axiom thm_REAL_LT_RNEG : forall x : R, forall y : R, (ltr x (oppr y)) = (ltr (addr x y) (R_of_nat (NUMERAL O))).
Axiom thm_REAL_LT_ADDNEG : forall x : R, forall y : R, forall z : R, (ltr y (addr x (oppr z))) = (ltr (addr y z) x).
Axiom thm_REAL_LT_ADDNEG2 : forall x : R, forall y : R, forall z : R, (ltr (addr x (oppr y)) z) = (ltr x (addr z y)).
Axiom thm_REAL_LT_ADD1 : forall x : R, forall y : R, (ler x y) -> ltr x (addr y (R_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_REAL_SUB_ADD : forall x : R, forall y : R, (addr (subr x y) y) = x.
Axiom thm_REAL_SUB_ADD2 : forall x : R, forall y : R, (addr y (subr x y)) = x.
Axiom thm_REAL_SUB_REFL : forall x : R, (subr x x) = (R_of_nat (NUMERAL O)).
Axiom thm_REAL_LE_DOUBLE : forall x : R, (ler (R_of_nat (NUMERAL O)) (addr x x)) = (ler (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_LE_NEGL : forall x : R, (ler (oppr x) x) = (ler (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_LE_NEGR : forall x : R, (ler x (oppr x)) = (ler x (R_of_nat (NUMERAL O))).
Axiom thm_REAL_NEG_EQ_0 : forall x : R, ((oppr x) = (R_of_nat (NUMERAL O))) = (x = (R_of_nat (NUMERAL O))).
Axiom thm_REAL_ADD_SUB : forall x : R, forall y : R, (subr (addr x y) x) = y.
Axiom thm_REAL_NEG_EQ : forall x : R, forall y : R, ((oppr x) = y) = (x = (oppr y)).
Axiom thm_REAL_NEG_MINUS1 : forall x : R, (oppr x) = (mulr (oppr (R_of_nat (NUMERAL (BIT1 O)))) x).
Axiom thm_REAL_LT_IMP_NE : forall x : R, forall y : R, (ltr x y) -> ~ (x = y).
Axiom thm_REAL_LE_ADDR : forall x : R, forall y : R, (ler x (addr x y)) = (ler (R_of_nat (NUMERAL O)) y).
Axiom thm_REAL_LE_ADDL : forall x : R, forall y : R, (ler y (addr x y)) = (ler (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_LT_ADDR : forall x : R, forall y : R, (ltr x (addr x y)) = (ltr (R_of_nat (NUMERAL O)) y).
Axiom thm_REAL_LT_ADDL : forall x : R, forall y : R, (ltr y (addr x y)) = (ltr (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_SUB_SUB : forall x : R, forall y : R, (subr (subr x y) x) = (oppr y).
Axiom thm_REAL_LT_ADD_SUB : forall x : R, forall y : R, forall z : R, (ltr (addr x y) z) = (ltr x (subr z y)).
Axiom thm_REAL_LT_SUB_RADD : forall x : R, forall y : R, forall z : R, (ltr (subr x y) z) = (ltr x (addr z y)).
Axiom thm_REAL_LT_SUB_LADD : forall x : R, forall y : R, forall z : R, (ltr x (subr y z)) = (ltr (addr x z) y).
Axiom thm_REAL_LE_SUB_LADD : forall x : R, forall y : R, forall z : R, (ler x (subr y z)) = (ler (addr x z) y).
Axiom thm_REAL_LE_SUB_RADD : forall x : R, forall y : R, forall z : R, (ler (subr x y) z) = (ler x (addr z y)).
Axiom thm_REAL_ADD2_SUB2 : forall a : R, forall b : R, forall c : R, forall d : R, (subr (addr a b) (addr c d)) = (addr (subr a c) (subr b d)).
Axiom thm_REAL_SUB_LZERO : forall x : R, (subr (R_of_nat (NUMERAL O)) x) = (oppr x).
Axiom thm_REAL_SUB_RZERO : forall x : R, (subr x (R_of_nat (NUMERAL O))) = x.
Axiom thm_REAL_LET_ADD2 : forall w : R, forall x : R, forall y : R, forall z : R, ((ler w x) /\ (ltr y z)) -> ltr (addr w y) (addr x z).
Axiom thm_REAL_LTE_ADD2 : forall w : R, forall x : R, forall y : R, forall z : R, ((ltr w x) /\ (ler y z)) -> ltr (addr w y) (addr x z).
Axiom thm_REAL_SUB_LNEG : forall x : R, forall y : R, (subr (oppr x) y) = (oppr (addr x y)).
Axiom thm_REAL_SUB_RNEG : forall x : R, forall y : R, (subr x (oppr y)) = (addr x y).
Axiom thm_REAL_SUB_NEG2 : forall x : R, forall y : R, (subr (oppr x) (oppr y)) = (subr y x).
Axiom thm_REAL_SUB_TRIANGLE : forall a : R, forall b : R, forall c : R, (addr (subr a b) (subr b c)) = (subr a c).
Axiom thm_REAL_EQ_SUB_LADD : forall x : R, forall y : R, forall z : R, (x = (subr y z)) = ((addr x z) = y).
Axiom thm_REAL_EQ_SUB_RADD : forall x : R, forall y : R, forall z : R, ((subr x y) = z) = (x = (addr z y)).
Axiom thm_REAL_SUB_SUB2 : forall x : R, forall y : R, (subr x (subr x y)) = y.
Axiom thm_REAL_ADD_SUB2 : forall x : R, forall y : R, (subr x (addr x y)) = (oppr y).
Axiom thm_REAL_EQ_IMP_LE : forall x : R, forall y : R, (x = y) -> ler x y.
Axiom thm_REAL_LT_IMP_NZ : forall x : R, (ltr (R_of_nat (NUMERAL O)) x) -> ~ (x = (R_of_nat (NUMERAL O))).
Axiom thm_REAL_DIFFSQ : forall x : R, forall y : R, (mulr (addr x y) (subr x y)) = (subr (mulr x x) (mulr y y)).
Axiom thm_REAL_EQ_NEG2 : forall x : R, forall y : R, ((oppr x) = (oppr y)) = (x = y).
Axiom thm_REAL_LT_NEG2 : forall x : R, forall y : R, (ltr (oppr x) (oppr y)) = (ltr y x).
Axiom thm_REAL_SUB_LDISTRIB : forall x : R, forall y : R, forall z : R, (mulr x (subr y z)) = (subr (mulr x y) (mulr x z)).
Axiom thm_REAL_SUB_RDISTRIB : forall x : R, forall y : R, forall z : R, (mulr (subr x y) z) = (subr (mulr x z) (mulr y z)).
Axiom thm_REAL_ABS_ZERO : forall x : R, ((normr x) = (R_of_nat (NUMERAL O))) = (x = (R_of_nat (NUMERAL O))).
Axiom thm_REAL_ABS_0 : (normr (R_of_nat (NUMERAL O))) = (R_of_nat (NUMERAL O)).
Axiom thm_REAL_ABS_1 : (normr (R_of_nat (NUMERAL (BIT1 O)))) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_ABS_TRIANGLE : forall x : R, forall y : R, ler (normr (addr x y)) (addr (normr x) (normr y)).
Axiom thm_REAL_ABS_TRIANGLE_LE : forall x : R, forall y : R, forall z : R, (ler (addr (normr x) (normr (subr y x))) z) -> ler (normr y) z.
Axiom thm_REAL_ABS_TRIANGLE_LT : forall x : R, forall y : R, forall z : R, (ltr (addr (normr x) (normr (subr y x))) z) -> ltr (normr y) z.
Axiom thm_REAL_ABS_POS : forall x : R, ler (R_of_nat (NUMERAL O)) (normr x).
Axiom thm_REAL_ABS_SUB : forall x : R, forall y : R, (normr (subr x y)) = (normr (subr y x)).
Axiom thm_REAL_ABS_NZ : forall x : R, (~ (x = (R_of_nat (NUMERAL O)))) = (ltr (R_of_nat (NUMERAL O)) (normr x)).
Axiom thm_REAL_ABS_ABS : forall x : R, (normr (normr x)) = (normr x).
Axiom thm_REAL_ABS_LE : forall x : R, ler x (normr x).
Axiom thm_REAL_ABS_REFL : forall x : R, ((normr x) = x) = (ler (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_ABS_BETWEEN : forall x : R, forall y : R, forall d : R, ((ltr (R_of_nat (NUMERAL O)) d) /\ ((ltr (subr x d) y) /\ (ltr y (addr x d)))) = (ltr (normr (subr y x)) d).
Axiom thm_REAL_ABS_BOUND : forall x : R, forall y : R, forall d : R, (ltr (normr (subr x y)) d) -> ltr y (addr x d).
Axiom thm_REAL_ABS_STILLNZ : forall x : R, forall y : R, (ltr (normr (subr x y)) (normr y)) -> ~ (x = (R_of_nat (NUMERAL O))).
Axiom thm_REAL_ABS_CASES : forall x : R, (x = (R_of_nat (NUMERAL O))) \/ (ltr (R_of_nat (NUMERAL O)) (normr x)).
Axiom thm_REAL_ABS_BETWEEN1 : forall x : R, forall y : R, forall z : R, ((ltr x z) /\ (ltr (normr (subr y x)) (subr z x))) -> ltr y z.
Axiom thm_REAL_ABS_SIGN : forall x : R, forall y : R, (ltr (normr (subr x y)) y) -> ltr (R_of_nat (NUMERAL O)) x.
Axiom thm_REAL_ABS_SIGN2 : forall x : R, forall y : R, (ltr (normr (subr x y)) (oppr y)) -> ltr x (R_of_nat (NUMERAL O)).
Axiom thm_REAL_ABS_CIRCLE : forall x : R, forall y : R, forall h : R, (ltr (normr h) (subr (normr y) (normr x))) -> ltr (normr (addr x h)) (normr y).
Axiom thm_REAL_SUB_ABS : forall x : R, forall y : R, ler (subr (normr x) (normr y)) (normr (subr x y)).
Axiom thm_REAL_ABS_SUB_ABS : forall x : R, forall y : R, ler (normr (subr (normr x) (normr y))) (normr (subr x y)).
Axiom thm_REAL_ABS_BETWEEN2 : forall x0 : R, forall x : R, forall y0 : R, forall y : R, ((ltr x0 y0) /\ ((ltr (mulr (R_of_nat (NUMERAL (BIT0 (BIT1 O)))) (normr (subr x x0))) (subr y0 x0)) /\ (ltr (mulr (R_of_nat (NUMERAL (BIT0 (BIT1 O)))) (normr (subr y y0))) (subr y0 x0)))) -> ltr x y.
Axiom thm_REAL_ABS_BOUNDS : forall x : R, forall k : R, (ler (normr x) k) = ((ler (oppr k) x) /\ (ler x k)).
Axiom thm_REAL_BOUNDS_LE : forall x : R, forall k : R, ((ler (oppr k) x) /\ (ler x k)) = (ler (normr x) k).
Axiom thm_REAL_BOUNDS_LT : forall x : R, forall k : R, ((ltr (oppr k) x) /\ (ltr x k)) = (ltr (normr x) k).
Axiom thm_REAL_MIN_MAX : forall x : R, forall y : R, (minr x y) = (oppr (maxr (oppr x) (oppr y))).
Axiom thm_REAL_MAX_MIN : forall x : R, forall y : R, (maxr x y) = (oppr (minr (oppr x) (oppr y))).
Axiom thm_REAL_MAX_MAX : forall x : R, forall y : R, (ler x (maxr x y)) /\ (ler y (maxr x y)).
Axiom thm_REAL_MIN_MIN : forall x : R, forall y : R, (ler (minr x y) x) /\ (ler (minr x y) y).
Axiom thm_REAL_MAX_SYM : forall x : R, forall y : R, (maxr x y) = (maxr y x).
Axiom thm_REAL_MIN_SYM : forall x : R, forall y : R, (minr x y) = (minr y x).
Axiom thm_REAL_LE_MAX : forall x : R, forall y : R, forall z : R, (ler z (maxr x y)) = ((ler z x) \/ (ler z y)).
Axiom thm_REAL_LE_MIN : forall x : R, forall y : R, forall z : R, (ler z (minr x y)) = ((ler z x) /\ (ler z y)).
Axiom thm_REAL_LT_MAX : forall x : R, forall y : R, forall z : R, (ltr z (maxr x y)) = ((ltr z x) \/ (ltr z y)).
Axiom thm_REAL_LT_MIN : forall x : R, forall y : R, forall z : R, (ltr z (minr x y)) = ((ltr z x) /\ (ltr z y)).
Axiom thm_REAL_MAX_LE : forall x : R, forall y : R, forall z : R, (ler (maxr x y) z) = ((ler x z) /\ (ler y z)).
Axiom thm_REAL_MIN_LE : forall x : R, forall y : R, forall z : R, (ler (minr x y) z) = ((ler x z) \/ (ler y z)).
Axiom thm_REAL_MAX_LT : forall x : R, forall y : R, forall z : R, (ltr (maxr x y) z) = ((ltr x z) /\ (ltr y z)).
Axiom thm_REAL_MIN_LT : forall x : R, forall y : R, forall z : R, (ltr (minr x y) z) = ((ltr x z) \/ (ltr y z)).
Axiom thm_REAL_MAX_ASSOC : forall x : R, forall y : R, forall z : R, (maxr x (maxr y z)) = (maxr (maxr x y) z).
Axiom thm_REAL_MIN_ASSOC : forall x : R, forall y : R, forall z : R, (minr x (minr y z)) = (minr (minr x y) z).
Axiom thm_REAL_MAX_ACI : forall (z : R) (x : R) (y : R), ((maxr x y) = (maxr y x)) /\ (((maxr (maxr x y) z) = (maxr x (maxr y z))) /\ (((maxr x (maxr y z)) = (maxr y (maxr x z))) /\ (((maxr x x) = x) /\ ((maxr x (maxr x y)) = (maxr x y))))).
Axiom thm_REAL_MIN_ACI : forall (z : R) (x : R) (y : R), ((minr x y) = (minr y x)) /\ (((minr (minr x y) z) = (minr x (minr y z))) /\ (((minr x (minr y z)) = (minr y (minr x z))) /\ (((minr x x) = x) /\ ((minr x (minr x y)) = (minr x y))))).
Axiom thm_REAL_ABS_MUL : forall x : R, forall y : R, (normr (mulr x y)) = (mulr (normr x) (normr y)).
Axiom thm_REAL_POW_LE : forall x : R, forall n : nat, (ler (R_of_nat (NUMERAL O)) x) -> ler (R_of_nat (NUMERAL O)) (expr x n).
Axiom thm_REAL_POW_LT : forall x : R, forall n : nat, (ltr (R_of_nat (NUMERAL O)) x) -> ltr (R_of_nat (NUMERAL O)) (expr x n).
Axiom thm_REAL_ABS_POW : forall x : R, forall n : nat, (normr (expr x n)) = (expr (normr x) n).
Axiom thm_REAL_LE_LMUL : forall x : R, forall y : R, forall z : R, ((ler (R_of_nat (NUMERAL O)) x) /\ (ler y z)) -> ler (mulr x y) (mulr x z).
Axiom thm_REAL_LE_RMUL : forall x : R, forall y : R, forall z : R, ((ler x y) /\ (ler (R_of_nat (NUMERAL O)) z)) -> ler (mulr x z) (mulr y z).
Axiom thm_REAL_LT_LMUL : forall x : R, forall y : R, forall z : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr y z)) -> ltr (mulr x y) (mulr x z).
Axiom thm_REAL_LT_RMUL : forall x : R, forall y : R, forall z : R, ((ltr x y) /\ (ltr (R_of_nat (NUMERAL O)) z)) -> ltr (mulr x z) (mulr y z).
Axiom thm_REAL_EQ_MUL_LCANCEL : forall x : R, forall y : R, forall z : R, ((mulr x y) = (mulr x z)) = ((x = (R_of_nat (NUMERAL O))) \/ (y = z)).
Axiom thm_REAL_EQ_MUL_RCANCEL : forall x : R, forall y : R, forall z : R, ((mulr x z) = (mulr y z)) = ((x = y) \/ (z = (R_of_nat (NUMERAL O)))).
Axiom thm_REAL_MUL_LINV_UNIQ : forall x : R, forall y : R, ((mulr x y) = (R_of_nat (NUMERAL (BIT1 O)))) -> (invr y) = x.
Axiom thm_REAL_MUL_RINV_UNIQ : forall x : R, forall y : R, ((mulr x y) = (R_of_nat (NUMERAL (BIT1 O)))) -> (invr x) = y.
Axiom thm_REAL_INV_INV : forall x : R, (invr (invr x)) = x.
Axiom thm_REAL_EQ_INV2 : forall x : R, forall y : R, ((invr x) = (invr y)) = (x = y).
Axiom thm_REAL_INV_EQ_0 : forall x : R, ((invr x) = (R_of_nat (NUMERAL O))) = (x = (R_of_nat (NUMERAL O))).
Axiom thm_REAL_LT_INV : forall x : R, (ltr (R_of_nat (NUMERAL O)) x) -> ltr (R_of_nat (NUMERAL O)) (invr x).
Axiom thm_REAL_LT_INV_EQ : forall x : R, (ltr (R_of_nat (NUMERAL O)) (invr x)) = (ltr (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_INV_NEG : forall x : R, (invr (oppr x)) = (oppr (invr x)).
Axiom thm_REAL_LE_INV_EQ : forall x : R, (ler (R_of_nat (NUMERAL O)) (invr x)) = (ler (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_LE_INV : forall x : R, (ler (R_of_nat (NUMERAL O)) x) -> ler (R_of_nat (NUMERAL O)) (invr x).
Axiom thm_REAL_MUL_RINV : forall x : R, (~ (x = (R_of_nat (NUMERAL O)))) -> (mulr x (invr x)) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_INV_1 : (invr (R_of_nat (NUMERAL (BIT1 O)))) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_INV_EQ_1 : forall x : R, ((invr x) = (R_of_nat (NUMERAL (BIT1 O)))) = (x = (R_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_REAL_DIV_1 : forall x : R, (divr x (R_of_nat (NUMERAL (BIT1 O)))) = x.
Axiom thm_REAL_DIV_REFL : forall x : R, (~ (x = (R_of_nat (NUMERAL O)))) -> (divr x x) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_DIV_RMUL : forall x : R, forall y : R, (~ (y = (R_of_nat (NUMERAL O)))) -> (mulr (divr x y) y) = x.
Axiom thm_REAL_DIV_LMUL : forall x : R, forall y : R, (~ (y = (R_of_nat (NUMERAL O)))) -> (mulr y (divr x y)) = x.
Axiom thm_REAL_DIV_EQ_1 : forall x : R, forall y : R, ((divr x y) = (R_of_nat (NUMERAL (BIT1 O)))) = ((x = y) /\ ((~ (x = (R_of_nat (NUMERAL O)))) /\ (~ (y = (R_of_nat (NUMERAL O)))))).
Axiom thm_REAL_ABS_INV : forall x : R, (normr (invr x)) = (invr (normr x)).
Axiom thm_REAL_ABS_DIV : forall x : R, forall y : R, (normr (divr x y)) = (divr (normr x) (normr y)).
Axiom thm_REAL_INV_MUL : forall x : R, forall y : R, (invr (mulr x y)) = (mulr (invr x) (invr y)).
Axiom thm_REAL_INV_DIV : forall x : R, forall y : R, (invr (divr x y)) = (divr y x).
Axiom thm_REAL_POW_MUL : forall x : R, forall y : R, forall n : nat, (expr (mulr x y) n) = (mulr (expr x n) (expr y n)).
Axiom thm_REAL_POW_INV : forall x : R, forall n : nat, (expr (invr x) n) = (invr (expr x n)).
Axiom thm_REAL_INV_POW : forall x : R, forall n : nat, (invr (expr x n)) = (expr (invr x) n).
Axiom thm_REAL_POW_DIV : forall x : R, forall y : R, forall n : nat, (expr (divr x y) n) = (divr (expr x n) (expr y n)).
Axiom thm_REAL_DIV_EQ_0 : forall x : R, forall y : R, ((divr x y) = (R_of_nat (NUMERAL O))) = ((x = (R_of_nat (NUMERAL O))) \/ (y = (R_of_nat (NUMERAL O)))).
Axiom thm_REAL_POW_ADD : forall x : R, forall m : nat, forall n : nat, (expr x (addn m n)) = (mulr (expr x m) (expr x n)).
Axiom thm_REAL_POW_NZ : forall x : R, forall n : nat, (~ (x = (R_of_nat (NUMERAL O)))) -> ~ ((expr x n) = (R_of_nat (NUMERAL O))).
Axiom thm_REAL_POW_SUB : forall x : R, forall m : nat, forall n : nat, ((~ (x = (R_of_nat (NUMERAL O)))) /\ (leqn m n)) -> (expr x (subn n m)) = (divr (expr x n) (expr x m)).
Axiom thm_REAL_LT_LCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr (mulr x y) (mulr x z))) -> ltr y z.
Axiom thm_REAL_LT_RCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((ltr (R_of_nat (NUMERAL O)) z) /\ (ltr (mulr x z) (mulr y z))) -> ltr x y.
Axiom thm_REAL_LE_LCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ler (mulr x y) (mulr x z))) -> ler y z.
Axiom thm_REAL_LE_RCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((ltr (R_of_nat (NUMERAL O)) z) /\ (ler (mulr x z) (mulr y z))) -> ler x y.
Axiom thm_REAL_LE_RMUL_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ler (mulr x z) (mulr y z)) = (ler x y).
Axiom thm_REAL_LE_LMUL_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ler (mulr z x) (mulr z y)) = (ler x y).
Axiom thm_REAL_LT_RMUL_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ltr (mulr x z) (mulr y z)) = (ltr x y).
Axiom thm_REAL_LT_LMUL_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ltr (mulr z x) (mulr z y)) = (ltr x y).
Axiom thm_REAL_LE_MUL_EQ : (forall x : R, forall y : R, (ltr (R_of_nat (NUMERAL O)) x) -> (ler (R_of_nat (NUMERAL O)) (mulr x y)) = (ler (R_of_nat (NUMERAL O)) y)) /\ (forall x : R, forall y : R, (ltr (R_of_nat (NUMERAL O)) y) -> (ler (R_of_nat (NUMERAL O)) (mulr x y)) = (ler (R_of_nat (NUMERAL O)) x)).
Axiom thm_REAL_LT_MUL_EQ : (forall x : R, forall y : R, (ltr (R_of_nat (NUMERAL O)) x) -> (ltr (R_of_nat (NUMERAL O)) (mulr x y)) = (ltr (R_of_nat (NUMERAL O)) y)) /\ (forall x : R, forall y : R, (ltr (R_of_nat (NUMERAL O)) y) -> (ltr (R_of_nat (NUMERAL O)) (mulr x y)) = (ltr (R_of_nat (NUMERAL O)) x)).
Axiom thm_REAL_MUL_POS_LT : forall x : R, forall y : R, (ltr (R_of_nat (NUMERAL O)) (mulr x y)) = (((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr (R_of_nat (NUMERAL O)) y)) \/ ((ltr x (R_of_nat (NUMERAL O))) /\ (ltr y (R_of_nat (NUMERAL O))))).
Axiom thm_REAL_MUL_POS_LE : forall x : R, forall y : R, (ler (R_of_nat (NUMERAL O)) (mulr x y)) = ((x = (R_of_nat (NUMERAL O))) \/ ((y = (R_of_nat (NUMERAL O))) \/ (((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr (R_of_nat (NUMERAL O)) y)) \/ ((ltr x (R_of_nat (NUMERAL O))) /\ (ltr y (R_of_nat (NUMERAL O))))))).
Axiom thm_REAL_LE_RDIV_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ler x (divr y z)) = (ler (mulr x z) y).
Axiom thm_REAL_LE_LDIV_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ler (divr x z) y) = (ler x (mulr y z)).
Axiom thm_REAL_LT_RDIV_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ltr x (divr y z)) = (ltr (mulr x z) y).
Axiom thm_REAL_LT_LDIV_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ltr (divr x z) y) = (ltr x (mulr y z)).
Axiom thm_REAL_EQ_RDIV_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (x = (divr y z)) = ((mulr x z) = y).
Axiom thm_REAL_EQ_LDIV_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> ((divr x z) = y) = (x = (mulr y z)).
Axiom thm_REAL_LT_DIV2_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ltr (divr x z) (divr y z)) = (ltr x y).
Axiom thm_REAL_LE_DIV2_EQ : forall x : R, forall y : R, forall z : R, (ltr (R_of_nat (NUMERAL O)) z) -> (ler (divr x z) (divr y z)) = (ler x y).
Axiom thm_REAL_MUL_2 : forall x : R, (mulr (R_of_nat (NUMERAL (BIT0 (BIT1 O)))) x) = (addr x x).
Axiom thm_REAL_POW_EQ_0 : forall x : R, forall n : nat, ((expr x n) = (R_of_nat (NUMERAL O))) = ((x = (R_of_nat (NUMERAL O))) /\ (~ (n = (NUMERAL O)))).
Axiom thm_REAL_LE_MUL2 : forall w : R, forall x : R, forall y : R, forall z : R, ((ler (R_of_nat (NUMERAL O)) w) /\ ((ler w x) /\ ((ler (R_of_nat (NUMERAL O)) y) /\ (ler y z)))) -> ler (mulr w y) (mulr x z).
Axiom thm_REAL_LT_MUL2 : forall w : R, forall x : R, forall y : R, forall z : R, ((ler (R_of_nat (NUMERAL O)) w) /\ ((ltr w x) /\ ((ler (R_of_nat (NUMERAL O)) y) /\ (ltr y z)))) -> ltr (mulr w y) (mulr x z).
Axiom thm_REAL_LT_SQUARE : forall x : R, (ltr (R_of_nat (NUMERAL O)) (mulr x x)) = (~ (x = (R_of_nat (NUMERAL O)))).
Axiom thm_REAL_POW_1 : forall x : R, (expr x (NUMERAL (BIT1 O))) = x.
Axiom thm_REAL_POW_ONE : forall n : nat, (expr (R_of_nat (NUMERAL (BIT1 O))) n) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_LT_INV2 : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr x y)) -> ltr (invr y) (invr x).
Axiom thm_REAL_LE_INV2 : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ler x y)) -> ler (invr y) (invr x).
Axiom thm_REAL_LT_LINV : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) y) /\ (ltr (invr y) x)) -> ltr (invr x) y.
Axiom thm_REAL_LT_RINV : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr x (invr y))) -> ltr y (invr x).
Axiom thm_REAL_LE_LINV : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) y) /\ (ler (invr y) x)) -> ler (invr x) y.
Axiom thm_REAL_LE_RINV : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ler x (invr y))) -> ler y (invr x).
Axiom thm_REAL_INV_LE_1 : forall x : R, (ler (R_of_nat (NUMERAL (BIT1 O))) x) -> ler (invr x) (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_INV_1_LE : forall x : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ler x (R_of_nat (NUMERAL (BIT1 O))))) -> ler (R_of_nat (NUMERAL (BIT1 O))) (invr x).
Axiom thm_REAL_INV_LT_1 : forall x : R, (ltr (R_of_nat (NUMERAL (BIT1 O))) x) -> ltr (invr x) (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_INV_1_LT : forall x : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr x (R_of_nat (NUMERAL (BIT1 O))))) -> ltr (R_of_nat (NUMERAL (BIT1 O))) (invr x).
Axiom thm_REAL_SUB_INV : forall x : R, forall y : R, ((~ (x = (R_of_nat (NUMERAL O)))) /\ (~ (y = (R_of_nat (NUMERAL O))))) -> (subr (invr x) (invr y)) = (divr (subr y x) (mulr x y)).
Axiom thm_REAL_DOWN : forall d : R, (ltr (R_of_nat (NUMERAL O)) d) -> exists e : R, (ltr (R_of_nat (NUMERAL O)) e) /\ (ltr e d).
Axiom thm_REAL_DOWN2 : forall d1 : R, forall d2 : R, ((ltr (R_of_nat (NUMERAL O)) d1) /\ (ltr (R_of_nat (NUMERAL O)) d2)) -> exists e : R, (ltr (R_of_nat (NUMERAL O)) e) /\ ((ltr e d1) /\ (ltr e d2)).
Axiom thm_REAL_POW_LE2 : forall n : nat, forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) x) /\ (ler x y)) -> ler (expr x n) (expr y n).
Axiom thm_REAL_POW_LE_1 : forall n : nat, forall x : R, (ler (R_of_nat (NUMERAL (BIT1 O))) x) -> ler (R_of_nat (NUMERAL (BIT1 O))) (expr x n).
Axiom thm_REAL_POW_1_LE : forall n : nat, forall x : R, ((ler (R_of_nat (NUMERAL O)) x) /\ (ler x (R_of_nat (NUMERAL (BIT1 O))))) -> ler (expr x n) (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_POW_MONO : forall m : nat, forall n : nat, forall x : R, ((ler (R_of_nat (NUMERAL (BIT1 O))) x) /\ (leqn m n)) -> ler (expr x m) (expr x n).
Axiom thm_REAL_POW_LT2 : forall n : nat, forall x : R, forall y : R, ((~ (n = (NUMERAL O))) /\ ((ler (R_of_nat (NUMERAL O)) x) /\ (ltr x y))) -> ltr (expr x n) (expr y n).
Axiom thm_REAL_POW_LT_1 : forall n : nat, forall x : R, ((~ (n = (NUMERAL O))) /\ (ltr (R_of_nat (NUMERAL (BIT1 O))) x)) -> ltr (R_of_nat (NUMERAL (BIT1 O))) (expr x n).
Axiom thm_REAL_POW_1_LT : forall n : nat, forall x : R, ((~ (n = (NUMERAL O))) /\ ((ler (R_of_nat (NUMERAL O)) x) /\ (ltr x (R_of_nat (NUMERAL (BIT1 O)))))) -> ltr (expr x n) (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_POW_MONO_LT : forall m : nat, forall n : nat, forall x : R, ((ltr (R_of_nat (NUMERAL (BIT1 O))) x) /\ (ltn m n)) -> ltr (expr x m) (expr x n).
Axiom thm_REAL_POW_POW : forall x : R, forall m : nat, forall n : nat, (expr (expr x m) n) = (expr x (muln m n)).
Axiom thm_REAL_EQ_RCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((~ (z = (R_of_nat (NUMERAL O)))) /\ ((mulr x z) = (mulr y z))) -> x = y.
Axiom thm_REAL_EQ_LCANCEL_IMP : forall x : R, forall y : R, forall z : R, ((~ (z = (R_of_nat (NUMERAL O)))) /\ ((mulr z x) = (mulr z y))) -> x = y.
Axiom thm_REAL_LT_DIV : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) x) /\ (ltr (R_of_nat (NUMERAL O)) y)) -> ltr (R_of_nat (NUMERAL O)) (divr x y).
Axiom thm_REAL_LE_DIV : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) x) /\ (ler (R_of_nat (NUMERAL O)) y)) -> ler (R_of_nat (NUMERAL O)) (divr x y).
Axiom thm_REAL_DIV_POW2 : forall x : R, forall m : nat, forall n : nat, (~ (x = (R_of_nat (NUMERAL O)))) -> (divr (expr x m) (expr x n)) = (@COND R (leqn n m) (expr x (subn m n)) (invr (expr x (subn n m)))).
Axiom thm_REAL_DIV_POW2_ALT : forall x : R, forall m : nat, forall n : nat, (~ (x = (R_of_nat (NUMERAL O)))) -> (divr (expr x m) (expr x n)) = (@COND R (ltn n m) (expr x (subn m n)) (invr (expr x (subn n m)))).
Axiom thm_REAL_LT_POW2 : forall n : nat, ltr (R_of_nat (NUMERAL O)) (expr (R_of_nat (NUMERAL (BIT0 (BIT1 O)))) n).
Axiom thm_REAL_LE_POW2 : forall n : nat, ler (R_of_nat (NUMERAL (BIT1 O))) (expr (R_of_nat (NUMERAL (BIT0 (BIT1 O)))) n).
Axiom thm_REAL_POW2_ABS : forall x : R, (expr (normr x) (NUMERAL (BIT0 (BIT1 O)))) = (expr x (NUMERAL (BIT0 (BIT1 O)))).
Axiom thm_REAL_LE_SQUARE_ABS : forall x : R, forall y : R, (ler (normr x) (normr y)) = (ler (expr x (NUMERAL (BIT0 (BIT1 O)))) (expr y (NUMERAL (BIT0 (BIT1 O))))).
Axiom thm_REAL_LT_SQUARE_ABS : forall x : R, forall y : R, (ltr (normr x) (normr y)) = (ltr (expr x (NUMERAL (BIT0 (BIT1 O)))) (expr y (NUMERAL (BIT0 (BIT1 O))))).
Axiom thm_REAL_EQ_SQUARE_ABS : forall x : R, forall y : R, ((normr x) = (normr y)) = ((expr x (NUMERAL (BIT0 (BIT1 O)))) = (expr y (NUMERAL (BIT0 (BIT1 O))))).
Axiom thm_REAL_LE_POW_2 : forall x : R, ler (R_of_nat (NUMERAL O)) (expr x (NUMERAL (BIT0 (BIT1 O)))).
Axiom thm_REAL_LT_POW_2 : forall x : R, (ltr (R_of_nat (NUMERAL O)) (expr x (NUMERAL (BIT0 (BIT1 O))))) = (~ (x = (R_of_nat (NUMERAL O)))).
Axiom thm_REAL_SOS_EQ_0 : forall x : R, forall y : R, ((addr (expr x (NUMERAL (BIT0 (BIT1 O)))) (expr y (NUMERAL (BIT0 (BIT1 O))))) = (R_of_nat (NUMERAL O))) = ((x = (R_of_nat (NUMERAL O))) /\ (y = (R_of_nat (NUMERAL O)))).
Axiom thm_REAL_POW_ZERO : forall n : nat, (expr (R_of_nat (NUMERAL O)) n) = (@COND R (n = (NUMERAL O)) (R_of_nat (NUMERAL (BIT1 O))) (R_of_nat (NUMERAL O))).
Axiom thm_REAL_POW_MONO_INV : forall m : nat, forall n : nat, forall x : R, ((ler (R_of_nat (NUMERAL O)) x) /\ ((ler x (R_of_nat (NUMERAL (BIT1 O)))) /\ (leqn n m))) -> ler (expr x m) (expr x n).
Axiom thm_REAL_POW_LE2_REV : forall n : nat, forall x : R, forall y : R, ((~ (n = (NUMERAL O))) /\ ((ler (R_of_nat (NUMERAL O)) y) /\ (ler (expr x n) (expr y n)))) -> ler x y.
Axiom thm_REAL_POW_LT2_REV : forall n : nat, forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) y) /\ (ltr (expr x n) (expr y n))) -> ltr x y.
Axiom thm_REAL_POW_EQ : forall n : nat, forall x : R, forall y : R, ((~ (n = (NUMERAL O))) /\ ((ler (R_of_nat (NUMERAL O)) x) /\ ((ler (R_of_nat (NUMERAL O)) y) /\ ((expr x n) = (expr y n))))) -> x = y.
Axiom thm_REAL_POW_EQ_ABS : forall n : nat, forall x : R, forall y : R, ((~ (n = (NUMERAL O))) /\ ((expr x n) = (expr y n))) -> (normr x) = (normr y).
Axiom thm_REAL_POW_EQ_1_IMP : forall x : R, forall n : nat, ((~ (n = (NUMERAL O))) /\ ((expr x n) = (R_of_nat (NUMERAL (BIT1 O))))) -> (normr x) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_POW_EQ_1 : forall x : R, forall n : nat, ((expr x n) = (R_of_nat (NUMERAL (BIT1 O)))) = ((((normr x) = (R_of_nat (NUMERAL (BIT1 O)))) /\ ((ltr x (R_of_nat (NUMERAL O))) -> even n)) \/ (n = (NUMERAL O))).
Axiom thm_REAL_POW_LT2_ODD : forall n : nat, forall x : R, forall y : R, ((ltr x y) /\ (oddn n)) -> ltr (expr x n) (expr y n).
Axiom thm_REAL_POW_LE2_ODD : forall n : nat, forall x : R, forall y : R, ((ler x y) /\ (oddn n)) -> ler (expr x n) (expr y n).
Axiom thm_REAL_POW_LT2_ODD_EQ : forall n : nat, forall x : R, forall y : R, (oddn n) -> (ltr (expr x n) (expr y n)) = (ltr x y).
Axiom thm_REAL_POW_LE2_ODD_EQ : forall n : nat, forall x : R, forall y : R, (oddn n) -> (ler (expr x n) (expr y n)) = (ler x y).
Axiom thm_REAL_POW_EQ_ODD_EQ : forall n : nat, forall x : R, forall y : R, (oddn n) -> ((expr x n) = (expr y n)) = (x = y).
Axiom thm_REAL_POW_EQ_ODD : forall n : nat, forall x : R, forall y : R, ((oddn n) /\ ((expr x n) = (expr y n))) -> x = y.
Axiom thm_REAL_POW_EQ_EQ : forall n : nat, forall x : R, forall y : R, ((expr x n) = (expr y n)) = (@COND Prop (even n) ((n = (NUMERAL O)) \/ ((normr x) = (normr y))) (x = y)).
Axiom thm_REAL_EVENPOW_ABS : forall x : R, forall n : nat, (even n) -> (expr (normr x) n) = (expr x n).
Axiom thm_REAL_OF_NUM_MOD : forall m : nat, forall n : nat, (R_of_nat (modn m n)) = (subr (R_of_nat m) (mulr (R_of_nat (divn m n)) (R_of_nat n))).
Axiom thm_REAL_OF_NUM_DIV : forall m : nat, forall n : nat, (R_of_nat (divn m n)) = (subr (divr (R_of_nat m) (R_of_nat n)) (divr (R_of_nat (modn m n)) (R_of_nat n))).
Axiom thm_REAL_CONVEX_BOUND2_LT : forall (b : R), forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((ltr x a) /\ ((ltr y b) /\ ((ler (R_of_nat (NUMERAL O)) u) /\ ((ler (R_of_nat (NUMERAL O)) v) /\ ((addr u v) = (R_of_nat (NUMERAL (BIT1 O)))))))) -> ltr (addr (mulr u x) (mulr v y)) (addr (mulr u a) (mulr v b)).
Axiom thm_REAL_CONVEX_BOUND2_LE : forall (b : R), forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((ler x a) /\ ((ler y b) /\ ((ler (R_of_nat (NUMERAL O)) u) /\ ((ler (R_of_nat (NUMERAL O)) v) /\ ((addr u v) = (R_of_nat (NUMERAL (BIT1 O)))))))) -> ler (addr (mulr u x) (mulr v y)) (addr (mulr u a) (mulr v b)).
Axiom thm_REAL_CONVEX_BOUND_LT : forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((ltr x a) /\ ((ltr y a) /\ ((ler (R_of_nat (NUMERAL O)) u) /\ ((ler (R_of_nat (NUMERAL O)) v) /\ ((addr u v) = (R_of_nat (NUMERAL (BIT1 O)))))))) -> ltr (addr (mulr u x) (mulr v y)) a.
Axiom thm_REAL_CONVEX_BOUND_LE : forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((ler x a) /\ ((ler y a) /\ ((ler (R_of_nat (NUMERAL O)) u) /\ ((ler (R_of_nat (NUMERAL O)) v) /\ ((addr u v) = (R_of_nat (NUMERAL (BIT1 O)))))))) -> ler (addr (mulr u x) (mulr v y)) a.
Axiom thm_REAL_CONVEX_BOUND_GT : forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((ltr a x) /\ ((ltr a y) /\ ((ler (R_of_nat (NUMERAL O)) u) /\ ((ler (R_of_nat (NUMERAL O)) v) /\ ((addr u v) = (R_of_nat (NUMERAL (BIT1 O)))))))) -> ltr a (addr (mulr u x) (mulr v y)).
Axiom thm_REAL_CONVEX_BOUND_GE : forall x : R, forall y : R, forall a : R, forall u : R, forall v : R, ((ler a x) /\ ((ler a y) /\ ((ler (R_of_nat (NUMERAL O)) u) /\ ((ler (R_of_nat (NUMERAL O)) v) /\ ((addr u v) = (R_of_nat (NUMERAL (BIT1 O)))))))) -> ler a (addr (mulr u x) (mulr v y)).
Axiom thm_REAL_CONVEX_BOUNDS_LE : forall x : R, forall y : R, forall a : R, forall b : R, forall u : R, forall v : R, ((ler a x) /\ ((ler x b) /\ ((ler a y) /\ ((ler y b) /\ ((ler (R_of_nat (NUMERAL O)) u) /\ ((ler (R_of_nat (NUMERAL O)) v) /\ ((addr u v) = (R_of_nat (NUMERAL (BIT1 O)))))))))) -> (ler a (addr (mulr u x) (mulr v y))) /\ (ler (addr (mulr u x) (mulr v y)) b).
Axiom thm_REAL_CONVEX_BOUNDS_LT : forall x : R, forall y : R, forall a : R, forall b : R, forall u : R, forall v : R, ((ltr a x) /\ ((ltr x b) /\ ((ltr a y) /\ ((ltr y b) /\ ((ler (R_of_nat (NUMERAL O)) u) /\ ((ler (R_of_nat (NUMERAL O)) v) /\ ((addr u v) = (R_of_nat (NUMERAL (BIT1 O)))))))))) -> (ltr a (addr (mulr u x) (mulr v y))) /\ (ltr (addr (mulr u x) (mulr v y)) b).
Axiom thm_REAL_ARCH_SIMPLE : forall x : R, exists n : nat, ler x (R_of_nat n).
Axiom thm_REAL_ARCH_LT : forall x : R, exists n : nat, ltr x (R_of_nat n).
Axiom thm_REAL_ARCH : forall x : R, (ltr (R_of_nat (NUMERAL O)) x) -> forall y : R, exists n : nat, ltr y (mulr (R_of_nat n) x).
Axiom thm_REAL_ARCH_INV : forall e : R, (ltr (R_of_nat (NUMERAL O)) e) = (exists n : nat, (~ (n = (NUMERAL O))) /\ ((ltr (R_of_nat (NUMERAL O)) (invr (R_of_nat n))) /\ (ltr (invr (R_of_nat n)) e))).
Axiom thm_REAL_POW_LBOUND : forall x : R, forall n : nat, (ler (R_of_nat (NUMERAL O)) x) -> ler (addr (R_of_nat (NUMERAL (BIT1 O))) (mulr (R_of_nat n) x)) (expr (addr (R_of_nat (NUMERAL (BIT1 O))) x) n).
Axiom thm_REAL_ARCH_POW : forall x : R, forall y : R, (ltr (R_of_nat (NUMERAL (BIT1 O))) x) -> exists n : nat, ltr y (expr x n).
Axiom thm_REAL_ARCH_POW2 : forall x : R, exists n : nat, ltr x (expr (R_of_nat (NUMERAL (BIT0 (BIT1 O)))) n).
Axiom thm_REAL_ARCH_POW_INV : forall x : R, forall y : R, ((ltr (R_of_nat (NUMERAL O)) y) /\ (ltr x (R_of_nat (NUMERAL (BIT1 O))))) -> exists n : nat, ltr (expr x n) y.
Axiom thm_real_sgn : forall x : R, (sgr x) = (@COND R (ltr (R_of_nat (NUMERAL O)) x) (R_of_nat (NUMERAL (BIT1 O))) (@COND R (ltr x (R_of_nat (NUMERAL O))) (oppr (R_of_nat (NUMERAL (BIT1 O)))) (R_of_nat (NUMERAL O)))).
Axiom thm_REAL_SGN_0 : (sgr (R_of_nat (NUMERAL O))) = (R_of_nat (NUMERAL O)).
Axiom thm_REAL_SGN_NEG : forall x : R, (sgr (oppr x)) = (oppr (sgr x)).
Axiom thm_REAL_SGN_ABS : forall x : R, (mulr (sgr x) (normr x)) = x.
Axiom thm_REAL_SGN_ABS_ALT : forall x : R, (mulr (sgr x) x) = (normr x).
Axiom thm_REAL_EQ_SGN_ABS : forall x : R, forall y : R, (x = y) = (((sgr x) = (sgr y)) /\ ((normr x) = (normr y))).
Axiom thm_REAL_ABS_SGN : forall x : R, (normr (sgr x)) = (sgr (normr x)).
Axiom thm_REAL_SGN : forall x : R, (sgr x) = (divr x (normr x)).
Axiom thm_REAL_SGN_MUL : forall x : R, forall y : R, (sgr (mulr x y)) = (mulr (sgr x) (sgr y)).
Axiom thm_REAL_SGN_INV : forall x : R, (sgr (invr x)) = (sgr x).
Axiom thm_REAL_SGN_DIV : forall x : R, forall y : R, (sgr (divr x y)) = (divr (sgr x) (sgr y)).
Axiom thm_REAL_SGN_EQ : (forall x : R, ((sgr x) = (R_of_nat (NUMERAL O))) = (x = (R_of_nat (NUMERAL O)))) /\ ((forall x : R, ((sgr x) = (R_of_nat (NUMERAL (BIT1 O)))) = (gtr x (R_of_nat (NUMERAL O)))) /\ (forall x : R, ((sgr x) = (oppr (R_of_nat (NUMERAL (BIT1 O))))) = (ltr x (R_of_nat (NUMERAL O))))).
Axiom thm_REAL_SGN_CASES : forall x : R, ((sgr x) = (R_of_nat (NUMERAL O))) \/ (((sgr x) = (R_of_nat (NUMERAL (BIT1 O)))) \/ ((sgr x) = (oppr (R_of_nat (NUMERAL (BIT1 O)))))).
Axiom thm_REAL_SGN_INEQS : (forall x : R, (ler (R_of_nat (NUMERAL O)) (sgr x)) = (ler (R_of_nat (NUMERAL O)) x)) /\ ((forall x : R, (ltr (R_of_nat (NUMERAL O)) (sgr x)) = (ltr (R_of_nat (NUMERAL O)) x)) /\ ((forall x : R, (ger (R_of_nat (NUMERAL O)) (sgr x)) = (ger (R_of_nat (NUMERAL O)) x)) /\ ((forall x : R, (gtr (R_of_nat (NUMERAL O)) (sgr x)) = (gtr (R_of_nat (NUMERAL O)) x)) /\ ((forall x : R, ((R_of_nat (NUMERAL O)) = (sgr x)) = ((R_of_nat (NUMERAL O)) = x)) /\ ((forall x : R, (ler (sgr x) (R_of_nat (NUMERAL O))) = (ler x (R_of_nat (NUMERAL O)))) /\ ((forall x : R, (ltr (sgr x) (R_of_nat (NUMERAL O))) = (ltr x (R_of_nat (NUMERAL O)))) /\ ((forall x : R, (ger (sgr x) (R_of_nat (NUMERAL O))) = (ger x (R_of_nat (NUMERAL O)))) /\ ((forall x : R, (gtr (sgr x) (R_of_nat (NUMERAL O))) = (gtr x (R_of_nat (NUMERAL O)))) /\ (forall x : R, ((sgr x) = (R_of_nat (NUMERAL O))) = (x = (R_of_nat (NUMERAL O)))))))))))).
Axiom thm_REAL_SGN_POW : forall x : R, forall n : nat, (sgr (expr x n)) = (expr (sgr x) n).
Axiom thm_REAL_SGN_POW_2 : forall x : R, (sgr (expr x (NUMERAL (BIT0 (BIT1 O))))) = (sgr (normr x)).
Axiom thm_REAL_SGN_REAL_SGN : forall x : R, (sgr (sgr x)) = (sgr x).
Axiom thm_REAL_INV_SGN : forall x : R, (invr (sgr x)) = (sgr x).
Axiom thm_REAL_SGN_EQ_INEQ : forall x : R, forall y : R, ((sgr x) = (sgr y)) = ((x = y) \/ (ltr (normr (subr x y)) (maxr (normr x) (normr y)))).
Axiom thm_REAL_SGNS_EQ : forall x : R, forall y : R, ((sgr x) = (sgr y)) = (((x = (R_of_nat (NUMERAL O))) = (y = (R_of_nat (NUMERAL O)))) /\ (((gtr x (R_of_nat (NUMERAL O))) = (gtr y (R_of_nat (NUMERAL O)))) /\ ((ltr x (R_of_nat (NUMERAL O))) = (ltr y (R_of_nat (NUMERAL O)))))).
Axiom thm_REAL_SGNS_EQ_ALT : forall x : R, forall y : R, ((sgr x) = (sgr y)) = (((x = (R_of_nat (NUMERAL O))) -> y = (R_of_nat (NUMERAL O))) /\ (((gtr x (R_of_nat (NUMERAL O))) -> gtr y (R_of_nat (NUMERAL O))) /\ ((ltr x (R_of_nat (NUMERAL O))) -> ltr y (R_of_nat (NUMERAL O))))).
Axiom thm_REAL_WLOG_LE : forall (P : R -> R -> Prop), ((forall x : R, forall y : R, (P x y) = (P y x)) /\ (forall x : R, forall y : R, (ler x y) -> P x y)) -> forall x : R, forall y : R, P x y.
Axiom thm_REAL_WLOG_LT : forall (P : R -> R -> Prop), ((forall x : R, P x x) /\ ((forall x : R, forall y : R, (P x y) = (P y x)) /\ (forall x : R, forall y : R, (ltr x y) -> P x y))) -> forall x : R, forall y : R, P x y.
Axiom thm_REAL_WLOG_LE_3 : forall P : R -> R -> R -> Prop, ((forall x : R, forall y : R, forall z : R, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : R, forall y : R, forall z : R, ((ler x y) /\ (ler y z)) -> P x y z)) -> forall x : R, forall y : R, forall z : R, P x y z.
Axiom thm_sqrt : forall x : R, (hol_sqrt x) = (@ε R (fun y : R => ((sgr y) = (sgr x)) /\ ((expr y (NUMERAL (BIT0 (BIT1 O)))) = (normr x)))).
Axiom thm_SQRT_UNIQUE : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) y) /\ ((expr y (NUMERAL (BIT0 (BIT1 O)))) = x)) -> (hol_sqrt x) = y.
Axiom thm_POW_2_SQRT : forall x : R, (ler (R_of_nat (NUMERAL O)) x) -> (hol_sqrt (expr x (NUMERAL (BIT0 (BIT1 O))))) = x.
Axiom thm_SQRT_0 : (hol_sqrt (R_of_nat (NUMERAL O))) = (R_of_nat (NUMERAL O)).
Axiom thm_SQRT_1 : (hol_sqrt (R_of_nat (NUMERAL (BIT1 O)))) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_POW_2_SQRT_ABS : forall x : R, (hol_sqrt (expr x (NUMERAL (BIT0 (BIT1 O))))) = (normr x).
Axiom thm_SQRT_WORKS_GEN : forall x : R, ((sgr (hol_sqrt x)) = (sgr x)) /\ ((expr (hol_sqrt x) (NUMERAL (BIT0 (BIT1 O)))) = (normr x)).
Axiom thm_SQRT_UNIQUE_GEN : forall x : R, forall y : R, (((sgr y) = (sgr x)) /\ ((expr y (NUMERAL (BIT0 (BIT1 O)))) = (normr x))) -> (hol_sqrt x) = y.
Axiom thm_SQRT_NEG : forall x : R, (hol_sqrt (oppr x)) = (oppr (hol_sqrt x)).
Axiom thm_REAL_SGN_SQRT : forall x : R, (sgr (hol_sqrt x)) = (sgr x).
Axiom thm_SQRT_WORKS : forall x : R, (ler (R_of_nat (NUMERAL O)) x) -> (ler (R_of_nat (NUMERAL O)) (hol_sqrt x)) /\ ((expr (hol_sqrt x) (NUMERAL (BIT0 (BIT1 O)))) = x).
Axiom thm_REAL_POS_EQ_SQUARE : forall x : R, (ler (R_of_nat (NUMERAL O)) x) = (exists y : R, (expr y (NUMERAL (BIT0 (BIT1 O)))) = x).
Axiom thm_SQRT_POS_LE : forall x : R, (ler (R_of_nat (NUMERAL O)) x) -> ler (R_of_nat (NUMERAL O)) (hol_sqrt x).
Axiom thm_SQRT_POW_2 : forall x : R, (ler (R_of_nat (NUMERAL O)) x) -> (expr (hol_sqrt x) (NUMERAL (BIT0 (BIT1 O)))) = x.
Axiom thm_SQRT_POW2 : forall x : R, ((expr (hol_sqrt x) (NUMERAL (BIT0 (BIT1 O)))) = x) = (ler (R_of_nat (NUMERAL O)) x).
Axiom thm_SQRT_MUL : forall x : R, forall y : R, (hol_sqrt (mulr x y)) = (mulr (hol_sqrt x) (hol_sqrt y)).
Axiom thm_SQRT_INV : forall x : R, (hol_sqrt (invr x)) = (invr (hol_sqrt x)).
Axiom thm_SQRT_DIV : forall x : R, forall y : R, (hol_sqrt (divr x y)) = (divr (hol_sqrt x) (hol_sqrt y)).
Axiom thm_SQRT_LT_0 : forall x : R, (ltr (R_of_nat (NUMERAL O)) (hol_sqrt x)) = (ltr (R_of_nat (NUMERAL O)) x).
Axiom thm_SQRT_EQ_0 : forall x : R, ((hol_sqrt x) = (R_of_nat (NUMERAL O))) = (x = (R_of_nat (NUMERAL O))).
Axiom thm_SQRT_LE_0 : forall x : R, (ler (R_of_nat (NUMERAL O)) (hol_sqrt x)) = (ler (R_of_nat (NUMERAL O)) x).
Axiom thm_REAL_ABS_SQRT : forall x : R, (normr (hol_sqrt x)) = (hol_sqrt (normr x)).
Axiom thm_SQRT_MONO_LT : forall x : R, forall y : R, (ltr x y) -> ltr (hol_sqrt x) (hol_sqrt y).
Axiom thm_SQRT_MONO_LE : forall x : R, forall y : R, (ler x y) -> ler (hol_sqrt x) (hol_sqrt y).
Axiom thm_SQRT_MONO_LT_EQ : forall x : R, forall y : R, (ltr (hol_sqrt x) (hol_sqrt y)) = (ltr x y).
Axiom thm_SQRT_MONO_LE_EQ : forall x : R, forall y : R, (ler (hol_sqrt x) (hol_sqrt y)) = (ler x y).
Axiom thm_SQRT_INJ : forall x : R, forall y : R, ((hol_sqrt x) = (hol_sqrt y)) = (x = y).
Axiom thm_SQRT_EQ_1 : forall x : R, ((hol_sqrt x) = (R_of_nat (NUMERAL (BIT1 O)))) = (x = (R_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_SQRT_POS_LT : forall x : R, (ltr (R_of_nat (NUMERAL O)) x) -> ltr (R_of_nat (NUMERAL O)) (hol_sqrt x).
Axiom thm_REAL_LE_LSQRT : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) y) /\ (ler x (expr y (NUMERAL (BIT0 (BIT1 O)))))) -> ler (hol_sqrt x) y.
Axiom thm_REAL_LE_RSQRT : forall x : R, forall y : R, (ler (expr x (NUMERAL (BIT0 (BIT1 O)))) y) -> ler x (hol_sqrt y).
Axiom thm_REAL_LT_LSQRT : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) y) /\ (ltr x (expr y (NUMERAL (BIT0 (BIT1 O)))))) -> ltr (hol_sqrt x) y.
Axiom thm_REAL_LT_RSQRT : forall x : R, forall y : R, (ltr (expr x (NUMERAL (BIT0 (BIT1 O)))) y) -> ltr x (hol_sqrt y).
Axiom thm_SQRT_EVEN_POW2 : forall n : nat, (even n) -> (hol_sqrt (expr (R_of_nat (NUMERAL (BIT0 (BIT1 O)))) n)) = (expr (R_of_nat (NUMERAL (BIT0 (BIT1 O)))) (divn n (NUMERAL (BIT0 (BIT1 O))))).
Axiom thm_REAL_DIV_SQRT : forall x : R, (ler (R_of_nat (NUMERAL O)) x) -> (divr x (hol_sqrt x)) = (hol_sqrt x).
Axiom thm_REAL_RSQRT_LE : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) x) /\ ((ler (R_of_nat (NUMERAL O)) y) /\ (ler x (hol_sqrt y)))) -> ler (expr x (NUMERAL (BIT0 (BIT1 O)))) y.
Axiom thm_REAL_LSQRT_LE : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) x) /\ (ler (hol_sqrt x) y)) -> ler x (expr y (NUMERAL (BIT0 (BIT1 O)))).
Axiom thm_REAL_SQRT_POW_2 : forall x : R, (expr (hol_sqrt x) (NUMERAL (BIT0 (BIT1 O)))) = (normr x).
Axiom thm_REAL_ABS_LE_SQRT_POS : forall x : R, forall y : R, ((ler (R_of_nat (NUMERAL O)) x) /\ (ler (R_of_nat (NUMERAL O)) y)) -> ler (normr (subr (hol_sqrt x) (hol_sqrt y))) (hol_sqrt (normr (subr x y))).
Axiom thm_REAL_ABS_LE_SQRT : forall x : R, forall y : R, ler (normr (subr (hol_sqrt x) (hol_sqrt y))) (hol_sqrt (mulr (R_of_nat (NUMERAL (BIT0 (BIT1 O)))) (normr (subr x y)))).
Axiom thm_DECIMAL : forall x : nat, forall y : nat, (DECIMAL x y) = (divr (R_of_nat x) (R_of_nat y)).
Axiom thm_RAT_LEMMA1 : forall (x1 : R) (x2 : R) (y1 : R) (y2 : R), ((~ (y1 = (R_of_nat (NUMERAL O)))) /\ (~ (y2 = (R_of_nat (NUMERAL O))))) -> (addr (divr x1 y1) (divr x2 y2)) = (mulr (addr (mulr x1 y2) (mulr x2 y1)) (mulr (invr y1) (invr y2))).
Axiom thm_RAT_LEMMA2 : forall (x1 : R) (x2 : R) (y1 : R) (y2 : R), ((ltr (R_of_nat (NUMERAL O)) y1) /\ (ltr (R_of_nat (NUMERAL O)) y2)) -> (addr (divr x1 y1) (divr x2 y2)) = (mulr (addr (mulr x1 y2) (mulr x2 y1)) (mulr (invr y1) (invr y2))).
Axiom thm_RAT_LEMMA3 : forall (x1 : R) (x2 : R) (y1 : R) (y2 : R), ((ltr (R_of_nat (NUMERAL O)) y1) /\ (ltr (R_of_nat (NUMERAL O)) y2)) -> (subr (divr x1 y1) (divr x2 y2)) = (mulr (subr (mulr x1 y2) (mulr x2 y1)) (mulr (invr y1) (invr y2))).
Axiom thm_RAT_LEMMA4 : forall (x1 : R) (y2 : R) (x2 : R) (y1 : R), ((ltr (R_of_nat (NUMERAL O)) y1) /\ (ltr (R_of_nat (NUMERAL O)) y2)) -> (ler (divr x1 y1) (divr x2 y2)) = (ler (mulr x1 y2) (mulr x2 y1)).
Axiom thm_RAT_LEMMA5 : forall (x1 : R) (y2 : R) (x2 : R) (y1 : R), ((ltr (R_of_nat (NUMERAL O)) y1) /\ (ltr (R_of_nat (NUMERAL O)) y2)) -> ((divr x1 y1) = (divr x2 y2)) = ((mulr x1 y2) = (mulr x2 y1)).
Axiom thm_REAL_LE_TRANS_LE : forall x : R, forall y : R, (ler x y) = (forall z : R, (ler y z) -> ler x z).
Axiom thm_REAL_LE_TRANS_LTE : forall x : R, forall y : R, (ler x y) = (forall z : R, (ltr y z) -> ler x z).
Axiom thm_REAL_LE_TRANS_LT : forall x : R, forall y : R, (ler x y) = (forall z : R, (ltr y z) -> ltr x z).
Axiom thm_REAL_SHRINK_RANGE : forall x : R, ltr (normr (divr x (addr (R_of_nat (NUMERAL (BIT1 O))) (normr x)))) (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_SHRINK_LT : forall x : R, forall y : R, (ltr (divr x (addr (R_of_nat (NUMERAL (BIT1 O))) (normr x))) (divr y (addr (R_of_nat (NUMERAL (BIT1 O))) (normr y)))) = (ltr x y).
Axiom thm_REAL_SHRINK_LE : forall x : R, forall y : R, (ler (divr x (addr (R_of_nat (NUMERAL (BIT1 O))) (normr x))) (divr y (addr (R_of_nat (NUMERAL (BIT1 O))) (normr y)))) = (ler x y).
Axiom thm_REAL_SHRINK_EQ : forall x : R, forall y : R, ((divr x (addr (R_of_nat (NUMERAL (BIT1 O))) (normr x))) = (divr y (addr (R_of_nat (NUMERAL (BIT1 O))) (normr y)))) = (x = y).
Axiom thm_REAL_SHRINK_GALOIS : forall x : R, forall y : R, ((divr x (addr (R_of_nat (NUMERAL (BIT1 O))) (normr x))) = y) = ((ltr (normr y) (R_of_nat (NUMERAL (BIT1 O)))) /\ ((divr y (subr (R_of_nat (NUMERAL (BIT1 O))) (normr y))) = x)).
Axiom thm_REAL_GROW_SHRINK : forall x : R, (divr (divr x (addr (R_of_nat (NUMERAL (BIT1 O))) (normr x))) (subr (R_of_nat (NUMERAL (BIT1 O))) (normr (divr x (addr (R_of_nat (NUMERAL (BIT1 O))) (normr x)))))) = x.
Axiom thm_REAL_SHRINK_GROW_EQ : forall x : R, ((divr (divr x (subr (R_of_nat (NUMERAL (BIT1 O))) (normr x))) (addr (R_of_nat (NUMERAL (BIT1 O))) (normr (divr x (subr (R_of_nat (NUMERAL (BIT1 O))) (normr x)))))) = x) = (ltr (normr x) (R_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_REAL_SHRINK_GROW : forall x : R, (ltr (normr x) (R_of_nat (NUMERAL (BIT1 O)))) -> (divr (divr x (subr (R_of_nat (NUMERAL (BIT1 O))) (normr x))) (addr (R_of_nat (NUMERAL (BIT1 O))) (normr (divr x (subr (R_of_nat (NUMERAL (BIT1 O))) (normr x)))))) = x.
Axiom thm_integer : forall x : R, (Rint x) = (exists n : nat, (normr x) = (R_of_nat n)).
Axiom thm_is_int : forall (x : R), (Rint x) = (exists n : nat, (x = (R_of_nat n)) \/ (x = (oppr (R_of_nat n)))).
Axiom thm_dest_int_rep : forall i : int, exists n : nat, ((real_of_int i) = (R_of_nat n)) \/ ((real_of_int i) = (oppr (R_of_nat n))).
Axiom thm_INTEGER_REAL_OF_INT : forall x : int, Rint (real_of_int x).
Axiom thm_int_eq : forall x : int, forall y : int, (x = y) = ((real_of_int x) = (real_of_int y)).
Axiom thm_int_le : forall x : int, forall y : int, (lez x y) = (ler (real_of_int x) (real_of_int y)).
Axiom thm_int_lt : forall x : int, forall y : int, (ltz x y) = (ltr (real_of_int x) (real_of_int y)).
Axiom thm_int_ge : forall x : int, forall y : int, (gez x y) = (ger (real_of_int x) (real_of_int y)).
Axiom thm_int_gt : forall x : int, forall y : int, (gtz x y) = (gtr (real_of_int x) (real_of_int y)).
Axiom thm_int_of_num : forall n : nat, (int_of_nat n) = (int_of_real (R_of_nat n)).
Axiom thm_int_of_num_th : forall n : nat, (real_of_int (int_of_nat n)) = (R_of_nat n).
Axiom thm_int_neg : forall i : int, (oppz i) = (int_of_real (oppr (real_of_int i))).
Axiom thm_int_neg_th : forall x : int, (real_of_int (oppz x)) = (oppr (real_of_int x)).
Axiom thm_int_add : forall x : int, forall y : int, (addz x y) = (int_of_real (addr (real_of_int x) (real_of_int y))).
Axiom thm_int_add_th : forall x : int, forall y : int, (real_of_int (addz x y)) = (addr (real_of_int x) (real_of_int y)).
Axiom thm_int_sub : forall x : int, forall y : int, (subz x y) = (int_of_real (subr (real_of_int x) (real_of_int y))).
Axiom thm_int_sub_th : forall x : int, forall y : int, (real_of_int (subz x y)) = (subr (real_of_int x) (real_of_int y)).
Axiom thm_int_mul : forall x : int, forall y : int, (mulz x y) = (int_of_real (mulr (real_of_int x) (real_of_int y))).
Axiom thm_int_mul_th : forall x : int, forall y : int, (real_of_int (mulz x y)) = (mulr (real_of_int x) (real_of_int y)).
Axiom thm_int_abs : forall x : int, (normz x) = (int_of_real (normr (real_of_int x))).
Axiom thm_int_abs_th : forall x : int, (real_of_int (normz x)) = (normr (real_of_int x)).
Axiom thm_int_sgn : forall x : int, (sgz x) = (int_of_real (sgr (real_of_int x))).
Axiom thm_int_sgn_th : forall x : int, (real_of_int (sgz x)) = (sgr (real_of_int x)).
Axiom thm_int_max : forall x : int, forall y : int, (maxz x y) = (int_of_real (maxr (real_of_int x) (real_of_int y))).
Axiom thm_int_max_th : forall x : int, forall y : int, (real_of_int (maxz x y)) = (maxr (real_of_int x) (real_of_int y)).
Axiom thm_int_min : forall x : int, forall y : int, (minz x y) = (int_of_real (minr (real_of_int x) (real_of_int y))).
Axiom thm_int_min_th : forall x : int, forall y : int, (real_of_int (minz x y)) = (minr (real_of_int x) (real_of_int y)).
Axiom thm_int_pow : forall x : int, forall n : nat, (expz x n) = (int_of_real (expr (real_of_int x) n)).
Axiom thm_int_pow_th : forall x : int, forall n : nat, (real_of_int (expz x n)) = (expr (real_of_int x) n).
Axiom thm_REAL_OF_INT_CLAUSES : (forall x : int, forall y : int, ((real_of_int x) = (real_of_int y)) = (x = y)) /\ ((forall x : int, forall y : int, (ger (real_of_int x) (real_of_int y)) = (gez x y)) /\ ((forall x : int, forall y : int, (gtr (real_of_int x) (real_of_int y)) = (gtz x y)) /\ ((forall x : int, forall y : int, (ler (real_of_int x) (real_of_int y)) = (lez x y)) /\ ((forall x : int, forall y : int, (ltr (real_of_int x) (real_of_int y)) = (ltz x y)) /\ ((forall x : int, forall y : int, (maxr (real_of_int x) (real_of_int y)) = (real_of_int (maxz x y))) /\ ((forall x : int, forall y : int, (minr (real_of_int x) (real_of_int y)) = (real_of_int (minz x y))) /\ ((forall n : nat, (R_of_nat n) = (real_of_int (int_of_nat n))) /\ ((forall x : int, (oppr (real_of_int x)) = (real_of_int (oppz x))) /\ ((forall x : int, (normr (real_of_int x)) = (real_of_int (normz x))) /\ ((forall x : int, forall y : int, (maxr (real_of_int x) (real_of_int y)) = (real_of_int (maxz x y))) /\ ((forall x : int, forall y : int, (minr (real_of_int x) (real_of_int y)) = (real_of_int (minz x y))) /\ ((forall x : int, (sgr (real_of_int x)) = (real_of_int (sgz x))) /\ ((forall x : int, forall y : int, (addr (real_of_int x) (real_of_int y)) = (real_of_int (addz x y))) /\ ((forall x : int, forall y : int, (subr (real_of_int x) (real_of_int y)) = (real_of_int (subz x y))) /\ ((forall x : int, forall y : int, (mulr (real_of_int x) (real_of_int y)) = (real_of_int (mulz x y))) /\ (forall x : int, forall n : nat, (expr (real_of_int x) n) = (real_of_int (expz x n)))))))))))))))))).
Axiom thm_INT_IMAGE : forall x : int, (exists n : nat, x = (int_of_nat n)) \/ (exists n : nat, x = (oppz (int_of_nat n))).
Axiom thm_FORALL_INT_CASES : forall P : int -> Prop, (forall x : int, P x) = ((forall n : nat, P (int_of_nat n)) /\ (forall n : nat, P (oppz (int_of_nat n)))).
Axiom thm_EXISTS_INT_CASES : forall P : int -> Prop, (exists x : int, P x) = ((exists n : nat, P (int_of_nat n)) \/ (exists n : nat, P (oppz (int_of_nat n)))).
Axiom thm_INT_LT_DISCRETE : forall x : int, forall y : int, (ltz x y) = (lez (addz x (int_of_nat (NUMERAL (BIT1 O)))) y).
Axiom thm_INT_GT_DISCRETE : forall x : int, forall y : int, (gtz x y) = (gez x (addz y (int_of_nat (NUMERAL (BIT1 O))))).
Axiom thm_INT_ABS_0 : (normz (int_of_nat (NUMERAL O))) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_ABS_1 : (normz (int_of_nat (NUMERAL (BIT1 O)))) = (int_of_nat (NUMERAL (BIT1 O))).
Axiom thm_INT_ABS_ABS : forall x : int, (normz (normz x)) = (normz x).
Axiom thm_INT_ABS_BETWEEN : forall x : int, forall y : int, forall d : int, ((ltz (int_of_nat (NUMERAL O)) d) /\ ((ltz (subz x d) y) /\ (ltz y (addz x d)))) = (ltz (normz (subz y x)) d).
Axiom thm_INT_ABS_BETWEEN1 : forall x : int, forall y : int, forall z : int, ((ltz x z) /\ (ltz (normz (subz y x)) (subz z x))) -> ltz y z.
Axiom thm_INT_ABS_BETWEEN2 : forall x0 : int, forall x : int, forall y0 : int, forall y : int, ((ltz x0 y0) /\ ((ltz (mulz (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) (normz (subz x x0))) (subz y0 x0)) /\ (ltz (mulz (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) (normz (subz y y0))) (subz y0 x0)))) -> ltz x y.
Axiom thm_INT_ABS_BOUND : forall x : int, forall y : int, forall d : int, (ltz (normz (subz x y)) d) -> ltz y (addz x d).
Axiom thm_INT_ABS_BOUNDS : forall x : int, forall k : int, (lez (normz x) k) = ((lez (oppz k) x) /\ (lez x k)).
Axiom thm_INT_ABS_CASES : forall x : int, (x = (int_of_nat (NUMERAL O))) \/ (ltz (int_of_nat (NUMERAL O)) (normz x)).
Axiom thm_INT_ABS_CIRCLE : forall x : int, forall y : int, forall h : int, (ltz (normz h) (subz (normz y) (normz x))) -> ltz (normz (addz x h)) (normz y).
Axiom thm_INT_ABS_LE : forall x : int, lez x (normz x).
Axiom thm_INT_ABS_MUL : forall x : int, forall y : int, (normz (mulz x y)) = (mulz (normz x) (normz y)).
Axiom thm_INT_ABS_NEG : forall x : int, (normz (oppz x)) = (normz x).
Axiom thm_INT_ABS_NUM : forall n : nat, (normz (int_of_nat n)) = (int_of_nat n).
Axiom thm_INT_ABS_NZ : forall x : int, (~ (x = (int_of_nat (NUMERAL O)))) = (ltz (int_of_nat (NUMERAL O)) (normz x)).
Axiom thm_INT_ABS_POS : forall x : int, lez (int_of_nat (NUMERAL O)) (normz x).
Axiom thm_INT_ABS_POW : forall x : int, forall n : nat, (normz (expz x n)) = (expz (normz x) n).
Axiom thm_INT_ABS_REFL : forall x : int, ((normz x) = x) = (lez (int_of_nat (NUMERAL O)) x).
Axiom thm_INT_ABS_SGN : forall x : int, (normz (sgz x)) = (sgz (normz x)).
Axiom thm_INT_ABS_SIGN : forall x : int, forall y : int, (ltz (normz (subz x y)) y) -> ltz (int_of_nat (NUMERAL O)) x.
Axiom thm_INT_ABS_SIGN2 : forall x : int, forall y : int, (ltz (normz (subz x y)) (oppz y)) -> ltz x (int_of_nat (NUMERAL O)).
Axiom thm_INT_ABS_STILLNZ : forall x : int, forall y : int, (ltz (normz (subz x y)) (normz y)) -> ~ (x = (int_of_nat (NUMERAL O))).
Axiom thm_INT_ABS_SUB : forall x : int, forall y : int, (normz (subz x y)) = (normz (subz y x)).
Axiom thm_INT_ABS_SUB_ABS : forall x : int, forall y : int, lez (normz (subz (normz x) (normz y))) (normz (subz x y)).
Axiom thm_INT_ABS_TRIANGLE : forall x : int, forall y : int, lez (normz (addz x y)) (addz (normz x) (normz y)).
Axiom thm_INT_ABS_ZERO : forall x : int, ((normz x) = (int_of_nat (NUMERAL O))) = (x = (int_of_nat (NUMERAL O))).
Axiom thm_INT_ADD2_SUB2 : forall a : int, forall b : int, forall c : int, forall d : int, (subz (addz a b) (addz c d)) = (addz (subz a c) (subz b d)).
Axiom thm_INT_ADD_AC : forall (n : int) (m : int) (p : int), ((addz m n) = (addz n m)) /\ (((addz (addz m n) p) = (addz m (addz n p))) /\ ((addz m (addz n p)) = (addz n (addz m p)))).
Axiom thm_INT_ADD_ASSOC : forall x : int, forall y : int, forall z : int, (addz x (addz y z)) = (addz (addz x y) z).
Axiom thm_INT_ADD_LDISTRIB : forall x : int, forall y : int, forall z : int, (mulz x (addz y z)) = (addz (mulz x y) (mulz x z)).
Axiom thm_INT_ADD_LID : forall x : int, (addz (int_of_nat (NUMERAL O)) x) = x.
Axiom thm_INT_ADD_LINV : forall x : int, (addz (oppz x) x) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_ADD_RDISTRIB : forall x : int, forall y : int, forall z : int, (mulz (addz x y) z) = (addz (mulz x z) (mulz y z)).
Axiom thm_INT_ADD_RID : forall x : int, (addz x (int_of_nat (NUMERAL O))) = x.
Axiom thm_INT_ADD_RINV : forall x : int, (addz x (oppz x)) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_ADD_SUB : forall x : int, forall y : int, (subz (addz x y) x) = y.
Axiom thm_INT_ADD_SUB2 : forall x : int, forall y : int, (subz x (addz x y)) = (oppz y).
Axiom thm_INT_ADD_SYM : forall x : int, forall y : int, (addz x y) = (addz y x).
Axiom thm_INT_BOUNDS_LE : forall x : int, forall k : int, ((lez (oppz k) x) /\ (lez x k)) = (lez (normz x) k).
Axiom thm_INT_BOUNDS_LT : forall x : int, forall k : int, ((ltz (oppz k) x) /\ (ltz x k)) = (ltz (normz x) k).
Axiom thm_INT_DIFFSQ : forall x : int, forall y : int, (mulz (addz x y) (subz x y)) = (subz (mulz x x) (mulz y y)).
Axiom thm_INT_ENTIRE : forall x : int, forall y : int, ((mulz x y) = (int_of_nat (NUMERAL O))) = ((x = (int_of_nat (NUMERAL O))) \/ (y = (int_of_nat (NUMERAL O)))).
Axiom thm_INT_EQ_ADD_LCANCEL : forall x : int, forall y : int, forall z : int, ((addz x y) = (addz x z)) = (y = z).
Axiom thm_INT_EQ_ADD_LCANCEL_0 : forall x : int, forall y : int, ((addz x y) = x) = (y = (int_of_nat (NUMERAL O))).
Axiom thm_INT_EQ_ADD_RCANCEL : forall x : int, forall y : int, forall z : int, ((addz x z) = (addz y z)) = (x = y).
Axiom thm_INT_EQ_ADD_RCANCEL_0 : forall x : int, forall y : int, ((addz x y) = y) = (x = (int_of_nat (NUMERAL O))).
Axiom thm_INT_EQ_IMP_LE : forall x : int, forall y : int, (x = y) -> lez x y.
Axiom thm_INT_EQ_LCANCEL_IMP : forall x : int, forall y : int, forall z : int, ((~ (z = (int_of_nat (NUMERAL O)))) /\ ((mulz z x) = (mulz z y))) -> x = y.
Axiom thm_INT_EQ_MUL_LCANCEL : forall x : int, forall y : int, forall z : int, ((mulz x y) = (mulz x z)) = ((x = (int_of_nat (NUMERAL O))) \/ (y = z)).
Axiom thm_INT_EQ_MUL_RCANCEL : forall x : int, forall y : int, forall z : int, ((mulz x z) = (mulz y z)) = ((x = y) \/ (z = (int_of_nat (NUMERAL O)))).
Axiom thm_INT_EQ_NEG2 : forall x : int, forall y : int, ((oppz x) = (oppz y)) = (x = y).
Axiom thm_INT_EQ_RCANCEL_IMP : forall x : int, forall y : int, forall z : int, ((~ (z = (int_of_nat (NUMERAL O)))) /\ ((mulz x z) = (mulz y z))) -> x = y.
Axiom thm_INT_EQ_SGN_ABS : forall x : int, forall y : int, (x = y) = (((sgz x) = (sgz y)) /\ ((normz x) = (normz y))).
Axiom thm_INT_EQ_SQUARE_ABS : forall x : int, forall y : int, ((normz x) = (normz y)) = ((expz x (NUMERAL (BIT0 (BIT1 O)))) = (expz y (NUMERAL (BIT0 (BIT1 O))))).
Axiom thm_INT_EQ_SUB_LADD : forall x : int, forall y : int, forall z : int, (x = (subz y z)) = ((addz x z) = y).
Axiom thm_INT_EQ_SUB_RADD : forall x : int, forall y : int, forall z : int, ((subz x y) = z) = (x = (addz z y)).
Axiom thm_INT_EVENPOW_ABS : forall x : int, forall n : nat, (even n) -> (expz (normz x) n) = (expz x n).
Axiom thm_INT_LET_ADD : forall x : int, forall y : int, ((lez (int_of_nat (NUMERAL O)) x) /\ (ltz (int_of_nat (NUMERAL O)) y)) -> ltz (int_of_nat (NUMERAL O)) (addz x y).
Axiom thm_INT_LET_ADD2 : forall w : int, forall x : int, forall y : int, forall z : int, ((lez w x) /\ (ltz y z)) -> ltz (addz w y) (addz x z).
Axiom thm_INT_LET_ANTISYM : forall x : int, forall y : int, ~ ((lez x y) /\ (ltz y x)).
Axiom thm_INT_LET_TOTAL : forall x : int, forall y : int, (lez x y) \/ (ltz y x).
Axiom thm_INT_LET_TRANS : forall x : int, forall y : int, forall z : int, ((lez x y) /\ (ltz y z)) -> ltz x z.
Axiom thm_INT_LE_01 : lez (int_of_nat (NUMERAL O)) (int_of_nat (NUMERAL (BIT1 O))).
Axiom thm_INT_LE_ADD : forall x : int, forall y : int, ((lez (int_of_nat (NUMERAL O)) x) /\ (lez (int_of_nat (NUMERAL O)) y)) -> lez (int_of_nat (NUMERAL O)) (addz x y).
Axiom thm_INT_LE_ADD2 : forall w : int, forall x : int, forall y : int, forall z : int, ((lez w x) /\ (lez y z)) -> lez (addz w y) (addz x z).
Axiom thm_INT_LE_ADDL : forall x : int, forall y : int, (lez y (addz x y)) = (lez (int_of_nat (NUMERAL O)) x).
Axiom thm_INT_LE_ADDR : forall x : int, forall y : int, (lez x (addz x y)) = (lez (int_of_nat (NUMERAL O)) y).
Axiom thm_INT_LE_ANTISYM : forall x : int, forall y : int, ((lez x y) /\ (lez y x)) = (x = y).
Axiom thm_INT_LE_DOUBLE : forall x : int, (lez (int_of_nat (NUMERAL O)) (addz x x)) = (lez (int_of_nat (NUMERAL O)) x).
Axiom thm_INT_LE_LADD : forall x : int, forall y : int, forall z : int, (lez (addz x y) (addz x z)) = (lez y z).
Axiom thm_INT_LE_LADD_IMP : forall x : int, forall y : int, forall z : int, (lez y z) -> lez (addz x y) (addz x z).
Axiom thm_INT_LE_LCANCEL_IMP : forall x : int, forall y : int, forall z : int, ((ltz (int_of_nat (NUMERAL O)) x) /\ (lez (mulz x y) (mulz x z))) -> lez y z.
Axiom thm_INT_LE_LMUL : forall x : int, forall y : int, forall z : int, ((lez (int_of_nat (NUMERAL O)) x) /\ (lez y z)) -> lez (mulz x y) (mulz x z).
Axiom thm_INT_LE_LMUL_EQ : forall x : int, forall y : int, forall z : int, (ltz (int_of_nat (NUMERAL O)) z) -> (lez (mulz z x) (mulz z y)) = (lez x y).
Axiom thm_INT_LE_LNEG : forall x : int, forall y : int, (lez (oppz x) y) = (lez (int_of_nat (NUMERAL O)) (addz x y)).
Axiom thm_INT_LE_LT : forall x : int, forall y : int, (lez x y) = ((ltz x y) \/ (x = y)).
Axiom thm_INT_LE_MAX : forall x : int, forall y : int, forall z : int, (lez z (maxz x y)) = ((lez z x) \/ (lez z y)).
Axiom thm_INT_LE_MIN : forall x : int, forall y : int, forall z : int, (lez z (minz x y)) = ((lez z x) /\ (lez z y)).
Axiom thm_INT_LE_MUL : forall x : int, forall y : int, ((lez (int_of_nat (NUMERAL O)) x) /\ (lez (int_of_nat (NUMERAL O)) y)) -> lez (int_of_nat (NUMERAL O)) (mulz x y).
Axiom thm_INT_LE_MUL2 : forall w : int, forall x : int, forall y : int, forall z : int, ((lez (int_of_nat (NUMERAL O)) w) /\ ((lez w x) /\ ((lez (int_of_nat (NUMERAL O)) y) /\ (lez y z)))) -> lez (mulz w y) (mulz x z).
Axiom thm_INT_LE_MUL_EQ : (forall x : int, forall y : int, (ltz (int_of_nat (NUMERAL O)) x) -> (lez (int_of_nat (NUMERAL O)) (mulz x y)) = (lez (int_of_nat (NUMERAL O)) y)) /\ (forall x : int, forall y : int, (ltz (int_of_nat (NUMERAL O)) y) -> (lez (int_of_nat (NUMERAL O)) (mulz x y)) = (lez (int_of_nat (NUMERAL O)) x)).
Axiom thm_INT_LE_NEG2 : forall x : int, forall y : int, (lez (oppz x) (oppz y)) = (lez y x).
Axiom thm_INT_LE_NEGL : forall x : int, (lez (oppz x) x) = (lez (int_of_nat (NUMERAL O)) x).
Axiom thm_INT_LE_NEGR : forall x : int, (lez x (oppz x)) = (lez x (int_of_nat (NUMERAL O))).
Axiom thm_INT_LE_NEGTOTAL : forall x : int, (lez (int_of_nat (NUMERAL O)) x) \/ (lez (int_of_nat (NUMERAL O)) (oppz x)).
Axiom thm_INT_LE_POW2 : forall n : nat, lez (int_of_nat (NUMERAL (BIT1 O))) (expz (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) n).
Axiom thm_INT_LE_POW_2 : forall x : int, lez (int_of_nat (NUMERAL O)) (expz x (NUMERAL (BIT0 (BIT1 O)))).
Axiom thm_INT_LE_RADD : forall x : int, forall y : int, forall z : int, (lez (addz x z) (addz y z)) = (lez x y).
Axiom thm_INT_LE_RCANCEL_IMP : forall x : int, forall y : int, forall z : int, ((ltz (int_of_nat (NUMERAL O)) z) /\ (lez (mulz x z) (mulz y z))) -> lez x y.
Axiom thm_INT_LE_REFL : forall x : int, lez x x.
Axiom thm_INT_LE_RMUL : forall x : int, forall y : int, forall z : int, ((lez x y) /\ (lez (int_of_nat (NUMERAL O)) z)) -> lez (mulz x z) (mulz y z).
Axiom thm_INT_LE_RMUL_EQ : forall x : int, forall y : int, forall z : int, (ltz (int_of_nat (NUMERAL O)) z) -> (lez (mulz x z) (mulz y z)) = (lez x y).
Axiom thm_INT_LE_RNEG : forall x : int, forall y : int, (lez x (oppz y)) = (lez (addz x y) (int_of_nat (NUMERAL O))).
Axiom thm_INT_LE_SQUARE : forall x : int, lez (int_of_nat (NUMERAL O)) (mulz x x).
Axiom thm_INT_LE_SQUARE_ABS : forall x : int, forall y : int, (lez (normz x) (normz y)) = (lez (expz x (NUMERAL (BIT0 (BIT1 O)))) (expz y (NUMERAL (BIT0 (BIT1 O))))).
Axiom thm_INT_LE_SUB_LADD : forall x : int, forall y : int, forall z : int, (lez x (subz y z)) = (lez (addz x z) y).
Axiom thm_INT_LE_SUB_RADD : forall x : int, forall y : int, forall z : int, (lez (subz x y) z) = (lez x (addz z y)).
Axiom thm_INT_LE_TOTAL : forall x : int, forall y : int, (lez x y) \/ (lez y x).
Axiom thm_INT_LE_TRANS : forall x : int, forall y : int, forall z : int, ((lez x y) /\ (lez y z)) -> lez x z.
Axiom thm_INT_LNEG_UNIQ : forall x : int, forall y : int, ((addz x y) = (int_of_nat (NUMERAL O))) = (x = (oppz y)).
Axiom thm_INT_LTE_ADD : forall x : int, forall y : int, ((ltz (int_of_nat (NUMERAL O)) x) /\ (lez (int_of_nat (NUMERAL O)) y)) -> ltz (int_of_nat (NUMERAL O)) (addz x y).
Axiom thm_INT_LTE_ADD2 : forall w : int, forall x : int, forall y : int, forall z : int, ((ltz w x) /\ (lez y z)) -> ltz (addz w y) (addz x z).
Axiom thm_INT_LTE_ANTISYM : forall x : int, forall y : int, ~ ((ltz x y) /\ (lez y x)).
Axiom thm_INT_LTE_TOTAL : forall x : int, forall y : int, (ltz x y) \/ (lez y x).
Axiom thm_INT_LTE_TRANS : forall x : int, forall y : int, forall z : int, ((ltz x y) /\ (lez y z)) -> ltz x z.
Axiom thm_INT_LT_01 : ltz (int_of_nat (NUMERAL O)) (int_of_nat (NUMERAL (BIT1 O))).
Axiom thm_INT_LT_ADD : forall x : int, forall y : int, ((ltz (int_of_nat (NUMERAL O)) x) /\ (ltz (int_of_nat (NUMERAL O)) y)) -> ltz (int_of_nat (NUMERAL O)) (addz x y).
Axiom thm_INT_LT_ADD1 : forall x : int, forall y : int, (lez x y) -> ltz x (addz y (int_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_INT_LT_ADD2 : forall w : int, forall x : int, forall y : int, forall z : int, ((ltz w x) /\ (ltz y z)) -> ltz (addz w y) (addz x z).
Axiom thm_INT_LT_ADDL : forall x : int, forall y : int, (ltz y (addz x y)) = (ltz (int_of_nat (NUMERAL O)) x).
Axiom thm_INT_LT_ADDNEG : forall x : int, forall y : int, forall z : int, (ltz y (addz x (oppz z))) = (ltz (addz y z) x).
Axiom thm_INT_LT_ADDNEG2 : forall x : int, forall y : int, forall z : int, (ltz (addz x (oppz y)) z) = (ltz x (addz z y)).
Axiom thm_INT_LT_ADDR : forall x : int, forall y : int, (ltz x (addz x y)) = (ltz (int_of_nat (NUMERAL O)) y).
Axiom thm_INT_LT_ADD_SUB : forall x : int, forall y : int, forall z : int, (ltz (addz x y) z) = (ltz x (subz z y)).
Axiom thm_INT_LT_ANTISYM : forall x : int, forall y : int, ~ ((ltz x y) /\ (ltz y x)).
Axiom thm_INT_LT_GT : forall x : int, forall y : int, (ltz x y) -> ~ (ltz y x).
Axiom thm_INT_LT_IMP_LE : forall x : int, forall y : int, (ltz x y) -> lez x y.
Axiom thm_INT_LT_IMP_NE : forall x : int, forall y : int, (ltz x y) -> ~ (x = y).
Axiom thm_INT_LT_LADD : forall x : int, forall y : int, forall z : int, (ltz (addz x y) (addz x z)) = (ltz y z).
Axiom thm_INT_LT_LADD_IMP : forall x : int, forall y : int, forall z : int, (ltz y z) -> ltz (addz x y) (addz x z).
Axiom thm_INT_LT_LCANCEL_IMP : forall x : int, forall y : int, forall z : int, ((ltz (int_of_nat (NUMERAL O)) x) /\ (ltz (mulz x y) (mulz x z))) -> ltz y z.
Axiom thm_INT_LT_LE : forall x : int, forall y : int, (ltz x y) = ((lez x y) /\ (~ (x = y))).
Axiom thm_INT_LT_LMUL : forall x : int, forall y : int, forall z : int, ((ltz (int_of_nat (NUMERAL O)) x) /\ (ltz y z)) -> ltz (mulz x y) (mulz x z).
Axiom thm_INT_LT_LMUL_EQ : forall x : int, forall y : int, forall z : int, (ltz (int_of_nat (NUMERAL O)) z) -> (ltz (mulz z x) (mulz z y)) = (ltz x y).
Axiom thm_INT_LT_LNEG : forall x : int, forall y : int, (ltz (oppz x) y) = (ltz (int_of_nat (NUMERAL O)) (addz x y)).
Axiom thm_INT_LT_MAX : forall x : int, forall y : int, forall z : int, (ltz z (maxz x y)) = ((ltz z x) \/ (ltz z y)).
Axiom thm_INT_LT_MIN : forall x : int, forall y : int, forall z : int, (ltz z (minz x y)) = ((ltz z x) /\ (ltz z y)).
Axiom thm_INT_LT_MUL : forall x : int, forall y : int, ((ltz (int_of_nat (NUMERAL O)) x) /\ (ltz (int_of_nat (NUMERAL O)) y)) -> ltz (int_of_nat (NUMERAL O)) (mulz x y).
Axiom thm_INT_LT_MUL2 : forall w : int, forall x : int, forall y : int, forall z : int, ((lez (int_of_nat (NUMERAL O)) w) /\ ((ltz w x) /\ ((lez (int_of_nat (NUMERAL O)) y) /\ (ltz y z)))) -> ltz (mulz w y) (mulz x z).
Axiom thm_INT_LT_MUL_EQ : (forall x : int, forall y : int, (ltz (int_of_nat (NUMERAL O)) x) -> (ltz (int_of_nat (NUMERAL O)) (mulz x y)) = (ltz (int_of_nat (NUMERAL O)) y)) /\ (forall x : int, forall y : int, (ltz (int_of_nat (NUMERAL O)) y) -> (ltz (int_of_nat (NUMERAL O)) (mulz x y)) = (ltz (int_of_nat (NUMERAL O)) x)).
Axiom thm_INT_LT_NEG2 : forall x : int, forall y : int, (ltz (oppz x) (oppz y)) = (ltz y x).
Axiom thm_INT_LT_NEGTOTAL : forall x : int, (x = (int_of_nat (NUMERAL O))) \/ ((ltz (int_of_nat (NUMERAL O)) x) \/ (ltz (int_of_nat (NUMERAL O)) (oppz x))).
Axiom thm_INT_LT_POW2 : forall n : nat, ltz (int_of_nat (NUMERAL O)) (expz (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) n).
Axiom thm_INT_LT_POW_2 : forall x : int, (ltz (int_of_nat (NUMERAL O)) (expz x (NUMERAL (BIT0 (BIT1 O))))) = (~ (x = (int_of_nat (NUMERAL O)))).
Axiom thm_INT_LT_RADD : forall x : int, forall y : int, forall z : int, (ltz (addz x z) (addz y z)) = (ltz x y).
Axiom thm_INT_LT_RCANCEL_IMP : forall x : int, forall y : int, forall z : int, ((ltz (int_of_nat (NUMERAL O)) z) /\ (ltz (mulz x z) (mulz y z))) -> ltz x y.
Axiom thm_INT_LT_REFL : forall x : int, ~ (ltz x x).
Axiom thm_INT_LT_RMUL : forall x : int, forall y : int, forall z : int, ((ltz x y) /\ (ltz (int_of_nat (NUMERAL O)) z)) -> ltz (mulz x z) (mulz y z).
Axiom thm_INT_LT_RMUL_EQ : forall x : int, forall y : int, forall z : int, (ltz (int_of_nat (NUMERAL O)) z) -> (ltz (mulz x z) (mulz y z)) = (ltz x y).
Axiom thm_INT_LT_RNEG : forall x : int, forall y : int, (ltz x (oppz y)) = (ltz (addz x y) (int_of_nat (NUMERAL O))).
Axiom thm_INT_LT_SQUARE : forall x : int, (ltz (int_of_nat (NUMERAL O)) (mulz x x)) = (~ (x = (int_of_nat (NUMERAL O)))).
Axiom thm_INT_LT_SQUARE_ABS : forall x : int, forall y : int, (ltz (normz x) (normz y)) = (ltz (expz x (NUMERAL (BIT0 (BIT1 O)))) (expz y (NUMERAL (BIT0 (BIT1 O))))).
Axiom thm_INT_LT_SUB_LADD : forall x : int, forall y : int, forall z : int, (ltz x (subz y z)) = (ltz (addz x z) y).
Axiom thm_INT_LT_SUB_RADD : forall x : int, forall y : int, forall z : int, (ltz (subz x y) z) = (ltz x (addz z y)).
Axiom thm_INT_LT_TOTAL : forall x : int, forall y : int, (x = y) \/ ((ltz x y) \/ (ltz y x)).
Axiom thm_INT_LT_TRANS : forall x : int, forall y : int, forall z : int, ((ltz x y) /\ (ltz y z)) -> ltz x z.
Axiom thm_INT_MAX_ACI : forall (z : int) (x : int) (y : int), ((maxz x y) = (maxz y x)) /\ (((maxz (maxz x y) z) = (maxz x (maxz y z))) /\ (((maxz x (maxz y z)) = (maxz y (maxz x z))) /\ (((maxz x x) = x) /\ ((maxz x (maxz x y)) = (maxz x y))))).
Axiom thm_INT_MAX_ASSOC : forall x : int, forall y : int, forall z : int, (maxz x (maxz y z)) = (maxz (maxz x y) z).
Axiom thm_INT_MAX_LE : forall x : int, forall y : int, forall z : int, (lez (maxz x y) z) = ((lez x z) /\ (lez y z)).
Axiom thm_INT_MAX_LT : forall x : int, forall y : int, forall z : int, (ltz (maxz x y) z) = ((ltz x z) /\ (ltz y z)).
Axiom thm_INT_MAX_MAX : forall x : int, forall y : int, (lez x (maxz x y)) /\ (lez y (maxz x y)).
Axiom thm_INT_MAX_MIN : forall x : int, forall y : int, (maxz x y) = (oppz (minz (oppz x) (oppz y))).
Axiom thm_INT_MAX_SYM : forall x : int, forall y : int, (maxz x y) = (maxz y x).
Axiom thm_INT_MIN_ACI : forall (z : int) (x : int) (y : int), ((minz x y) = (minz y x)) /\ (((minz (minz x y) z) = (minz x (minz y z))) /\ (((minz x (minz y z)) = (minz y (minz x z))) /\ (((minz x x) = x) /\ ((minz x (minz x y)) = (minz x y))))).
Axiom thm_INT_MIN_ASSOC : forall x : int, forall y : int, forall z : int, (minz x (minz y z)) = (minz (minz x y) z).
Axiom thm_INT_MIN_LE : forall x : int, forall y : int, forall z : int, (lez (minz x y) z) = ((lez x z) \/ (lez y z)).
Axiom thm_INT_MIN_LT : forall x : int, forall y : int, forall z : int, (ltz (minz x y) z) = ((ltz x z) \/ (ltz y z)).
Axiom thm_INT_MIN_MAX : forall x : int, forall y : int, (minz x y) = (oppz (maxz (oppz x) (oppz y))).
Axiom thm_INT_MIN_MIN : forall x : int, forall y : int, (lez (minz x y) x) /\ (lez (minz x y) y).
Axiom thm_INT_MIN_SYM : forall x : int, forall y : int, (minz x y) = (minz y x).
Axiom thm_INT_MUL_2 : forall x : int, (mulz (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) x) = (addz x x).
Axiom thm_INT_MUL_AC : forall (n : int) (m : int) (p : int), ((mulz m n) = (mulz n m)) /\ (((mulz (mulz m n) p) = (mulz m (mulz n p))) /\ ((mulz m (mulz n p)) = (mulz n (mulz m p)))).
Axiom thm_INT_MUL_ASSOC : forall x : int, forall y : int, forall z : int, (mulz x (mulz y z)) = (mulz (mulz x y) z).
Axiom thm_INT_MUL_LID : forall x : int, (mulz (int_of_nat (NUMERAL (BIT1 O))) x) = x.
Axiom thm_INT_MUL_LNEG : forall x : int, forall y : int, (mulz (oppz x) y) = (oppz (mulz x y)).
Axiom thm_INT_MUL_LZERO : forall x : int, (mulz (int_of_nat (NUMERAL O)) x) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_MUL_POS_LE : forall x : int, forall y : int, (lez (int_of_nat (NUMERAL O)) (mulz x y)) = ((x = (int_of_nat (NUMERAL O))) \/ ((y = (int_of_nat (NUMERAL O))) \/ (((ltz (int_of_nat (NUMERAL O)) x) /\ (ltz (int_of_nat (NUMERAL O)) y)) \/ ((ltz x (int_of_nat (NUMERAL O))) /\ (ltz y (int_of_nat (NUMERAL O))))))).
Axiom thm_INT_MUL_POS_LT : forall x : int, forall y : int, (ltz (int_of_nat (NUMERAL O)) (mulz x y)) = (((ltz (int_of_nat (NUMERAL O)) x) /\ (ltz (int_of_nat (NUMERAL O)) y)) \/ ((ltz x (int_of_nat (NUMERAL O))) /\ (ltz y (int_of_nat (NUMERAL O))))).
Axiom thm_INT_MUL_RID : forall x : int, (mulz x (int_of_nat (NUMERAL (BIT1 O)))) = x.
Axiom thm_INT_MUL_RNEG : forall x : int, forall y : int, (mulz x (oppz y)) = (oppz (mulz x y)).
Axiom thm_INT_MUL_RZERO : forall x : int, (mulz x (int_of_nat (NUMERAL O))) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_MUL_SYM : forall x : int, forall y : int, (mulz x y) = (mulz y x).
Axiom thm_INT_NEG_0 : (oppz (int_of_nat (NUMERAL O))) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_NEG_ADD : forall x : int, forall y : int, (oppz (addz x y)) = (addz (oppz x) (oppz y)).
Axiom thm_INT_NEG_EQ : forall x : int, forall y : int, ((oppz x) = y) = (x = (oppz y)).
Axiom thm_INT_NEG_EQ_0 : forall x : int, ((oppz x) = (int_of_nat (NUMERAL O))) = (x = (int_of_nat (NUMERAL O))).
Axiom thm_INT_NEG_GE0 : forall x : int, (lez (int_of_nat (NUMERAL O)) (oppz x)) = (lez x (int_of_nat (NUMERAL O))).
Axiom thm_INT_NEG_GT0 : forall x : int, (ltz (int_of_nat (NUMERAL O)) (oppz x)) = (ltz x (int_of_nat (NUMERAL O))).
Axiom thm_INT_NEG_LE0 : forall x : int, (lez (oppz x) (int_of_nat (NUMERAL O))) = (lez (int_of_nat (NUMERAL O)) x).
Axiom thm_INT_NEG_LMUL : forall x : int, forall y : int, (oppz (mulz x y)) = (mulz (oppz x) y).
Axiom thm_INT_NEG_LT0 : forall x : int, (ltz (oppz x) (int_of_nat (NUMERAL O))) = (ltz (int_of_nat (NUMERAL O)) x).
Axiom thm_INT_NEG_MINUS1 : forall x : int, (oppz x) = (mulz (oppz (int_of_nat (NUMERAL (BIT1 O)))) x).
Axiom thm_INT_NEG_MUL2 : forall x : int, forall y : int, (mulz (oppz x) (oppz y)) = (mulz x y).
Axiom thm_INT_NEG_NEG : forall x : int, (oppz (oppz x)) = x.
Axiom thm_INT_NEG_RMUL : forall x : int, forall y : int, (oppz (mulz x y)) = (mulz x (oppz y)).
Axiom thm_INT_NEG_SUB : forall x : int, forall y : int, (oppz (subz x y)) = (subz y x).
Axiom thm_INT_NOT_EQ : forall x : int, forall y : int, (~ (x = y)) = ((ltz x y) \/ (ltz y x)).
Axiom thm_INT_NOT_LE : forall x : int, forall y : int, (~ (lez x y)) = (ltz y x).
Axiom thm_INT_NOT_LT : forall x : int, forall y : int, (~ (ltz x y)) = (lez y x).
Axiom thm_INT_OF_NUM_ADD : forall m : nat, forall n : nat, (addz (int_of_nat m) (int_of_nat n)) = (int_of_nat (addn m n)).
Axiom thm_INT_OF_NUM_CLAUSES : (forall m : nat, forall n : nat, ((int_of_nat m) = (int_of_nat n)) = (m = n)) /\ ((forall m : nat, forall n : nat, (gez (int_of_nat m) (int_of_nat n)) = (geqn m n)) /\ ((forall m : nat, forall n : nat, (gtz (int_of_nat m) (int_of_nat n)) = (gtn m n)) /\ ((forall m : nat, forall n : nat, (lez (int_of_nat m) (int_of_nat n)) = (leqn m n)) /\ ((forall m : nat, forall n : nat, (ltz (int_of_nat m) (int_of_nat n)) = (ltn m n)) /\ ((forall m : nat, forall n : nat, (maxz (int_of_nat m) (int_of_nat n)) = (int_of_nat (maxn m n))) /\ ((forall m : nat, forall n : nat, (minz (int_of_nat m) (int_of_nat n)) = (int_of_nat (minn m n))) /\ ((forall m : nat, forall n : nat, (addz (int_of_nat m) (int_of_nat n)) = (int_of_nat (addn m n))) /\ ((forall m : nat, forall n : nat, (mulz (int_of_nat m) (int_of_nat n)) = (int_of_nat (muln m n))) /\ (forall x : nat, forall n : nat, (expz (int_of_nat x) n) = (int_of_nat (expn x n))))))))))).
Axiom thm_INT_OF_NUM_EQ : forall m : nat, forall n : nat, ((int_of_nat m) = (int_of_nat n)) = (m = n).
Axiom thm_INT_OF_NUM_GE : forall m : nat, forall n : nat, (gez (int_of_nat m) (int_of_nat n)) = (geqn m n).
Axiom thm_INT_OF_NUM_GT : forall m : nat, forall n : nat, (gtz (int_of_nat m) (int_of_nat n)) = (gtn m n).
Axiom thm_INT_OF_NUM_LE : forall m : nat, forall n : nat, (lez (int_of_nat m) (int_of_nat n)) = (leqn m n).
Axiom thm_INT_OF_NUM_LT : forall m : nat, forall n : nat, (ltz (int_of_nat m) (int_of_nat n)) = (ltn m n).
Axiom thm_INT_OF_NUM_MAX : forall m : nat, forall n : nat, (maxz (int_of_nat m) (int_of_nat n)) = (int_of_nat (maxn m n)).
Axiom thm_INT_OF_NUM_MIN : forall m : nat, forall n : nat, (minz (int_of_nat m) (int_of_nat n)) = (int_of_nat (minn m n)).
Axiom thm_INT_OF_NUM_MOD : forall m : nat, forall n : nat, (int_of_nat (modn m n)) = (subz (int_of_nat m) (mulz (int_of_nat (divn m n)) (int_of_nat n))).
Axiom thm_INT_OF_NUM_MUL : forall m : nat, forall n : nat, (mulz (int_of_nat m) (int_of_nat n)) = (int_of_nat (muln m n)).
Axiom thm_INT_OF_NUM_POW : forall x : nat, forall n : nat, (expz (int_of_nat x) n) = (int_of_nat (expn x n)).
Axiom thm_INT_OF_NUM_SUB : forall m : nat, forall n : nat, (leqn m n) -> (subz (int_of_nat n) (int_of_nat m)) = (int_of_nat (subn n m)).
Axiom thm_INT_OF_NUM_SUB_CASES : forall m : nat, forall n : nat, (subz (int_of_nat m) (int_of_nat n)) = (@COND int (leqn n m) (int_of_nat (subn m n)) (oppz (int_of_nat (subn n m)))).
Axiom thm_INT_OF_NUM_SUC : forall n : nat, (addz (int_of_nat n) (int_of_nat (NUMERAL (BIT1 O)))) = (int_of_nat (S n)).
Axiom thm_INT_POS : forall n : nat, lez (int_of_nat (NUMERAL O)) (int_of_nat n).
Axiom thm_INT_POS_EQ_SQUARE : forall x : int, (lez (int_of_nat (NUMERAL O)) x) = (exists y : R, (expr y (NUMERAL (BIT0 (BIT1 O)))) = (real_of_int x)).
Axiom thm_INT_POS_NZ : forall x : int, (ltz (int_of_nat (NUMERAL O)) x) -> ~ (x = (int_of_nat (NUMERAL O))).
Axiom thm_INT_POW2_ABS : forall x : int, (expz (normz x) (NUMERAL (BIT0 (BIT1 O)))) = (expz x (NUMERAL (BIT0 (BIT1 O)))).
Axiom thm_INT_POW_1 : forall x : int, (expz x (NUMERAL (BIT1 O))) = x.
Axiom thm_INT_POW_1_LE : forall n : nat, forall x : int, ((lez (int_of_nat (NUMERAL O)) x) /\ (lez x (int_of_nat (NUMERAL (BIT1 O))))) -> lez (expz x n) (int_of_nat (NUMERAL (BIT1 O))).
Axiom thm_INT_POW_1_LT : forall n : nat, forall x : int, ((~ (n = (NUMERAL O))) /\ ((lez (int_of_nat (NUMERAL O)) x) /\ (ltz x (int_of_nat (NUMERAL (BIT1 O)))))) -> ltz (expz x n) (int_of_nat (NUMERAL (BIT1 O))).
Axiom thm_INT_POW_2 : forall x : int, (expz x (NUMERAL (BIT0 (BIT1 O)))) = (mulz x x).
Axiom thm_INT_POW_ADD : forall x : int, forall m : nat, forall n : nat, (expz x (addn m n)) = (mulz (expz x m) (expz x n)).
Axiom thm_INT_POW_EQ : forall n : nat, forall x : int, forall y : int, ((~ (n = (NUMERAL O))) /\ ((lez (int_of_nat (NUMERAL O)) x) /\ ((lez (int_of_nat (NUMERAL O)) y) /\ ((expz x n) = (expz y n))))) -> x = y.
Axiom thm_INT_POW_EQ_0 : forall x : int, forall n : nat, ((expz x n) = (int_of_nat (NUMERAL O))) = ((x = (int_of_nat (NUMERAL O))) /\ (~ (n = (NUMERAL O)))).
Axiom thm_INT_POW_EQ_1 : forall x : int, forall n : nat, ((expz x n) = (int_of_nat (NUMERAL (BIT1 O)))) = ((((normz x) = (int_of_nat (NUMERAL (BIT1 O)))) /\ ((ltz x (int_of_nat (NUMERAL O))) -> even n)) \/ (n = (NUMERAL O))).
Axiom thm_INT_POW_EQ_1_IMP : forall x : int, forall n : nat, ((~ (n = (NUMERAL O))) /\ ((expz x n) = (int_of_nat (NUMERAL (BIT1 O))))) -> (normz x) = (int_of_nat (NUMERAL (BIT1 O))).
Axiom thm_INT_POW_EQ_ABS : forall n : nat, forall x : int, forall y : int, ((~ (n = (NUMERAL O))) /\ ((expz x n) = (expz y n))) -> (normz x) = (normz y).
Axiom thm_INT_POW_EQ_EQ : forall n : nat, forall x : int, forall y : int, ((expz x n) = (expz y n)) = (@COND Prop (even n) ((n = (NUMERAL O)) \/ ((normz x) = (normz y))) (x = y)).
Axiom thm_INT_POW_EQ_ODD : forall n : nat, forall x : int, forall y : int, ((oddn n) /\ ((expz x n) = (expz y n))) -> x = y.
Axiom thm_INT_POW_EQ_ODD_EQ : forall n : nat, forall x : int, forall y : int, (oddn n) -> ((expz x n) = (expz y n)) = (x = y).
Axiom thm_INT_POW_LBOUND : forall x : int, forall n : nat, (lez (int_of_nat (NUMERAL O)) x) -> lez (addz (int_of_nat (NUMERAL (BIT1 O))) (mulz (int_of_nat n) x)) (expz (addz (int_of_nat (NUMERAL (BIT1 O))) x) n).
Axiom thm_INT_POW_LE : forall x : int, forall n : nat, (lez (int_of_nat (NUMERAL O)) x) -> lez (int_of_nat (NUMERAL O)) (expz x n).
Axiom thm_INT_POW_LE2 : forall n : nat, forall x : int, forall y : int, ((lez (int_of_nat (NUMERAL O)) x) /\ (lez x y)) -> lez (expz x n) (expz y n).
Axiom thm_INT_POW_LE2_ODD : forall n : nat, forall x : int, forall y : int, ((lez x y) /\ (oddn n)) -> lez (expz x n) (expz y n).
Axiom thm_INT_POW_LE2_ODD_EQ : forall n : nat, forall x : int, forall y : int, (oddn n) -> (lez (expz x n) (expz y n)) = (lez x y).
Axiom thm_INT_POW_LE2_REV : forall n : nat, forall x : int, forall y : int, ((~ (n = (NUMERAL O))) /\ ((lez (int_of_nat (NUMERAL O)) y) /\ (lez (expz x n) (expz y n)))) -> lez x y.
Axiom thm_INT_POW_LE_1 : forall n : nat, forall x : int, (lez (int_of_nat (NUMERAL (BIT1 O))) x) -> lez (int_of_nat (NUMERAL (BIT1 O))) (expz x n).
Axiom thm_INT_POW_LT : forall x : int, forall n : nat, (ltz (int_of_nat (NUMERAL O)) x) -> ltz (int_of_nat (NUMERAL O)) (expz x n).
Axiom thm_INT_POW_LT2 : forall n : nat, forall x : int, forall y : int, ((~ (n = (NUMERAL O))) /\ ((lez (int_of_nat (NUMERAL O)) x) /\ (ltz x y))) -> ltz (expz x n) (expz y n).
Axiom thm_INT_POW_LT2_ODD : forall n : nat, forall x : int, forall y : int, ((ltz x y) /\ (oddn n)) -> ltz (expz x n) (expz y n).
Axiom thm_INT_POW_LT2_ODD_EQ : forall n : nat, forall x : int, forall y : int, (oddn n) -> (ltz (expz x n) (expz y n)) = (ltz x y).
Axiom thm_INT_POW_LT2_REV : forall n : nat, forall x : int, forall y : int, ((lez (int_of_nat (NUMERAL O)) y) /\ (ltz (expz x n) (expz y n))) -> ltz x y.
Axiom thm_INT_POW_LT_1 : forall n : nat, forall x : int, ((~ (n = (NUMERAL O))) /\ (ltz (int_of_nat (NUMERAL (BIT1 O))) x)) -> ltz (int_of_nat (NUMERAL (BIT1 O))) (expz x n).
Axiom thm_INT_POW_MONO : forall m : nat, forall n : nat, forall x : int, ((lez (int_of_nat (NUMERAL (BIT1 O))) x) /\ (leqn m n)) -> lez (expz x m) (expz x n).
Axiom thm_INT_POW_MONO_LT : forall m : nat, forall n : nat, forall x : int, ((ltz (int_of_nat (NUMERAL (BIT1 O))) x) /\ (ltn m n)) -> ltz (expz x m) (expz x n).
Axiom thm_INT_POW_MUL : forall x : int, forall y : int, forall n : nat, (expz (mulz x y) n) = (mulz (expz x n) (expz y n)).
Axiom thm_INT_POW_NEG : forall x : int, forall n : nat, (expz (oppz x) n) = (@COND int (even n) (expz x n) (oppz (expz x n))).
Axiom thm_INT_POW_NZ : forall x : int, forall n : nat, (~ (x = (int_of_nat (NUMERAL O)))) -> ~ ((expz x n) = (int_of_nat (NUMERAL O))).
Axiom thm_INT_POW_ONE : forall n : nat, (expz (int_of_nat (NUMERAL (BIT1 O))) n) = (int_of_nat (NUMERAL (BIT1 O))).
Axiom thm_INT_POW_POW : forall x : int, forall m : nat, forall n : nat, (expz (expz x m) n) = (expz x (muln m n)).
Axiom thm_INT_POW_ZERO : forall n : nat, (expz (int_of_nat (NUMERAL O)) n) = (@COND int (n = (NUMERAL O)) (int_of_nat (NUMERAL (BIT1 O))) (int_of_nat (NUMERAL O))).
Axiom thm_INT_RNEG_UNIQ : forall x : int, forall y : int, ((addz x y) = (int_of_nat (NUMERAL O))) = (y = (oppz x)).
Axiom thm_INT_SGN : forall x : int, (sgz x) = (@COND int (ltz (int_of_nat (NUMERAL O)) x) (int_of_nat (NUMERAL (BIT1 O))) (@COND int (ltz x (int_of_nat (NUMERAL O))) (oppz (int_of_nat (NUMERAL (BIT1 O)))) (int_of_nat (NUMERAL O)))).
Axiom thm_INT_SGNS_EQ : forall x : int, forall y : int, ((sgz x) = (sgz y)) = (((x = (int_of_nat (NUMERAL O))) = (y = (int_of_nat (NUMERAL O)))) /\ (((gtz x (int_of_nat (NUMERAL O))) = (gtz y (int_of_nat (NUMERAL O)))) /\ ((ltz x (int_of_nat (NUMERAL O))) = (ltz y (int_of_nat (NUMERAL O)))))).
Axiom thm_INT_SGNS_EQ_ALT : forall x : int, forall y : int, ((sgz x) = (sgz y)) = (((x = (int_of_nat (NUMERAL O))) -> y = (int_of_nat (NUMERAL O))) /\ (((gtz x (int_of_nat (NUMERAL O))) -> gtz y (int_of_nat (NUMERAL O))) /\ ((ltz x (int_of_nat (NUMERAL O))) -> ltz y (int_of_nat (NUMERAL O))))).
Axiom thm_INT_SGN_0 : (sgz (int_of_nat (NUMERAL O))) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_SGN_ABS : forall x : int, (mulz (sgz x) (normz x)) = x.
Axiom thm_INT_SGN_ABS_ALT : forall x : int, (mulz (sgz x) x) = (normz x).
Axiom thm_INT_SGN_CASES : forall x : int, ((sgz x) = (int_of_nat (NUMERAL O))) \/ (((sgz x) = (int_of_nat (NUMERAL (BIT1 O)))) \/ ((sgz x) = (oppz (int_of_nat (NUMERAL (BIT1 O)))))).
Axiom thm_INT_SGN_EQ : (forall x : int, ((sgz x) = (int_of_nat (NUMERAL O))) = (x = (int_of_nat (NUMERAL O)))) /\ ((forall x : int, ((sgz x) = (int_of_nat (NUMERAL (BIT1 O)))) = (gtz x (int_of_nat (NUMERAL O)))) /\ (forall x : int, ((sgz x) = (oppz (int_of_nat (NUMERAL (BIT1 O))))) = (ltz x (int_of_nat (NUMERAL O))))).
Axiom thm_INT_SGN_EQ_INEQ : forall x : int, forall y : int, ((sgz x) = (sgz y)) = ((x = y) \/ (ltz (normz (subz x y)) (maxz (normz x) (normz y)))).
Axiom thm_INT_SGN_INEQS : (forall x : int, (lez (int_of_nat (NUMERAL O)) (sgz x)) = (lez (int_of_nat (NUMERAL O)) x)) /\ ((forall x : int, (ltz (int_of_nat (NUMERAL O)) (sgz x)) = (ltz (int_of_nat (NUMERAL O)) x)) /\ ((forall x : int, (gez (int_of_nat (NUMERAL O)) (sgz x)) = (gez (int_of_nat (NUMERAL O)) x)) /\ ((forall x : int, (gtz (int_of_nat (NUMERAL O)) (sgz x)) = (gtz (int_of_nat (NUMERAL O)) x)) /\ ((forall x : int, ((int_of_nat (NUMERAL O)) = (sgz x)) = ((int_of_nat (NUMERAL O)) = x)) /\ ((forall x : int, (lez (sgz x) (int_of_nat (NUMERAL O))) = (lez x (int_of_nat (NUMERAL O)))) /\ ((forall x : int, (ltz (sgz x) (int_of_nat (NUMERAL O))) = (ltz x (int_of_nat (NUMERAL O)))) /\ ((forall x : int, (gez (sgz x) (int_of_nat (NUMERAL O))) = (gez x (int_of_nat (NUMERAL O)))) /\ ((forall x : int, (gtz (sgz x) (int_of_nat (NUMERAL O))) = (gtz x (int_of_nat (NUMERAL O)))) /\ (forall x : int, ((sgz x) = (int_of_nat (NUMERAL O))) = (x = (int_of_nat (NUMERAL O)))))))))))).
Axiom thm_INT_SGN_INT_SGN : forall x : int, (sgz (sgz x)) = (sgz x).
Axiom thm_INT_SGN_MUL : forall x : int, forall y : int, (sgz (mulz x y)) = (mulz (sgz x) (sgz y)).
Axiom thm_INT_SGN_NEG : forall x : int, (sgz (oppz x)) = (oppz (sgz x)).
Axiom thm_INT_SGN_POW : forall x : int, forall n : nat, (sgz (expz x n)) = (expz (sgz x) n).
Axiom thm_INT_SGN_POW_2 : forall x : int, (sgz (expz x (NUMERAL (BIT0 (BIT1 O))))) = (sgz (normz x)).
Axiom thm_INT_SOS_EQ_0 : forall x : int, forall y : int, ((addz (expz x (NUMERAL (BIT0 (BIT1 O)))) (expz y (NUMERAL (BIT0 (BIT1 O))))) = (int_of_nat (NUMERAL O))) = ((x = (int_of_nat (NUMERAL O))) /\ (y = (int_of_nat (NUMERAL O)))).
Axiom thm_INT_SUB_0 : forall x : int, forall y : int, ((subz x y) = (int_of_nat (NUMERAL O))) = (x = y).
Axiom thm_INT_SUB_ABS : forall x : int, forall y : int, lez (subz (normz x) (normz y)) (normz (subz x y)).
Axiom thm_INT_SUB_ADD : forall x : int, forall y : int, (addz (subz x y) y) = x.
Axiom thm_INT_SUB_ADD2 : forall x : int, forall y : int, (addz y (subz x y)) = x.
Axiom thm_INT_SUB_LDISTRIB : forall x : int, forall y : int, forall z : int, (mulz x (subz y z)) = (subz (mulz x y) (mulz x z)).
Axiom thm_INT_SUB_LE : forall x : int, forall y : int, (lez (int_of_nat (NUMERAL O)) (subz x y)) = (lez y x).
Axiom thm_INT_SUB_LNEG : forall x : int, forall y : int, (subz (oppz x) y) = (oppz (addz x y)).
Axiom thm_INT_SUB_LT : forall x : int, forall y : int, (ltz (int_of_nat (NUMERAL O)) (subz x y)) = (ltz y x).
Axiom thm_INT_SUB_LZERO : forall x : int, (subz (int_of_nat (NUMERAL O)) x) = (oppz x).
Axiom thm_INT_SUB_NEG2 : forall x : int, forall y : int, (subz (oppz x) (oppz y)) = (subz y x).
Axiom thm_INT_SUB_RDISTRIB : forall x : int, forall y : int, forall z : int, (mulz (subz x y) z) = (subz (mulz x z) (mulz y z)).
Axiom thm_INT_SUB_REFL : forall x : int, (subz x x) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_SUB_RNEG : forall x : int, forall y : int, (subz x (oppz y)) = (addz x y).
Axiom thm_INT_SUB_RZERO : forall x : int, (subz x (int_of_nat (NUMERAL O))) = x.
Axiom thm_INT_SUB_SUB : forall x : int, forall y : int, (subz (subz x y) x) = (oppz y).
Axiom thm_INT_SUB_SUB2 : forall x : int, forall y : int, (subz x (subz x y)) = y.
Axiom thm_INT_SUB_TRIANGLE : forall a : int, forall b : int, forall c : int, (addz (subz a b) (subz b c)) = (subz a c).
Axiom thm_INT_WLOG_LE : forall (P : int -> int -> Prop), ((forall x : int, forall y : int, (P x y) = (P y x)) /\ (forall x : int, forall y : int, (lez x y) -> P x y)) -> forall x : int, forall y : int, P x y.
Axiom thm_INT_WLOG_LT : forall (P : int -> int -> Prop), ((forall x : int, P x x) /\ ((forall x : int, forall y : int, (P x y) = (P y x)) /\ (forall x : int, forall y : int, (ltz x y) -> P x y))) -> forall x : int, forall y : int, P x y.
Axiom thm_INT_WLOG_LE_3 : forall P : int -> int -> int -> Prop, ((forall x : int, forall y : int, forall z : int, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : int, forall y : int, forall z : int, ((lez x y) /\ (lez y z)) -> P x y z)) -> forall x : int, forall y : int, forall z : int, P x y z.
Axiom thm_INT_FORALL_POS : forall P : int -> Prop, (forall n : nat, P (int_of_nat n)) = (forall i : int, (lez (int_of_nat (NUMERAL O)) i) -> P i).
Axiom thm_INT_EXISTS_POS : forall P : int -> Prop, (exists n : nat, P (int_of_nat n)) = (exists i : int, (lez (int_of_nat (NUMERAL O)) i) /\ (P i)).
Axiom thm_INT_FORALL_ABS : forall P : int -> Prop, (forall n : nat, P (int_of_nat n)) = (forall x : int, P (normz x)).
Axiom thm_INT_EXISTS_ABS : forall P : int -> Prop, (exists n : nat, P (int_of_nat n)) = (exists x : int, P (normz x)).
Axiom thm_INT_POW : forall (x : int), ((expz x (NUMERAL O)) = (int_of_nat (NUMERAL (BIT1 O)))) /\ (forall n : nat, (expz x (S n)) = (mulz x (expz x n))).
Axiom thm_INT_ABS : forall x : int, (normz x) = (@COND int (lez (int_of_nat (NUMERAL O)) x) x (oppz x)).
Axiom thm_INT_GE : forall x : int, forall y : int, (gez x y) = (lez y x).
Axiom thm_INT_GT : forall x : int, forall y : int, (gtz x y) = (ltz y x).
Axiom thm_INT_LT : forall x : int, forall y : int, (ltz x y) = (~ (lez y x)).
Axiom thm_INT_SUB : forall x : int, forall y : int, (subz x y) = (addz x (oppz y)).
Axiom thm_INT_MAX : forall x : int, forall y : int, (maxz x y) = (@COND int (lez x y) y x).
Axiom thm_INT_MIN : forall x : int, forall y : int, (minz x y) = (@COND int (lez x y) x y).
Axiom thm_INT_OF_NUM_EXISTS : forall x : int, (exists n : nat, x = (int_of_nat n)) = (lez (int_of_nat (NUMERAL O)) x).
Axiom thm_INT_LE_DISCRETE : forall x : int, forall y : int, (lez x y) = (ltz x (addz y (int_of_nat (NUMERAL (BIT1 O))))).
Axiom thm_INT_LE_TRANS_LE : forall x : int, forall y : int, (lez x y) = (forall z : int, (lez y z) -> lez x z).
Axiom thm_INT_LE_TRANS_LT : forall x : int, forall y : int, (lez x y) = (forall z : int, (ltz y z) -> ltz x z).
Axiom thm_INT_MUL_EQ_1 : forall x : int, forall y : int, ((mulz x y) = (int_of_nat (NUMERAL (BIT1 O)))) = (((x = (int_of_nat (NUMERAL (BIT1 O)))) /\ (y = (int_of_nat (NUMERAL (BIT1 O))))) \/ ((x = (oppz (int_of_nat (NUMERAL (BIT1 O))))) /\ (y = (oppz (int_of_nat (NUMERAL (BIT1 O))))))).
Axiom thm_INT_ABS_MUL_1 : forall x : int, forall y : int, ((normz (mulz x y)) = (int_of_nat (NUMERAL (BIT1 O)))) = (((normz x) = (int_of_nat (NUMERAL (BIT1 O)))) /\ ((normz y) = (int_of_nat (NUMERAL (BIT1 O))))).
Axiom thm_INT_WOP : forall (P : int -> Prop), (exists x : int, (lez (int_of_nat (NUMERAL O)) x) /\ (P x)) = (exists x : int, (lez (int_of_nat (NUMERAL O)) x) /\ ((P x) /\ (forall y : int, ((lez (int_of_nat (NUMERAL O)) y) /\ (P y)) -> lez x y))).
Axiom thm_INT_ARCH : forall x : int, forall d : int, (~ (d = (int_of_nat (NUMERAL O)))) -> exists c : int, ltz x (mulz c d).
Axiom thm_INT_DIVMOD_EXIST_0 : forall m : int, forall n : int, exists q : int, exists r : int, @COND Prop (n = (int_of_nat (NUMERAL O))) ((q = (int_of_nat (NUMERAL O))) /\ (r = m)) ((lez (int_of_nat (NUMERAL O)) r) /\ ((ltz r (normz n)) /\ (m = (addz (mulz q n) r)))).
Axiom thm_INT_DIVISION : forall m : int, forall n : int, (~ (n = (int_of_nat (NUMERAL O)))) -> (m = (addz (mulz (divz m n) n) (modz m n))) /\ ((lez (int_of_nat (NUMERAL O)) (modz m n)) /\ (ltz (modz m n) (normz n))).
Axiom thm_INT_DIVISION_SIMP : forall m : int, forall n : int, (addz (mulz (divz m n) n) (modz m n)) = m.
Axiom thm_INT_REM_POS : forall a : int, forall b : int, (~ (b = (int_of_nat (NUMERAL O)))) -> lez (int_of_nat (NUMERAL O)) (modz a b).
Axiom thm_INT_DIV_0 : forall m : int, (divz m (int_of_nat (NUMERAL O))) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_REM_0 : forall m : int, (modz m (int_of_nat (NUMERAL O))) = m.
Axiom thm_INT_REM_POS_EQ : forall m : int, forall n : int, (lez (int_of_nat (NUMERAL O)) (modz m n)) = ((n = (int_of_nat (NUMERAL O))) -> lez (int_of_nat (NUMERAL O)) m).
Axiom thm_INT_REM_DIV : forall m : int, forall n : int, (modz m n) = (subz m (mulz (divz m n) n)).
Axiom thm_INT_LT_REM : forall x : int, forall n : int, (ltz (int_of_nat (NUMERAL O)) n) -> ltz (modz x n) n.
Axiom thm_INT_LT_REM_EQ : forall m : int, forall n : int, (ltz (modz m n) n) = ((ltz (int_of_nat (NUMERAL O)) n) \/ ((n = (int_of_nat (NUMERAL O))) /\ (ltz m (int_of_nat (NUMERAL O))))).
Axiom thm_cong : forall {A : Type'}, forall rel : A -> A -> Prop, forall x : A, forall y : A, (@eq2 A x y rel) = (rel x y).
Axiom thm_real_mod : forall x : R, forall y : R, forall n : R, (congruent_modzr n x y) = (exists q : R, (Rint q) /\ ((subr x y) = (mulr q n))).
Axiom thm_int_divides : forall b : int, forall a : int, (dividez a b) = (exists x : int, b = (mulz a x)).
Axiom thm_INT_DIVIDES_LE : forall x : int, forall y : int, (dividez x y) -> (lez (normz x) (normz y)) \/ (y = (int_of_nat (NUMERAL O))).
Axiom thm_int_mod : forall n : int, forall x : int, forall y : int, (int_mod n x y) = (dividez n (subz x y)).
Axiom thm_int_congruent : forall x : int, forall y : int, forall n : int, (@eq2 int x y (int_mod n)) = (exists d : int, (subz x y) = (mulz n d)).
Axiom thm_INT_CONG_IMP_EQ : forall x : int, forall y : int, forall n : int, ((ltz (normz (subz x y)) n) /\ (@eq2 int x y (int_mod n))) -> x = y.
Axiom thm_int_coprime : forall a : int, forall b : int, (pair_coprimez (@pair int int a b)) = (exists x : int, exists y : int, (addz (mulz a x) (mulz b y)) = (int_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_INT_DIVMOD_UNIQ : forall m : int, forall n : int, forall q : int, forall r : int, ((m = (addz (mulz q n) r)) /\ ((lez (int_of_nat (NUMERAL O)) r) /\ (ltz r (normz n)))) -> ((divz m n) = q) /\ ((modz m n) = r).
Axiom thm_INT_DIV_UNIQ : forall m : int, forall n : int, forall q : int, forall r : int, ((m = (addz (mulz q n) r)) /\ ((lez (int_of_nat (NUMERAL O)) r) /\ (ltz r (normz n)))) -> (divz m n) = q.
Axiom thm_INT_REM_UNIQ : forall m : int, forall n : int, forall q : int, forall r : int, ((m = (addz (mulz q n) r)) /\ ((lez (int_of_nat (NUMERAL O)) r) /\ (ltz r (normz n)))) -> (modz m n) = r.
Axiom thm_INT_REM_LT : forall m : int, forall n : int, (((~ (n = (int_of_nat (NUMERAL O)))) -> lez (int_of_nat (NUMERAL O)) m) /\ (ltz m n)) -> (modz m n) = m.
Axiom thm_INT_DIV_LT : forall m : int, forall n : int, (((~ (n = (int_of_nat (NUMERAL O)))) -> lez (int_of_nat (NUMERAL O)) m) /\ (ltz m n)) -> (divz m n) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_REM_RNEG : forall m : int, forall n : int, (modz m (oppz n)) = (modz m n).
Axiom thm_INT_DIV_RNEG : forall m : int, forall n : int, (divz m (oppz n)) = (oppz (divz m n)).
Axiom thm_INT_REM_RABS : forall x : int, forall y : int, (modz x (normz y)) = (modz x y).
Axiom thm_INT_REM_REM : forall m : int, forall n : int, (modz (modz m n) n) = (modz m n).
Axiom thm_INT_REM_EQ : forall m : int, forall n : int, forall p : int, ((modz m p) = (modz n p)) = (@eq2 int m n (int_mod p)).
Axiom thm_INT_REM_ZERO : forall n : int, (modz (int_of_nat (NUMERAL O)) n) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_DIV_ZERO : forall n : int, (divz (int_of_nat (NUMERAL O)) n) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_REM_EQ_0 : forall m : int, forall n : int, ((modz m n) = (int_of_nat (NUMERAL O))) = (dividez n m).
Axiom thm_INT_MUL_DIV_EQ : (forall m : int, forall n : int, ((mulz n (divz m n)) = m) = (dividez n m)) /\ (forall m : int, forall n : int, ((mulz (divz m n) n) = m) = (dividez n m)).
Axiom thm_INT_CONG_LREM : forall x : int, forall y : int, forall n : int, (@eq2 int (modz x n) y (int_mod n)) = (@eq2 int x y (int_mod n)).
Axiom thm_INT_CONG_RREM : forall x : int, forall y : int, forall n : int, (@eq2 int x (modz y n) (int_mod n)) = (@eq2 int x y (int_mod n)).
Axiom thm_INT_REM_MOD_SELF : forall m : int, forall n : int, @eq2 int (modz m n) m (int_mod n).
Axiom thm_INT_REM_REM_MUL : (forall m : int, forall n : int, forall p : int, (modz (modz m (mulz n p)) n) = (modz m n)) /\ (forall m : int, forall n : int, forall p : int, (modz (modz m (mulz n p)) p) = (modz m p)).
Axiom thm_INT_CONG_SOLVE_BOUNDS : forall a : int, forall n : int, (~ (n = (int_of_nat (NUMERAL O)))) -> exists x : int, (lez (int_of_nat (NUMERAL O)) x) /\ ((ltz x (normz n)) /\ (@eq2 int x a (int_mod n))).
Axiom thm_INT_NEG_REM : forall n : int, forall p : int, (modz (oppz (modz n p)) p) = (modz (oppz n) p).
Axiom thm_INT_ADD_REM : forall m : int, forall n : int, forall p : int, (modz (addz (modz m p) (modz n p)) p) = (modz (addz m n) p).
Axiom thm_INT_SUB_REM : forall m : int, forall n : int, forall p : int, (modz (subz (modz m p) (modz n p)) p) = (modz (subz m n) p).
Axiom thm_INT_MUL_REM : forall m : int, forall n : int, forall p : int, (modz (mulz (modz m p) (modz n p)) p) = (modz (mulz m n) p).
Axiom thm_INT_POW_REM : forall m : int, forall n : nat, forall p : int, (modz (expz (modz m p) n) p) = (modz (expz m n) p).
Axiom thm_INT_OF_NUM_REM : forall m : nat, forall n : nat, (modz (int_of_nat m) (int_of_nat n)) = (int_of_nat (modn m n)).
Axiom thm_INT_OF_NUM_DIV : forall m : nat, forall n : nat, (divz (int_of_nat m) (int_of_nat n)) = (int_of_nat (divn m n)).
Axiom thm_INT_REM_REFL : forall n : int, (modz n n) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_DIV_REFL : forall n : int, (divz n n) = (@COND int (n = (int_of_nat (NUMERAL O))) (int_of_nat (NUMERAL O)) (int_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_INT_REM_LNEG : forall m : int, forall n : int, (modz (oppz m) n) = (@COND int ((modz m n) = (int_of_nat (NUMERAL O))) (int_of_nat (NUMERAL O)) (subz (normz n) (modz m n))).
Axiom thm_INT_DIV_LNEG : forall m : int, forall n : int, (divz (oppz m) n) = (@COND int ((modz m n) = (int_of_nat (NUMERAL O))) (oppz (divz m n)) (subz (oppz (divz m n)) (sgz n))).
Axiom thm_INT_DIV_NEG2 : forall m : int, forall n : int, (divz (oppz m) (oppz n)) = (@COND int ((modz m n) = (int_of_nat (NUMERAL O))) (divz m n) (addz (divz m n) (sgz n))).
Axiom thm_INT_REM_NEG2 : forall m : int, forall n : int, (modz (oppz m) (oppz n)) = (@COND int ((modz m n) = (int_of_nat (NUMERAL O))) (int_of_nat (NUMERAL O)) (subz (normz n) (modz m n))).
Axiom thm_INT_REM_1 : forall n : int, (modz n (int_of_nat (NUMERAL (BIT1 O)))) = (int_of_nat (NUMERAL O)).
Axiom thm_INT_DIV_1 : forall n : int, (divz n (int_of_nat (NUMERAL (BIT1 O)))) = n.
Axiom thm_INT_REM_MUL : (forall m : int, forall n : int, (modz (mulz m n) n) = (int_of_nat (NUMERAL O))) /\ (forall m : int, forall n : int, (modz (mulz m n) m) = (int_of_nat (NUMERAL O))).
Axiom thm_INT_DIV_MUL : (forall m : int, forall n : int, (~ (n = (int_of_nat (NUMERAL O)))) -> (divz (mulz m n) n) = m) /\ (forall m : int, forall n : int, (~ (m = (int_of_nat (NUMERAL O)))) -> (divz (mulz m n) m) = n).
Axiom thm_INT_DIV_LT_EQ : forall a : int, forall b : int, forall c : int, (ltz (int_of_nat (NUMERAL O)) a) -> (ltz (divz b a) c) = (ltz b (mulz a c)).
Axiom thm_INT_LE_DIV_EQ : forall a : int, forall b : int, forall c : int, (ltz (int_of_nat (NUMERAL O)) a) -> (lez c (divz b a)) = (lez (mulz a c) b).
Axiom thm_INT_DIV_LE_EQ : forall a : int, forall b : int, forall c : int, (ltz (int_of_nat (NUMERAL O)) a) -> (lez (divz b a) c) = (ltz b (mulz a (addz c (int_of_nat (NUMERAL (BIT1 O)))))).
Axiom thm_INT_LT_DIV_EQ : forall a : int, forall b : int, forall c : int, (ltz (int_of_nat (NUMERAL O)) a) -> (ltz c (divz b a)) = (lez (mulz a (addz c (int_of_nat (NUMERAL (BIT1 O))))) b).
Axiom thm_INT_DIV_LE : forall m : int, forall n : int, lez (normz (divz m n)) (normz m).
Axiom thm_INT_REM_MUL_REM : forall m : int, forall n : int, forall p : int, (lez (int_of_nat (NUMERAL O)) n) -> (modz m (mulz n p)) = (addz (mulz n (modz (divz m n) p)) (modz m n)).
Axiom thm_INT_DIV_DIV : forall m : int, forall n : int, forall p : int, (lez (int_of_nat (NUMERAL O)) n) -> (divz (divz m n) p) = (divz m (mulz n p)).
Axiom thm_INT_DIV_EQ_0 : forall m : int, forall n : int, ((divz m n) = (int_of_nat (NUMERAL O))) = ((n = (int_of_nat (NUMERAL O))) \/ ((lez (int_of_nat (NUMERAL O)) m) /\ (ltz m (normz n)))).
Axiom thm_INT_REM_EQ_SELF : forall m : int, forall n : int, ((modz m n) = m) = ((n = (int_of_nat (NUMERAL O))) \/ ((lez (int_of_nat (NUMERAL O)) m) /\ (ltz m (normz n)))).
Axiom thm_INT_REM_UNIQUE : forall m : int, forall n : int, forall p : int, ((modz m n) = p) = ((((n = (int_of_nat (NUMERAL O))) /\ (m = p)) \/ ((lez (int_of_nat (NUMERAL O)) p) /\ (ltz p (normz n)))) /\ (@eq2 int m p (int_mod n))).
Axiom thm_INT_DIV_REM : forall m : int, forall n : int, forall p : int, (lez (int_of_nat (NUMERAL O)) n) -> (modz (divz m n) p) = (divz (modz m (mulz n p)) n).
Axiom thm_INT_REM_REM_LE : forall m : int, forall n : int, forall p : int, ((~ (n = (int_of_nat (NUMERAL O)))) /\ (lez (normz n) (normz p))) -> (modz (modz m n) p) = (modz m n).
Axiom thm_INT_LE_DIV : forall m : int, forall n : int, ((lez (int_of_nat (NUMERAL O)) m) /\ (lez (int_of_nat (NUMERAL O)) n)) -> lez (int_of_nat (NUMERAL O)) (divz m n).
Axiom thm_INT_LT_DIV : forall m : int, forall n : int, ((ltz (int_of_nat (NUMERAL O)) n) /\ (lez n m)) -> ltz (int_of_nat (NUMERAL O)) (divz m n).
Axiom thm_INT_REM_LE_EQ : forall m : int, forall n : int, (lez (modz m n) m) = ((n = (int_of_nat (NUMERAL O))) \/ (lez (int_of_nat (NUMERAL O)) m)).
Axiom thm_INT_REM_LE : forall m : int, forall n : int, forall p : int, (((n = (int_of_nat (NUMERAL O))) \/ (lez (int_of_nat (NUMERAL O)) m)) /\ (lez m p)) -> lez (modz m n) p.
Axiom thm_INT_REM_MUL_ADD : (forall m : int, forall n : int, forall p : int, (modz (addz (mulz m n) p) n) = (modz p n)) /\ ((forall m : int, forall n : int, forall p : int, (modz (addz (mulz n m) p) n) = (modz p n)) /\ ((forall m : int, forall n : int, forall p : int, (modz (addz p (mulz m n)) n) = (modz p n)) /\ (forall m : int, forall n : int, forall p : int, (modz (addz p (mulz n m)) n) = (modz p n)))).
Axiom thm_INT_DIV_MUL_ADD : (forall m : int, forall n : int, forall p : int, (~ (n = (int_of_nat (NUMERAL O)))) -> (divz (addz (mulz m n) p) n) = (addz m (divz p n))) /\ ((forall m : int, forall n : int, forall p : int, (~ (n = (int_of_nat (NUMERAL O)))) -> (divz (addz (mulz n m) p) n) = (addz m (divz p n))) /\ ((forall m : int, forall n : int, forall p : int, (~ (n = (int_of_nat (NUMERAL O)))) -> (divz (addz p (mulz m n)) n) = (addz (divz p n) m)) /\ (forall m : int, forall n : int, forall p : int, (~ (n = (int_of_nat (NUMERAL O)))) -> (divz (addz p (mulz n m)) n) = (addz (divz p n) m)))).
Axiom thm_INT_CONG_DIV2 : forall a : int, forall b : int, forall m : int, forall n : int, (@eq2 int a b (int_mod (mulz m n))) -> @eq2 int (divz a m) (divz b m) (int_mod n).
Axiom thm_INT_REM_2_CASES : forall n : int, ((modz n (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (int_of_nat (NUMERAL O))) \/ ((modz n (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (int_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_NOT_INT_REM_2 : (forall n : int, (~ ((modz n (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (int_of_nat (NUMERAL O)))) = ((modz n (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (int_of_nat (NUMERAL (BIT1 O))))) /\ (forall n : int, (~ ((modz n (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (int_of_nat (NUMERAL (BIT1 O))))) = ((modz n (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (int_of_nat (NUMERAL O)))).
Axiom thm_INT_REM_2_DIVIDES : (forall n : int, ((modz n (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (int_of_nat (NUMERAL O))) = (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) n)) /\ (forall n : int, ((modz n (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (int_of_nat (NUMERAL (BIT1 O)))) = (~ (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) n))).
Axiom thm_INT_REM_2_EXPAND : forall x : int, (modz x (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (@COND int (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) x) (int_of_nat (NUMERAL O)) (int_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_INT_REM_2_NEG : forall x : int, (modz (oppz x) (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (modz x (int_of_nat (NUMERAL (BIT0 (BIT1 O))))).
Axiom thm_INT_DIVIDES_DIV_SELF : forall n : int, forall d : int, (dividez d n) -> dividez (divz n d) n.
Axiom thm_INT_DIV_BY_DIV : forall m : int, forall n : int, ((~ (n = (int_of_nat (NUMERAL O)))) /\ (dividez m n)) -> (divz n (divz n m)) = m.
Axiom thm_INT_DIVIDES_DIV_DIVIDES : forall n : int, forall d : int, forall e : int, ((dividez d n) /\ ((n = (int_of_nat (NUMERAL O))) -> e = (int_of_nat (NUMERAL O)))) -> (dividez (divz n d) e) = (dividez n (mulz d e)).
Axiom thm_INT_DIVIDES_DIVIDES_DIV : forall n : int, forall d : int, forall e : int, (dividez d n) -> (dividez e (divz n d)) = (dividez (mulz d e) n).
Axiom thm_INT_DIVIDES_DIVIDES_DIV_EQ : forall n : int, forall d : int, forall e : int, ((dividez d n) /\ (dividez e (divz n d))) = (dividez (mulz d e) n).
Axiom thm_INT_2_DIVIDES_ADD : forall m : int, forall n : int, (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) (addz m n)) = ((dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) m) = (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) n)).
Axiom thm_INT_2_DIVIDES_SUB : forall m : int, forall n : int, (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) (subz m n)) = ((dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) m) = (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) n)).
Axiom thm_INT_2_DIVIDES_MUL : forall m : int, forall n : int, (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) (mulz m n)) = ((dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) m) \/ (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) n)).
Axiom thm_INT_2_DIVIDES_POW : forall n : int, forall k : nat, (dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) (expz n k)) = ((dividez (int_of_nat (NUMERAL (BIT0 (BIT1 O)))) n) /\ (~ (k = (NUMERAL O)))).
Axiom thm_WF_INT_MEASURE : forall {A : Type'}, forall P : A -> Prop, forall m : A -> int, ((forall x : A, lez (int_of_nat (NUMERAL O)) (m x)) /\ (forall x : A, (forall y : A, (ltz (m y) (m x)) -> P y) -> P x)) -> forall x : A, P x.
Axiom thm_WF_INT_MEASURE_2 : forall {A B : Type'}, forall P : A -> B -> Prop, forall m : A -> B -> int, ((forall x : A, forall y : B, lez (int_of_nat (NUMERAL O)) (m x y)) /\ (forall x : A, forall y : B, (forall x' : A, forall y' : B, (ltz (m x' y') (m x y)) -> P x' y') -> P x y)) -> forall x : A, forall y : B, P x y.
Axiom thm_INT_GCD_EXISTS : forall a : int, forall b : int, exists d : int, (dividez d a) /\ ((dividez d b) /\ (exists x : int, exists y : int, d = (addz (mulz a x) (mulz b y)))).
Axiom thm_INT_GCD_EXISTS_POS : forall a : int, forall b : int, exists d : int, (lez (int_of_nat (NUMERAL O)) d) /\ ((dividez d a) /\ ((dividez d b) /\ (exists x : int, exists y : int, d = (addz (mulz a x) (mulz b y))))).
Axiom thm_int_lcm : forall m : int, forall n : int, (pair_lcmz (@pair int int m n)) = (@COND int ((mulz m n) = (int_of_nat (NUMERAL O))) (int_of_nat (NUMERAL O)) (divz (normz (mulz m n)) (pair_gcdz (@pair int int m n)))).
Axiom thm_INT_DIVIDES_LABS : forall d : int, forall n : int, (dividez (normz d) n) = (dividez d n).
Axiom thm_INT_DIVIDES_RABS : forall d : int, forall n : int, (dividez d (normz n)) = (dividez d n).
Axiom thm_INT_DIVIDES_ABS : (forall d : int, forall n : int, (dividez (normz d) n) = (dividez d n)) /\ (forall d : int, forall n : int, (dividez d (normz n)) = (dividez d n)).
Axiom thm_INT_LCM_POS : forall m : int, forall n : int, lez (int_of_nat (NUMERAL O)) (pair_lcmz (@pair int int m n)).
Axiom thm_INT_MUL_GCD_LCM : forall m : int, forall n : int, (mulz (pair_gcdz (@pair int int m n)) (pair_lcmz (@pair int int m n))) = (normz (mulz m n)).
Axiom thm_INT_MUL_LCM_GCD : forall m : int, forall n : int, (mulz (pair_lcmz (@pair int int m n)) (pair_gcdz (@pair int int m n))) = (normz (mulz m n)).
Axiom thm_INT_DIVIDES_LCM_GCD : forall m : int, forall n : int, forall d : int, (dividez d (pair_lcmz (@pair int int m n))) = (dividez (mulz d (pair_gcdz (@pair int int m n))) (mulz m n)).
Axiom thm_INT_LCM_DIVIDES : forall m : int, forall n : int, forall d : int, (dividez (pair_lcmz (@pair int int m n)) d) = ((dividez m d) /\ (dividez n d)).
Axiom thm_INT_LCM : forall m : int, forall n : int, (dividez m (pair_lcmz (@pair int int m n))) /\ ((dividez n (pair_lcmz (@pair int int m n))) /\ (forall d : int, ((dividez m d) /\ (dividez n d)) -> dividez (pair_lcmz (@pair int int m n)) d)).
Axiom thm_num_of_int : forall x : int, (num_of_int x) = (@ε nat (fun n : nat => (int_of_nat n) = x)).
Axiom thm_NUM_OF_INT_OF_NUM : forall n : nat, (num_of_int (int_of_nat n)) = n.
Axiom thm_INT_OF_NUM_OF_INT : forall x : int, (lez (int_of_nat (NUMERAL O)) x) -> (int_of_nat (num_of_int x)) = x.
Axiom thm_NUM_OF_INT : forall x : int, (lez (int_of_nat (NUMERAL O)) x) = ((int_of_nat (num_of_int x)) = x).
Axiom thm_NUM_OF_INT_ADD : forall x : int, forall y : int, ((lez (int_of_nat (NUMERAL O)) x) /\ (lez (int_of_nat (NUMERAL O)) y)) -> (num_of_int (addz x y)) = (addn (num_of_int x) (num_of_int y)).
Axiom thm_NUM_OF_INT_MUL : forall x : int, forall y : int, ((lez (int_of_nat (NUMERAL O)) x) /\ (lez (int_of_nat (NUMERAL O)) y)) -> (num_of_int (mulz x y)) = (muln (num_of_int x) (num_of_int y)).
Axiom thm_NUM_OF_INT_POW : forall x : int, forall n : nat, (lez (int_of_nat (NUMERAL O)) x) -> (num_of_int (expz x n)) = (expn (num_of_int x) n).
Axiom thm_num_divides : forall a : nat, forall b : nat, (num_divides a b) = (dividez (int_of_nat a) (int_of_nat b)).
Axiom thm_num_mod : forall n : nat, forall x : nat, forall y : nat, (num_mod n x y) = (int_mod (int_of_nat n) (int_of_nat x) (int_of_nat y)).
Axiom thm_num_congruent : forall x : nat, forall y : nat, forall n : nat, (@eq2 nat x y (num_mod n)) = (@eq2 int (int_of_nat x) (int_of_nat y) (int_mod (int_of_nat n))).
Axiom thm_num_coprime : forall a : nat, forall b : nat, (num_coprime (@pair nat nat a b)) = (pair_coprimez (@pair int int (int_of_nat a) (int_of_nat b))).
Axiom thm_num_gcd : forall a : nat, forall b : nat, (num_gcd (@pair nat nat a b)) = (num_of_int (pair_gcdz (@pair int int (int_of_nat a) (int_of_nat b)))).
Axiom thm_num_lcm : forall a : nat, forall b : nat, (num_lcm (@pair nat nat a b)) = (num_of_int (pair_lcmz (@pair int int (int_of_nat a) (int_of_nat b)))).
Axiom thm_BINARY_INDUCT : forall P : nat -> Prop, ((P (NUMERAL O)) /\ (forall n : nat, (P n) -> (P (muln (NUMERAL (BIT0 (BIT1 O))) n)) /\ (P (addn (muln (NUMERAL (BIT0 (BIT1 O))) n) (NUMERAL (BIT1 O)))))) -> forall n : nat, P n.
Axiom thm_NUM_CASES_BINARY : forall P : nat -> Prop, (forall n : nat, P n) = ((forall n : nat, P (muln (NUMERAL (BIT0 (BIT1 O))) n)) /\ (forall n : nat, P (addn (muln (NUMERAL (BIT0 (BIT1 O))) n) (NUMERAL (BIT1 O))))).
Axiom thm_num_WF_DOWN : forall P : nat -> Prop, forall m : nat, ((forall n : nat, (leqn m n) -> P n) /\ (forall n : nat, ((ltn n m) /\ (forall p : nat, (ltn n p) -> P p)) -> P n)) -> forall n : nat, P n.
Axiom thm_INT_REM_REM_POW_MIN : forall x : int, forall p : int, forall m : nat, forall n : nat, (modz (modz x (expz p m)) (expz p n)) = (modz x (expz p (minn m n))).
Axiom thm_NUM_GCD : forall a : nat, forall b : nat, (int_of_nat (num_gcd (@pair nat nat a b))) = (pair_gcdz (@pair int int (int_of_nat a) (int_of_nat b))).
Axiom thm_NUM_LCM : forall a : nat, forall b : nat, (int_of_nat (num_lcm (@pair nat nat a b))) = (pair_lcmz (@pair int int (int_of_nat a) (int_of_nat b))).
Axiom thm_CONG : forall x : nat, forall y : nat, forall n : nat, (@eq2 nat x y (num_mod n)) = ((modn x n) = (modn y n)).
Axiom thm_CONG_LMOD : forall x : nat, forall y : nat, forall n : nat, (@eq2 nat (modn x n) y (num_mod n)) = (@eq2 nat x y (num_mod n)).
Axiom thm_CONG_RMOD : forall x : nat, forall y : nat, forall n : nat, (@eq2 nat x (modn y n) (num_mod n)) = (@eq2 nat x y (num_mod n)).
Axiom thm_CONG_DIV2 : forall a : nat, forall b : nat, forall m : nat, forall n : nat, (@eq2 nat a b (num_mod (muln m n))) -> @eq2 nat (divn a m) (divn b m) (num_mod n).
Axiom thm_divides : forall (b : nat) (a : nat), (num_divides a b) = (exists x : nat, b = (muln a x)).
Axiom thm_DIVIDES_LE : forall m : nat, forall n : nat, (num_divides m n) -> (leqn m n) \/ (n = (NUMERAL O)).
Axiom thm_DIVIDES_LE_STRONG : forall m : nat, forall n : nat, (num_divides m n) -> ((leqn (NUMERAL (BIT1 O)) m) /\ (leqn m n)) \/ (n = (NUMERAL O)).
Axiom thm_DIVIDES_LE_IMP : forall m : nat, forall n : nat, ((num_divides m n) /\ ((n = (NUMERAL O)) -> m = (NUMERAL O))) -> leqn m n.
Axiom thm_PROPERLY_DIVIDES_LE_IMP : forall m : nat, forall n : nat, ((num_divides m n) /\ ((~ (n = (NUMERAL O))) /\ (~ (m = n)))) -> leqn (muln (NUMERAL (BIT0 (BIT1 O))) m) n.
Axiom thm_DIVIDES_ANTISYM : forall m : nat, forall n : nat, ((num_divides m n) /\ (num_divides n m)) = (m = n).
Axiom thm_DIVIDES_ONE : forall n : nat, (num_divides n (NUMERAL (BIT1 O))) = (n = (NUMERAL (BIT1 O))).
Axiom thm_DIV_ADD : forall d : nat, forall a : nat, forall b : nat, ((num_divides d a) \/ (num_divides d b)) -> (divn (addn a b) d) = (addn (divn a d) (divn b d)).
Axiom thm_DIVIDES_MOD : forall m : nat, forall n : nat, (num_divides m n) = ((modn n m) = (NUMERAL O)).
Axiom thm_DIVIDES_DIV_MULT : forall m : nat, forall n : nat, (num_divides m n) = ((muln (divn n m) m) = n).
Axiom thm_DIV_BY_DIV : forall m : nat, forall n : nat, ((~ (n = (NUMERAL O))) /\ (num_divides m n)) -> (divn n (divn n m)) = m.
Axiom thm_DIVIDES_DIV_DIVIDES : forall n : nat, forall d : nat, forall e : nat, ((num_divides d n) /\ ((n = (NUMERAL O)) -> e = (NUMERAL O))) -> (num_divides (divn n d) e) = (num_divides n (muln d e)).
Axiom thm_DIVIDES_DIV_SELF : forall n : nat, forall d : nat, (num_divides d n) -> num_divides (divn n d) n.
Axiom thm_DIVIDES_DIVIDES_DIV : forall n : nat, forall d : nat, forall e : nat, (num_divides d n) -> (num_divides e (divn n d)) = (num_divides (muln d e) n).
Axiom thm_DIVIDES_DIVIDES_DIV_EQ : forall n : nat, forall d : nat, forall e : nat, ((num_divides d n) /\ (num_divides e (divn n d))) = (num_divides (muln d e) n).
Axiom thm_DIVIDES_DIVIDES_DIV_IMP : forall n : nat, forall d : nat, forall e : nat, (num_divides (muln d e) n) -> num_divides e (divn n d).
Axiom thm_MULT_DIV : (forall m : nat, forall n : nat, forall p : nat, (num_divides p m) -> (divn (muln m n) p) = (muln (divn m p) n)) /\ (forall m : nat, forall n : nat, forall p : nat, (num_divides p n) -> (divn (muln m n) p) = (muln m (divn n p))).
Axiom thm_COPRIME_LMOD : forall a : nat, forall n : nat, (num_coprime (@pair nat nat (modn a n) n)) = (num_coprime (@pair nat nat a n)).
Axiom thm_COPRIME_RMOD : forall a : nat, forall n : nat, (num_coprime (@pair nat nat n (modn a n))) = (num_coprime (@pair nat nat n a)).
Axiom thm_INT_CONG_NUM_EXISTS : forall x : int, forall y : int, ((y = (int_of_nat (NUMERAL O))) -> lez (int_of_nat (NUMERAL O)) x) -> exists n : nat, @eq2 int (int_of_nat n) x (int_mod y).
Axiom thm_GCD : forall a : nat, forall b : nat, ((num_divides (num_gcd (@pair nat nat a b)) a) /\ (num_divides (num_gcd (@pair nat nat a b)) b)) /\ (forall e : nat, ((num_divides e a) /\ (num_divides e b)) -> num_divides e (num_gcd (@pair nat nat a b))).
Axiom thm_coprime : forall (a : nat) (b : nat), (num_coprime (@pair nat nat a b)) = (forall d : nat, ((num_divides d a) /\ (num_divides d b)) -> d = (NUMERAL (BIT1 O))).
Axiom thm_prime : forall p : nat, (prime p) = ((~ (p = (NUMERAL (BIT1 O)))) /\ (forall x : nat, (num_divides x p) -> (x = (NUMERAL (BIT1 O))) \/ (x = p))).
Axiom thm_ONE_OR_PRIME : forall p : nat, ((p = (NUMERAL (BIT1 O))) \/ (prime p)) = (forall n : nat, (num_divides n p) -> (n = (NUMERAL (BIT1 O))) \/ (n = p)).
Axiom thm_ONE_OR_PRIME_DIVIDES_OR_COPRIME : forall p : nat, ((p = (NUMERAL (BIT1 O))) \/ (prime p)) = (forall n : nat, (num_divides p n) \/ (num_coprime (@pair nat nat p n))).
Axiom thm_PRIME_COPRIME_EQ_NONDIVISIBLE : forall p : nat, (prime p) = (forall n : nat, (num_coprime (@pair nat nat p n)) = (~ (num_divides p n))).
Axiom thm_ZERO_ONE_OR_PRIME_DIVPROD : forall p : nat, forall a : nat, forall b : nat, ((p = (NUMERAL O)) \/ ((p = (NUMERAL (BIT1 O))) \/ (prime p))) -> (num_divides p (muln a b)) = ((num_divides p a) \/ (num_divides p b)).
Axiom thm_ZERO_ONE_OR_PRIME : forall p : nat, ((p = (NUMERAL O)) \/ ((p = (NUMERAL (BIT1 O))) \/ (prime p))) = (forall a : nat, forall b : nat, (num_divides p (muln a b)) -> (num_divides p a) \/ (num_divides p b)).
Axiom thm_real_zpow : forall z : R, forall i : int, (real_zpow z i) = (@COND R (lez (int_of_nat (NUMERAL O)) i) (expr z (num_of_int i)) (invr (expr z (num_of_int (oppz i))))).
Axiom thm_REAL_POW_ZPOW : forall x : R, forall n : nat, (expr x n) = (real_zpow x (int_of_nat n)).
Axiom thm_REAL_ZPOW_NUM : forall x : R, forall n : nat, (real_zpow x (int_of_nat n)) = (expr x n).
Axiom thm_REAL_ZPOW_0 : forall x : R, (real_zpow x (int_of_nat (NUMERAL O))) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_ZPOW_1 : forall x : R, (real_zpow x (int_of_nat (NUMERAL (BIT1 O)))) = x.
Axiom thm_REAL_ZPOW_2 : forall x : R, (real_zpow x (int_of_nat (NUMERAL (BIT0 (BIT1 O))))) = (mulr x x).
Axiom thm_REAL_ZPOW_ONE : forall n : int, (real_zpow (R_of_nat (NUMERAL (BIT1 O))) n) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_REAL_ZPOW_NEG : forall x : R, forall n : int, (real_zpow x (oppz n)) = (invr (real_zpow x n)).
Axiom thm_REAL_ZPOW_MINUS1 : forall x : R, (real_zpow x (oppz (int_of_nat (NUMERAL (BIT1 O))))) = (invr x).
Axiom thm_REAL_ZPOW_ZERO : forall n : int, (real_zpow (R_of_nat (NUMERAL O)) n) = (@COND R (n = (int_of_nat (NUMERAL O))) (R_of_nat (NUMERAL (BIT1 O))) (R_of_nat (NUMERAL O))).
Axiom thm_REAL_ZPOW_POW : (forall x : R, forall n : nat, (real_zpow x (int_of_nat n)) = (expr x n)) /\ (forall x : R, forall n : nat, (real_zpow x (oppz (int_of_nat n))) = (invr (expr x n))).
Axiom thm_REAL_INV_ZPOW : forall x : R, forall n : int, (invr (real_zpow x n)) = (real_zpow (invr x) n).
Axiom thm_REAL_ZPOW_INV : forall x : R, forall n : int, (real_zpow (invr x) n) = (invr (real_zpow x n)).
Axiom thm_REAL_ZPOW_ZPOW : forall x : R, forall m : int, forall n : int, (real_zpow (real_zpow x m) n) = (real_zpow x (mulz m n)).
Axiom thm_REAL_ZPOW_MUL : forall x : R, forall y : R, forall n : int, (real_zpow (mulr x y) n) = (mulr (real_zpow x n) (real_zpow y n)).
Axiom thm_REAL_ZPOW_DIV : forall x : R, forall y : R, forall n : int, (real_zpow (divr x y) n) = (divr (real_zpow x n) (real_zpow y n)).
Axiom thm_REAL_ZPOW_ADD : forall x : R, forall m : int, forall n : int, (~ (x = (R_of_nat (NUMERAL O)))) -> (real_zpow x (addz m n)) = (mulr (real_zpow x m) (real_zpow x n)).
Axiom thm_REAL_ZPOW_SUB : forall x : R, forall m : int, forall n : int, (~ (x = (R_of_nat (NUMERAL O)))) -> (real_zpow x (subz m n)) = (divr (real_zpow x m) (real_zpow x n)).
Axiom thm_REAL_ZPOW_LE : forall x : R, forall n : int, (ler (R_of_nat (NUMERAL O)) x) -> ler (R_of_nat (NUMERAL O)) (real_zpow x n).
Axiom thm_REAL_ZPOW_LT : forall x : R, forall n : int, (ltr (R_of_nat (NUMERAL O)) x) -> ltr (R_of_nat (NUMERAL O)) (real_zpow x n).
Axiom thm_REAL_ZPOW_EQ_0 : forall x : R, forall n : int, ((real_zpow x n) = (R_of_nat (NUMERAL O))) = ((x = (R_of_nat (NUMERAL O))) /\ (~ (n = (int_of_nat (NUMERAL O))))).
Axiom thm_REAL_ABS_ZPOW : forall x : R, forall n : int, (normr (real_zpow x n)) = (real_zpow (normr x) n).
Axiom thm_REAL_SGN_ZPOW : forall x : R, forall n : int, (sgr (real_zpow x n)) = (real_zpow (sgr x) n).
Axiom thm_IN : forall {A : Type'}, forall P : A -> Prop, forall x : A, (@IN A x P) = (P x).
Axiom thm_EXTENSION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (s = t) = (forall x : A, (@IN A x s) = (@IN A x t)).
Axiom thm_GSPEC : forall {A : Type'}, forall p : A -> Prop, (@GSPEC A p) = p.
Axiom thm_SETSPEC : forall {A : Type'}, forall P : Prop, forall v : A, forall t : A, (@SETSPEC A v P t) = (P /\ (v = t)).
Axiom thm_IN_ELIM_THM : forall {A : Type'}, (forall P : (Prop -> A -> Prop) -> Prop, forall x : A, (@IN A x (@GSPEC A (fun v : A => P (@SETSPEC A v)))) = (P (fun p : Prop => fun t : A => p /\ (x = t)))) /\ ((forall p : A -> Prop, forall x : A, (@IN A x (@GSPEC A (fun v : A => exists y : A, @SETSPEC A v (p y) y))) = (p x)) /\ ((forall P : (Prop -> A -> Prop) -> Prop, forall x : A, (@GSPEC A (fun v : A => P (@SETSPEC A v)) x) = (P (fun p : Prop => fun t : A => p /\ (x = t)))) /\ ((forall p : A -> Prop, forall x : A, (@GSPEC A (fun v : A => exists y : A, @SETSPEC A v (p y) y) x) = (p x)) /\ (forall p : A -> Prop, forall x : A, (@IN A x (fun y : A => p y)) = (p x))))).
Axiom thm_EMPTY : forall {A : Type'}, (@set0 A) = (fun x : A => False).
Axiom thm_INSERT_DEF : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@INSERT A x s) = (fun y : A => (@IN A y s) \/ (y = x)).
Axiom thm_UNIV : forall {A : Type'}, (@setT A) = (fun x : A => True).
Axiom thm_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setU A s t) = (@GSPEC A (fun GEN_PVAR_0 : A => exists x : A, @SETSPEC A GEN_PVAR_0 ((@IN A x s) \/ (@IN A x t)) x)).
Axiom thm_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@UNIONS A s) = (@GSPEC A (fun GEN_PVAR_1 : A => exists x : A, @SETSPEC A GEN_PVAR_1 (exists u : A -> Prop, (@IN (A -> Prop) u s) /\ (@IN A x u)) x)).
Axiom thm_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setI A s t) = (@GSPEC A (fun GEN_PVAR_2 : A => exists x : A, @SETSPEC A GEN_PVAR_2 ((@IN A x s) /\ (@IN A x t)) x)).
Axiom thm_INTERS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@INTERS A s) = (@GSPEC A (fun GEN_PVAR_3 : A => exists x : A, @SETSPEC A GEN_PVAR_3 (forall u : A -> Prop, (@IN (A -> Prop) u s) -> @IN A x u) x)).
Axiom thm_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setD A s t) = (@GSPEC A (fun GEN_PVAR_4 : A => exists x : A, @SETSPEC A GEN_PVAR_4 ((@IN A x s) /\ (~ (@IN A x t))) x)).
Axiom thm_INSERT : forall {A : Type'} (s : A -> Prop) (x : A), (@INSERT A x s) = (@GSPEC A (fun GEN_PVAR_5 : A => exists y : A, @SETSPEC A GEN_PVAR_5 ((@IN A y s) \/ (y = x)) y)).
Axiom thm_DELETE : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@DELETE A s x) = (@GSPEC A (fun GEN_PVAR_6 : A => exists y : A, @SETSPEC A GEN_PVAR_6 ((@IN A y s) /\ (~ (y = x))) y)).
Axiom thm_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) = (forall x : A, (@IN A x s) -> @IN A x t).
Axiom thm_PSUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@proper A s t) = ((@subset A s t) /\ (~ (s = t))).
Axiom thm_DISJOINT : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A s t) = ((@setI A s t) = (@set0 A)).
Axiom thm_SING : forall {A : Type'}, forall s : A -> Prop, (@is_set1 A s) = (exists x : A, s = (@INSERT A x (@set0 A))).
Axiom thm_FINITE_RULES : forall {A : Type'}, (@finite_set A (@set0 A)) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> @finite_set A (@INSERT A x s)).
Axiom thm_FINITE_CASES : forall {A : Type'}, forall a : A -> Prop, (@finite_set A a) = ((a = (@set0 A)) \/ (exists x : A, exists s : A -> Prop, (a = (@INSERT A x s)) /\ (@finite_set A s))).
Axiom thm_FINITE_INDUCT : forall {A : Type'}, forall FINITE' : (A -> Prop) -> Prop, ((FINITE' (@set0 A)) /\ (forall x : A, forall s : A -> Prop, (FINITE' s) -> FINITE' (@INSERT A x s))) -> forall a : A -> Prop, (@finite_set A a) -> FINITE' a.
Axiom thm_INFINITE : forall {A : Type'}, forall s : A -> Prop, (@INFINITE A s) = (~ (@finite_set A s)).
Axiom thm_IMAGE : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@IMAGE A B f s) = (@GSPEC B (fun GEN_PVAR_7 : B => exists y : B, @SETSPEC B GEN_PVAR_7 (exists x : A, (@IN A x s) /\ (y = (f x))) y)).
Axiom thm_INJ : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, forall f : A -> B, (@INJ A B f s t) = ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_SURJ : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, forall f : A -> B, (@SURJ A B f s t) = ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : B, (@IN B x t) -> exists y : A, (@IN A y s) /\ ((f y) = x))).
Axiom thm_BIJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, (@BIJ A B f s t) = ((@INJ A B f s t) /\ (@SURJ A B f s t)).
Axiom thm_CHOICE : forall {A : Type'}, forall s : A -> Prop, (@CHOICE A s) = (@ε A (fun x : A => @IN A x s)).
Axiom thm_REST : forall {A : Type'}, forall s : A -> Prop, (@REST A s) = (@DELETE A s (@CHOICE A s)).
Axiom thm_NOT_IN_EMPTY : forall {A : Type'}, forall x : A, ~ (@IN A x (@set0 A)).
Axiom thm_IN_UNIV : forall {A : Type'}, forall x : A, @IN A x (@setT A).
Axiom thm_IN_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@IN A x (@setU A s t)) = ((@IN A x s) \/ (@IN A x t)).
Axiom thm_IN_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall x : A, (@IN A x (@UNIONS A s)) = (exists t : A -> Prop, (@IN (A -> Prop) t s) /\ (@IN A x t)).
Axiom thm_IN_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@IN A x (@setI A s t)) = ((@IN A x s) /\ (@IN A x t)).
Axiom thm_IN_INTERS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall x : A, (@IN A x (@INTERS A s)) = (forall t : A -> Prop, (@IN (A -> Prop) t s) -> @IN A x t).
Axiom thm_IN_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@IN A x (@setD A s t)) = ((@IN A x s) /\ (~ (@IN A x t))).
Axiom thm_IN_INSERT : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@IN A x (@INSERT A y s)) = ((x = y) \/ (@IN A x s)).
Axiom thm_IN_DELETE : forall {A : Type'}, forall s : A -> Prop, forall x : A, forall y : A, (@IN A x (@DELETE A s y)) = ((@IN A x s) /\ (~ (x = y))).
Axiom thm_IN_SING : forall {A : Type'}, forall x : A, forall y : A, (@IN A x (@INSERT A y (@set0 A))) = (x = y).
Axiom thm_IN_IMAGE : forall {A B : Type'}, forall y : B, forall s : A -> Prop, forall f : A -> B, (@IN B y (@IMAGE A B f s)) = (exists x : A, (y = (f x)) /\ (@IN A x s)).
Axiom thm_IN_REST : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@IN A x (@REST A s)) = ((@IN A x s) /\ (~ (x = (@CHOICE A s)))).
Axiom thm_FORALL_IN_INSERT : forall {A : Type'}, forall P : A -> Prop, forall a : A, forall s : A -> Prop, (forall x : A, (@IN A x (@INSERT A a s)) -> P x) = ((P a) /\ (forall x : A, (@IN A x s) -> P x)).
Axiom thm_EXISTS_IN_INSERT : forall {A : Type'}, forall P : A -> Prop, forall a : A, forall s : A -> Prop, (exists x : A, (@IN A x (@INSERT A a s)) /\ (P x)) = ((P a) \/ (exists x : A, (@IN A x s) /\ (P x))).
Axiom thm_FORALL_IN_UNION : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (forall x : A, (@IN A x (@setU A s t)) -> P x) = ((forall x : A, (@IN A x s) -> P x) /\ (forall x : A, (@IN A x t) -> P x)).
Axiom thm_EXISTS_IN_UNION : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (exists x : A, (@IN A x (@setU A s t)) /\ (P x)) = ((exists x : A, (@IN A x s) /\ (P x)) \/ (exists x : A, (@IN A x t) /\ (P x))).
Axiom thm_FORALL_IN_IMAGE : forall {A B : Type'} (P : B -> Prop), forall f : A -> B, forall s : A -> Prop, (forall y : B, (@IN B y (@IMAGE A B f s)) -> P y) = (forall x : A, (@IN A x s) -> P (f x)).
Axiom thm_EXISTS_IN_IMAGE : forall {A B : Type'} (P : B -> Prop), forall f : A -> B, forall s : A -> Prop, (exists y : B, (@IN B y (@IMAGE A B f s)) /\ (P y)) = (exists x : A, (@IN A x s) /\ (P (f x))).
Axiom thm_FORALL_IN_GSPEC : forall {A B C D E : Type'}, (forall P : A -> Prop, forall Q : B -> Prop, forall f : A -> B, (forall z : B, (@IN B z (@GSPEC B (fun GEN_PVAR_8 : B => exists x : A, @SETSPEC B GEN_PVAR_8 (P x) (f x)))) -> Q z) = (forall x : A, (P x) -> Q (f x))) /\ ((forall P : A -> B -> Prop, forall Q : C -> Prop, forall f : A -> B -> C, (forall z : C, (@IN C z (@GSPEC C (fun GEN_PVAR_9 : C => exists x : A, exists y : B, @SETSPEC C GEN_PVAR_9 (P x y) (f x y)))) -> Q z) = (forall x : A, forall y : B, (P x y) -> Q (f x y))) /\ ((forall P : A -> B -> C -> Prop, forall Q : D -> Prop, forall f : A -> B -> C -> D, (forall z : D, (@IN D z (@GSPEC D (fun GEN_PVAR_10 : D => exists w : A, exists x : B, exists y : C, @SETSPEC D GEN_PVAR_10 (P w x y) (f w x y)))) -> Q z) = (forall w : A, forall x : B, forall y : C, (P w x y) -> Q (f w x y))) /\ (forall P : A -> B -> C -> D -> Prop, forall Q : E -> Prop, forall f : A -> B -> C -> D -> E, (forall z : E, (@IN E z (@GSPEC E (fun GEN_PVAR_11 : E => exists v : A, exists w : B, exists x : C, exists y : D, @SETSPEC E GEN_PVAR_11 (P v w x y) (f v w x y)))) -> Q z) = (forall v : A, forall w : B, forall x : C, forall y : D, (P v w x y) -> Q (f v w x y))))).
Axiom thm_EXISTS_IN_GSPEC : forall {A B C D E : Type'}, (forall P : A -> Prop, forall Q : B -> Prop, forall f : A -> B, (exists z : B, (@IN B z (@GSPEC B (fun GEN_PVAR_12 : B => exists x : A, @SETSPEC B GEN_PVAR_12 (P x) (f x)))) /\ (Q z)) = (exists x : A, (P x) /\ (Q (f x)))) /\ ((forall P : A -> B -> Prop, forall Q : C -> Prop, forall f : A -> B -> C, (exists z : C, (@IN C z (@GSPEC C (fun GEN_PVAR_13 : C => exists x : A, exists y : B, @SETSPEC C GEN_PVAR_13 (P x y) (f x y)))) /\ (Q z)) = (exists x : A, exists y : B, (P x y) /\ (Q (f x y)))) /\ ((forall P : A -> B -> C -> Prop, forall Q : D -> Prop, forall f : A -> B -> C -> D, (exists z : D, (@IN D z (@GSPEC D (fun GEN_PVAR_14 : D => exists w : A, exists x : B, exists y : C, @SETSPEC D GEN_PVAR_14 (P w x y) (f w x y)))) /\ (Q z)) = (exists w : A, exists x : B, exists y : C, (P w x y) /\ (Q (f w x y)))) /\ (forall P : A -> B -> C -> D -> Prop, forall Q : E -> Prop, forall f : A -> B -> C -> D -> E, (exists z : E, (@IN E z (@GSPEC E (fun GEN_PVAR_15 : E => exists v : A, exists w : B, exists x : C, exists y : D, @SETSPEC E GEN_PVAR_15 (P v w x y) (f v w x y)))) /\ (Q z)) = (exists v : A, exists w : B, exists x : C, exists y : D, (P v w x y) /\ (Q (f v w x y)))))).
Axiom thm_UNIONS_IMAGE : forall {A B : Type'}, forall f : A -> B -> Prop, forall s : A -> Prop, (@UNIONS B (@IMAGE A (B -> Prop) f s)) = (@GSPEC B (fun GEN_PVAR_16 : B => exists y : B, @SETSPEC B GEN_PVAR_16 (exists x : A, (@IN A x s) /\ (@IN B y (f x))) y)).
Axiom thm_INTERS_IMAGE : forall {A B : Type'}, forall f : A -> B -> Prop, forall s : A -> Prop, (@INTERS B (@IMAGE A (B -> Prop) f s)) = (@GSPEC B (fun GEN_PVAR_17 : B => exists y : B, @SETSPEC B GEN_PVAR_17 (forall x : A, (@IN A x s) -> @IN B y (f x)) y)).
Axiom thm_UNIONS_GSPEC : forall {A B C D : Type'}, (forall P : A -> Prop, forall f : A -> B -> Prop, (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_18 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_18 (P x) (f x)))) = (@GSPEC B (fun GEN_PVAR_19 : B => exists a : B, @SETSPEC B GEN_PVAR_19 (exists x : A, (P x) /\ (@IN B a (f x))) a))) /\ ((forall P : A -> B -> Prop, forall f : A -> B -> C -> Prop, (@UNIONS C (@GSPEC (C -> Prop) (fun GEN_PVAR_20 : C -> Prop => exists x : A, exists y : B, @SETSPEC (C -> Prop) GEN_PVAR_20 (P x y) (f x y)))) = (@GSPEC C (fun GEN_PVAR_21 : C => exists a : C, @SETSPEC C GEN_PVAR_21 (exists x : A, exists y : B, (P x y) /\ (@IN C a (f x y))) a))) /\ (forall P : A -> B -> C -> Prop, forall f : A -> B -> C -> D -> Prop, (@UNIONS D (@GSPEC (D -> Prop) (fun GEN_PVAR_22 : D -> Prop => exists x : A, exists y : B, exists z : C, @SETSPEC (D -> Prop) GEN_PVAR_22 (P x y z) (f x y z)))) = (@GSPEC D (fun GEN_PVAR_23 : D => exists a : D, @SETSPEC D GEN_PVAR_23 (exists x : A, exists y : B, exists z : C, (P x y z) /\ (@IN D a (f x y z))) a)))).
Axiom thm_INTERS_GSPEC : forall {A B C D : Type'}, (forall P : A -> Prop, forall f : A -> B -> Prop, (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_24 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_24 (P x) (f x)))) = (@GSPEC B (fun GEN_PVAR_25 : B => exists a : B, @SETSPEC B GEN_PVAR_25 (forall x : A, (P x) -> @IN B a (f x)) a))) /\ ((forall P : A -> B -> Prop, forall f : A -> B -> C -> Prop, (@INTERS C (@GSPEC (C -> Prop) (fun GEN_PVAR_26 : C -> Prop => exists x : A, exists y : B, @SETSPEC (C -> Prop) GEN_PVAR_26 (P x y) (f x y)))) = (@GSPEC C (fun GEN_PVAR_27 : C => exists a : C, @SETSPEC C GEN_PVAR_27 (forall x : A, forall y : B, (P x y) -> @IN C a (f x y)) a))) /\ (forall P : A -> B -> C -> Prop, forall f : A -> B -> C -> D -> Prop, (@INTERS D (@GSPEC (D -> Prop) (fun GEN_PVAR_28 : D -> Prop => exists x : A, exists y : B, exists z : C, @SETSPEC (D -> Prop) GEN_PVAR_28 (P x y z) (f x y z)))) = (@GSPEC D (fun GEN_PVAR_29 : D => exists a : D, @SETSPEC D GEN_PVAR_29 (forall x : A, forall y : B, forall z : C, (P x y z) -> @IN D a (f x y z)) a)))).
Axiom thm_CHOICE_DEF : forall {A : Type'}, forall s : A -> Prop, (~ (s = (@set0 A))) -> @IN A (@CHOICE A s) s.
Axiom thm_NOT_EQUAL_SETS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (~ (s = t)) = (exists x : A, (@IN A x t) = (~ (@IN A x s))).
Axiom thm_INSERT_RESTRICT : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall a : A, (@GSPEC A (fun GEN_PVAR_30 : A => exists x : A, @SETSPEC A GEN_PVAR_30 ((@IN A x (@INSERT A a s)) /\ (P x)) x)) = (@COND (A -> Prop) (P a) (@INSERT A a (@GSPEC A (fun GEN_PVAR_31 : A => exists x : A, @SETSPEC A GEN_PVAR_31 ((@IN A x s) /\ (P x)) x))) (@GSPEC A (fun GEN_PVAR_32 : A => exists x : A, @SETSPEC A GEN_PVAR_32 ((@IN A x s) /\ (P x)) x))).
Axiom thm_UNIV_1 : (@setT unit) = (@INSERT unit tt (@set0 unit)).
Axiom thm_MEMBER_NOT_EMPTY : forall {A : Type'}, forall s : A -> Prop, (exists x : A, @IN A x s) = (~ (s = (@set0 A))).
Axiom thm_UNIV_NOT_EMPTY : forall {A : Type'}, ~ ((@setT A) = (@set0 A)).
Axiom thm_EMPTY_NOT_UNIV : forall {A : Type'}, ~ ((@set0 A) = (@setT A)).
Axiom thm_EQ_UNIV : forall {A : Type'} (s : A -> Prop), (forall x : A, @IN A x s) = (s = (@setT A)).
Axiom thm_SUBSET_TRANS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@subset A s t) /\ (@subset A t u)) -> @subset A s u.
Axiom thm_SUBSET_REFL : forall {A : Type'}, forall s : A -> Prop, @subset A s s.
Axiom thm_SUBSET_ANTISYM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@subset A s t) /\ (@subset A t s)) -> s = t.
Axiom thm_SUBSET_ANTISYM_EQ : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@subset A s t) /\ (@subset A t s)) = (s = t).
Axiom thm_EMPTY_SUBSET : forall {A : Type'}, forall s : A -> Prop, @subset A (@set0 A) s.
Axiom thm_SUBSET_EMPTY : forall {A : Type'}, forall s : A -> Prop, (@subset A s (@set0 A)) = (s = (@set0 A)).
Axiom thm_SUBSET_UNIV : forall {A : Type'}, forall s : A -> Prop, @subset A s (@setT A).
Axiom thm_UNIV_SUBSET : forall {A : Type'}, forall s : A -> Prop, (@subset A (@setT A) s) = (s = (@setT A)).
Axiom thm_SING_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@subset A (@INSERT A x (@set0 A)) s) = (@IN A x s).
Axiom thm_SUBSET_RESTRICT : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, @subset A (@GSPEC A (fun GEN_PVAR_33 : A => exists x : A, @SETSPEC A GEN_PVAR_33 ((@IN A x s) /\ (P x)) x)) s.
Axiom thm_PSUBSET_TRANS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@proper A s t) /\ (@proper A t u)) -> @proper A s u.
Axiom thm_PSUBSET_SUBSET_TRANS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@proper A s t) /\ (@subset A t u)) -> @proper A s u.
Axiom thm_SUBSET_PSUBSET_TRANS : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@subset A s t) /\ (@proper A t u)) -> @proper A s u.
Axiom thm_PSUBSET_IRREFL : forall {A : Type'}, forall s : A -> Prop, ~ (@proper A s s).
Axiom thm_NOT_PSUBSET_EMPTY : forall {A : Type'}, forall s : A -> Prop, ~ (@proper A s (@set0 A)).
Axiom thm_NOT_UNIV_PSUBSET : forall {A : Type'}, forall s : A -> Prop, ~ (@proper A (@setT A) s).
Axiom thm_PSUBSET_UNIV : forall {A : Type'}, forall s : A -> Prop, (@proper A s (@setT A)) = (exists x : A, ~ (@IN A x s)).
Axiom thm_PSUBSET_ALT : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@proper A s t) = ((@subset A s t) /\ (exists a : A, (@IN A a t) /\ (~ (@IN A a s)))).
Axiom thm_UNION_ASSOC : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@setU A (@setU A s t) u) = (@setU A s (@setU A t u)).
Axiom thm_UNION_IDEMPOT : forall {A : Type'}, forall s : A -> Prop, (@setU A s s) = s.
Axiom thm_UNION_COMM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setU A s t) = (@setU A t s).
Axiom thm_SUBSET_UNION : forall {A : Type'}, (forall s : A -> Prop, forall t : A -> Prop, @subset A s (@setU A s t)) /\ (forall s : A -> Prop, forall t : A -> Prop, @subset A s (@setU A t s)).
Axiom thm_SUBSET_UNION_ABSORPTION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) = ((@setU A s t) = t).
Axiom thm_UNION_EMPTY : forall {A : Type'}, (forall s : A -> Prop, (@setU A (@set0 A) s) = s) /\ (forall s : A -> Prop, (@setU A s (@set0 A)) = s).
Axiom thm_UNION_UNIV : forall {A : Type'}, (forall s : A -> Prop, (@setU A (@setT A) s) = (@setT A)) /\ (forall s : A -> Prop, (@setU A s (@setT A)) = (@setT A)).
Axiom thm_EMPTY_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@setU A s t) = (@set0 A)) = ((s = (@set0 A)) /\ (t = (@set0 A))).
Axiom thm_UNION_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@subset A (@setU A s t) u) = ((@subset A s u) /\ (@subset A t u)).
Axiom thm_UNION_RESTRICT : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (@GSPEC A (fun GEN_PVAR_34 : A => exists x : A, @SETSPEC A GEN_PVAR_34 ((@IN A x (@setU A s t)) /\ (P x)) x)) = (@setU A (@GSPEC A (fun GEN_PVAR_35 : A => exists x : A, @SETSPEC A GEN_PVAR_35 ((@IN A x s) /\ (P x)) x)) (@GSPEC A (fun GEN_PVAR_36 : A => exists x : A, @SETSPEC A GEN_PVAR_36 ((@IN A x t) /\ (P x)) x))).
Axiom thm_FORALL_SUBSET_UNION : forall {A : Type'} (P : (A -> Prop) -> Prop), forall t : A -> Prop, forall u : A -> Prop, (forall s : A -> Prop, (@subset A s (@setU A t u)) -> P s) = (forall t' : A -> Prop, forall u' : A -> Prop, ((@subset A t' t) /\ (@subset A u' u)) -> P (@setU A t' u')).
Axiom thm_EXISTS_SUBSET_UNION : forall {A : Type'} (P : (A -> Prop) -> Prop), forall t : A -> Prop, forall u : A -> Prop, (exists s : A -> Prop, (@subset A s (@setU A t u)) /\ (P s)) = (exists t' : A -> Prop, exists u' : A -> Prop, (@subset A t' t) /\ ((@subset A u' u) /\ (P (@setU A t' u')))).
Axiom thm_FORALL_SUBSET_INSERT : forall {A : Type'} (P : (A -> Prop) -> Prop), forall a : A, forall t : A -> Prop, (forall s : A -> Prop, (@subset A s (@INSERT A a t)) -> P s) = (forall s : A -> Prop, (@subset A s t) -> (P s) /\ (P (@INSERT A a s))).
Axiom thm_EXISTS_SUBSET_INSERT : forall {A : Type'} (P : (A -> Prop) -> Prop), forall a : A, forall t : A -> Prop, (exists s : A -> Prop, (@subset A s (@INSERT A a t)) /\ (P s)) = (exists s : A -> Prop, (@subset A s t) /\ ((P s) \/ (P (@INSERT A a s)))).
Axiom thm_INTER_ASSOC : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@setI A (@setI A s t) u) = (@setI A s (@setI A t u)).
Axiom thm_INTER_IDEMPOT : forall {A : Type'}, forall s : A -> Prop, (@setI A s s) = s.
Axiom thm_INTER_COMM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setI A s t) = (@setI A t s).
Axiom thm_INTER_SUBSET : forall {A : Type'}, (forall s : A -> Prop, forall t : A -> Prop, @subset A (@setI A s t) s) /\ (forall s : A -> Prop, forall t : A -> Prop, @subset A (@setI A t s) s).
Axiom thm_SUBSET_INTER_ABSORPTION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) = ((@setI A s t) = s).
Axiom thm_INTER_EMPTY : forall {A : Type'}, (forall s : A -> Prop, (@setI A (@set0 A) s) = (@set0 A)) /\ (forall s : A -> Prop, (@setI A s (@set0 A)) = (@set0 A)).
Axiom thm_INTER_UNIV : forall {A : Type'}, (forall s : A -> Prop, (@setI A (@setT A) s) = s) /\ (forall s : A -> Prop, (@setI A s (@setT A)) = s).
Axiom thm_SUBSET_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@subset A s (@setI A t u)) = ((@subset A s t) /\ (@subset A s u)).
Axiom thm_INTER_RESTRICT : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (@GSPEC A (fun GEN_PVAR_37 : A => exists x : A, @SETSPEC A GEN_PVAR_37 ((@IN A x (@setI A s t)) /\ (P x)) x)) = (@setI A (@GSPEC A (fun GEN_PVAR_38 : A => exists x : A, @SETSPEC A GEN_PVAR_38 ((@IN A x s) /\ (P x)) x)) (@GSPEC A (fun GEN_PVAR_39 : A => exists x : A, @SETSPEC A GEN_PVAR_39 ((@IN A x t) /\ (P x)) x))).
Axiom thm_UNION_OVER_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@setI A s (@setU A t u)) = (@setU A (@setI A s t) (@setI A s u)).
Axiom thm_INTER_OVER_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@setU A s (@setI A t u)) = (@setI A (@setU A s t) (@setU A s u)).
Axiom thm_IN_DISJOINT : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A s t) = (~ (exists x : A, (@IN A x s) /\ (@IN A x t))).
Axiom thm_DISJOINT_SYM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A s t) = (@DISJOINT A t s).
Axiom thm_DISJOINT_EMPTY : forall {A : Type'}, forall s : A -> Prop, (@DISJOINT A (@set0 A) s) /\ (@DISJOINT A s (@set0 A)).
Axiom thm_DISJOINT_EMPTY_REFL : forall {A : Type'}, forall s : A -> Prop, (s = (@set0 A)) = (@DISJOINT A s s).
Axiom thm_DISJOINT_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@DISJOINT A (@setU A s t) u) = ((@DISJOINT A s u) /\ (@DISJOINT A t u)).
Axiom thm_DISJOINT_SING : forall {A : Type'}, (forall s : A -> Prop, forall a : A, (@DISJOINT A s (@INSERT A a (@set0 A))) = (~ (@IN A a s))) /\ (forall s : A -> Prop, forall a : A, (@DISJOINT A (@INSERT A a (@set0 A)) s) = (~ (@IN A a s))).
Axiom thm_DIFF_EMPTY : forall {A : Type'}, forall s : A -> Prop, (@setD A s (@set0 A)) = s.
Axiom thm_EMPTY_DIFF : forall {A : Type'}, forall s : A -> Prop, (@setD A (@set0 A) s) = (@set0 A).
Axiom thm_DIFF_UNIV : forall {A : Type'}, forall s : A -> Prop, (@setD A s (@setT A)) = (@set0 A).
Axiom thm_DIFF_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@setD A (@setD A s t) t) = (@setD A s t).
Axiom thm_DIFF_EQ_EMPTY : forall {A : Type'}, forall s : A -> Prop, (@setD A s s) = (@set0 A).
Axiom thm_SUBSET_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, @subset A (@setD A s t) s.
Axiom thm_COMPL_COMPL : forall {A : Type'}, forall s : A -> Prop, (@setD A (@setT A) (@setD A (@setT A) s)) = s.
Axiom thm_DIFF_RESTRICT : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (@GSPEC A (fun GEN_PVAR_40 : A => exists x : A, @SETSPEC A GEN_PVAR_40 ((@IN A x (@setD A s t)) /\ (P x)) x)) = (@setD A (@GSPEC A (fun GEN_PVAR_41 : A => exists x : A, @SETSPEC A GEN_PVAR_41 ((@IN A x s) /\ (P x)) x)) (@GSPEC A (fun GEN_PVAR_42 : A => exists x : A, @SETSPEC A GEN_PVAR_42 ((@IN A x t) /\ (P x)) x))).
Axiom thm_COMPONENT : forall {A : Type'}, forall x : A, forall s : A -> Prop, @IN A x (@INSERT A x s).
Axiom thm_DECOMPOSITION : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@IN A x s) = (exists t : A -> Prop, (s = (@INSERT A x t)) /\ (~ (@IN A x t))).
Axiom thm_SET_CASES : forall {A : Type'}, forall s : A -> Prop, (s = (@set0 A)) \/ (exists x : A, exists t : A -> Prop, (s = (@INSERT A x t)) /\ (~ (@IN A x t))).
Axiom thm_ABSORPTION : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@IN A x s) = ((@INSERT A x s) = s).
Axiom thm_INSERT_INSERT : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@INSERT A x (@INSERT A x s)) = (@INSERT A x s).
Axiom thm_INSERT_COMM : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@INSERT A x (@INSERT A y s)) = (@INSERT A y (@INSERT A x s)).
Axiom thm_INSERT_UNIV : forall {A : Type'}, forall x : A, (@INSERT A x (@setT A)) = (@setT A).
Axiom thm_NOT_INSERT_EMPTY : forall {A : Type'}, forall x : A, forall s : A -> Prop, ~ ((@INSERT A x s) = (@set0 A)).
Axiom thm_NOT_EMPTY_INSERT : forall {A : Type'}, forall x : A, forall s : A -> Prop, ~ ((@set0 A) = (@INSERT A x s)).
Axiom thm_INSERT_UNION : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@setU A (@INSERT A x s) t) = (@COND (A -> Prop) (@IN A x t) (@setU A s t) (@INSERT A x (@setU A s t))).
Axiom thm_INSERT_UNION_EQ : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@setU A (@INSERT A x s) t) = (@INSERT A x (@setU A s t)).
Axiom thm_INSERT_INTER : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@setI A (@INSERT A x s) t) = (@COND (A -> Prop) (@IN A x t) (@INSERT A x (@setI A s t)) (@setI A s t)).
Axiom thm_DISJOINT_INSERT : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@DISJOINT A (@INSERT A x s) t) = ((@DISJOINT A s t) /\ (~ (@IN A x t))).
Axiom thm_INSERT_SUBSET : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@subset A (@INSERT A x s) t) = ((@IN A x t) /\ (@subset A s t)).
Axiom thm_SUBSET_INSERT : forall {A : Type'}, forall x : A, forall s : A -> Prop, (~ (@IN A x s)) -> forall t : A -> Prop, (@subset A s (@INSERT A x t)) = (@subset A s t).
Axiom thm_INSERT_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@setD A (@INSERT A x s) t) = (@COND (A -> Prop) (@IN A x t) (@setD A s t) (@INSERT A x (@setD A s t))).
Axiom thm_INSERT_AC : forall {A : Type'} (y : A) (x : A) (s : A -> Prop), ((@INSERT A x (@INSERT A y s)) = (@INSERT A y (@INSERT A x s))) /\ ((@INSERT A x (@INSERT A x s)) = (@INSERT A x s)).
Axiom thm_INTER_ACI : forall {A : Type'} (r : A -> Prop) (p : A -> Prop) (q : A -> Prop), ((@setI A p q) = (@setI A q p)) /\ (((@setI A (@setI A p q) r) = (@setI A p (@setI A q r))) /\ (((@setI A p (@setI A q r)) = (@setI A q (@setI A p r))) /\ (((@setI A p p) = p) /\ ((@setI A p (@setI A p q)) = (@setI A p q))))).
Axiom thm_UNION_ACI : forall {A : Type'} (r : A -> Prop) (p : A -> Prop) (q : A -> Prop), ((@setU A p q) = (@setU A q p)) /\ (((@setU A (@setU A p q) r) = (@setU A p (@setU A q r))) /\ (((@setU A p (@setU A q r)) = (@setU A q (@setU A p r))) /\ (((@setU A p p) = p) /\ ((@setU A p (@setU A p q)) = (@setU A p q))))).
Axiom thm_DELETE_NON_ELEMENT : forall {A : Type'}, forall x : A, forall s : A -> Prop, (~ (@IN A x s)) = ((@DELETE A s x) = s).
Axiom thm_IN_DELETE_EQ : forall {A : Type'}, forall s : A -> Prop, forall x : A, forall x' : A, ((@IN A x s) = (@IN A x' s)) = ((@IN A x (@DELETE A s x')) = (@IN A x' (@DELETE A s x))).
Axiom thm_EMPTY_DELETE : forall {A : Type'}, forall x : A, (@DELETE A (@set0 A) x) = (@set0 A).
Axiom thm_DELETE_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@DELETE A (@DELETE A s x) x) = (@DELETE A s x).
Axiom thm_DELETE_COMM : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@DELETE A (@DELETE A s x) y) = (@DELETE A (@DELETE A s y) x).
Axiom thm_DELETE_SUBSET : forall {A : Type'}, forall x : A, forall s : A -> Prop, @subset A (@DELETE A s x) s.
Axiom thm_SUBSET_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@subset A s (@DELETE A t x)) = ((~ (@IN A x s)) /\ (@subset A s t)).
Axiom thm_SUBSET_INSERT_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@subset A s (@INSERT A x t)) = (@subset A (@DELETE A s x) t).
Axiom thm_DIFF_INSERT : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@setD A s (@INSERT A x t)) = (@setD A (@DELETE A s x) t).
Axiom thm_PSUBSET_INSERT_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@proper A s t) = (exists x : A, (~ (@IN A x s)) /\ (@subset A (@INSERT A x s) t)).
Axiom thm_DELETE_INSERT : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@DELETE A (@INSERT A x s) y) = (@COND (A -> Prop) (x = y) (@DELETE A s y) (@INSERT A x (@DELETE A s y))).
Axiom thm_INSERT_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@IN A x s) -> (@INSERT A x (@DELETE A s x)) = s.
Axiom thm_DELETE_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@setI A (@DELETE A s x) t) = (@DELETE A (@setI A s t) x).
Axiom thm_DISJOINT_DELETE_SYM : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@DISJOINT A (@DELETE A s x) t) = (@DISJOINT A (@DELETE A t x) s).
Axiom thm_UNIONS_0 : forall {A : Type'}, (@UNIONS A (@set0 (A -> Prop))) = (@set0 A).
Axiom thm_UNIONS_1 : forall {A : Type'}, forall s : A -> Prop, (@UNIONS A (@INSERT (A -> Prop) s (@set0 (A -> Prop)))) = s.
Axiom thm_UNIONS_2 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@UNIONS A (@INSERT (A -> Prop) s (@INSERT (A -> Prop) t (@set0 (A -> Prop))))) = (@setU A s t).
Axiom thm_UNIONS_INSERT : forall {A : Type'}, forall s : A -> Prop, forall u : (A -> Prop) -> Prop, (@UNIONS A (@INSERT (A -> Prop) s u)) = (@setU A s (@UNIONS A u)).
Axiom thm_FORALL_IN_UNIONS : forall {A : Type'}, forall P : A -> Prop, forall s : (A -> Prop) -> Prop, (forall x : A, (@IN A x (@UNIONS A s)) -> P x) = (forall t : A -> Prop, forall x : A, ((@IN (A -> Prop) t s) /\ (@IN A x t)) -> P x).
Axiom thm_EXISTS_IN_UNIONS : forall {A : Type'}, forall P : A -> Prop, forall s : (A -> Prop) -> Prop, (exists x : A, (@IN A x (@UNIONS A s)) /\ (P x)) = (exists t : A -> Prop, exists x : A, (@IN (A -> Prop) t s) /\ ((@IN A x t) /\ (P x))).
Axiom thm_EMPTY_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, ((@UNIONS A s) = (@set0 A)) = (forall t : A -> Prop, (@IN (A -> Prop) t s) -> t = (@set0 A)).
Axiom thm_INTER_UNIONS : forall {A : Type'}, (forall s : (A -> Prop) -> Prop, forall t : A -> Prop, (@setI A (@UNIONS A s) t) = (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_43 : A -> Prop => exists x : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_43 (@IN (A -> Prop) x s) (@setI A x t))))) /\ (forall s : (A -> Prop) -> Prop, forall t : A -> Prop, (@setI A t (@UNIONS A s)) = (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_44 : A -> Prop => exists x : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_44 (@IN (A -> Prop) x s) (@setI A t x))))).
Axiom thm_UNIONS_SUBSET : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall t : A -> Prop, (@subset A (@UNIONS A f) t) = (forall s : A -> Prop, (@IN (A -> Prop) s f) -> @subset A s t).
Axiom thm_SUBSET_UNIONS : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall g : (A -> Prop) -> Prop, (@subset (A -> Prop) f g) -> @subset A (@UNIONS A f) (@UNIONS A g).
Axiom thm_UNIONS_UNION : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (@UNIONS A (@setU (A -> Prop) s t)) = (@setU A (@UNIONS A s) (@UNIONS A t)).
Axiom thm_INTERS_UNION : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (@INTERS A (@setU (A -> Prop) s t)) = (@setI A (@INTERS A s) (@INTERS A t)).
Axiom thm_UNIONS_MONO : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (forall x : A -> Prop, (@IN (A -> Prop) x s) -> exists y : A -> Prop, (@IN (A -> Prop) y t) /\ (@subset A x y)) -> @subset A (@UNIONS A s) (@UNIONS A t).
Axiom thm_UNIONS_MONO_IMAGE : forall {A B : Type'}, forall f : A -> B -> Prop, forall g : A -> B -> Prop, forall s : A -> Prop, (forall x : A, (@IN A x s) -> @subset B (f x) (g x)) -> @subset B (@UNIONS B (@IMAGE A (B -> Prop) f s)) (@UNIONS B (@IMAGE A (B -> Prop) g s)).
Axiom thm_UNIONS_UNIV : forall {A : Type'}, (@UNIONS A (@setT (A -> Prop))) = (@setT A).
Axiom thm_UNIONS_INSERT_EMPTY : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@UNIONS A (@INSERT (A -> Prop) (@set0 A) s)) = (@UNIONS A s).
Axiom thm_UNIONS_DELETE_EMPTY : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@UNIONS A (@DELETE (A -> Prop) s (@set0 A))) = (@UNIONS A s).
Axiom thm_INTERS_0 : forall {A : Type'}, (@INTERS A (@set0 (A -> Prop))) = (@setT A).
Axiom thm_INTERS_1 : forall {A : Type'}, forall s : A -> Prop, (@INTERS A (@INSERT (A -> Prop) s (@set0 (A -> Prop)))) = s.
Axiom thm_INTERS_2 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@INTERS A (@INSERT (A -> Prop) s (@INSERT (A -> Prop) t (@set0 (A -> Prop))))) = (@setI A s t).
Axiom thm_INTERS_INSERT : forall {A : Type'}, forall s : A -> Prop, forall u : (A -> Prop) -> Prop, (@INTERS A (@INSERT (A -> Prop) s u)) = (@setI A s (@INTERS A u)).
Axiom thm_SUBSET_INTERS : forall {A : Type'}, forall s : A -> Prop, forall f : (A -> Prop) -> Prop, (@subset A s (@INTERS A f)) = (forall t : A -> Prop, (@IN (A -> Prop) t f) -> @subset A s t).
Axiom thm_INTERS_SUBSET : forall {A : Type'}, forall u : (A -> Prop) -> Prop, forall s : A -> Prop, ((~ (u = (@set0 (A -> Prop)))) /\ (forall t : A -> Prop, (@IN (A -> Prop) t u) -> @subset A t s)) -> @subset A (@INTERS A u) s.
Axiom thm_INTERS_SUBSET_STRONG : forall {A : Type'}, forall u : (A -> Prop) -> Prop, forall s : A -> Prop, (exists t : A -> Prop, (@IN (A -> Prop) t u) /\ (@subset A t s)) -> @subset A (@INTERS A u) s.
Axiom thm_INTERS_ANTIMONO : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall g : (A -> Prop) -> Prop, (@subset (A -> Prop) g f) -> @subset A (@INTERS A f) (@INTERS A g).
Axiom thm_INTERS_EQ_UNIV : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@INTERS A f) = (@setT A)) = (forall s : A -> Prop, (@IN (A -> Prop) s f) -> s = (@setT A)).
Axiom thm_INTERS_ANTIMONO_GEN : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (forall y : A -> Prop, (@IN (A -> Prop) y t) -> exists x : A -> Prop, (@IN (A -> Prop) x s) /\ (@subset A x y)) -> @subset A (@INTERS A s) (@INTERS A t).
Axiom thm_IMAGE_CLAUSES : forall {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop), ((@IMAGE A B f (@set0 A)) = (@set0 B)) /\ ((@IMAGE A B f (@INSERT A x s)) = (@INSERT B (f x) (@IMAGE A B f s))).
Axiom thm_IMAGE_UNION : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (@IMAGE A B f (@setU A s t)) = (@setU B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_ID : forall {A : Type'}, forall s : A -> Prop, (@IMAGE A A (fun x : A => x) s) = s.
Axiom thm_IMAGE_I : forall {A : Type'}, forall s : A -> Prop, (@IMAGE A A (@I A) s) = s.
Axiom thm_IMAGE_o : forall {A B C : Type'}, forall f : B -> C, forall g : A -> B, forall s : A -> Prop, (@IMAGE A C (@o A B C f g) s) = (@IMAGE B C f (@IMAGE A B g s)).
Axiom thm_IMAGE_SUBSET : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) -> @subset B (@IMAGE A B f s) (@IMAGE A B f t).
Axiom thm_IMAGE_INTER_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (forall x : A, forall y : A, ((f x) = (f y)) -> x = y) -> (@IMAGE A B f (@setI A s t)) = (@setI B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_DIFF_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y t) /\ ((f x) = (f y)))) -> x = y) -> (@IMAGE A B f (@setD A s t)) = (@setD B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_DIFF_INJ_ALT : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@subset A t s)) -> (@IMAGE A B f (@setD A s t)) = (@setD B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_DELETE_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall a : A, (forall x : A, ((@IN A x s) /\ ((f x) = (f a))) -> x = a) -> (@IMAGE A B f (@DELETE A s a)) = (@DELETE B (@IMAGE A B f s) (f a)).
Axiom thm_IMAGE_DELETE_INJ_ALT : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall a : A, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@IN A a s)) -> (@IMAGE A B f (@DELETE A s a)) = (@DELETE B (@IMAGE A B f s) (f a)).
Axiom thm_IMAGE_EQ_EMPTY : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((@IMAGE A B f s) = (@set0 B)) = (s = (@set0 A)).
Axiom thm_FORALL_IN_IMAGE_2 : forall {A B : Type'}, forall f : A -> B, forall P : B -> B -> Prop, forall s : A -> Prop, (forall x : B, forall y : B, ((@IN B x (@IMAGE A B f s)) /\ (@IN B y (@IMAGE A B f s))) -> P x y) = (forall x : A, forall y : A, ((@IN A x s) /\ (@IN A y s)) -> P (f x) (f y)).
Axiom thm_IMAGE_CONST : forall {A B : Type'}, forall s : A -> Prop, forall c : B, (@IMAGE A B (fun x : A => c) s) = (@COND (B -> Prop) (s = (@set0 A)) (@set0 B) (@INSERT B c (@set0 B))).
Axiom thm_SIMPLE_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@GSPEC B (fun GEN_PVAR_45 : B => exists x : A, @SETSPEC B GEN_PVAR_45 (@IN A x s) (f x))) = (@IMAGE A B f s).
Axiom thm_SIMPLE_IMAGE_GEN : forall {A B : Type'}, forall f : A -> B, forall P : A -> Prop, (@GSPEC B (fun GEN_PVAR_46 : B => exists x : A, @SETSPEC B GEN_PVAR_46 (P x) (f x))) = (@IMAGE A B f (@GSPEC A (fun GEN_PVAR_47 : A => exists x : A, @SETSPEC A GEN_PVAR_47 (P x) x))).
Axiom thm_IMAGE_UNIONS : forall {A B : Type'}, forall f : A -> B, forall s : (A -> Prop) -> Prop, (@IMAGE A B f (@UNIONS A s)) = (@UNIONS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) s)).
Axiom thm_FUN_IN_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall x : A, (@IN A x s) -> @IN B (f x) (@IMAGE A B f s).
Axiom thm_SURJECTIVE_IMAGE_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((forall y : B, (@IN B y t) -> exists x : A, (f x) = y) /\ (forall x : A, (@IN B (f x) t) = (@IN A x s))) -> (@IMAGE A B f s) = t.
Axiom thm_IMAGE_EQ : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (g x)) -> (@IMAGE A B f s) = (@IMAGE A B g s).
Axiom thm_EMPTY_GSPEC : forall {A : Type'}, (@GSPEC A (fun GEN_PVAR_48 : A => exists x : A, @SETSPEC A GEN_PVAR_48 False x)) = (@set0 A).
Axiom thm_UNIV_GSPEC : forall {A : Type'}, (@GSPEC A (fun GEN_PVAR_49 : A => exists x : A, @SETSPEC A GEN_PVAR_49 True x)) = (@setT A).
Axiom thm_SING_GSPEC : forall {A : Type'}, (forall a : A, (@GSPEC A (fun GEN_PVAR_50 : A => exists x : A, @SETSPEC A GEN_PVAR_50 (x = a) x)) = (@INSERT A a (@set0 A))) /\ (forall a : A, (@GSPEC A (fun GEN_PVAR_51 : A => exists x : A, @SETSPEC A GEN_PVAR_51 (a = x) x)) = (@INSERT A a (@set0 A))).
Axiom thm_SING_ALT : forall {A : Type'}, forall s : A -> Prop, (exists x : A, s = (@INSERT A x (@set0 A))) = (@ex1 A (fun x : A => @IN A x s)).
Axiom thm_IN_GSPEC : forall {A : Type'}, forall s : A -> Prop, (@GSPEC A (fun GEN_PVAR_52 : A => exists x : A, @SETSPEC A GEN_PVAR_52 (@IN A x s) x)) = s.
Axiom thm_IN_ELIM_PAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, forall a : A, forall b : B, (@IN (prod A B) (@pair A B a b) (@GSPEC (prod A B) (fun GEN_PVAR_53 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_53 (P x y) (@pair A B x y)))) = (P a b).
Axiom thm_IN_ELIM_TRIPLE_THM : forall {A B C : Type'}, (forall P : A -> B -> C -> Prop, forall a : A, forall b : B, forall c : C, (@IN (prod A (prod B C)) (@pair A (prod B C) a (@pair B C b c)) (@GSPEC (prod A (prod B C)) (fun GEN_PVAR_54 : prod A (prod B C) => exists x : A, exists y : B, exists z : C, @SETSPEC (prod A (prod B C)) GEN_PVAR_54 (P x y z) (@pair A (prod B C) x (@pair B C y z))))) = (P a b c)) /\ (forall P : A -> B -> C -> Prop, forall a : A, forall b : B, forall c : C, (@IN (prod (prod A B) C) (@pair (prod A B) C (@pair A B a b) c) (@GSPEC (prod (prod A B) C) (fun GEN_PVAR_55 : prod (prod A B) C => exists x : A, exists y : B, exists z : C, @SETSPEC (prod (prod A B) C) GEN_PVAR_55 (P x y z) (@pair (prod A B) C (@pair A B x y) z)))) = (P a b c)).
Axiom thm_IN_ELIM_QUAD_THM : forall {A B C D : Type'}, (forall P : A -> B -> C -> D -> Prop, forall a : A, forall b : B, forall c : C, forall d : D, (@IN (prod A (prod B (prod C D))) (@pair A (prod B (prod C D)) a (@pair B (prod C D) b (@pair C D c d))) (@GSPEC (prod A (prod B (prod C D))) (fun GEN_PVAR_56 : prod A (prod B (prod C D)) => exists w : A, exists x : B, exists y : C, exists z : D, @SETSPEC (prod A (prod B (prod C D))) GEN_PVAR_56 (P w x y z) (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))))) = (P a b c d)) /\ ((forall P : A -> B -> C -> D -> Prop, forall a : A, forall b : B, forall c : C, forall d : D, (@IN (prod (prod A B) (prod C D)) (@pair (prod A B) (prod C D) (@pair A B a b) (@pair C D c d)) (@GSPEC (prod (prod A B) (prod C D)) (fun GEN_PVAR_57 : prod (prod A B) (prod C D) => exists w : A, exists x : B, exists y : C, exists z : D, @SETSPEC (prod (prod A B) (prod C D)) GEN_PVAR_57 (P w x y z) (@pair (prod A B) (prod C D) (@pair A B w x) (@pair C D y z))))) = (P a b c d)) /\ (forall P : A -> B -> C -> D -> Prop, forall a : A, forall b : B, forall c : C, forall d : D, (@IN (prod (prod (prod A B) C) D) (@pair (prod (prod A B) C) D (@pair (prod A B) C (@pair A B a b) c) d) (@GSPEC (prod (prod (prod A B) C) D) (fun GEN_PVAR_58 : prod (prod (prod A B) C) D => exists w : A, exists x : B, exists y : C, exists z : D, @SETSPEC (prod (prod (prod A B) C) D) GEN_PVAR_58 (P w x y z) (@pair (prod (prod A B) C) D (@pair (prod A B) C (@pair A B w x) y) z)))) = (P a b c d))).
Axiom thm_SET_PAIR_THM : forall {A B : Type'}, forall P : (prod A B) -> Prop, (@GSPEC (prod A B) (fun GEN_PVAR_59 : prod A B => exists p : prod A B, @SETSPEC (prod A B) GEN_PVAR_59 (P p) p)) = (@GSPEC (prod A B) (fun GEN_PVAR_60 : prod A B => exists a : A, exists b : B, @SETSPEC (prod A B) GEN_PVAR_60 (P (@pair A B a b)) (@pair A B a b))).
Axiom thm_SET_PROVE_CASES : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((P (@set0 A)) /\ (forall a : A, forall s : A -> Prop, (~ (@IN A a s)) -> P (@INSERT A a s))) -> forall s : A -> Prop, P s.
Axiom thm_UNIONS_SINGS_GEN : forall {A : Type'}, forall P : A -> Prop, (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_61 : A -> Prop => exists x : A, @SETSPEC (A -> Prop) GEN_PVAR_61 (P x) (@INSERT A x (@set0 A))))) = (@GSPEC A (fun GEN_PVAR_62 : A => exists x : A, @SETSPEC A GEN_PVAR_62 (P x) x)).
Axiom thm_UNIONS_SINGS : forall {A : Type'}, forall s : A -> Prop, (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_63 : A -> Prop => exists x : A, @SETSPEC (A -> Prop) GEN_PVAR_63 (@IN A x s) (@INSERT A x (@set0 A))))) = s.
Axiom thm_IMAGE_INTERS : forall {A B : Type'}, forall f : A -> B, forall s : (A -> Prop) -> Prop, ((~ (s = (@set0 (A -> Prop)))) /\ (forall x : A, forall y : A, ((@IN A x (@UNIONS A s)) /\ ((@IN A y (@UNIONS A s)) /\ ((f x) = (f y)))) -> x = y)) -> (@IMAGE A B f (@INTERS A s)) = (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) s)).
Axiom thm_DIFF_INTERS : forall {A : Type'}, forall u : A -> Prop, forall s : (A -> Prop) -> Prop, (@setD A u (@INTERS A s)) = (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_64 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_64 (@IN (A -> Prop) t s) (@setD A u t)))).
Axiom thm_INTERS_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@INTERS A s) = (@setD A (@setT A) (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_65 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_65 (@IN (A -> Prop) t s) (@setD A (@setT A) t))))).
Axiom thm_UNIONS_INTERS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@UNIONS A s) = (@setD A (@setT A) (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_66 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_66 (@IN (A -> Prop) t s) (@setD A (@setT A) t))))).
Axiom thm_UNIONS_DIFF : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : A -> Prop, (@setD A (@UNIONS A s) t) = (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_67 : A -> Prop => exists x : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_67 (@IN (A -> Prop) x s) (@setD A x t)))).
Axiom thm_DIFF_UNIONS : forall {A : Type'}, forall u : A -> Prop, forall s : (A -> Prop) -> Prop, (@setD A u (@UNIONS A s)) = (@setI A u (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_68 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_68 (@IN (A -> Prop) t s) (@setD A u t))))).
Axiom thm_DIFF_UNIONS_NONEMPTY : forall {A : Type'}, forall u : A -> Prop, forall s : (A -> Prop) -> Prop, (~ (s = (@set0 (A -> Prop)))) -> (@setD A u (@UNIONS A s)) = (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_69 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_69 (@IN (A -> Prop) t s) (@setD A u t)))).
Axiom thm_INTERS_OVER_UNIONS : forall {A B : Type'}, forall f : A -> (B -> Prop) -> Prop, forall s : A -> Prop, (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_70 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_70 (@IN A x s) (@UNIONS B (f x))))) = (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_74 : B -> Prop => exists g : A -> B -> Prop, @SETSPEC (B -> Prop) GEN_PVAR_74 (forall x : A, (@IN A x s) -> @IN (B -> Prop) (g x) (f x)) (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_73 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_73 (@IN A x s) (g x))))))).
Axiom thm_INTER_INTERS : forall {A : Type'}, (forall f : (A -> Prop) -> Prop, forall s : A -> Prop, (@setI A s (@INTERS A f)) = (@COND (A -> Prop) (f = (@set0 (A -> Prop))) s (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_75 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_75 (@IN (A -> Prop) t f) (@setI A s t)))))) /\ (forall f : (A -> Prop) -> Prop, forall s : A -> Prop, (@setI A (@INTERS A f) s) = (@COND (A -> Prop) (f = (@set0 (A -> Prop))) s (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_76 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_76 (@IN (A -> Prop) t f) (@setI A t s)))))).
Axiom thm_UNIONS_OVER_INTERS : forall {A B : Type'}, forall f : A -> (B -> Prop) -> Prop, forall s : A -> Prop, (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_77 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_77 (@IN A x s) (@INTERS B (f x))))) = (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_81 : B -> Prop => exists g : A -> B -> Prop, @SETSPEC (B -> Prop) GEN_PVAR_81 (forall x : A, (@IN A x s) -> @IN (B -> Prop) (g x) (f x)) (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_80 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_80 (@IN A x s) (g x))))))).
Axiom thm_UNIONS_EQ_INTERS : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@UNIONS A f) = (@INTERS A f)) = (exists s : A -> Prop, f = (@INSERT (A -> Prop) s (@set0 (A -> Prop)))).
Axiom thm_EXISTS_UNIQUE_UNIONS_INTERS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@ex1 (A -> Prop) (fun s : A -> Prop => P s)) = ((@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_82 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_82 (P s) s))) = (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_83 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_83 (P s) s)))).
Axiom thm_IMAGE_INTERS_SUBSET : forall {A B : Type'}, forall f : A -> B, forall g : (A -> Prop) -> Prop, @subset B (@IMAGE A B f (@INTERS A g)) (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) g)).
Axiom thm_IMAGE_INTER_SUBSET : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, @subset B (@IMAGE A B f (@setI A s t)) (@setI B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_INTER_SATURATED_GEN : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (((@subset A (@GSPEC A (fun GEN_PVAR_84 : A => exists x : A, @SETSPEC A GEN_PVAR_84 ((@IN A x u) /\ (@IN B (f x) (@IMAGE A B f s))) x)) s) /\ (@subset A t u)) \/ ((@subset A (@GSPEC A (fun GEN_PVAR_85 : A => exists x : A, @SETSPEC A GEN_PVAR_85 ((@IN A x u) /\ (@IN B (f x) (@IMAGE A B f t))) x)) t) /\ (@subset A s u))) -> (@IMAGE A B f (@setI A s t)) = (@setI B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_INTERS_SATURATED_GEN : forall {A B : Type'}, forall f : A -> B, forall g : (A -> Prop) -> Prop, forall s : A -> Prop, forall u : A -> Prop, ((~ (g = (@set0 (A -> Prop)))) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t g) -> @subset A t u) /\ (forall t : A -> Prop, (@IN (A -> Prop) t (@DELETE (A -> Prop) g s)) -> @subset A (@GSPEC A (fun GEN_PVAR_87 : A => exists x : A, @SETSPEC A GEN_PVAR_87 ((@IN A x u) /\ (@IN B (f x) (@IMAGE A B f t))) x)) t))) -> (@IMAGE A B f (@INTERS A g)) = (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) g)).
Axiom thm_IMAGE_INTER_SATURATED : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@subset A (@GSPEC A (fun GEN_PVAR_88 : A => exists x : A, @SETSPEC A GEN_PVAR_88 (@IN B (f x) (@IMAGE A B f s)) x)) s) \/ (@subset A (@GSPEC A (fun GEN_PVAR_89 : A => exists x : A, @SETSPEC A GEN_PVAR_89 (@IN B (f x) (@IMAGE A B f t)) x)) t)) -> (@IMAGE A B f (@setI A s t)) = (@setI B (@IMAGE A B f s) (@IMAGE A B f t)).
Axiom thm_IMAGE_INTERS_SATURATED : forall {A B : Type'}, forall f : A -> B, forall g : (A -> Prop) -> Prop, forall s : A -> Prop, ((~ (g = (@set0 (A -> Prop)))) /\ (forall t : A -> Prop, (@IN (A -> Prop) t (@DELETE (A -> Prop) g s)) -> @subset A (@GSPEC A (fun GEN_PVAR_90 : A => exists x : A, @SETSPEC A GEN_PVAR_90 (@IN B (f x) (@IMAGE A B f t)) x)) t)) -> (@IMAGE A B f (@INTERS A g)) = (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) g)).
Axiom thm_FINITE_INDUCT_STRONG : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((P (@set0 A)) /\ (forall x : A, forall s : A -> Prop, ((P s) /\ ((~ (@IN A x s)) /\ (@finite_set A s))) -> P (@INSERT A x s))) -> forall s : A -> Prop, (@finite_set A s) -> P s.
Axiom thm_INJECTIVE_ON_ALT : forall {A B : Type'}, forall P : A -> Prop, forall f : A -> B, (forall x : A, forall y : A, ((P x) /\ ((P y) /\ ((f x) = (f y)))) -> x = y) = (forall x : A, forall y : A, ((P x) /\ (P y)) -> ((f x) = (f y)) = (x = y)).
Axiom thm_INJECTIVE_ALT : forall {A B : Type'}, forall f : A -> B, (forall x : A, forall y : A, ((f x) = (f y)) -> x = y) = (forall x : A, forall y : A, ((f x) = (f y)) = (x = y)).
Axiom thm_SURJECTIVE_ON_RIGHT_INVERSE : forall {A B : Type'} (s : A -> Prop), forall f : A -> B, forall t : B -> Prop, (forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y)) = (exists g : B -> A, forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)).
Axiom thm_INJECTIVE_ON_LEFT_INVERSE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) = (exists g : B -> A, forall x : A, (@IN A x s) -> (g (f x)) = x).
Axiom thm_BIJECTIVE_ON_LEFT_RIGHT_INVERSE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, (forall x : A, (@IN A x s) -> @IN B (f x) t) -> ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y))) = (exists g : B -> A, (forall y : B, (@IN B y t) -> @IN A (g y) s) /\ ((forall y : B, (@IN B y t) -> (f (g y)) = y) /\ (forall x : A, (@IN A x s) -> (g (f x)) = x))).
Axiom thm_SURJECTIVE_RIGHT_INVERSE : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (exists g : B -> A, forall y : B, (f (g y)) = y).
Axiom thm_INJECTIVE_LEFT_INVERSE : forall {A B : Type'}, forall f : A -> B, (forall x : A, forall y : A, ((f x) = (f y)) -> x = y) = (exists g : B -> A, forall x : A, (g (f x)) = x).
Axiom thm_BIJECTIVE_LEFT_RIGHT_INVERSE : forall {A B : Type'}, forall f : A -> B, ((forall x : A, forall y : A, ((f x) = (f y)) -> x = y) /\ (forall y : B, exists x : A, (f x) = y)) = (exists g : B -> A, (forall y : B, (f (g y)) = y) /\ (forall x : A, (g (f x)) = x)).
Axiom thm_FUNCTION_FACTORS_LEFT_GEN : forall {A B C : Type'}, forall P : A -> Prop, forall f : A -> B, forall g : A -> C, (forall x : A, forall y : A, ((P x) /\ ((P y) /\ ((g x) = (g y)))) -> (f x) = (f y)) = (exists h : C -> B, forall x : A, (P x) -> (f x) = (h (g x))).
Axiom thm_FUNCTION_FACTORS_LEFT : forall {A B C : Type'}, forall f : A -> B, forall g : A -> C, (forall x : A, forall y : A, ((g x) = (g y)) -> (f x) = (f y)) = (exists h : C -> B, f = (@o A C B h g)).
Axiom thm_FUNCTION_FACTORS_RIGHT_GEN : forall {A B C : Type'}, forall P : A -> Prop, forall f : A -> C, forall g : B -> C, (forall x : A, (P x) -> exists y : B, (g y) = (f x)) = (exists h : A -> B, forall x : A, (P x) -> (f x) = (g (h x))).
Axiom thm_FUNCTION_FACTORS_RIGHT : forall {A B C : Type'}, forall f : A -> C, forall g : B -> C, (forall x : A, exists y : B, (g y) = (f x)) = (exists h : A -> B, f = (@o A B C g h)).
Axiom thm_SURJECTIVE_FORALL_THM : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (forall P : B -> Prop, (forall x : A, P (f x)) = (forall y : B, P y)).
Axiom thm_SURJECTIVE_EXISTS_THM : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (forall P : B -> Prop, (exists x : A, P (f x)) = (exists y : B, P y)).
Axiom thm_SURJECTIVE_IMAGE_THM : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (forall P : B -> Prop, (@IMAGE A B f (@GSPEC A (fun GEN_PVAR_91 : A => exists x : A, @SETSPEC A GEN_PVAR_91 (P (f x)) x))) = (@GSPEC B (fun GEN_PVAR_92 : B => exists x : B, @SETSPEC B GEN_PVAR_92 (P x) x))).
Axiom thm_IMAGE_INJECTIVE_IMAGE_OF_SUBSET : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, exists t : A -> Prop, (@subset A t s) /\ (((@IMAGE A B f s) = (@IMAGE A B f t)) /\ (forall x : A, forall y : A, ((@IN A x t) /\ ((@IN A y t) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_FINITE_EMPTY : forall {A : Type'}, @finite_set A (@set0 A).
Axiom thm_FINITE_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ (@subset A s t)) -> @finite_set A s.
Axiom thm_FINITE_RESTRICT : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, (@finite_set A s) -> @finite_set A (@GSPEC A (fun GEN_PVAR_93 : A => exists x : A, @SETSPEC A GEN_PVAR_93 ((@IN A x s) /\ (P x)) x)).
Axiom thm_FINITE_UNION_IMP : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@finite_set A t)) -> @finite_set A (@setU A s t).
Axiom thm_FINITE_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@finite_set A (@setU A s t)) = ((@finite_set A s) /\ (@finite_set A t)).
Axiom thm_FINITE_INTER : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) \/ (@finite_set A t)) -> @finite_set A (@setI A s t).
Axiom thm_FINITE_INSERT : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@finite_set A (@INSERT A x s)) = (@finite_set A s).
Axiom thm_FINITE_SING : forall {A : Type'}, forall a : A, @finite_set A (@INSERT A a (@set0 A)).
Axiom thm_FINITE_DELETE_IMP : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@finite_set A s) -> @finite_set A (@DELETE A s x).
Axiom thm_FINITE_DELETE : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@finite_set A (@DELETE A s x)) = (@finite_set A s).
Axiom thm_FINITE_FINITE_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@finite_set (A -> Prop) s) -> (@finite_set A (@UNIONS A s)) = (forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t).
Axiom thm_FINITE_IMAGE_EXPAND : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> @finite_set B (@GSPEC B (fun GEN_PVAR_96 : B => exists y : B, @SETSPEC B GEN_PVAR_96 (exists x : A, (@IN A x s) /\ (y = (f x))) y)).
Axiom thm_FINITE_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> @finite_set B (@IMAGE A B f s).
Axiom thm_FINITE_IMAGE_INJ_GENERAL : forall {A B : Type'}, forall f : A -> B, forall A' : B -> Prop, forall s : A -> Prop, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@finite_set B A')) -> @finite_set A (@GSPEC A (fun GEN_PVAR_97 : A => exists x : A, @SETSPEC A GEN_PVAR_97 ((@IN A x s) /\ (@IN B (f x) A')) x)).
Axiom thm_FINITE_FINITE_PREIMAGE_GENERAL : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set B t) /\ (forall y : B, (@IN B y t) -> @finite_set A (@GSPEC A (fun GEN_PVAR_100 : A => exists x : A, @SETSPEC A GEN_PVAR_100 ((@IN A x s) /\ ((f x) = y)) x)))) -> @finite_set A (@GSPEC A (fun GEN_PVAR_101 : A => exists x : A, @SETSPEC A GEN_PVAR_101 ((@IN A x s) /\ (@IN B (f x) t)) x)).
Axiom thm_FINITE_FINITE_PREIMAGE : forall {A B : Type'}, forall f : A -> B, forall t : B -> Prop, ((@finite_set B t) /\ (forall y : B, (@IN B y t) -> @finite_set A (@GSPEC A (fun GEN_PVAR_102 : A => exists x : A, @SETSPEC A GEN_PVAR_102 ((f x) = y) x)))) -> @finite_set A (@GSPEC A (fun GEN_PVAR_103 : A => exists x : A, @SETSPEC A GEN_PVAR_103 (@IN B (f x) t) x)).
Axiom thm_FINITE_IMAGE_INJ_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@finite_set B (@IMAGE A B f s)) = (@finite_set A s).
Axiom thm_FINITE_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, forall A' : B -> Prop, ((forall x : A, forall y : A, ((f x) = (f y)) -> x = y) /\ (@finite_set B A')) -> @finite_set A (@GSPEC A (fun GEN_PVAR_104 : A => exists x : A, @SETSPEC A GEN_PVAR_104 (@IN B (f x) A') x)).
Axiom thm_FINITE_IMAGE_GEN : forall {A B C : Type'}, forall f : A -> B, forall g : A -> C, forall s : A -> Prop, forall t : B -> Prop, ((@subset B (@IMAGE A B f s) t) /\ ((@finite_set B t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> (g x) = (g y)))) -> @finite_set C (@IMAGE A C g s).
Axiom thm_INFINITE_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((@INFINITE A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)) -> @INFINITE B (@IMAGE A B f s).
Axiom thm_INFINITE_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, (forall x : A, forall y : A, ((f x) = (f y)) -> x = y) -> forall s : A -> Prop, (@INFINITE A s) -> @INFINITE B (@IMAGE A B f s).
Axiom thm_INFINITE_NONEMPTY : forall {A : Type'}, forall s : A -> Prop, (@INFINITE A s) -> ~ (s = (@set0 A)).
Axiom thm_INFINITE_DIFF_FINITE : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@INFINITE A s) /\ (@finite_set A t)) -> @INFINITE A (@setD A s t).
Axiom thm_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, forall s : B -> Prop, forall t : A -> Prop, (@subset B s (@IMAGE A B f t)) = (exists u : A -> Prop, (@subset A u t) /\ ((forall x : A, forall y : A, ((@IN A x u) /\ (@IN A y u)) -> ((f x) = (f y)) = (x = y)) /\ (s = (@IMAGE A B f u)))).
Axiom thm_SUBSET_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : B -> Prop, forall t : A -> Prop, (@subset B s (@IMAGE A B f t)) = (exists u : A -> Prop, (@subset A u t) /\ (s = (@IMAGE A B f u))).
Axiom thm_EXISTS_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (exists t : B -> Prop, (@subset B t (@IMAGE A B f s)) /\ (P t)) = (exists t : A -> Prop, (@subset A t s) /\ (P (@IMAGE A B f t))).
Axiom thm_FORALL_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (forall t : B -> Prop, (@subset B t (@IMAGE A B f s)) -> P t) = (forall t : A -> Prop, (@subset A t s) -> P (@IMAGE A B f t)).
Axiom thm_EXISTS_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (exists t : B -> Prop, (@subset B t (@IMAGE A B f s)) /\ (P t)) = (exists t : A -> Prop, (@subset A t s) /\ ((forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y)) /\ (P (@IMAGE A B f t)))).
Axiom thm_FORALL_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (forall t : B -> Prop, (@subset B t (@IMAGE A B f s)) -> P t) = (forall t : A -> Prop, ((@subset A t s) /\ (forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y))) -> P (@IMAGE A B f t)).
Axiom thm_EXISTS_FINITE_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (exists t : B -> Prop, (@finite_set B t) /\ ((@subset B t (@IMAGE A B f s)) /\ (P t))) = (exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ ((forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y)) /\ (P (@IMAGE A B f t))))).
Axiom thm_FORALL_FINITE_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (forall t : B -> Prop, ((@finite_set B t) /\ (@subset B t (@IMAGE A B f s))) -> P t) = (forall t : A -> Prop, ((@finite_set A t) /\ ((@subset A t s) /\ (forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y)))) -> P (@IMAGE A B f t)).
Axiom thm_EXISTS_FINITE_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (exists t : B -> Prop, (@finite_set B t) /\ ((@subset B t (@IMAGE A B f s)) /\ (P t))) = (exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (P (@IMAGE A B f t)))).
Axiom thm_FORALL_FINITE_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, (forall t : B -> Prop, ((@finite_set B t) /\ (@subset B t (@IMAGE A B f s))) -> P t) = (forall t : A -> Prop, ((@finite_set A t) /\ (@subset A t s)) -> P (@IMAGE A B f t)).
Axiom thm_FINITE_SUBSET_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set B t) /\ (@subset B t (@IMAGE A B f s))) = (exists s' : A -> Prop, (@finite_set A s') /\ ((@subset A s' s) /\ (t = (@IMAGE A B f s')))).
Axiom thm_FINITE_SUBSET_IMAGE_IMP : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set B t) /\ (@subset B t (@IMAGE A B f s))) -> exists s' : A -> Prop, (@finite_set A s') /\ ((@subset A s' s) /\ (@subset B t (@IMAGE A B f s'))).
Axiom thm_FINITE_IMAGE_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set B (@IMAGE A B f s)) = (exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ ((@IMAGE A B f s) = (@IMAGE A B f t)))).
Axiom thm_FINITE_IMAGE_EQ_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set B (@IMAGE A B f s)) = (exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (((@IMAGE A B f s) = (@IMAGE A B f t)) /\ (forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y))))).
Axiom thm_FINITE_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@finite_set A s) -> @finite_set A (@setD A s t).
Axiom thm_INFINITE_SUPERSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@INFINITE A s) /\ (@subset A s t)) -> @INFINITE A t.
Axiom thm_FINITE_TRANSITIVITY_CHAIN : forall {A : Type'}, forall R' : A -> A -> Prop, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, ~ (R' x x)) /\ ((forall x : A, forall y : A, forall z : A, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall x : A, (@IN A x s) -> exists y : A, (@IN A y s) /\ (R' x y))))) -> s = (@set0 A).
Axiom thm_UNIONS_MAXIMAL_SETS : forall {A : Type'}, forall f : (A -> Prop) -> Prop, (@finite_set (A -> Prop) f) -> (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_106 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_106 ((@IN (A -> Prop) t f) /\ (forall u : A -> Prop, (@IN (A -> Prop) u f) -> ~ (@proper A t u))) t))) = (@UNIONS A f).
Axiom thm_FINITE_SUBSET_UNIONS : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall s : A -> Prop, ((@finite_set A s) /\ (@subset A s (@UNIONS A f))) -> exists f' : (A -> Prop) -> Prop, (@finite_set (A -> Prop) f') /\ ((@subset (A -> Prop) f' f) /\ (@subset A s (@UNIONS A f'))).
Axiom thm_UNIONS_IN_CHAIN : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) f) /\ ((~ (f = (@set0 (A -> Prop)))) /\ (forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s f) /\ (@IN (A -> Prop) t f)) -> (@subset A s t) \/ (@subset A t s)))) -> @IN (A -> Prop) (@UNIONS A f) f.
Axiom thm_INTERS_IN_CHAIN : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) f) /\ ((~ (f = (@set0 (A -> Prop)))) /\ (forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s f) /\ (@IN (A -> Prop) t f)) -> (@subset A s t) \/ (@subset A t s)))) -> @IN (A -> Prop) (@INTERS A f) f.
Axiom thm_FINITE_SUBSET_UNIONS_DIRECTED_EQ : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall s : A -> Prop, ((~ (f = (@set0 (A -> Prop)))) /\ ((forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t f) /\ (@IN (A -> Prop) u f)) -> exists v : A -> Prop, (@IN (A -> Prop) v f) /\ ((@subset A t v) /\ (@subset A u v))) /\ (@finite_set A s))) -> (@subset A s (@UNIONS A f)) = (exists t : A -> Prop, (@IN (A -> Prop) t f) /\ (@subset A s t)).
Axiom thm_FINITE_SUBSET_UNIONS_CHAIN : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall s : A -> Prop, ((@finite_set A s) /\ ((@subset A s (@UNIONS A f)) /\ ((~ (f = (@set0 (A -> Prop)))) /\ (forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t f) /\ (@IN (A -> Prop) u f)) -> (@subset A t u) \/ (@subset A u t))))) -> exists t : A -> Prop, (@IN (A -> Prop) t f) /\ (@subset A s t).
Axiom thm_FINREC : forall {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : A -> B -> B), ((@FINREC A B f b s a (NUMERAL O)) = ((s = (@set0 A)) /\ (a = b))) /\ ((@FINREC A B f b s a (S n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((@FINREC A B f b (@DELETE A s x) c n) /\ (a = (f x c))))).
Axiom thm_FINREC_1_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, forall s : A -> Prop, forall a : B, (@FINREC A B f b s a (S (NUMERAL O))) = (exists x : A, (s = (@INSERT A x (@set0 A))) /\ (a = (f x b))).
Axiom thm_FINREC_SUC_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> forall n : nat, forall s : A -> Prop, forall z : B, (@FINREC A B f b s z (S n)) -> forall x : A, (@IN A x s) -> exists w : B, (@FINREC A B f b (@DELETE A s x) w n) /\ (z = (f x w)).
Axiom thm_FINREC_UNIQUE_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> forall n1 : nat, forall n2 : nat, forall s : A -> Prop, forall a1 : B, forall a2 : B, ((@FINREC A B f b s a1 n1) /\ (@FINREC A B f b s a2 n2)) -> (a1 = a2) /\ (n1 = n2).
Axiom thm_FINREC_EXISTS_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, forall s : A -> Prop, (@finite_set A s) -> exists a : B, exists n : nat, @FINREC A B f b s a n.
Axiom thm_FINREC_FUN_LEMMA : forall {A B C : Type'}, forall P : A -> Prop, forall R' : A -> B -> C -> Prop, ((forall s : A, (P s) -> exists a : B, exists n : C, R' s a n) /\ (forall n1 : C, forall n2 : C, forall s : A, forall a1 : B, forall a2 : B, ((R' s a1 n1) /\ (R' s a2 n2)) -> (a1 = a2) /\ (n1 = n2))) -> exists f : A -> B, forall s : A, forall a : B, (P s) -> (exists n : C, R' s a n) = ((f s) = a).
Axiom thm_FINREC_FUN : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> exists g : (A -> Prop) -> B, ((g (@set0 A)) = b) /\ (forall s : A -> Prop, forall x : A, ((@finite_set A s) /\ (@IN A x s)) -> (g s) = (f x (g (@DELETE A s x)))).
Axiom thm_SET_RECURSION_LEMMA : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> exists g : (A -> Prop) -> B, ((g (@set0 A)) = b) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> (g (@INSERT A x s)) = (@COND B (@IN A x s) (g s) (f x (g s)))).
Axiom thm_ITSET : forall {A B : Type'}, forall b : B, forall f : A -> B -> B, forall s : A -> Prop, (@fold_set A B f s b) = (@ε ((A -> Prop) -> B) (fun g : (A -> Prop) -> B => ((g (@set0 A)) = b) /\ (forall x : A, forall s' : A -> Prop, (@finite_set A s') -> (g (@INSERT A x s')) = (@COND B (@IN A x s') (g s') (f x (g s'))))) s).
Axiom thm_FINITE_RECURSION : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> ((@fold_set A B f (@set0 A) b) = b) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> (@fold_set A B f (@INSERT A x s) b) = (@COND B (@IN A x s) (@fold_set A B f s b) (f x (@fold_set A B f s b)))).
Axiom thm_FINITE_RECURSION_DELETE : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> ((@fold_set A B f (@set0 A) b) = b) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> (@fold_set A B f s b) = (@COND B (@IN A x s) (f x (@fold_set A B f (@DELETE A s x) b)) (@fold_set A B f (@DELETE A s x) b))).
Axiom thm_ITSET_EQ : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B -> B, forall g : A -> B -> B, forall b : B, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> (f x) = (g x)) /\ ((forall x : A, forall y : A, forall s' : B, (~ (x = y)) -> (f x (f y s')) = (f y (f x s'))) /\ (forall x : A, forall y : A, forall s' : B, (~ (x = y)) -> (g x (g y s')) = (g y (g x s')))))) -> (@fold_set A B f s b) = (@fold_set A B g s b).
Axiom thm_CARD : forall {A : Type'}, forall s : A -> Prop, (@CARD A s) = (@fold_set A nat (fun x : A => fun n : nat => S n) s (NUMERAL O)).
Axiom thm_CARD_CLAUSES : forall {A : Type'}, ((@CARD A (@set0 A)) = (NUMERAL O)) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> (@CARD A (@INSERT A x s)) = (@COND nat (@IN A x s) (@CARD A s) (S (@CARD A s)))).
Axiom thm_CARD_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ ((@setI A s t) = (@set0 A)))) -> (@CARD A (@setU A s t)) = (addn (@CARD A s) (@CARD A t)).
Axiom thm_CARD_DELETE : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@finite_set A s) -> (@CARD A (@DELETE A s x)) = (@COND nat (@IN A x s) (subn (@CARD A s) (NUMERAL (BIT1 O))) (@CARD A s)).
Axiom thm_CARD_UNION_EQ : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@finite_set A u) /\ (((@setI A s t) = (@set0 A)) /\ ((@setU A s t) = u))) -> (addn (@CARD A s) (@CARD A t)) = (@CARD A u).
Axiom thm_CARD_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@subset A t s)) -> (@CARD A (@setD A s t)) = (subn (@CARD A s) (@CARD A t)).
Axiom thm_CARD_EQ_0 : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> ((@CARD A s) = (NUMERAL O)) = (s = (@set0 A)).
Axiom thm_CARD_SING : forall {A : Type'}, forall a : A, (@CARD A (@INSERT A a (@set0 A))) = (NUMERAL (BIT1 O)).
Axiom thm_FINITE_INDUCT_DELETE : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((P (@set0 A)) /\ (forall s : A -> Prop, ((@finite_set A s) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ ((P (@DELETE A s x)) -> P s))) -> forall s : A -> Prop, (@finite_set A s) -> P s.
Axiom thm_HAS_SIZE : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@HAS_SIZE A s n) = ((@finite_set A s) /\ ((@CARD A s) = n)).
Axiom thm_HAS_SIZE_CARD : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@HAS_SIZE A s n) -> (@CARD A s) = n.
Axiom thm_HAS_SIZE_0 : forall {A : Type'}, forall s : A -> Prop, (@HAS_SIZE A s (NUMERAL O)) = (s = (@set0 A)).
Axiom thm_HAS_SIZE_SUC : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@HAS_SIZE A s (S n)) = ((~ (s = (@set0 A))) /\ (forall a : A, (@IN A a s) -> @HAS_SIZE A (@DELETE A s a) n)).
Axiom thm_HAS_SIZE_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE A s m) /\ ((@HAS_SIZE A t n) /\ (@DISJOINT A s t))) -> @HAS_SIZE A (@setU A s t) (addn m n).
Axiom thm_HAS_SIZE_DIFF : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE A s m) /\ ((@HAS_SIZE A t n) /\ (@subset A t s))) -> @HAS_SIZE A (@setD A s t) (subn m n).
Axiom thm_HAS_SIZE_UNIONS : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE A s m) /\ ((forall x : A, (@IN A x s) -> @HAS_SIZE B (t x) n) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ (~ (x = y)))) -> @DISJOINT B (t x) (t y)))) -> @HAS_SIZE B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_109 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_109 (@IN A x s) (t x)))) (muln m n).
Axiom thm_FINITE_HAS_SIZE : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) = (@HAS_SIZE A s (@CARD A s)).
Axiom thm_HAS_SIZE_CLAUSES : forall {A : Type'} (n : nat) (s : A -> Prop), ((@HAS_SIZE A s (NUMERAL O)) = (s = (@set0 A))) /\ ((@HAS_SIZE A s (S n)) = (exists a : A, exists t : A -> Prop, (@HAS_SIZE A t n) /\ ((~ (@IN A a t)) /\ (s = (@INSERT A a t))))).
Axiom thm_CARD_SUBSET_EQ : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@finite_set A b) /\ ((@subset A a b) /\ ((@CARD A a) = (@CARD A b)))) -> a = b.
Axiom thm_CARD_SUBSET : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@subset A a b) /\ (@finite_set A b)) -> leqn (@CARD A a) (@CARD A b).
Axiom thm_CARD_SUBSET_LE : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@finite_set A b) /\ ((@subset A a b) /\ (leqn (@CARD A b) (@CARD A a)))) -> a = b.
Axiom thm_SUBSET_CARD_EQ : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ (@subset A s t)) -> ((@CARD A s) = (@CARD A t)) = (s = t).
Axiom thm_FINITE_CARD_LE_SUBSET : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall n : nat, ((@subset A s t) /\ ((@finite_set A t) /\ (leqn (@CARD A t) n))) -> (@finite_set A s) /\ (leqn (@CARD A s) n).
Axiom thm_CARD_PSUBSET : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@proper A a b) /\ (@finite_set A b)) -> ltn (@CARD A a) (@CARD A b).
Axiom thm_CARD_PSUBSET_IMP : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@subset A a b) /\ (~ ((@CARD A a) = (@CARD A b)))) -> @proper A a b.
Axiom thm_CARD_PSUBSET_EQ : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@finite_set A b) /\ (@subset A a b)) -> (@proper A a b) = (ltn (@CARD A a) (@CARD A b)).
Axiom thm_CARD_UNION_LE : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@finite_set A t)) -> leqn (@CARD A (@setU A s t)) (addn (@CARD A s) (@CARD A t)).
Axiom thm_FINITE_CARD_LE_UNION : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall m : nat, forall n : nat, (((@finite_set A s) /\ (leqn (@CARD A s) m)) /\ ((@finite_set A t) /\ (leqn (@CARD A t) n))) -> (@finite_set A (@setU A s t)) /\ (leqn (@CARD A (@setU A s t)) (addn m n)).
Axiom thm_CARD_UNIONS_LE : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE A s m) /\ (forall x : A, (@IN A x s) -> (@finite_set B (t x)) /\ (leqn (@CARD B (t x)) n))) -> leqn (@CARD B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_115 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_115 (@IN A x s) (t x))))) (muln m n).
Axiom thm_CARD_UNION_GEN : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@finite_set A t)) -> (@CARD A (@setU A s t)) = (subn (addn (@CARD A s) (@CARD A t)) (@CARD A (@setI A s t))).
Axiom thm_CARD_UNION_OVERLAP_EQ : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@finite_set A t)) -> ((@CARD A (@setU A s t)) = (addn (@CARD A s) (@CARD A t))) = ((@setI A s t) = (@set0 A)).
Axiom thm_CARD_UNION_OVERLAP : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (ltn (@CARD A (@setU A s t)) (addn (@CARD A s) (@CARD A t))))) -> ~ ((@setI A s t) = (@set0 A)).
Axiom thm_CARD_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@finite_set A s)) -> (@CARD B (@IMAGE A B f s)) = (@CARD A s).
Axiom thm_HAS_SIZE_IMAGE_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall n : nat, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@HAS_SIZE A s n)) -> @HAS_SIZE B (@IMAGE A B f s) n.
Axiom thm_CARD_IMAGE_LE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> leqn (@CARD B (@IMAGE A B f s)) (@CARD A s).
Axiom thm_FINITE_CARD_LE_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall n : nat, ((@finite_set A s) /\ (leqn (@CARD A s) n)) -> (@finite_set B (@IMAGE A B f s)) /\ (leqn (@CARD B (@IMAGE A B f s)) n).
Axiom thm_CARD_IMAGE_INJ_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((f x) = y))))) -> (@CARD B t) = (@CARD A s).
Axiom thm_CARD_SUBSET_IMAGE : forall {A B : Type'}, forall f : A -> B, forall s : B -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ (@subset B s (@IMAGE A B f t))) -> leqn (@CARD B s) (@CARD A t).
Axiom thm_HAS_SIZE_IMAGE_INJ_EQ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall n : nat, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@HAS_SIZE B (@IMAGE A B f s) n) = (@HAS_SIZE A s n).
Axiom thm_CARD_IMAGE_EQ_INJ : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> ((@CARD B (@IMAGE A B f s)) = (@CARD A s)) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_EXISTS_SMALL_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, forall n : nat, (exists t : B -> Prop, (@finite_set B t) /\ ((ltn (@CARD B t) n) /\ ((@subset B t (@IMAGE A B f s)) /\ (P t)))) = (exists t : A -> Prop, (@finite_set A t) /\ ((ltn (@CARD A t) n) /\ ((@subset A t s) /\ ((forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y)) /\ (P (@IMAGE A B f t)))))).
Axiom thm_FORALL_SMALL_SUBSET_IMAGE_INJ : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, forall n : nat, (forall t : B -> Prop, ((@finite_set B t) /\ ((ltn (@CARD B t) n) /\ (@subset B t (@IMAGE A B f s)))) -> P t) = (forall t : A -> Prop, ((@finite_set A t) /\ ((ltn (@CARD A t) n) /\ ((@subset A t s) /\ (forall x : A, forall y : A, ((@IN A x t) /\ (@IN A y t)) -> ((f x) = (f y)) = (x = y))))) -> P (@IMAGE A B f t)).
Axiom thm_EXISTS_SMALL_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, forall n : nat, (exists t : B -> Prop, (@finite_set B t) /\ ((ltn (@CARD B t) n) /\ ((@subset B t (@IMAGE A B f s)) /\ (P t)))) = (exists t : A -> Prop, (@finite_set A t) /\ ((ltn (@CARD A t) n) /\ ((@subset A t s) /\ (P (@IMAGE A B f t))))).
Axiom thm_FORALL_SMALL_SUBSET_IMAGE : forall {A B : Type'}, forall P : (B -> Prop) -> Prop, forall f : A -> B, forall s : A -> Prop, forall n : nat, (forall t : B -> Prop, ((@finite_set B t) /\ ((ltn (@CARD B t) n) /\ (@subset B t (@IMAGE A B f s)))) -> P t) = (forall t : A -> Prop, ((@finite_set A t) /\ ((ltn (@CARD A t) n) /\ (@subset A t s))) -> P (@IMAGE A B f t)).
Axiom thm_CARD_IMAGE_LE2 : forall {A B C : Type'}, forall f : A -> B, forall g : A -> C, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((g x) = (g y)))) -> (f x) = (f y))) -> leqn (@CARD B (@IMAGE A B f s)) (@CARD C (@IMAGE A C g s)).
Axiom thm_CARD_IMAGE_LT2 : forall {A B C : Type'}, forall f : A -> B, forall g : A -> C, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((g x) = (g y)))) -> (f x) = (f y)) /\ (~ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> (g x) = (g y))))) -> ltn (@CARD B (@IMAGE A B f s)) (@CARD C (@IMAGE A C g s)).
Axiom thm_CHOOSE_SUBSET_STRONG : forall {A : Type'}, forall n : nat, forall s : A -> Prop, ((@finite_set A s) -> leqn n (@CARD A s)) -> exists t : A -> Prop, (@subset A t s) /\ (@HAS_SIZE A t n).
Axiom thm_CHOOSE_SUBSET_EQ : forall {A : Type'}, forall n : nat, forall s : A -> Prop, ((@finite_set A s) -> leqn n (@CARD A s)) = (exists t : A -> Prop, (@subset A t s) /\ (@HAS_SIZE A t n)).
Axiom thm_CHOOSE_SUBSET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> forall n : nat, (leqn n (@CARD A s)) -> exists t : A -> Prop, (@subset A t s) /\ (@HAS_SIZE A t n).
Axiom thm_CHOOSE_SUBSET_BETWEEN : forall {A : Type'}, forall n : nat, forall s : A -> Prop, forall u : A -> Prop, ((@subset A s u) /\ ((@finite_set A s) /\ ((leqn (@CARD A s) n) /\ ((@finite_set A u) -> leqn n (@CARD A u))))) -> exists t : A -> Prop, (@subset A s t) /\ ((@subset A t u) /\ (@HAS_SIZE A t n)).
Axiom thm_CARD_LE_UNIONS_CHAIN : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall n : nat, ((forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t f) /\ (@IN (A -> Prop) u f)) -> (@subset A t u) \/ (@subset A u t)) /\ (forall t : A -> Prop, (@IN (A -> Prop) t f) -> (@finite_set A t) /\ (leqn (@CARD A t) n))) -> (@finite_set A (@UNIONS A f)) /\ (leqn (@CARD A (@UNIONS A f)) n).
Axiom thm_CARD_LE_1 : forall {A : Type'}, forall s : A -> Prop, ((@finite_set A s) /\ (leqn (@CARD A s) (NUMERAL (BIT1 O)))) = (exists a : A, @subset A s (@INSERT A a (@set0 A))).
Axiom thm_INVOLUTION_EVEN_NOFIXPOINTS : forall {A : Type'}, forall f : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> (@IN A (f x) s) /\ ((~ ((f x) = x)) /\ ((f (f x)) = x)))) -> even (@CARD A s).
Axiom thm_INVOLUTION_EVEN_FIXPOINTS : forall {A : Type'}, forall f : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> (@IN A (f x) s) /\ ((f (f x)) = x))) -> (even (@CARD A (@GSPEC A (fun GEN_PVAR_120 : A => exists x : A, @SETSPEC A GEN_PVAR_120 ((@IN A x s) /\ ((f x) = x)) x)))) = (even (@CARD A s)).
Axiom thm_HAS_SIZE_PRODUCT_DEPENDENT : forall {A B : Type'}, forall s : A -> Prop, forall m : nat, forall t : A -> B -> Prop, forall n : nat, ((@HAS_SIZE A s m) /\ (forall x : A, (@IN A x s) -> @HAS_SIZE B (t x) n)) -> @HAS_SIZE (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_123 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_123 ((@IN A x s) /\ (@IN B y (t x))) (@pair A B x y))) (muln m n).
Axiom thm_FINITE_PRODUCT_DEPENDENT : forall {A B C : Type'}, forall f : A -> B -> C, forall s : A -> Prop, forall t : A -> B -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> @finite_set B (t x))) -> @finite_set C (@GSPEC C (fun GEN_PVAR_128 : C => exists x : A, exists y : B, @SETSPEC C GEN_PVAR_128 ((@IN A x s) /\ (@IN B y (t x))) (f x y))).
Axiom thm_FINITE_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> @finite_set (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_129 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_129 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y))).
Axiom thm_CARD_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@CARD (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_130 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_130 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y)))) = (muln (@CARD A s) (@CARD B t)).
Axiom thm_HAS_SIZE_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall m : nat, forall t : B -> Prop, forall n : nat, ((@HAS_SIZE A s m) /\ (@HAS_SIZE B t n)) -> @HAS_SIZE (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_131 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_131 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y))) (muln m n).
Axiom thm_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@CROSS A B s t) = (@GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y))).
Axiom thm_IN_CROSS : forall {A B : Type'}, forall x : A, forall y : B, forall s : A -> Prop, forall t : B -> Prop, (@IN (prod A B) (@pair A B x y) (@CROSS A B s t)) = ((@IN A x s) /\ (@IN B y t)).
Axiom thm_HAS_SIZE_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE A s m) /\ (@HAS_SIZE B t n)) -> @HAS_SIZE (prod A B) (@CROSS A B s t) (muln m n).
Axiom thm_FINITE_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> @finite_set (prod A B) (@CROSS A B s t).
Axiom thm_CARD_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@CARD (prod A B) (@CROSS A B s t)) = (muln (@CARD A s) (@CARD B t)).
Axiom thm_CROSS_EQ_EMPTY : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@CROSS A B s t) = (@set0 (prod A B))) = ((s = (@set0 A)) \/ (t = (@set0 B))).
Axiom thm_CROSS_EMPTY : forall {_98772 _98785 A B : Type'}, (forall s : A -> Prop, (@CROSS A _98772 s (@set0 _98772)) = (@set0 (prod A _98772))) /\ (forall t : B -> Prop, (@CROSS _98785 B (@set0 _98785) t) = (@set0 (prod _98785 B))).
Axiom thm_CROSS_SING : forall {A B : Type'}, forall x : A, forall y : B, (@CROSS A B (@INSERT A x (@set0 A)) (@INSERT B y (@set0 B))) = (@INSERT (prod A B) (@pair A B x y) (@set0 (prod A B))).
Axiom thm_CROSS_UNIV : forall {A B : Type'}, (@CROSS A B (@setT A) (@setT B)) = (@setT (prod A B)).
Axiom thm_FINITE_CROSS_EQ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@finite_set (prod A B) (@CROSS A B s t)) = ((s = (@set0 A)) \/ ((t = (@set0 B)) \/ ((@finite_set A s) /\ (@finite_set B t)))).
Axiom thm_INFINITE_CROSS_EQ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@INFINITE (prod A B) (@CROSS A B s t)) = (((~ (s = (@set0 A))) /\ (@INFINITE B t)) \/ ((@INFINITE A s) /\ (~ (t = (@set0 B))))).
Axiom thm_FINITE_CROSS_UNIV : forall {A B : Type'}, (@finite_set (prod A B) (@setT (prod A B))) = ((@finite_set A (@setT A)) /\ (@finite_set B (@setT B))).
Axiom thm_INFINITE_CROSS_UNIV : forall {A B : Type'}, (@INFINITE (prod A B) (@setT (prod A B))) = ((@INFINITE A (@setT A)) \/ (@INFINITE B (@setT B))).
Axiom thm_FINITE_UNIV_PAIR : forall {A : Type'}, (@finite_set (prod A A) (@setT (prod A A))) = (@finite_set A (@setT A)).
Axiom thm_INFINITE_UNIV_PAIR : forall {A : Type'}, (@INFINITE (prod A A) (@setT (prod A A))) = (@INFINITE A (@setT A)).
Axiom thm_FORALL_IN_CROSS : forall {A B : Type'}, forall P : (prod A B) -> Prop, forall s : A -> Prop, forall t : B -> Prop, (forall z : prod A B, (@IN (prod A B) z (@CROSS A B s t)) -> P z) = (forall x : A, forall y : B, ((@IN A x s) /\ (@IN B y t)) -> P (@pair A B x y)).
Axiom thm_EXISTS_IN_CROSS : forall {A B : Type'}, forall P : (prod A B) -> Prop, forall s : A -> Prop, forall t : B -> Prop, (exists z : prod A B, (@IN (prod A B) z (@CROSS A B s t)) /\ (P z)) = (exists x : A, exists y : B, (@IN A x s) /\ ((@IN B y t) /\ (P (@pair A B x y)))).
Axiom thm_SUBSET_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall s' : A -> Prop, forall t' : B -> Prop, (@subset (prod A B) (@CROSS A B s t) (@CROSS A B s' t')) = ((s = (@set0 A)) \/ ((t = (@set0 B)) \/ ((@subset A s s') /\ (@subset B t t')))).
Axiom thm_CROSS_MONO : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall s' : A -> Prop, forall t' : B -> Prop, ((@subset A s s') /\ (@subset B t t')) -> @subset (prod A B) (@CROSS A B s t) (@CROSS A B s' t').
Axiom thm_CROSS_EQ : forall {A B : Type'}, forall s : A -> Prop, forall s' : A -> Prop, forall t : B -> Prop, forall t' : B -> Prop, ((@CROSS A B s t) = (@CROSS A B s' t')) = ((((s = (@set0 A)) \/ (t = (@set0 B))) /\ ((s' = (@set0 A)) \/ (t' = (@set0 B)))) \/ ((s = s') /\ (t = t'))).
Axiom thm_IMAGE_FST_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@IMAGE (prod A B) A (@fst A B) (@CROSS A B s t)) = (@COND (A -> Prop) (t = (@set0 B)) (@set0 A) s).
Axiom thm_IMAGE_SND_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@IMAGE (prod A B) B (@snd A B) (@CROSS A B s t)) = (@COND (B -> Prop) (s = (@set0 A)) (@set0 B) t).
Axiom thm_IMAGE_PAIRED_CROSS : forall {A B C D : Type'}, forall f : A -> B, forall g : C -> D, forall s : A -> Prop, forall t : C -> Prop, (@IMAGE (prod A C) (prod B D) (@GABS ((prod A C) -> prod B D) (fun f' : (prod A C) -> prod B D => forall x : A, forall y : C, @eq (prod B D) (f' (@pair A C x y)) (@pair B D (f x) (g y)))) (@CROSS A C s t)) = (@CROSS B D (@IMAGE A B f s) (@IMAGE C D g t)).
Axiom thm_CROSS_INTER : forall {A B : Type'}, (forall s : A -> Prop, forall t : B -> Prop, forall u : B -> Prop, (@CROSS A B s (@setI B t u)) = (@setI (prod A B) (@CROSS A B s t) (@CROSS A B s u))) /\ (forall s : A -> Prop, forall t : A -> Prop, forall u : B -> Prop, (@CROSS A B (@setI A s t) u) = (@setI (prod A B) (@CROSS A B s u) (@CROSS A B t u))).
Axiom thm_CROSS_UNION : forall {A B : Type'}, (forall s : A -> Prop, forall t : B -> Prop, forall u : B -> Prop, (@CROSS A B s (@setU B t u)) = (@setU (prod A B) (@CROSS A B s t) (@CROSS A B s u))) /\ (forall s : A -> Prop, forall t : A -> Prop, forall u : B -> Prop, (@CROSS A B (@setU A s t) u) = (@setU (prod A B) (@CROSS A B s u) (@CROSS A B t u))).
Axiom thm_CROSS_DIFF : forall {A B : Type'}, (forall s : A -> Prop, forall t : B -> Prop, forall u : B -> Prop, (@CROSS A B s (@setD B t u)) = (@setD (prod A B) (@CROSS A B s t) (@CROSS A B s u))) /\ (forall s : A -> Prop, forall t : A -> Prop, forall u : B -> Prop, (@CROSS A B (@setD A s t) u) = (@setD (prod A B) (@CROSS A B s u) (@CROSS A B t u))).
Axiom thm_INTER_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall s' : A -> Prop, forall t : B -> Prop, forall t' : B -> Prop, (@setI (prod A B) (@CROSS A B s t) (@CROSS A B s' t')) = (@CROSS A B (@setI A s s') (@setI B t t')).
Axiom thm_CROSS_UNIONS : forall {A B : Type'}, (forall s : A -> Prop, forall f : (A -> Prop) -> Prop, (@CROSS A A s (@UNIONS A f)) = (@UNIONS (prod A A) (@GSPEC ((prod A A) -> Prop) (fun GEN_PVAR_134 : (prod A A) -> Prop => exists t : A -> Prop, @SETSPEC ((prod A A) -> Prop) GEN_PVAR_134 (@IN (A -> Prop) t f) (@CROSS A A s t))))) /\ (forall f : (A -> Prop) -> Prop, forall t : B -> Prop, (@CROSS A B (@UNIONS A f) t) = (@UNIONS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_135 : (prod A B) -> Prop => exists s : A -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_135 (@IN (A -> Prop) s f) (@CROSS A B s t))))).
Axiom thm_CROSS_UNIONS_UNIONS : forall {A B : Type'}, forall f : (A -> Prop) -> Prop, forall g : (B -> Prop) -> Prop, (@CROSS A B (@UNIONS A f) (@UNIONS B g)) = (@UNIONS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_133 : (prod A B) -> Prop => exists s : A -> Prop, exists t : B -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_133 ((@IN (A -> Prop) s f) /\ (@IN (B -> Prop) t g)) (@CROSS A B s t)))).
Axiom thm_CROSS_INTERS : forall {A B : Type'}, (forall s : A -> Prop, forall f : (A -> Prop) -> Prop, (@CROSS A A s (@INTERS A f)) = (@COND ((prod A A) -> Prop) (f = (@set0 (A -> Prop))) (@CROSS A A s (@setT A)) (@INTERS (prod A A) (@GSPEC ((prod A A) -> Prop) (fun GEN_PVAR_139 : (prod A A) -> Prop => exists t : A -> Prop, @SETSPEC ((prod A A) -> Prop) GEN_PVAR_139 (@IN (A -> Prop) t f) (@CROSS A A s t)))))) /\ (forall f : (A -> Prop) -> Prop, forall t : B -> Prop, (@CROSS A B (@INTERS A f) t) = (@COND ((prod A B) -> Prop) (f = (@set0 (A -> Prop))) (@CROSS A B (@setT A) t) (@INTERS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_140 : (prod A B) -> Prop => exists s : A -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_140 (@IN (A -> Prop) s f) (@CROSS A B s t)))))).
Axiom thm_CROSS_INTERS_INTERS : forall {A B : Type'}, forall f : (A -> Prop) -> Prop, forall g : (B -> Prop) -> Prop, (@CROSS A B (@INTERS A f) (@INTERS B g)) = (@COND ((prod A B) -> Prop) (f = (@set0 (A -> Prop))) (@INTERS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_136 : (prod A B) -> Prop => exists t : B -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_136 (@IN (B -> Prop) t g) (@CROSS A B (@setT A) t)))) (@COND ((prod A B) -> Prop) (g = (@set0 (B -> Prop))) (@INTERS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_137 : (prod A B) -> Prop => exists s : A -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_137 (@IN (A -> Prop) s f) (@CROSS A B s (@setT B))))) (@INTERS (prod A B) (@GSPEC ((prod A B) -> Prop) (fun GEN_PVAR_138 : (prod A B) -> Prop => exists s : A -> Prop, exists t : B -> Prop, @SETSPEC ((prod A B) -> Prop) GEN_PVAR_138 ((@IN (A -> Prop) s f) /\ (@IN (B -> Prop) t g)) (@CROSS A B s t)))))).
Axiom thm_DISJOINT_CROSS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall s' : A -> Prop, forall t' : B -> Prop, (@DISJOINT (prod A B) (@CROSS A B s t) (@CROSS A B s' t')) = ((@DISJOINT A s s') \/ (@DISJOINT B t t')).
Axiom thm_ARB : forall {A : Type'}, (@ARB A) = (@ε A (fun x : A => False)).
Axiom thm_EXTENSIONAL : forall {A B : Type'}, forall s : A -> Prop, (@EXTENSIONAL A B s) = (@GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x s)) -> (f x) = (@ARB B)) f)).
Axiom thm_IN_EXTENSIONAL : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@IN (A -> B) f (@EXTENSIONAL A B s)) = (forall x : A, (~ (@IN A x s)) -> (f x) = (@ARB B)).
Axiom thm_IN_EXTENSIONAL_UNDEFINED : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, ((@IN (A -> B) f (@EXTENSIONAL A B s)) /\ (~ (@IN A x s))) -> (f x) = (@ARB B).
Axiom thm_EXTENSIONAL_EMPTY : forall {A B : Type'}, (@EXTENSIONAL A B (@set0 A)) = (@INSERT (A -> B) (fun x : A => @ARB B) (@set0 (A -> B))).
Axiom thm_EXTENSIONAL_UNIV : forall {A B : Type'}, forall f : A -> B, @EXTENSIONAL A B (@setT A) f.
Axiom thm_EXTENSIONAL_EQ : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, ((@IN (A -> B) f (@EXTENSIONAL A B s)) /\ ((@IN (A -> B) g (@EXTENSIONAL A B s)) /\ (forall x : A, (@IN A x s) -> (f x) = (g x)))) -> f = g.
Axiom thm_RESTRICTION : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, (@RESTRICTION A B s f x) = (@COND B (@IN A x s) (f x) (@ARB B)).
Axiom thm_RESTRICTION_THM : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@RESTRICTION A B s f) = (fun x : A => @COND B (@IN A x s) (f x) (@ARB B)).
Axiom thm_RESTRICTION_DEFINED : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, (@IN A x s) -> (@RESTRICTION A B s f x) = (f x).
Axiom thm_RESTRICTION_UNDEFINED : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, (~ (@IN A x s)) -> (@RESTRICTION A B s f x) = (@ARB B).
Axiom thm_RESTRICTION_EQ : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, forall y : B, ((@IN A x s) /\ ((f x) = y)) -> (@RESTRICTION A B s f x) = y.
Axiom thm_RESTRICTION_IN_EXTENSIONAL : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, @IN (A -> B) (@RESTRICTION A B s f) (@EXTENSIONAL A B s).
Axiom thm_RESTRICTION_EXTENSION : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, ((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (forall x : A, (@IN A x s) -> (f x) = (g x)).
Axiom thm_RESTRICTION_FIXPOINT : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, ((@RESTRICTION A B s f) = f) = (@IN (A -> B) f (@EXTENSIONAL A B s)).
Axiom thm_RESTRICTION_UNIV : forall {A B : Type'}, forall f : A -> B, (@RESTRICTION A B (@setT A) f) = f.
Axiom thm_RESTRICTION_RESTRICTION : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall f : A -> B, (@subset A s t) -> (@RESTRICTION A B s (@RESTRICTION A B t f)) = (@RESTRICTION A B s f).
Axiom thm_RESTRICTION_IDEMP : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@RESTRICTION A B s (@RESTRICTION A B s f)) = (@RESTRICTION A B s f).
Axiom thm_IMAGE_RESTRICTION : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, (@subset A s t) -> (@IMAGE A B (@RESTRICTION A B t f) s) = (@IMAGE A B f s).
Axiom thm_RESTRICTION_COMPOSE_RIGHT : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall s : A -> Prop, (@RESTRICTION A C s (@o A B C g (@RESTRICTION A B s f))) = (@RESTRICTION A C s (@o A B C g f)).
Axiom thm_RESTRICTION_COMPOSE_LEFT : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall s : A -> Prop, forall t : B -> Prop, (@subset B (@IMAGE A B f s) t) -> (@RESTRICTION A C s (@o A B C (@RESTRICTION B C t g) f)) = (@RESTRICTION A C s (@o A B C g f)).
Axiom thm_RESTRICTION_COMPOSE : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall s : A -> Prop, forall t : B -> Prop, (@subset B (@IMAGE A B f s) t) -> (@RESTRICTION A C s (@o A B C (@RESTRICTION B C t g) (@RESTRICTION A B s f))) = (@RESTRICTION A C s (@o A B C g f)).
Axiom thm_RESTRICTION_UNIQUE : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, ((@RESTRICTION A B s f) = g) = ((@EXTENSIONAL A B s g) /\ (forall x : A, (@IN A x s) -> (f x) = (g x))).
Axiom thm_RESTRICTION_UNIQUE_ALT : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, (f = (@RESTRICTION A B s g)) = ((@EXTENSIONAL A B s f) /\ (forall x : A, (@IN A x s) -> (f x) = (g x))).
Axiom thm_cartesian_product : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@cartesian_product A K k s) = (@GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A k f) /\ (forall i : K, (@IN K i k) -> @IN A (f i) (s i))) f)).
Axiom thm_IN_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall x : K -> A, (@IN (K -> A) x (@cartesian_product A K k s)) = ((@EXTENSIONAL K A k x) /\ (forall i : K, (@IN K i k) -> @IN A (x i) (s i))).
Axiom thm_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@cartesian_product A K k s) = (@GSPEC (K -> A) (fun GEN_PVAR_143 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_143 (forall i : K, @IN A (f i) (@COND (A -> Prop) (@IN K i k) (s i) (@INSERT A (@ARB A) (@set0 A)))) f)).
Axiom thm_RESTRICTION_IN_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall f : K -> A, (@IN (K -> A) (@RESTRICTION K A k f) (@cartesian_product A K k s)) = (forall i : K, (@IN K i k) -> @IN A (f i) (s i)).
Axiom thm_CARTESIAN_PRODUCT_AS_RESTRICTIONS : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@cartesian_product A K k s) = (@GSPEC (K -> A) (fun GEN_PVAR_144 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_144 (forall i : K, (@IN K i k) -> @IN A (f i) (s i)) (@RESTRICTION K A k f))).
Axiom thm_CARTESIAN_PRODUCT_EQ_EMPTY : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, ((@cartesian_product A K k s) = (@set0 (K -> A))) = (exists i : K, (@IN K i k) /\ ((s i) = (@set0 A))).
Axiom thm_CARTESIAN_PRODUCT_EMPTY : forall {A K : Type'}, forall s : K -> A -> Prop, (@cartesian_product A K (@set0 K) s) = (@INSERT (K -> A) (fun i : K => @ARB A) (@set0 (K -> A))).
Axiom thm_CARTESIAN_PRODUCT_EQ_MEMBERS : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall x : K -> A, forall y : K -> A, ((@IN (K -> A) x (@cartesian_product A K k s)) /\ ((@IN (K -> A) y (@cartesian_product A K k s)) /\ (forall i : K, (@IN K i k) -> (x i) = (y i)))) -> x = y.
Axiom thm_CARTESIAN_PRODUCT_EQ_MEMBERS_EQ : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall x : K -> A, forall y : K -> A, ((@IN (K -> A) x (@cartesian_product A K k s)) /\ (@IN (K -> A) y (@cartesian_product A K k s))) -> (x = y) = (forall i : K, (@IN K i k) -> (x i) = (y i)).
Axiom thm_SUBSET_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@subset (K -> A) (@cartesian_product A K k s) (@cartesian_product A K k t)) = (((@cartesian_product A K k s) = (@set0 (K -> A))) \/ (forall i : K, (@IN K i k) -> @subset A (s i) (t i))).
Axiom thm_CARTESIAN_PRODUCT_EQ : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = ((((@cartesian_product A K k s) = (@set0 (K -> A))) /\ ((@cartesian_product A K k t) = (@set0 (K -> A)))) \/ (forall i : K, (@IN K i k) -> (s i) = (t i))).
Axiom thm_INTER_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@setI (K -> A) (@cartesian_product A K k s) (@cartesian_product A K k t)) = (@cartesian_product A K k (fun i : K => @setI A (s i) (t i))).
Axiom thm_CARTESIAN_PRODUCT_UNIV : forall {A K : Type'}, (@cartesian_product A K (@setT K) (fun i : K => @setT A)) = (@setT (K -> A)).
Axiom thm_CARTESIAN_PRODUCT_SINGS : forall {A K : Type'}, forall k : K -> Prop, forall x : K -> A, (@EXTENSIONAL K A k x) -> (@cartesian_product A K k (fun i : K => @INSERT A (x i) (@set0 A))) = (@INSERT (K -> A) x (@set0 (K -> A))).
Axiom thm_CARTESIAN_PRODUCT_SINGS_GEN : forall {A K : Type'}, forall k : K -> Prop, forall x : K -> A, (@cartesian_product A K k (fun i : K => @INSERT A (x i) (@set0 A))) = (@INSERT (K -> A) (@RESTRICTION K A k x) (@set0 (K -> A))).
Axiom thm_IMAGE_PROJECTION_CARTESIAN_PRODUCT : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall i : K, (@IMAGE (K -> A) A (fun x : K -> A => x i) (@cartesian_product A K k s)) = (@COND (A -> Prop) ((@cartesian_product A K k s) = (@set0 (K -> A))) (@set0 A) (@COND (A -> Prop) (@IN K i k) (s i) (@INSERT A (@ARB A) (@set0 A)))).
Axiom thm_FORALL_CARTESIAN_PRODUCT_ELEMENTS : forall {A K : Type'}, forall P : K -> A -> Prop, forall k : K -> Prop, forall s : K -> A -> Prop, (forall z : K -> A, forall i : K, ((@IN (K -> A) z (@cartesian_product A K k s)) /\ (@IN K i k)) -> P i (z i)) = (((@cartesian_product A K k s) = (@set0 (K -> A))) \/ (forall i : K, forall x : A, ((@IN K i k) /\ (@IN A x (s i))) -> P i x)).
Axiom thm_FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ : forall {A K : Type'}, forall P : K -> A -> Prop, forall k : K -> Prop, forall s : K -> A -> Prop, (~ ((@cartesian_product A K k s) = (@set0 (K -> A)))) -> (forall i : K, forall x : A, ((@IN K i k) /\ (@IN A x (s i))) -> P i x) = (forall z : K -> A, forall i : K, ((@IN (K -> A) z (@cartesian_product A K k s)) /\ (@IN K i k)) -> P i (z i)).
Axiom thm_EXISTS_CARTESIAN_PRODUCT_ELEMENT : forall {A K : Type'}, forall P : K -> A -> Prop, forall k : K -> Prop, forall s : K -> A -> Prop, (exists z : K -> A, (@IN (K -> A) z (@cartesian_product A K k s)) /\ (forall i : K, (@IN K i k) -> P i (z i))) = (forall i : K, (@IN K i k) -> exists x : A, (@IN A x (s i)) /\ (P i x)).
Axiom thm_product_map : forall {A B K : Type'}, forall k : K -> Prop, forall f : K -> A -> B, (@product_map A B K k f) = (fun x : K -> A => @RESTRICTION K B k (fun i : K => f i (x i))).
Axiom thm_PRODUCT_MAP_RESTRICTION : forall {A B K : Type'}, forall f : K -> A -> B, forall k : K -> Prop, forall x : K -> A, (@product_map A B K k f (@RESTRICTION K A k x)) = (@RESTRICTION K B k (fun i : K => f i (x i))).
Axiom thm_IMAGE_PRODUCT_MAP : forall {A B K : Type'}, forall f : K -> A -> B, forall k : K -> Prop, forall s : K -> A -> Prop, (@IMAGE (K -> A) (K -> B) (@product_map A B K k f) (@cartesian_product A K k s)) = (@cartesian_product B K k (fun i : K => @IMAGE A B (f i) (s i))).
Axiom thm_disjoint_union : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@disjoint_union A K k s) = (@GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i k) /\ (@IN A x (s i))) (@pair K A i x))).
Axiom thm_SUBSET_DISJOINT_UNION : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@subset (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (forall i : K, (@IN K i k) -> @subset A (s i) (t i)).
Axiom thm_DISJOINT_UNION_EQ : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, ((@disjoint_union A K k s) = (@disjoint_union A K k t)) = (forall i : K, (@IN K i k) -> (s i) = (t i)).
Axiom thm_SUBSET_DISJOINT_UNION_EXISTS : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall u : (prod K A) -> Prop, (@subset (prod K A) u (@disjoint_union A K k s)) = (exists t : K -> A -> Prop, (u = (@disjoint_union A K k t)) /\ (forall i : K, (@IN K i k) -> @subset A (t i) (s i))).
Axiom thm_INTER_DISJOINT_UNION : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@setI (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (@disjoint_union A K k (fun i : K => @setI A (s i) (t i))).
Axiom thm_UNION_DISJOINT_UNION : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@setU (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (@disjoint_union A K k (fun i : K => @setU A (s i) (t i))).
Axiom thm_DISJOINT_UNION_EQ_EMPTY : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, ((@disjoint_union A K k s) = (@set0 (prod K A))) = (forall i : K, (@IN K i k) -> (s i) = (@set0 A)).
Axiom thm_DISJOINT_DISJOINT_UNION : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, forall t : K -> A -> Prop, (@DISJOINT (prod K A) (@disjoint_union A K k s) (@disjoint_union A K k t)) = (forall i : K, (@IN K i k) -> @DISJOINT A (s i) (t i)).
Axiom thm_HAS_SIZE_FUNSPACE : forall {A B : Type'}, forall d : B, forall n : nat, forall t : B -> Prop, forall m : nat, forall s : A -> Prop, ((@HAS_SIZE A s m) /\ (@HAS_SIZE B t n)) -> @HAS_SIZE (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_150 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_150 ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, (~ (@IN A x s)) -> (f x) = d)) f)) (expn n m).
Axiom thm_CARD_FUNSPACE : forall {A B : Type'} (d : B), forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@CARD (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_151 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_151 ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, (~ (@IN A x s)) -> (f x) = d)) f))) = (expn (@CARD B t) (@CARD A s)).
Axiom thm_FINITE_FUNSPACE : forall {A B : Type'} (d : B), forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> @finite_set (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_152 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_152 ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, (~ (@IN A x s)) -> (f x) = d)) f)).
Axiom thm_HAS_SIZE_FUNSPACE_UNIV : forall {A B : Type'}, forall m : nat, forall n : nat, ((@HAS_SIZE A (@setT A) m) /\ (@HAS_SIZE B (@setT B) n)) -> @HAS_SIZE (A -> B) (@setT (A -> B)) (expn n m).
Axiom thm_CARD_FUNSPACE_UNIV : forall {A B : Type'}, ((@finite_set A (@setT A)) /\ (@finite_set B (@setT B))) -> (@CARD (A -> B) (@setT (A -> B))) = (expn (@CARD B (@setT B)) (@CARD A (@setT A))).
Axiom thm_FINITE_FUNSPACE_UNIV : forall {A B : Type'}, ((@finite_set A (@setT A)) /\ (@finite_set B (@setT B))) -> @finite_set (A -> B) (@setT (A -> B)).
Axiom thm_HAS_SIZE_BOOL : @HAS_SIZE Prop (@setT Prop) (NUMERAL (BIT0 (BIT1 O))).
Axiom thm_CARD_BOOL : (@CARD Prop (@setT Prop)) = (NUMERAL (BIT0 (BIT1 O))).
Axiom thm_FINITE_BOOL : @finite_set Prop (@setT Prop).
Axiom thm_HAS_SIZE_POWERSET : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@HAS_SIZE A s n) -> @HAS_SIZE (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_155 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_155 (@subset A t s) t)) (expn (NUMERAL (BIT0 (BIT1 O))) n).
Axiom thm_CARD_POWERSET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (@CARD (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_156 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_156 (@subset A t s) t))) = (expn (NUMERAL (BIT0 (BIT1 O))) (@CARD A s)).
Axiom thm_FINITE_POWERSET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> @finite_set (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_157 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_157 (@subset A t s) t)).
Axiom thm_FINITE_POWERSET_EQ : forall {A : Type'}, forall s : A -> Prop, (@finite_set (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_158 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_158 (@subset A t s) t))) = (@finite_set A s).
Axiom thm_FINITE_RESTRICTED_SUBSETS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@finite_set A s) -> @finite_set (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_160 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_160 ((@subset A t s) /\ (P t)) t)).
Axiom thm_FINITE_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@finite_set A (@UNIONS A s)) = ((@finite_set (A -> Prop) s) /\ (forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t)).
Axiom thm_FINITE_CARD_LE_UNIONS : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall m : nat, forall n : nat, ((forall x : A, (@IN A x s) -> (@finite_set B (t x)) /\ (leqn (@CARD B (t x)) n)) /\ ((@finite_set A s) /\ (leqn (@CARD A s) m))) -> (@finite_set B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_161 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_161 (@IN A x s) (t x))))) /\ (leqn (@CARD B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_162 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_162 (@IN A x s) (t x))))) (muln m n)).
Axiom thm_POWERSET_CLAUSES : forall {A : Type'}, ((@GSPEC (A -> Prop) (fun GEN_PVAR_163 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_163 (@subset A s (@set0 A)) s)) = (@INSERT (A -> Prop) (@set0 A) (@set0 (A -> Prop)))) /\ (forall a : A, forall t : A -> Prop, (@GSPEC (A -> Prop) (fun GEN_PVAR_164 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_164 (@subset A s (@INSERT A a t)) s)) = (@setU (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_165 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_165 (@subset A s t) s)) (@IMAGE (A -> Prop) (A -> Prop) (fun s : A -> Prop => @INSERT A a s) (@GSPEC (A -> Prop) (fun GEN_PVAR_166 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_166 (@subset A s t) s))))).
Axiom thm_FINITE_IMAGE_INFINITE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((@INFINITE A s) /\ (@finite_set B (@IMAGE A B f s))) -> exists a : A, (@IN A a s) /\ (@INFINITE A (@GSPEC A (fun GEN_PVAR_171 : A => exists x : A, @SETSPEC A GEN_PVAR_171 ((@IN A x s) /\ ((f x) = (f a))) x))).
Axiom thm_FINITE_RESTRICTED_POWERSET : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@finite_set (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_176 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_176 ((@subset A t s) /\ (@HAS_SIZE A t n)) t))) = ((@finite_set A s) \/ (n = (NUMERAL O))).
Axiom thm_FINITE_RESTRICTED_FUNSPACE : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall k : A -> B, ((@finite_set A s) /\ (@finite_set B t)) -> @finite_set (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_180 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_180 ((@subset B (@IMAGE A B f s) t) /\ (@subset A (@GSPEC A (fun GEN_PVAR_179 : A => exists x : A, @SETSPEC A GEN_PVAR_179 (~ ((f x) = (k x))) x)) s)) f)).
Axiom thm_NUMSEG_CLAUSES_LT : ((@GSPEC nat (fun GEN_PVAR_181 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_181 (ltn i (NUMERAL O)) i)) = (@set0 nat)) /\ (forall k : nat, (@GSPEC nat (fun GEN_PVAR_182 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_182 (ltn i (S k)) i)) = (@INSERT nat k (@GSPEC nat (fun GEN_PVAR_183 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_183 (ltn i k) i)))).
Axiom thm_HAS_SIZE_NUMSEG_LT : forall n : nat, @HAS_SIZE nat (@GSPEC nat (fun GEN_PVAR_184 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_184 (ltn m n) m)) n.
Axiom thm_CARD_NUMSEG_LT : forall n : nat, (@CARD nat (@GSPEC nat (fun GEN_PVAR_185 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_185 (ltn m n) m))) = n.
Axiom thm_FINITE_NUMSEG_LT : forall n : nat, @finite_set nat (@GSPEC nat (fun GEN_PVAR_186 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_186 (ltn m n) m)).
Axiom thm_NUMSEG_CLAUSES_LE : ((@GSPEC nat (fun GEN_PVAR_187 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_187 (leqn i (NUMERAL O)) i)) = (@INSERT nat (NUMERAL O) (@set0 nat))) /\ (forall k : nat, (@GSPEC nat (fun GEN_PVAR_188 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_188 (leqn i (S k)) i)) = (@INSERT nat (S k) (@GSPEC nat (fun GEN_PVAR_189 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_189 (leqn i k) i)))).
Axiom thm_HAS_SIZE_NUMSEG_LE : forall n : nat, @HAS_SIZE nat (@GSPEC nat (fun GEN_PVAR_190 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_190 (leqn m n) m)) (addn n (NUMERAL (BIT1 O))).
Axiom thm_FINITE_NUMSEG_LE : forall n : nat, @finite_set nat (@GSPEC nat (fun GEN_PVAR_191 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_191 (leqn m n) m)).
Axiom thm_CARD_NUMSEG_LE : forall n : nat, (@CARD nat (@GSPEC nat (fun GEN_PVAR_192 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_192 (leqn m n) m))) = (addn n (NUMERAL (BIT1 O))).
Axiom thm_num_FINITE : forall s : nat -> Prop, (@finite_set nat s) = (exists a : nat, forall x : nat, (@IN nat x s) -> leqn x a).
Axiom thm_num_FINITE_AVOID : forall s : nat -> Prop, (@finite_set nat s) -> exists a : nat, ~ (@IN nat a s).
Axiom thm_num_INFINITE_EQ : forall s : nat -> Prop, (@INFINITE nat s) = (forall N' : nat, exists n : nat, (leqn N' n) /\ (@IN nat n s)).
Axiom thm_num_INFINITE : @INFINITE nat (@setT nat).
Axiom thm_string_INFINITE : @INFINITE (seq Ascii.ascii) (@setT (seq Ascii.ascii)).
Axiom thm_FINITE_REAL_INTERVAL : (forall a : R, ~ (@finite_set R (@GSPEC R (fun GEN_PVAR_202 : R => exists x : R, @SETSPEC R GEN_PVAR_202 (ltr a x) x)))) /\ ((forall a : R, ~ (@finite_set R (@GSPEC R (fun GEN_PVAR_203 : R => exists x : R, @SETSPEC R GEN_PVAR_203 (ler a x) x)))) /\ ((forall b : R, ~ (@finite_set R (@GSPEC R (fun GEN_PVAR_204 : R => exists x : R, @SETSPEC R GEN_PVAR_204 (ltr x b) x)))) /\ ((forall b : R, ~ (@finite_set R (@GSPEC R (fun GEN_PVAR_205 : R => exists x : R, @SETSPEC R GEN_PVAR_205 (ler x b) x)))) /\ ((forall a : R, forall b : R, (@finite_set R (@GSPEC R (fun GEN_PVAR_206 : R => exists x : R, @SETSPEC R GEN_PVAR_206 ((ltr a x) /\ (ltr x b)) x))) = (ler b a)) /\ ((forall a : R, forall b : R, (@finite_set R (@GSPEC R (fun GEN_PVAR_207 : R => exists x : R, @SETSPEC R GEN_PVAR_207 ((ler a x) /\ (ltr x b)) x))) = (ler b a)) /\ ((forall a : R, forall b : R, (@finite_set R (@GSPEC R (fun GEN_PVAR_208 : R => exists x : R, @SETSPEC R GEN_PVAR_208 ((ltr a x) /\ (ler x b)) x))) = (ler b a)) /\ (forall a : R, forall b : R, (@finite_set R (@GSPEC R (fun GEN_PVAR_209 : R => exists x : R, @SETSPEC R GEN_PVAR_209 ((ler a x) /\ (ler x b)) x))) = (ler b a)))))))).
Axiom thm_real_INFINITE : @INFINITE R (@setT R).
Axiom thm_HAS_SIZE_INDEX : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@HAS_SIZE A s n) -> exists f : nat -> A, (forall m : nat, (ltn m n) -> @IN A (f m) s) /\ (forall x : A, (@IN A x s) -> @ex1 nat (fun m : nat => (ltn m n) /\ ((f m) = x))).
Axiom thm_INFINITE_ENUMERATE : forall s : nat -> Prop, (@INFINITE nat s) -> exists r : nat -> nat, (forall m : nat, forall n : nat, (ltn m n) -> ltn (r m) (r n)) /\ ((@IMAGE nat nat r (@setT nat)) = s).
Axiom thm_INFINITE_ENUMERATE_EQ : forall s : nat -> Prop, (@INFINITE nat s) = (exists r : nat -> nat, (forall m : nat, forall n : nat, (ltn m n) -> ltn (r m) (r n)) /\ ((@IMAGE nat nat r (@setT nat)) = s)).
Axiom thm_INFINITE_ENUMERATE_SUBSET : forall {A : Type'}, forall s : A -> Prop, (@INFINITE A s) = (exists f : nat -> A, (forall x : nat, @IN A (f x) s) /\ (forall x : nat, forall y : nat, ((f x) = (f y)) -> x = y)).
Axiom thm_set_of_list : forall {A : Type'} (h : A) (t : seq A), ((@set_of_list A (@nil A)) = (@set0 A)) /\ ((@set_of_list A (@cons A h t)) = (@INSERT A h (@set_of_list A t))).
Axiom thm_list_of_set : forall {A : Type'}, forall s : A -> Prop, (@list_of_set A s) = (@ε (seq A) (fun l : seq A => ((@set_of_list A l) = s) /\ ((@size A l) = (@CARD A s)))).
Axiom thm_LIST_OF_SET_PROPERTIES : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> ((@set_of_list A (@list_of_set A s)) = s) /\ ((@size A (@list_of_set A s)) = (@CARD A s)).
Axiom thm_SET_OF_LIST_OF_SET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (@set_of_list A (@list_of_set A s)) = s.
Axiom thm_LENGTH_LIST_OF_SET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (@size A (@list_of_set A s)) = (@CARD A s).
Axiom thm_MEM_LIST_OF_SET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> forall x : A, (@MEM A x (@list_of_set A s)) = (@IN A x s).
Axiom thm_FINITE_SET_OF_LIST : forall {A : Type'}, forall l : seq A, @finite_set A (@set_of_list A l).
Axiom thm_IN_SET_OF_LIST : forall {A : Type'}, forall x : A, forall l : seq A, (@IN A x (@set_of_list A l)) = (@MEM A x l).
Axiom thm_SET_OF_LIST_APPEND : forall {A : Type'}, forall l1 : seq A, forall l2 : seq A, (@set_of_list A (@cat A l1 l2)) = (@setU A (@set_of_list A l1) (@set_of_list A l2)).
Axiom thm_SET_OF_LIST_MAP : forall {A B : Type'}, forall f : A -> B, forall l : seq A, (@set_of_list B (@map A B f l)) = (@IMAGE A B f (@set_of_list A l)).
Axiom thm_SET_OF_LIST_EQ_EMPTY : forall {A : Type'}, forall l : seq A, ((@set_of_list A l) = (@set0 A)) = (l = (@nil A)).
Axiom thm_LIST_OF_SET_EMPTY : forall {A : Type'}, (@list_of_set A (@set0 A)) = (@nil A).
Axiom thm_LIST_OF_SET_SING : forall {A : Type'}, forall a : A, (@list_of_set A (@INSERT A a (@set0 A))) = (@cons A a (@nil A)).
Axiom thm_pairwise : forall {A : Type'}, forall s : A -> Prop, forall r : A -> A -> Prop, (@pairwise A r s) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ (~ (x = y)))) -> r x y).
Axiom thm_PAIRWISE_EMPTY : forall {A : Type'}, forall r : A -> A -> Prop, (@pairwise A r (@set0 A)) = True.
Axiom thm_PAIRWISE_SING : forall {A : Type'}, forall r : A -> A -> Prop, forall x : A, (@pairwise A r (@INSERT A x (@set0 A))) = True.
Axiom thm_PAIRWISE_IMP : forall {A : Type'}, forall P : A -> A -> Prop, forall Q : A -> A -> Prop, forall s : A -> Prop, ((@pairwise A P s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((P x y) /\ (~ (x = y))))) -> Q x y)) -> @pairwise A Q s.
Axiom thm_PAIRWISE_MONO : forall {A : Type'}, forall r : A -> A -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@pairwise A r s) /\ (@subset A t s)) -> @pairwise A r t.
Axiom thm_PAIRWISE_AND : forall {A : Type'}, forall R' : A -> A -> Prop, forall R'' : A -> A -> Prop, forall s : A -> Prop, ((@pairwise A R' s) /\ (@pairwise A R'' s)) = (@pairwise A (fun x : A => fun y : A => (R' x y) /\ (R'' x y)) s).
Axiom thm_PAIRWISE_INSERT : forall {A : Type'}, forall r : A -> A -> Prop, forall x : A, forall s : A -> Prop, (@pairwise A r (@INSERT A x s)) = ((forall y : A, ((@IN A y s) /\ (~ (y = x))) -> (r x y) /\ (r y x)) /\ (@pairwise A r s)).
Axiom thm_PAIRWISE_INSERT_SYMMETRIC : forall {A : Type'}, forall r : A -> A -> Prop, forall x : A, forall s : A -> Prop, (forall y : A, (@IN A y s) -> (r x y) = (r y x)) -> (@pairwise A r (@INSERT A x s)) = ((forall y : A, ((@IN A y s) /\ (~ (y = x))) -> r x y) /\ (@pairwise A r s)).
Axiom thm_PAIRWISE_IMAGE : forall {A B : Type'} (s : A -> Prop), forall r : B -> B -> Prop, forall f : A -> B, (@pairwise B r (@IMAGE A B f s)) = (@pairwise A (fun x : A => fun y : A => (~ ((f x) = (f y))) -> r (f x) (f y)) s).
Axiom thm_PAIRWISE_UNION : forall {A : Type'}, forall R' : A -> A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (@pairwise A R' (@setU A s t)) = ((@pairwise A R' s) /\ ((@pairwise A R' t) /\ (forall x : A, forall y : A, ((@IN A x (@setD A s t)) /\ (@IN A y (@setD A t s))) -> (R' x y) /\ (R' y x)))).
Axiom thm_PAIRWISE_CHAIN_UNIONS : forall {A : Type'}, forall R' : A -> A -> Prop, forall c : (A -> Prop) -> Prop, ((forall s : A -> Prop, (@IN (A -> Prop) s c) -> @pairwise A R' s) /\ (forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s c) /\ (@IN (A -> Prop) t c)) -> (@subset A s t) \/ (@subset A t s))) -> @pairwise A R' (@UNIONS A c).
Axiom thm_DIFF_UNIONS_PAIRWISE_DISJOINT : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, ((@pairwise (A -> Prop) (@DISJOINT A) s) /\ (@subset (A -> Prop) t s)) -> (@setD A (@UNIONS A s) (@UNIONS A t)) = (@UNIONS A (@setD (A -> Prop) s t)).
Axiom thm_INTER_UNIONS_PAIRWISE_DISJOINT : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall t : (A -> Prop) -> Prop, (@pairwise (A -> Prop) (@DISJOINT A) (@setU (A -> Prop) s t)) -> (@setI A (@UNIONS A s) (@UNIONS A t)) = (@UNIONS A (@setI (A -> Prop) s t)).
Axiom thm_PSUBSET_UNIONS_PAIRWISE_DISJOINT : forall {A : Type'}, forall u : (A -> Prop) -> Prop, forall v : (A -> Prop) -> Prop, ((@pairwise (A -> Prop) (@DISJOINT A) v) /\ (@proper (A -> Prop) u (@DELETE (A -> Prop) v (@set0 A)))) -> @proper A (@UNIONS A u) (@UNIONS A v).
Axiom thm_UNION_OF : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (@UNION_OF A P Q) = (fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (P u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> Q c) /\ ((@UNIONS A u) = s))).
Axiom thm_INTERSECTION_OF : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (@INTERSECTION_OF A P Q) = (fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (P u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> Q c) /\ ((@INTERS A u) = s))).
Axiom thm_UNION_OF_INC : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall s : A -> Prop, ((P (@INSERT (A -> Prop) s (@set0 (A -> Prop)))) /\ (Q s)) -> @UNION_OF A P Q s.
Axiom thm_INTERSECTION_OF_INC : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall s : A -> Prop, ((P (@INSERT (A -> Prop) s (@set0 (A -> Prop)))) /\ (Q s)) -> @INTERSECTION_OF A P Q s.
Axiom thm_UNION_OF_MONO : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall Q' : (A -> Prop) -> Prop, forall s : A -> Prop, ((@UNION_OF A P Q s) /\ (forall x : A -> Prop, (Q x) -> Q' x)) -> @UNION_OF A P Q' s.
Axiom thm_INTERSECTION_OF_MONO : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall Q' : (A -> Prop) -> Prop, forall s : A -> Prop, ((@INTERSECTION_OF A P Q s) /\ (forall x : A -> Prop, (Q x) -> Q' x)) -> @INTERSECTION_OF A P Q' s.
Axiom thm_FORALL_UNION_OF : forall {A : Type'} (P : ((A -> Prop) -> Prop) -> Prop) (Q : (A -> Prop) -> Prop) (R' : (A -> Prop) -> Prop), (forall s : A -> Prop, (@UNION_OF A P Q s) -> R' s) = (forall t : (A -> Prop) -> Prop, ((P t) /\ (forall c : A -> Prop, (@IN (A -> Prop) c t) -> Q c)) -> R' (@UNIONS A t)).
Axiom thm_FORALL_INTERSECTION_OF : forall {A : Type'} (P : ((A -> Prop) -> Prop) -> Prop) (Q : (A -> Prop) -> Prop) (R' : (A -> Prop) -> Prop), (forall s : A -> Prop, (@INTERSECTION_OF A P Q s) -> R' s) = (forall t : (A -> Prop) -> Prop, ((P t) /\ (forall c : A -> Prop, (@IN (A -> Prop) c t) -> Q c)) -> R' (@INTERS A t)).
Axiom thm_UNION_OF_EMPTY : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (P (@set0 (A -> Prop))) -> @UNION_OF A P Q (@set0 A).
Axiom thm_INTERSECTION_OF_EMPTY : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (P (@set0 (A -> Prop))) -> @INTERSECTION_OF A P Q (@setT A).
Axiom thm_ARBITRARY : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@ARBITRARY A s) = True.
Axiom thm_ARBITRARY_UNION_OF_ALT : forall {A : Type'}, forall B : (A -> Prop) -> Prop, forall s : A -> Prop, (@UNION_OF A (@ARBITRARY A) B s) = (forall x : A, (@IN A x s) -> exists u : A -> Prop, (@IN (A -> Prop) u B) /\ ((@IN A x u) /\ (@subset A u s))).
Axiom thm_ARBITRARY_UNION_OF_EMPTY : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @UNION_OF A (@ARBITRARY A) P (@set0 A).
Axiom thm_ARBITRARY_INTERSECTION_OF_EMPTY : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @INTERSECTION_OF A (@ARBITRARY A) P (@setT A).
Axiom thm_ARBITRARY_UNION_OF_INC : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (P s) -> @UNION_OF A (@ARBITRARY A) P s.
Axiom thm_ARBITRARY_INTERSECTION_OF_INC : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (P s) -> @INTERSECTION_OF A (@ARBITRARY A) P s.
Axiom thm_ARBITRARY_UNION_OF_COMPLEMENT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@UNION_OF A (@ARBITRARY A) P s) = (@INTERSECTION_OF A (@ARBITRARY A) (fun s' : A -> Prop => P (@setD A (@setT A) s')) (@setD A (@setT A) s)).
Axiom thm_ARBITRARY_INTERSECTION_OF_COMPLEMENT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@INTERSECTION_OF A (@ARBITRARY A) P s) = (@UNION_OF A (@ARBITRARY A) (fun s' : A -> Prop => P (@setD A (@setT A) s')) (@setD A (@setT A) s)).
Axiom thm_ARBITRARY_UNION_OF_IDEMPOT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@UNION_OF A (@ARBITRARY A) (@UNION_OF A (@ARBITRARY A) P)) = (@UNION_OF A (@ARBITRARY A) P).
Axiom thm_ARBITRARY_INTERSECTION_OF_IDEMPOT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@INTERSECTION_OF A (@ARBITRARY A) (@INTERSECTION_OF A (@ARBITRARY A) P)) = (@INTERSECTION_OF A (@ARBITRARY A) P).
Axiom thm_ARBITRARY_UNION_OF_UNIONS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @UNION_OF A (@ARBITRARY A) P s) -> @UNION_OF A (@ARBITRARY A) P (@UNIONS A u).
Axiom thm_ARBITRARY_UNION_OF_UNION : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@ARBITRARY A) P s) /\ (@UNION_OF A (@ARBITRARY A) P t)) -> @UNION_OF A (@ARBITRARY A) P (@setU A s t).
Axiom thm_ARBITRARY_INTERSECTION_OF_INTERS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @INTERSECTION_OF A (@ARBITRARY A) P s) -> @INTERSECTION_OF A (@ARBITRARY A) P (@INTERS A u).
Axiom thm_ARBITRARY_INTERSECTION_OF_INTER : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@ARBITRARY A) P s) /\ (@INTERSECTION_OF A (@ARBITRARY A) P t)) -> @INTERSECTION_OF A (@ARBITRARY A) P (@setI A s t).
Axiom thm_ARBITRARY_UNION_OF_INTER_EQ : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@ARBITRARY A) P s) /\ (@UNION_OF A (@ARBITRARY A) P t)) -> @UNION_OF A (@ARBITRARY A) P (@setI A s t)) = (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> @UNION_OF A (@ARBITRARY A) P (@setI A s t)).
Axiom thm_ARBITRARY_UNION_OF_INTER : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@setI A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@ARBITRARY A) P s) /\ (@UNION_OF A (@ARBITRARY A) P t)) -> @UNION_OF A (@ARBITRARY A) P (@setI A s t).
Axiom thm_ARBITRARY_INTERSECTION_OF_UNION_EQ : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@ARBITRARY A) P s) /\ (@INTERSECTION_OF A (@ARBITRARY A) P t)) -> @INTERSECTION_OF A (@ARBITRARY A) P (@setU A s t)) = (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> @INTERSECTION_OF A (@ARBITRARY A) P (@setU A s t)).
Axiom thm_ARBITRARY_INTERSECTION_OF_UNION : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@setU A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@ARBITRARY A) P s) /\ (@INTERSECTION_OF A (@ARBITRARY A) P t)) -> @INTERSECTION_OF A (@ARBITRARY A) P (@setU A s t).
Axiom thm_FINITE_UNION_OF_EMPTY : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @UNION_OF A (@finite_set (A -> Prop)) P (@set0 A).
Axiom thm_FINITE_INTERSECTION_OF_EMPTY : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setT A).
Axiom thm_FINITE_UNION_OF_INC : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (P s) -> @UNION_OF A (@finite_set (A -> Prop)) P s.
Axiom thm_FINITE_INTERSECTION_OF_INC : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (P s) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P s.
Axiom thm_FINITE_UNION_OF_COMPLEMENT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@UNION_OF A (@finite_set (A -> Prop)) P s) = (@INTERSECTION_OF A (@finite_set (A -> Prop)) (fun s' : A -> Prop => P (@setD A (@setT A) s')) (@setD A (@setT A) s)).
Axiom thm_FINITE_INTERSECTION_OF_COMPLEMENT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@INTERSECTION_OF A (@finite_set (A -> Prop)) P s) = (@UNION_OF A (@finite_set (A -> Prop)) (fun s' : A -> Prop => P (@setD A (@setT A) s')) (@setD A (@setT A) s)).
Axiom thm_FINITE_UNION_OF_IDEMPOT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@UNION_OF A (@finite_set (A -> Prop)) (@UNION_OF A (@finite_set (A -> Prop)) P)) = (@UNION_OF A (@finite_set (A -> Prop)) P).
Axiom thm_FINITE_INTERSECTION_OF_IDEMPOT : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@INTERSECTION_OF A (@finite_set (A -> Prop)) (@INTERSECTION_OF A (@finite_set (A -> Prop)) P)) = (@INTERSECTION_OF A (@finite_set (A -> Prop)) P).
Axiom thm_FINITE_UNION_OF_UNIONS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) u) /\ (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @UNION_OF A (@finite_set (A -> Prop)) P s)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@UNIONS A u).
Axiom thm_FINITE_UNION_OF_UNION : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@finite_set (A -> Prop)) P s) /\ (@UNION_OF A (@finite_set (A -> Prop)) P t)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@setU A s t).
Axiom thm_FINITE_INTERSECTION_OF_INTERS : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) u) /\ (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P s)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@INTERS A u).
Axiom thm_FINITE_INTERSECTION_OF_INTER : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@finite_set (A -> Prop)) P s) /\ (@INTERSECTION_OF A (@finite_set (A -> Prop)) P t)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setI A s t).
Axiom thm_FINITE_UNION_OF_INTER_EQ : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@finite_set (A -> Prop)) P s) /\ (@UNION_OF A (@finite_set (A -> Prop)) P t)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@setI A s t)) = (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@setI A s t)).
Axiom thm_FINITE_UNION_OF_INTER : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@setI A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@finite_set (A -> Prop)) P s) /\ (@UNION_OF A (@finite_set (A -> Prop)) P t)) -> @UNION_OF A (@finite_set (A -> Prop)) P (@setI A s t).
Axiom thm_FINITE_INTERSECTION_OF_UNION_EQ : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@finite_set (A -> Prop)) P s) /\ (@INTERSECTION_OF A (@finite_set (A -> Prop)) P t)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setU A s t)) = (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setU A s t)).
Axiom thm_FINITE_INTERSECTION_OF_UNION : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@setU A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@finite_set (A -> Prop)) P s) /\ (@INTERSECTION_OF A (@finite_set (A -> Prop)) P t)) -> @INTERSECTION_OF A (@finite_set (A -> Prop)) P (@setU A s t).
Axiom thm_CARD_SET_OF_LIST_LE : forall {A : Type'}, forall l : seq A, leqn (@CARD A (@set_of_list A l)) (@size A l).
Axiom thm_HAS_SIZE_SET_OF_LIST : forall {A : Type'}, forall l : seq A, (@HAS_SIZE A (@set_of_list A l) (@size A l)) = (@PAIRWISE A (fun x : A => fun y : A => ~ (x = y)) l).
Axiom thm_SURJECTIVE_IFF_INJECTIVE_GEN : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, ((@finite_set A s) /\ ((@finite_set B t) /\ (((@CARD A s) = (@CARD B t)) /\ (@subset B (@IMAGE A B f s) t)))) -> (forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y)) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_SURJECTIVE_IFF_INJECTIVE : forall {A : Type'}, forall s : A -> Prop, forall f : A -> A, ((@finite_set A s) /\ (@subset A (@IMAGE A A f s) s)) -> (forall y : A, (@IN A y s) -> exists x : A, (@IN A x s) /\ ((f x) = y)) = (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_IMAGE_IMP_INJECTIVE_GEN : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, ((@finite_set A s) /\ (((@CARD A s) = (@CARD B t)) /\ ((@IMAGE A B f s) = t))) -> forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y.
Axiom thm_IMAGE_IMP_INJECTIVE : forall {A : Type'}, forall s : A -> Prop, forall f : A -> A, ((@finite_set A s) /\ ((@IMAGE A A f s) = s)) -> forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y.
Axiom thm_HAS_SIZE_IMAGE_INJ_RESTRICT : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, forall P : B -> Prop, forall n : nat, ((@finite_set A s) /\ ((@finite_set B t) /\ (((@CARD A s) = (@CARD B t)) /\ ((@subset B (@IMAGE A B f s) t) /\ ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@HAS_SIZE A (@GSPEC A (fun GEN_PVAR_219 : A => exists x : A, @SETSPEC A GEN_PVAR_219 ((@IN A x s) /\ (P (f x))) x)) n)))))) -> @HAS_SIZE B (@GSPEC B (fun GEN_PVAR_220 : B => exists x : B, @SETSPEC B GEN_PVAR_220 ((@IN B x t) /\ (P x)) x)) n.
Axiom thm_CARD_LE_INJ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ ((@finite_set B t) /\ (leqn (@CARD A s) (@CARD B t)))) -> exists f : A -> B, (@subset B (@IMAGE A B f s) t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_FORALL_IN_CLAUSES : forall {A : Type'}, (forall P : A -> Prop, (forall x : A, (@IN A x (@set0 A)) -> P x) = True) /\ (forall P : A -> Prop, forall a : A, forall s : A -> Prop, (forall x : A, (@IN A x (@INSERT A a s)) -> P x) = ((P a) /\ (forall x : A, (@IN A x s) -> P x))).
Axiom thm_EXISTS_IN_CLAUSES : forall {A : Type'}, (forall P : A -> Prop, (exists x : A, (@IN A x (@set0 A)) /\ (P x)) = False) /\ (forall P : A -> Prop, forall a : A, forall s : A -> Prop, (exists x : A, (@IN A x (@INSERT A a s)) /\ (P x)) = ((P a) \/ (exists x : A, (@IN A x s) /\ (P x)))).
Axiom thm_INJECTIVE_ON_IMAGE : forall {A B : Type'}, forall f : A -> B, forall u : A -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((@subset A s u) /\ ((@subset A t u) /\ ((@IMAGE A B f s) = (@IMAGE A B f t)))) -> s = t) = (forall x : A, forall y : A, ((@IN A x u) /\ ((@IN A y u) /\ ((f x) = (f y)))) -> x = y).
Axiom thm_INJECTIVE_IMAGE : forall {A B : Type'}, forall f : A -> B, (forall s : A -> Prop, forall t : A -> Prop, ((@IMAGE A B f s) = (@IMAGE A B f t)) -> s = t) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
Axiom thm_SURJECTIVE_ON_IMAGE : forall {A B : Type'}, forall f : A -> B, forall u : A -> Prop, forall v : B -> Prop, (forall t : B -> Prop, (@subset B t v) -> exists s : A -> Prop, (@subset A s u) /\ ((@IMAGE A B f s) = t)) = (forall y : B, (@IN B y v) -> exists x : A, (@IN A x u) /\ ((f x) = y)).
Axiom thm_SURJECTIVE_IMAGE : forall {A B : Type'}, forall f : A -> B, (forall t : B -> Prop, exists s : A -> Prop, (@IMAGE A B f s) = t) = (forall y : B, exists x : A, (f x) = y).
Axiom thm_INJECTIVE_ON_PREIMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall u : B -> Prop, (forall t : B -> Prop, forall t' : B -> Prop, ((@subset B t u) /\ ((@subset B t' u) /\ ((@GSPEC A (fun GEN_PVAR_222 : A => exists x : A, @SETSPEC A GEN_PVAR_222 ((@IN A x s) /\ (@IN B (f x) t)) x)) = (@GSPEC A (fun GEN_PVAR_223 : A => exists x : A, @SETSPEC A GEN_PVAR_223 ((@IN A x s) /\ (@IN B (f x) t')) x))))) -> t = t') = (@subset B u (@IMAGE A B f s)).
Axiom thm_SURJECTIVE_ON_PREIMAGE : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall u : B -> Prop, (forall k : A -> Prop, (@subset A k s) -> exists t : B -> Prop, (@subset B t u) /\ ((@GSPEC A (fun GEN_PVAR_224 : A => exists x : A, @SETSPEC A GEN_PVAR_224 ((@IN A x s) /\ (@IN B (f x) t)) x)) = k)) = ((@subset B (@IMAGE A B f s) u) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_INJECTIVE_PREIMAGE : forall {A B : Type'}, forall f : A -> B, (forall t : B -> Prop, forall t' : B -> Prop, ((@GSPEC A (fun GEN_PVAR_225 : A => exists x : A, @SETSPEC A GEN_PVAR_225 (@IN B (f x) t) x)) = (@GSPEC A (fun GEN_PVAR_226 : A => exists x : A, @SETSPEC A GEN_PVAR_226 (@IN B (f x) t') x))) -> t = t') = ((@IMAGE A B f (@setT A)) = (@setT B)).
Axiom thm_SURJECTIVE_PREIMAGE : forall {A B : Type'}, forall f : A -> B, (forall k : A -> Prop, exists t : B -> Prop, (@GSPEC A (fun GEN_PVAR_227 : A => exists x : A, @SETSPEC A GEN_PVAR_227 (@IN B (f x) t) x)) = k) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
Axiom thm_CARD_EQ_BIJECTION : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ ((@finite_set B t) /\ ((@CARD A s) = (@CARD B t)))) -> exists f : A -> B, (forall x : A, (@IN A x s) -> @IN B (f x) t) /\ ((forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ ((f x) = y)) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_CARD_EQ_BIJECTIONS : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ ((@finite_set B t) /\ ((@CARD A s) = (@CARD B t)))) -> exists f : A -> B, exists g : B -> A, (forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)).
Axiom thm_CARD_EQ_BIJECTIONS_SPECIAL : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall a : A, forall b : B, ((@finite_set A s) /\ ((@finite_set B t) /\ (((@CARD A s) = (@CARD B t)) /\ ((@IN A a s) /\ (@IN B b t))))) -> exists f : A -> B, exists g : B -> A, ((f a) = b) /\ (((g b) = a) /\ ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)))).
Axiom thm_BIJECTIONS_HAS_SIZE : forall {A B : Type'} (n : nat), forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, forall g : B -> A, ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ ((forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)) /\ (@HAS_SIZE A s n))) -> @HAS_SIZE B t n.
Axiom thm_BIJECTIONS_HAS_SIZE_EQ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, forall g : B -> A, ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y))) -> forall n : nat, (@HAS_SIZE A s n) = (@HAS_SIZE B t n).
Axiom thm_BIJECTIONS_CARD_EQ : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> B, forall g : B -> A, (((@finite_set A s) \/ (@finite_set B t)) /\ ((forall x : A, (@IN A x s) -> (@IN B (f x) t) /\ ((g (f x)) = x)) /\ (forall y : B, (@IN B y t) -> (@IN A (g y) s) /\ ((f (g y)) = y)))) -> (@CARD A s) = (@CARD B t).
Axiom thm_WF_FINITE : forall {A : Type'}, forall lt2 : A -> A -> Prop, ((forall x : A, ~ (lt2 x x)) /\ ((forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z) /\ (forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_229 : A => exists y : A, @SETSPEC A GEN_PVAR_229 (lt2 y x) y))))) -> @well_founded A lt2.
Axiom thm_WF_PSUBSET : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> @well_founded (A -> Prop) (fun t1 : A -> Prop => fun t2 : A -> Prop => (@proper A t1 t2) /\ (@subset A t2 s)).
Axiom thm_le_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@le_c A B s t) = (exists f : A -> B, (forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
Axiom thm_lt_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@lt_c A B s t) = ((@le_c A B s t) /\ (~ (@le_c B A t s))).
Axiom thm_eq_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@eq_c A B s t) = (exists f : A -> B, (forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((f x) = y)))).
Axiom thm_ge_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@ge_c A B s t) = (@le_c B A t s).
Axiom thm_gt_c : forall {A B : Type'}, forall t : B -> Prop, forall s : A -> Prop, (@gt_c A B s t) = (@lt_c B A t s).
Axiom thm_LE_C : forall {A B : Type'}, forall s : B -> Prop, forall t : A -> Prop, (@le_c B A s t) = (exists g : A -> B, forall x : B, (@IN B x s) -> exists y : A, (@IN A y t) /\ ((g y) = x)).
Axiom thm_GE_C : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@ge_c A B s t) = (exists f : A -> B, forall y : B, (@IN B y t) -> exists x : A, (@IN A x s) /\ (y = (f x))).
Axiom thm_COUNTABLE : forall {A : Type'}, forall t : A -> Prop, (@COUNTABLE A t) = (@ge_c nat A (@setT nat) t).
Axiom thm_sup : forall s : R -> Prop, (sup s) = (@ε R (fun a : R => (forall x : R, (@IN R x s) -> ler x a) /\ (forall b : R, (forall x : R, (@IN R x s) -> ler x b) -> ler a b))).
Axiom thm_SUP_EQ : forall s : R -> Prop, forall t : R -> Prop, (forall b : R, (forall x : R, (@IN R x s) -> ler x b) = (forall x : R, (@IN R x t) -> ler x b)) -> (sup s) = (sup t).
Axiom thm_SUP : forall s : R -> Prop, ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> ler x b)) -> (forall x : R, (@IN R x s) -> ler x (sup s)) /\ (forall b : R, (forall x : R, (@IN R x s) -> ler x b) -> ler (sup s) b).
Axiom thm_SUP_FINITE_LEMMA : forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> exists b : R, (@IN R b s) /\ (forall x : R, (@IN R x s) -> ler x b).
Axiom thm_SUP_FINITE : forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (@IN R (sup s) s) /\ (forall x : R, (@IN R x s) -> ler x (sup s)).
Axiom thm_REAL_LE_SUP_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (ler a (sup s)) = (exists x : R, (@IN R x s) /\ (ler a x)).
Axiom thm_REAL_SUP_LE_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (ler (sup s) a) = (forall x : R, (@IN R x s) -> ler x a).
Axiom thm_REAL_LT_SUP_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (ltr a (sup s)) = (exists x : R, (@IN R x s) /\ (ltr a x)).
Axiom thm_REAL_SUP_LT_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (ltr (sup s) a) = (forall x : R, (@IN R x s) -> ltr x a).
Axiom thm_REAL_SUP_UNIQUE : forall s : R -> Prop, forall b : R, ((forall x : R, (@IN R x s) -> ler x b) /\ (forall b' : R, (ltr b' b) -> exists x : R, (@IN R x s) /\ (ltr b' x))) -> (sup s) = b.
Axiom thm_REAL_SUP_LE : forall (s : R -> Prop), forall b : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> ler x b)) -> ler (sup s) b.
Axiom thm_REAL_SUP_LE_SUBSET : forall s : R -> Prop, forall t : R -> Prop, ((~ (s = (@set0 R))) /\ ((@subset R s t) /\ (exists b : R, forall x : R, (@IN R x t) -> ler x b))) -> ler (sup s) (sup t).
Axiom thm_REAL_SUP_BOUNDS : forall s : R -> Prop, forall a : R, forall b : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> (ler a x) /\ (ler x b))) -> (ler a (sup s)) /\ (ler (sup s) b).
Axiom thm_REAL_ABS_SUP_LE : forall s : R -> Prop, forall a : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> ler (normr x) a)) -> ler (normr (sup s)) a.
Axiom thm_REAL_SUP_ASCLOSE : forall s : R -> Prop, forall l : R, forall e : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> ler (normr (subr x l)) e)) -> ler (normr (subr (sup s) l)) e.
Axiom thm_SUP_UNIQUE_FINITE : forall (a : R), forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> ((sup s) = a) = ((@IN R a s) /\ (forall y : R, (@IN R y s) -> ler y a)).
Axiom thm_SUP_INSERT_FINITE : forall x : R, forall s : R -> Prop, (@finite_set R s) -> (sup (@INSERT R x s)) = (@COND R (s = (@set0 R)) x (maxr x (sup s))).
Axiom thm_SUP_SING : forall a : R, (sup (@INSERT R a (@set0 R))) = a.
Axiom thm_SUP_INSERT_INSERT : forall a : R, forall b : R, forall s : R -> Prop, (sup (@INSERT R b (@INSERT R a s))) = (sup (@INSERT R (maxr a b) s)).
Axiom thm_REAL_LE_SUP : forall s : R -> Prop, forall a : R, forall b : R, forall y : R, ((@IN R y s) /\ ((ler a y) /\ (forall x : R, (@IN R x s) -> ler x b))) -> ler a (sup s).
Axiom thm_REAL_SUP_LE_EQ : forall s : R -> Prop, forall y : R, ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> ler x b)) -> (ler (sup s) y) = (forall x : R, (@IN R x s) -> ler x y).
Axiom thm_SUP_UNIQUE : forall s : R -> Prop, forall b : R, (forall c : R, (forall x : R, (@IN R x s) -> ler x c) = (ler b c)) -> (sup s) = b.
Axiom thm_SUP_UNION : forall s : R -> Prop, forall t : R -> Prop, ((~ (s = (@set0 R))) /\ ((~ (t = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> ler x b) /\ (exists c : R, forall x : R, (@IN R x t) -> ler x c)))) -> (sup (@setU R s t)) = (maxr (sup s) (sup t)).
Axiom thm_ELEMENT_LE_SUP : forall s : R -> Prop, forall a : R, ((exists b : R, forall x : R, (@IN R x s) -> ler x b) /\ (@IN R a s)) -> ler a (sup s).
Axiom thm_SUP_APPROACH : forall s : R -> Prop, forall c : R, ((~ (s = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> ler x b) /\ (ltr c (sup s)))) -> exists x : R, (@IN R x s) /\ (ltr c x).
Axiom thm_REAL_MAX_SUP : forall x : R, forall y : R, (maxr x y) = (sup (@INSERT R x (@INSERT R y (@set0 R)))).
Axiom thm_inf : forall s : R -> Prop, (inf s) = (@ε R (fun a : R => (forall x : R, (@IN R x s) -> ler a x) /\ (forall b : R, (forall x : R, (@IN R x s) -> ler b x) -> ler b a))).
Axiom thm_INF_EQ : forall s : R -> Prop, forall t : R -> Prop, (forall a : R, (forall x : R, (@IN R x s) -> ler a x) = (forall x : R, (@IN R x t) -> ler a x)) -> (inf s) = (inf t).
Axiom thm_INF : forall s : R -> Prop, ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> ler b x)) -> (forall x : R, (@IN R x s) -> ler (inf s) x) /\ (forall b : R, (forall x : R, (@IN R x s) -> ler b x) -> ler b (inf s)).
Axiom thm_INF_FINITE_LEMMA : forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> exists b : R, (@IN R b s) /\ (forall x : R, (@IN R x s) -> ler b x).
Axiom thm_INF_FINITE : forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (@IN R (inf s) s) /\ (forall x : R, (@IN R x s) -> ler (inf s) x).
Axiom thm_REAL_LE_INF_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (ler a (inf s)) = (forall x : R, (@IN R x s) -> ler a x).
Axiom thm_REAL_INF_LE_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (ler (inf s) a) = (exists x : R, (@IN R x s) /\ (ler x a)).
Axiom thm_REAL_LT_INF_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (ltr a (inf s)) = (forall x : R, (@IN R x s) -> ltr a x).
Axiom thm_REAL_INF_LT_FINITE : forall s : R -> Prop, forall a : R, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> (ltr (inf s) a) = (exists x : R, (@IN R x s) /\ (ltr x a)).
Axiom thm_REAL_INF_UNIQUE : forall s : R -> Prop, forall b : R, ((forall x : R, (@IN R x s) -> ler b x) /\ (forall b' : R, (ltr b b') -> exists x : R, (@IN R x s) /\ (ltr x b'))) -> (inf s) = b.
Axiom thm_REAL_LE_INF : forall (s : R -> Prop), forall b : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> ler b x)) -> ler b (inf s).
Axiom thm_REAL_LE_INF_SUBSET : forall s : R -> Prop, forall t : R -> Prop, ((~ (t = (@set0 R))) /\ ((@subset R t s) /\ (exists b : R, forall x : R, (@IN R x s) -> ler b x))) -> ler (inf s) (inf t).
Axiom thm_REAL_INF_BOUNDS : forall s : R -> Prop, forall a : R, forall b : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> (ler a x) /\ (ler x b))) -> (ler a (inf s)) /\ (ler (inf s) b).
Axiom thm_REAL_ABS_INF_LE : forall s : R -> Prop, forall a : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> ler (normr x) a)) -> ler (normr (inf s)) a.
Axiom thm_REAL_INF_ASCLOSE : forall s : R -> Prop, forall l : R, forall e : R, ((~ (s = (@set0 R))) /\ (forall x : R, (@IN R x s) -> ler (normr (subr x l)) e)) -> ler (normr (subr (inf s) l)) e.
Axiom thm_INF_UNIQUE_FINITE : forall (a : R), forall s : R -> Prop, ((@finite_set R s) /\ (~ (s = (@set0 R)))) -> ((inf s) = a) = ((@IN R a s) /\ (forall y : R, (@IN R y s) -> ler a y)).
Axiom thm_INF_INSERT_FINITE : forall x : R, forall s : R -> Prop, (@finite_set R s) -> (inf (@INSERT R x s)) = (@COND R (s = (@set0 R)) x (minr x (inf s))).
Axiom thm_INF_SING : forall a : R, (inf (@INSERT R a (@set0 R))) = a.
Axiom thm_INF_INSERT_INSERT : forall a : R, forall b : R, forall s : R -> Prop, (inf (@INSERT R b (@INSERT R a s))) = (inf (@INSERT R (minr a b) s)).
Axiom thm_REAL_SUP_EQ_INF : forall s : R -> Prop, ((~ (s = (@set0 R))) /\ (exists B : R, forall x : R, (@IN R x s) -> ler (normr x) B)) -> ((sup s) = (inf s)) = (exists a : R, s = (@INSERT R a (@set0 R))).
Axiom thm_REAL_INF_LE : forall s : R -> Prop, forall a : R, forall b : R, forall y : R, ((@IN R y s) /\ ((ler y b) /\ (forall x : R, (@IN R x s) -> ler a x))) -> ler (inf s) b.
Axiom thm_REAL_LE_INF_EQ : forall s : R -> Prop, forall y : R, ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> ler b x)) -> (ler y (inf s)) = (forall x : R, (@IN R x s) -> ler y x).
Axiom thm_INF_UNIQUE : forall s : R -> Prop, forall b : R, (forall c : R, (forall x : R, (@IN R x s) -> ler c x) = (ler c b)) -> (inf s) = b.
Axiom thm_INF_UNION : forall s : R -> Prop, forall t : R -> Prop, ((~ (s = (@set0 R))) /\ ((~ (t = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> ler b x) /\ (exists c : R, forall x : R, (@IN R x t) -> ler c x)))) -> (inf (@setU R s t)) = (minr (inf s) (inf t)).
Axiom thm_INF_LE_ELEMENT : forall s : R -> Prop, forall a : R, ((exists b : R, forall x : R, (@IN R x s) -> ler b x) /\ (@IN R a s)) -> ler (inf s) a.
Axiom thm_INF_APPROACH : forall s : R -> Prop, forall c : R, ((~ (s = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> ler b x) /\ (ltr (inf s) c))) -> exists x : R, (@IN R x s) /\ (ltr x c).
Axiom thm_REAL_MIN_INF : forall x : R, forall y : R, (minr x y) = (inf (@INSERT R x (@INSERT R y (@set0 R)))).
Axiom thm_has_inf : forall s : R -> Prop, forall b : R, (has_inf s b) = (forall c : R, (forall x : R, (@IN R x s) -> ler c x) = (ler c b)).
Axiom thm_has_sup : forall s : R -> Prop, forall b : R, (has_sup s b) = (forall c : R, (forall x : R, (@IN R x s) -> ler x c) = (ler b c)).
Axiom thm_HAS_INF_LBOUND : forall s : R -> Prop, forall b : R, forall x : R, ((has_inf s b) /\ (@IN R x s)) -> ler b x.
Axiom thm_HAS_SUP_UBOUND : forall s : R -> Prop, forall b : R, forall x : R, ((has_sup s b) /\ (@IN R x s)) -> ler x b.
Axiom thm_HAS_INF_INF : forall s : R -> Prop, forall l : R, (has_inf s l) = ((~ (s = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> ler b x) /\ ((inf s) = l))).
Axiom thm_HAS_SUP_SUP : forall s : R -> Prop, forall l : R, (has_sup s l) = ((~ (s = (@set0 R))) /\ ((exists b : R, forall x : R, (@IN R x s) -> ler x b) /\ ((sup s) = l))).
Axiom thm_INF_EXISTS : forall s : R -> Prop, (exists l : R, has_inf s l) = ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> ler b x)).
Axiom thm_SUP_EXISTS : forall s : R -> Prop, (exists l : R, has_sup s l) = ((~ (s = (@set0 R))) /\ (exists b : R, forall x : R, (@IN R x s) -> ler x b)).
Axiom thm_HAS_INF_APPROACH : forall s : R -> Prop, forall l : R, forall c : R, ((has_inf s l) /\ (ltr l c)) -> exists x : R, (@IN R x s) /\ (ltr x c).
Axiom thm_HAS_SUP_APPROACH : forall s : R -> Prop, forall l : R, forall c : R, ((has_sup s l) /\ (ltr c l)) -> exists x : R, (@IN R x s) /\ (ltr c x).
Axiom thm_HAS_INF : forall s : R -> Prop, forall l : R, (has_inf s l) = ((~ (s = (@set0 R))) /\ ((forall x : R, (@IN R x s) -> ler l x) /\ (forall c : R, (ltr l c) -> exists x : R, (@IN R x s) /\ (ltr x c)))).
Axiom thm_HAS_SUP : forall s : R -> Prop, forall l : R, (has_sup s l) = ((~ (s = (@set0 R))) /\ ((forall x : R, (@IN R x s) -> ler x l) /\ (forall c : R, (ltr c l) -> exists x : R, (@IN R x s) /\ (ltr c x)))).
Axiom thm_HAS_INF_LE : forall s : R -> Prop, forall t : R -> Prop, forall l : R, forall m : R, ((has_inf s l) /\ ((has_inf t m) /\ (forall y : R, (@IN R y t) -> exists x : R, (@IN R x s) /\ (ler x y)))) -> ler l m.
Axiom thm_HAS_SUP_LE : forall s : R -> Prop, forall t : R -> Prop, forall l : R, forall m : R, ((has_sup s l) /\ ((has_sup t m) /\ (forall y : R, (@IN R y t) -> exists x : R, (@IN R x s) /\ (ler y x)))) -> ler m l.
Axiom thm_numseg : forall m : nat, forall n : nat, (dotdot m n) = (@GSPEC nat (fun GEN_PVAR_231 : nat => exists x : nat, @SETSPEC nat GEN_PVAR_231 ((leqn m x) /\ (leqn x n)) x)).
Axiom thm_FINITE_NUMSEG : forall m : nat, forall n : nat, @finite_set nat (dotdot m n).
Axiom thm_NUMSEG_COMBINE_R : forall m : nat, forall p : nat, forall n : nat, ((leqn m (addn p (NUMERAL (BIT1 O)))) /\ (leqn p n)) -> (@setU nat (dotdot m p) (dotdot (addn p (NUMERAL (BIT1 O))) n)) = (dotdot m n).
Axiom thm_NUMSEG_COMBINE_L : forall m : nat, forall p : nat, forall n : nat, ((leqn m p) /\ (leqn p (addn n (NUMERAL (BIT1 O))))) -> (@setU nat (dotdot m (subn p (NUMERAL (BIT1 O)))) (dotdot p n)) = (dotdot m n).
Axiom thm_NUMSEG_LREC : forall m : nat, forall n : nat, (leqn m n) -> (@INSERT nat m (dotdot (addn m (NUMERAL (BIT1 O))) n)) = (dotdot m n).
Axiom thm_NUMSEG_RREC : forall m : nat, forall n : nat, (leqn m n) -> (@INSERT nat n (dotdot m (subn n (NUMERAL (BIT1 O))))) = (dotdot m n).
Axiom thm_NUMSEG_REC : forall m : nat, forall n : nat, (leqn m (S n)) -> (dotdot m (S n)) = (@INSERT nat (S n) (dotdot m n)).
Axiom thm_IN_NUMSEG : forall m : nat, forall n : nat, forall p : nat, (@IN nat p (dotdot m n)) = ((leqn m p) /\ (leqn p n)).
Axiom thm_IN_NUMSEG_0 : forall m : nat, forall n : nat, (@IN nat m (dotdot (NUMERAL O) n)) = (leqn m n).
Axiom thm_NUMSEG_SING : forall n : nat, (dotdot n n) = (@INSERT nat n (@set0 nat)).
Axiom thm_NUMSEG_EMPTY : forall m : nat, forall n : nat, ((dotdot m n) = (@set0 nat)) = (ltn n m).
Axiom thm_EMPTY_NUMSEG : forall m : nat, forall n : nat, (ltn n m) -> (dotdot m n) = (@set0 nat).
Axiom thm_FINITE_SUBSET_NUMSEG : forall s : nat -> Prop, (@finite_set nat s) = (exists n : nat, @subset nat s (dotdot (NUMERAL O) n)).
Axiom thm_CARD_NUMSEG_LEMMA : forall m : nat, forall d : nat, (@CARD nat (dotdot m (addn m d))) = (addn d (NUMERAL (BIT1 O))).
Axiom thm_CARD_NUMSEG : forall m : nat, forall n : nat, (@CARD nat (dotdot m n)) = (subn (addn n (NUMERAL (BIT1 O))) m).
Axiom thm_HAS_SIZE_NUMSEG : forall m : nat, forall n : nat, @HAS_SIZE nat (dotdot m n) (subn (addn n (NUMERAL (BIT1 O))) m).
Axiom thm_CARD_NUMSEG_1 : forall n : nat, (@CARD nat (dotdot (NUMERAL (BIT1 O)) n)) = n.
Axiom thm_HAS_SIZE_NUMSEG_1 : forall n : nat, @HAS_SIZE nat (dotdot (NUMERAL (BIT1 O)) n) n.
Axiom thm_NUMSEG_CLAUSES : (forall m : nat, (dotdot m (NUMERAL O)) = (@COND (nat -> Prop) (m = (NUMERAL O)) (@INSERT nat (NUMERAL O) (@set0 nat)) (@set0 nat))) /\ (forall m : nat, forall n : nat, (dotdot m (S n)) = (@COND (nat -> Prop) (leqn m (S n)) (@INSERT nat (S n) (dotdot m n)) (dotdot m n))).
Axiom thm_FINITE_INDEX_NUMSEG : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) = (exists f : nat -> A, (forall i : nat, forall j : nat, ((@IN nat i (dotdot (NUMERAL (BIT1 O)) (@CARD A s))) /\ ((@IN nat j (dotdot (NUMERAL (BIT1 O)) (@CARD A s))) /\ ((f i) = (f j)))) -> i = j) /\ (s = (@IMAGE nat A f (dotdot (NUMERAL (BIT1 O)) (@CARD A s))))).
Axiom thm_FINITE_INDEX_NUMBERS : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) = (exists k : nat -> Prop, exists f : nat -> A, (forall i : nat, forall j : nat, ((@IN nat i k) /\ ((@IN nat j k) /\ ((f i) = (f j)))) -> i = j) /\ ((@finite_set nat k) /\ (s = (@IMAGE nat A f k)))).
Axiom thm_INTER_NUMSEG : forall m : nat, forall n : nat, forall p : nat, forall q : nat, (@setI nat (dotdot m n) (dotdot p q)) = (dotdot (maxn m p) (minn n q)).
Axiom thm_DISJOINT_NUMSEG : forall m : nat, forall n : nat, forall p : nat, forall q : nat, (@DISJOINT nat (dotdot m n) (dotdot p q)) = ((ltn n p) \/ ((ltn q m) \/ ((ltn n m) \/ (ltn q p)))).
Axiom thm_NUMSEG_ADD_SPLIT : forall m : nat, forall n : nat, forall p : nat, (leqn m (addn n (NUMERAL (BIT1 O)))) -> (dotdot m (addn n p)) = (@setU nat (dotdot m n) (dotdot (addn n (NUMERAL (BIT1 O))) (addn n p))).
Axiom thm_NUMSEG_OFFSET_IMAGE : forall m : nat, forall n : nat, forall p : nat, (dotdot (addn m p) (addn n p)) = (@IMAGE nat nat (fun i : nat => addn i p) (dotdot m n)).
Axiom thm_SUBSET_NUMSEG : forall m : nat, forall n : nat, forall p : nat, forall q : nat, (@subset nat (dotdot m n) (dotdot p q)) = ((ltn n m) \/ ((leqn p m) /\ (leqn n q))).
Axiom thm_NUMSEG_LE : forall n : nat, (@GSPEC nat (fun GEN_PVAR_233 : nat => exists x : nat, @SETSPEC nat GEN_PVAR_233 (leqn x n) x)) = (dotdot (NUMERAL O) n).
Axiom thm_NUMSEG_LT : forall n : nat, (@GSPEC nat (fun GEN_PVAR_234 : nat => exists x : nat, @SETSPEC nat GEN_PVAR_234 (ltn x n) x)) = (@COND (nat -> Prop) (n = (NUMERAL O)) (@set0 nat) (dotdot (NUMERAL O) (subn n (NUMERAL (BIT1 O))))).
Axiom thm_TOPOLOGICAL_SORT : forall {A : Type'}, forall lt2 : A -> A -> Prop, ((forall x : A, forall y : A, ((lt2 x y) /\ (lt2 y x)) -> x = y) /\ (forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z)) -> forall n : nat, forall s : A -> Prop, (@HAS_SIZE A s n) -> exists f : nat -> A, (s = (@IMAGE nat A f (dotdot (NUMERAL (BIT1 O)) n))) /\ (forall j : nat, forall k : nat, ((@IN nat j (dotdot (NUMERAL (BIT1 O)) n)) /\ ((@IN nat k (dotdot (NUMERAL (BIT1 O)) n)) /\ (ltn j k))) -> ~ (lt2 (f k) (f j))).
Axiom thm_FINITE_INT_SEG : (forall l : int, forall r : int, @finite_set int (@GSPEC int (fun GEN_PVAR_235 : int => exists x : int, @SETSPEC int GEN_PVAR_235 ((lez l x) /\ (lez x r)) x))) /\ ((forall l : int, forall r : int, @finite_set int (@GSPEC int (fun GEN_PVAR_236 : int => exists x : int, @SETSPEC int GEN_PVAR_236 ((lez l x) /\ (ltz x r)) x))) /\ ((forall l : int, forall r : int, @finite_set int (@GSPEC int (fun GEN_PVAR_237 : int => exists x : int, @SETSPEC int GEN_PVAR_237 ((ltz l x) /\ (lez x r)) x))) /\ (forall l : int, forall r : int, @finite_set int (@GSPEC int (fun GEN_PVAR_238 : int => exists x : int, @SETSPEC int GEN_PVAR_238 ((ltz l x) /\ (ltz x r)) x))))).
Axiom thm_neutral : forall {A : Type'}, forall op : A -> A -> A, (@neutral A op) = (@ε A (fun x : A => forall y : A, ((op x y) = y) /\ ((op y x) = y))).
Axiom thm_monoidal : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) = ((forall x : A, forall y : A, (op x y) = (op y x)) /\ ((forall x : A, forall y : A, forall z : A, (op x (op y z)) = (op (op x y) z)) /\ (forall x : A, (op (@neutral A op) x) = x))).
Axiom thm_MONOIDAL_AC : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) -> (forall a : A, (op (@neutral A op) a) = a) /\ ((forall a : A, (op a (@neutral A op)) = a) /\ ((forall a : A, forall b : A, (op a b) = (op b a)) /\ ((forall a : A, forall b : A, forall c : A, (op (op a b) c) = (op a (op b c))) /\ (forall a : A, forall b : A, forall c : A, (op a (op b c)) = (op b (op a c)))))).
Axiom thm_support : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall op : B -> B -> B, (@support A B op f s) = (@GSPEC A (fun GEN_PVAR_239 : A => exists x : A, @SETSPEC A GEN_PVAR_239 ((@IN A x s) /\ (~ ((f x) = (@neutral B op)))) x)).
Axiom thm_iterate : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall op : B -> B -> B, (@iterate A B op s f) = (@COND B (@finite_set A (@support A B op f s)) (@fold_set A B (fun x : A => fun a : B => op (f x) a) (@support A B op f s) (@neutral B op)) (@neutral B op)).
Axiom thm_IN_SUPPORT : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall x : A, forall s : A -> Prop, (@IN A x (@support A B op f s)) = ((@IN A x s) /\ (~ ((f x) = (@neutral B op)))).
Axiom thm_SUPPORT_SUPPORT : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (@support A B op f (@support A B op f s)) = (@support A B op f s).
Axiom thm_SUPPORT_EMPTY : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (@neutral B op)) = ((@support A B op f s) = (@set0 A)).
Axiom thm_SUPPORT_SUBSET : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, @subset A (@support A B op f s) s.
Axiom thm_FINITE_SUPPORT : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (@finite_set A s) -> @finite_set A (@support A B op f s).
Axiom thm_SUPPORT_CLAUSES : forall {A B C : Type'} (op : C -> C -> C), (forall f : A -> C, (@support A C op f (@set0 A)) = (@set0 A)) /\ ((forall f : A -> C, forall x : A, forall s : A -> Prop, (@support A C op f (@INSERT A x s)) = (@COND (A -> Prop) ((f x) = (@neutral C op)) (@support A C op f s) (@INSERT A x (@support A C op f s)))) /\ ((forall f : A -> C, forall x : A, forall s : A -> Prop, (@support A C op f (@DELETE A s x)) = (@DELETE A (@support A C op f s) x)) /\ ((forall f : A -> C, forall s : A -> Prop, forall t : A -> Prop, (@support A C op f (@setU A s t)) = (@setU A (@support A C op f s) (@support A C op f t))) /\ ((forall f : A -> C, forall s : A -> Prop, forall t : A -> Prop, (@support A C op f (@setI A s t)) = (@setI A (@support A C op f s) (@support A C op f t))) /\ ((forall f : A -> C, forall s : A -> Prop, forall t : A -> Prop, (@support A C op f (@setD A s t)) = (@setD A (@support A C op f s) (@support A C op f t))) /\ (forall f : A -> B, forall g : B -> C, forall s : A -> Prop, (@support B C op g (@IMAGE A B f s)) = (@IMAGE A B f (@support A C op (@o A B C g f) s)))))))).
Axiom thm_SUPPORT_DELTA : forall {A B : Type'}, forall op : B -> B -> B, forall s : A -> Prop, forall f : A -> B, forall a : A, (@support A B op (fun x : A => @COND B (x = a) (f x) (@neutral B op)) s) = (@COND (A -> Prop) (@IN A a s) (@support A B op f (@INSERT A a (@set0 A))) (@set0 A)).
Axiom thm_FINITE_SUPPORT_DELTA : forall {A B : Type'} (s : A -> Prop), forall op : B -> B -> B, forall f : A -> B, forall a : A, @finite_set A (@support A B op (fun x : A => @COND B (x = a) (f x) (@neutral B op)) s).
Axiom thm_ITERATE_SUPPORT : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (@iterate A B op (@support A B op f s) f) = (@iterate A B op s f).
Axiom thm_ITERATE_EXPAND_CASES : forall {A B : Type'}, forall op : B -> B -> B, forall f : A -> B, forall s : A -> Prop, (@iterate A B op s f) = (@COND B (@finite_set A (@support A B op f s)) (@iterate A B op (@support A B op f s) f) (@neutral B op)).
Axiom thm_ITERATE_CLAUSES_GEN : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> (forall f : A -> B, (@iterate A B op (@set0 A) f) = (@neutral B op)) /\ (forall f : A -> B, forall x : A, forall s : A -> Prop, (@finite_set A (@support A B op f s)) -> (@iterate A B op (@INSERT A x s) f) = (@COND B (@IN A x s) (@iterate A B op s f) (op (f x) (@iterate A B op s f)))).
Axiom thm_ITERATE_CLAUSES : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> (forall f : A -> C, (@iterate A C op (@set0 A) f) = (@neutral C op)) /\ (forall f : B -> C, forall x : B, forall s : B -> Prop, (@finite_set B s) -> (@iterate B C op (@INSERT B x s) f) = (@COND C (@IN B x s) (@iterate B C op s f) (op (f x) (@iterate B C op s f)))).
Axiom thm_ITERATE_UNION : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (@DISJOINT A s t))) -> (@iterate A B op (@setU A s t) f) = (op (@iterate A B op s f) (@iterate A B op t f)).
Axiom thm_ITERATE_UNION_GEN : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A (@support A B op f s)) /\ ((@finite_set A (@support A B op f t)) /\ (@DISJOINT A (@support A B op f s) (@support A B op f t)))) -> (@iterate A B op (@setU A s t) f) = (op (@iterate A B op s f) (@iterate A B op t f)).
Axiom thm_ITERATE_DIFF : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@subset A t s)) -> (op (@iterate A B op (@setD A s t) f) (@iterate A B op t f)) = (@iterate A B op s f).
Axiom thm_ITERATE_DIFF_GEN : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A (@support A B op f s)) /\ (@subset A (@support A B op f t) (@support A B op f s))) -> (op (@iterate A B op (@setD A s t) f) (@iterate A B op t f)) = (@iterate A B op s f).
Axiom thm_ITERATE_INCL_EXCL : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall s : A -> Prop, forall t : A -> Prop, forall f : A -> B, ((@finite_set A s) /\ (@finite_set A t)) -> (op (@iterate A B op s f) (@iterate A B op t f)) = (op (@iterate A B op (@setU A s t) f) (@iterate A B op (@setI A s t) f)).
Axiom thm_ITERATE_CLOSED : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall P : B -> Prop, ((P (@neutral B op)) /\ (forall x : B, forall y : B, ((P x) /\ (P y)) -> P (op x y))) -> forall f : A -> B, forall s : A -> Prop, (forall x : A, ((@IN A x s) /\ (~ ((f x) = (@neutral B op)))) -> P (f x)) -> P (@iterate A B op s f).
Axiom thm_ITERATE_RELATED : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall R' : B -> B -> Prop, ((R' (@neutral B op) (@neutral B op)) /\ (forall x1 : B, forall y1 : B, forall x2 : B, forall y2 : B, ((R' x1 x2) /\ (R' y1 y2)) -> R' (op x1 y1) (op x2 y2))) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))) -> R' (@iterate A B op s f) (@iterate A B op s g).
Axiom thm_ITERATE_EQ_NEUTRAL : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (@neutral B op)) -> (@iterate A B op s f) = (@neutral B op).
Axiom thm_ITERATE_SING : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall x : A, (@iterate A B op (@INSERT A x (@set0 A)) f) = (f x).
Axiom thm_ITERATE_CLOSED_NONEMPTY : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall P : B -> Prop, (forall x : B, forall y : B, ((P x) /\ (P y)) -> P (op x y)) -> forall f : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> P (f x)))) -> P (@iterate A B op s f).
Axiom thm_ITERATE_RELATED_NONEMPTY : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall R' : B -> B -> Prop, (forall x1 : B, forall y1 : B, forall x2 : B, forall y2 : B, ((R' x1 x2) /\ (R' y1 y2)) -> R' (op x1 y1) (op x2 y2)) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x)))) -> R' (@iterate A B op s f) (@iterate A B op s g).
Axiom thm_ITERATE_DELETE : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall a : A, ((@finite_set A s) /\ (@IN A a s)) -> (op (f a) (@iterate A B op (@DELETE A s a) f)) = (@iterate A B op s f).
Axiom thm_ITERATE_DELTA : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall a : A, forall s : A -> Prop, (@iterate A B op s (fun x : A => @COND B (x = a) (f x) (@neutral B op))) = (@COND B (@IN A a s) (f a) (@neutral B op)).
Axiom thm_ITERATE_IMAGE : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall f : A -> B, forall g : B -> C, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@iterate B C op (@IMAGE A B f s) g) = (@iterate A C op s (@o A B C g f)).
Axiom thm_ITERATE_BIJECTION : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall p : A -> A, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall y : A, (@IN A y s) -> @ex1 A (fun x : A => (@IN A x s) /\ ((p x) = y)))) -> (@iterate A B op s f) = (@iterate A B op s (@o A A B f p)).
Axiom thm_ITERATE_ITERATE_PRODUCT : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall s : A -> Prop, forall t : A -> B -> Prop, forall x : A -> B -> C, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> @finite_set B (t i))) -> (@iterate A C op s (fun i : A => @iterate B C op (t i) (x i))) = (@iterate (prod A B) C op (@GSPEC (prod A B) (fun GEN_PVAR_243 : prod A B => exists i : A, exists j : B, @SETSPEC (prod A B) GEN_PVAR_243 ((@IN A i s) /\ (@IN B j (t i))) (@pair A B i j))) (@GABS ((prod A B) -> C) (fun f : (prod A B) -> C => forall i : A, forall j : B, @eq C (f (@pair A B i j)) (x i j)))).
Axiom thm_ITERATE_EQ : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (g x)) -> (@iterate A B op s f) = (@iterate A B op s g).
Axiom thm_ITERATE_RESTRICT_SET : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall P : A -> Prop, forall s : A -> Prop, forall f : A -> B, (@iterate A B op (@GSPEC A (fun GEN_PVAR_244 : A => exists x : A, @SETSPEC A GEN_PVAR_244 ((@IN A x s) /\ (P x)) x)) f) = (@iterate A B op s (fun x : A => @COND B (P x) (f x) (@neutral B op))).
Axiom thm_ITERATE_EQ_GENERAL : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall s : A -> Prop, forall t : B -> Prop, forall f : A -> C, forall g : B -> C, forall h : A -> B, ((forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((h x) = y))) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ ((g (h x)) = (f x)))) -> (@iterate A C op s f) = (@iterate B C op t g).
Axiom thm_ITERATE_EQ_GENERAL_INVERSES : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall s : A -> Prop, forall t : B -> Prop, forall f : A -> C, forall g : B -> C, forall h : A -> B, forall k : B -> A, ((forall y : B, (@IN B y t) -> (@IN A (k y) s) /\ ((h (k y)) = y)) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ (((k (h x)) = x) /\ ((g (h x)) = (f x))))) -> (@iterate A C op s f) = (@iterate B C op t g).
Axiom thm_ITERATE_INJECTION : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall p : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((p x) = (p y)))) -> x = y))) -> (@iterate A B op s (@o A A B f p)) = (@iterate A B op s f).
Axiom thm_ITERATE_UNION_NONZERO : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (forall x : A, (@IN A x (@setI A s t)) -> (f x) = (@neutral B op)))) -> (@iterate A B op (@setU A s t) f) = (op (@iterate A B op s f) (@iterate A B op t f)).
Axiom thm_ITERATE_OP : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, (@finite_set A s) -> (@iterate A B op s (fun x : A => op (f x) (g x))) = (op (@iterate A B op s f) (@iterate A B op s g)).
Axiom thm_ITERATE_SUPERSET : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall u : A -> Prop, forall v : A -> Prop, ((@subset A u v) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (@neutral B op))) -> (@iterate A B op v f) = (@iterate A B op u f).
Axiom thm_ITERATE_UNIV : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, (@subset A (@support A B op f (@setT A)) s) -> (@iterate A B op s f) = (@iterate A B op (@setT A) f).
Axiom thm_ITERATE_SWAP : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall f : A -> B -> C, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@iterate A C op s (fun i : A => @iterate B C op t (f i))) = (@iterate B C op t (fun j : B => @iterate A C op s (fun i : A => f i j))).
Axiom thm_ITERATE_IMAGE_NONZERO : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall g : B -> C, forall f : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((~ (x = y)) /\ ((f x) = (f y))))) -> (g (f x)) = (@neutral C op))) -> (@iterate B C op (@IMAGE A B f s) g) = (@iterate A C op s (@o A B C g f)).
Axiom thm_ITERATE_IMAGE_GEN : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall f : A -> B, forall g : A -> C, forall s : A -> Prop, (@finite_set A s) -> (@iterate A C op s g) = (@iterate B C op (@IMAGE A B f s) (fun y : B => @iterate A C op (@GSPEC A (fun GEN_PVAR_247 : A => exists x : A, @SETSPEC A GEN_PVAR_247 ((@IN A x s) /\ ((f x) = y)) x)) g)).
Axiom thm_ITERATE_CASES : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall s : A -> Prop, forall P : A -> Prop, forall f : A -> B, forall g : A -> B, (@finite_set A s) -> (@iterate A B op s (fun x : A => @COND B (P x) (f x) (g x))) = (op (@iterate A B op (@GSPEC A (fun GEN_PVAR_250 : A => exists x : A, @SETSPEC A GEN_PVAR_250 ((@IN A x s) /\ (P x)) x)) f) (@iterate A B op (@GSPEC A (fun GEN_PVAR_251 : A => exists x : A, @SETSPEC A GEN_PVAR_251 ((@IN A x s) /\ (~ (P x))) x)) g)).
Axiom thm_ITERATE_OP_GEN : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, ((@finite_set A (@support A B op f s)) /\ (@finite_set A (@support A B op g s))) -> (@iterate A B op s (fun x : A => op (f x) (g x))) = (op (@iterate A B op s f) (@iterate A B op s g)).
Axiom thm_ITERATE_CLAUSES_NUMSEG : forall {A : Type'} (f : nat -> A), forall op : A -> A -> A, (@monoidal A op) -> (forall m : nat, (@iterate nat A op (dotdot m (NUMERAL O)) f) = (@COND A (m = (NUMERAL O)) (f (NUMERAL O)) (@neutral A op))) /\ (forall m : nat, forall n : nat, (@iterate nat A op (dotdot m (S n)) f) = (@COND A (leqn m (S n)) (op (@iterate nat A op (dotdot m n) f) (f (S n))) (@iterate nat A op (dotdot m n) f))).
Axiom thm_ITERATE_CLAUSES_NUMSEG_LT : forall {A : Type'} (f : nat -> A), forall op : A -> A -> A, (@monoidal A op) -> ((@iterate nat A op (@GSPEC nat (fun GEN_PVAR_256 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_256 (ltn i (NUMERAL O)) i)) f) = (@neutral A op)) /\ (forall k : nat, (@iterate nat A op (@GSPEC nat (fun GEN_PVAR_257 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_257 (ltn i (S k)) i)) f) = (op (@iterate nat A op (@GSPEC nat (fun GEN_PVAR_258 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_258 (ltn i k) i)) f) (f k))).
Axiom thm_ITERATE_CLAUSES_NUMSEG_LE : forall {A : Type'} (f : nat -> A), forall op : A -> A -> A, (@monoidal A op) -> ((@iterate nat A op (@GSPEC nat (fun GEN_PVAR_259 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_259 (leqn i (NUMERAL O)) i)) f) = (f (NUMERAL O))) /\ (forall k : nat, (@iterate nat A op (@GSPEC nat (fun GEN_PVAR_260 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_260 (leqn i (S k)) i)) f) = (op (@iterate nat A op (@GSPEC nat (fun GEN_PVAR_261 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_261 (leqn i k) i)) f) (f (S k)))).
Axiom thm_ITERATE_PAIR : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) -> forall f : nat -> A, forall m : nat, forall n : nat, (@iterate nat A op (dotdot (muln (NUMERAL (BIT0 (BIT1 O))) m) (addn (muln (NUMERAL (BIT0 (BIT1 O))) n) (NUMERAL (BIT1 O)))) f) = (@iterate nat A op (dotdot m n) (fun i : nat => op (f (muln (NUMERAL (BIT0 (BIT1 O))) i)) (f (addn (muln (NUMERAL (BIT0 (BIT1 O))) i) (NUMERAL (BIT1 O)))))).
Axiom thm_ITERATE_REFLECT : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) -> forall x : nat -> A, forall m : nat, forall n : nat, (@iterate nat A op (dotdot m n) x) = (@COND A (ltn n m) (@neutral A op) (@iterate nat A op (dotdot (NUMERAL O) (subn n m)) (fun i : nat => x (subn n i)))).
Axiom thm_ITERATO_SUPPORT : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (@iterato A K dom neut op ltle (@GSPEC K (fun GEN_PVAR_270 : K => exists i : K, @SETSPEC K GEN_PVAR_270 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) f) = (@iterato A K dom neut op ltle k f).
Axiom thm_ITERATO_EXPAND_CASES : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (@iterato A K dom neut op ltle k f) = (@COND A (@finite_set K (@GSPEC K (fun GEN_PVAR_271 : K => exists i : K, @SETSPEC K GEN_PVAR_271 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) (@iterato A K dom neut op ltle (@GSPEC K (fun GEN_PVAR_272 : K => exists i : K, @SETSPEC K GEN_PVAR_272 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) f) neut).
Axiom thm_ITERATO_CLAUSES_GEN : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall f : K -> A, ((@iterato A K dom neut op ltle (@set0 K) f) = neut) /\ (forall i : K, forall k : K -> Prop, ((@finite_set K (@GSPEC K (fun GEN_PVAR_274 : K => exists j : K, @SETSPEC K GEN_PVAR_274 ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j))) /\ ((forall j : K, (@IN K j k) -> (i = j) \/ ((ltle i j) \/ (ltle j i))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) -> (@iterato A K dom neut op ltle (@INSERT K i k) f) = (@COND A ((@IN A (f i) dom) -> ((f i) = neut) \/ (@IN K i k)) (@iterato A K dom neut op ltle k f) (op (f i) (@iterato A K dom neut op ltle k f)))).
Axiom thm_ITERATO_CLAUSES : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall f : K -> A, ((@iterato A K dom neut op ltle (@set0 K) f) = neut) /\ (forall i : K, forall k : K -> Prop, ((@finite_set K (@GSPEC K (fun GEN_PVAR_275 : K => exists i' : K, @SETSPEC K GEN_PVAR_275 ((@IN K i' k) /\ (@IN A (f i') (@setD A dom (@INSERT A neut (@set0 A))))) i'))) /\ (forall j : K, (@IN K j k) -> (ltle i j) /\ (~ (ltle j i)))) -> (@iterato A K dom neut op ltle (@INSERT K i k) f) = (@COND A ((@IN A (f i) dom) -> ((f i) = neut) \/ (@IN K i k)) (@iterato A K dom neut op ltle k f) (op (f i) (@iterato A K dom neut op ltle k f)))).
Axiom thm_ITERATO_CLAUSES_EXISTS : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall f : K -> A, ((@iterato A K dom neut op ltle (@set0 K) f) = neut) /\ (forall k : K -> Prop, ((@finite_set K (@GSPEC K (fun GEN_PVAR_276 : K => exists i : K, @SETSPEC K GEN_PVAR_276 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_277 : K => exists i : K, @SETSPEC K GEN_PVAR_277 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) -> exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ ((@iterato A K dom neut op ltle k f) = (op (f i) (@iterato A K dom neut op ltle (@DELETE K k i) f))))).
Axiom thm_ITERATO_EQ : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, forall g : K -> A, (forall i : K, (@IN K i k) -> (f i) = (g i)) -> (@iterato A K dom neut op ltle k f) = (@iterato A K dom neut op ltle k g).
Axiom thm_ITERATO_INDUCT : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, forall P : A -> Prop, ((P neut) /\ (forall i : K, forall x : A, ((@IN K i k) /\ ((@IN A (f i) dom) /\ ((~ ((f i) = neut)) /\ (P x)))) -> P (op (f i) x))) -> P (@iterato A K dom neut op ltle k f).
Axiom thm_ITERATO_CLOSED : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, forall P : A -> Prop, ((P neut) /\ ((forall x : A, forall y : A, ((P x) /\ (P y)) -> P (op x y)) /\ (forall i : K, ((@IN K i k) /\ ((@IN A (f i) dom) /\ (~ ((f i) = neut)))) -> P (f i)))) -> P (@iterato A K dom neut op ltle k f).
Axiom thm_ITERATO_ITERATE : forall {A K : Type'}, forall op : A -> A -> A, forall ltle : K -> K -> Prop, (@monoidal A op) -> (@iterato A K (@setT A) (@neutral A op) op ltle) = (@iterate K A op).
Axiom thm_ITERATO_CLAUSES_NUMSEG_LEFT : forall {A : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall f : nat -> A, forall m : nat, forall n : nat, (@iterato A nat dom neut op leqn (dotdot m n) f) = (@COND A (leqn m n) (@COND A ((@IN A (f m) dom) -> (f m) = neut) (@iterato A nat dom neut op leqn (dotdot (addn m (NUMERAL (BIT1 O))) n) f) (op (f m) (@iterato A nat dom neut op leqn (dotdot (addn m (NUMERAL (BIT1 O))) n) f))) neut).
Axiom thm_nproduct : forall {A : Type'}, (@nproduct A) = (@iterate A nat muln).
Axiom thm_NEUTRAL_MUL : (@neutral nat muln) = (NUMERAL (BIT1 O)).
Axiom thm_MONOIDAL_MUL : @monoidal nat muln.
Axiom thm_NPRODUCT_CLAUSES : forall {A B : Type'}, (forall f : A -> nat, (@nproduct A (@set0 A) f) = (NUMERAL (BIT1 O))) /\ (forall x : B, forall f : B -> nat, forall s : B -> Prop, (@finite_set B s) -> (@nproduct B (@INSERT B x s) f) = (@COND nat (@IN B x s) (@nproduct B s f) (muln (f x) (@nproduct B s f)))).
Axiom thm_iproduct : forall {A : Type'}, (@iproduct A) = (@iterate A int mulz).
Axiom thm_NEUTRAL_INT_MUL : (@neutral int mulz) = (int_of_nat (NUMERAL (BIT1 O))).
Axiom thm_MONOIDAL_INT_MUL : @monoidal int mulz.
Axiom thm_IPRODUCT_CLAUSES : forall {A B : Type'}, (forall f : A -> int, (@iproduct A (@set0 A) f) = (int_of_nat (NUMERAL (BIT1 O)))) /\ (forall x : B, forall f : B -> int, forall s : B -> Prop, (@finite_set B s) -> (@iproduct B (@INSERT B x s) f) = (@COND int (@IN B x s) (@iproduct B s f) (mulz (f x) (@iproduct B s f)))).
Axiom thm_product : forall {A : Type'}, (@product A) = (@iterate A R mulr).
Axiom thm_NEUTRAL_REAL_MUL : (@neutral R mulr) = (R_of_nat (NUMERAL (BIT1 O))).
Axiom thm_MONOIDAL_REAL_MUL : @monoidal R mulr.
Axiom thm_PRODUCT_CLAUSES : forall {A B : Type'}, (forall f : A -> R, (@product A (@set0 A) f) = (R_of_nat (NUMERAL (BIT1 O)))) /\ (forall x : B, forall f : B -> R, forall s : B -> Prop, (@finite_set B s) -> (@product B (@INSERT B x s) f) = (@COND R (@IN B x s) (@product B s f) (mulr (f x) (@product B s f)))).
Axiom thm_isum : forall {A : Type'}, (@isum A) = (@iterate A int addz).
Axiom thm_NEUTRAL_INT_ADD : (@neutral int addz) = (int_of_nat (NUMERAL O)).
Axiom thm_MONOIDAL_INT_ADD : @monoidal int addz.
Axiom thm_ISUM_CLAUSES : forall {A B : Type'}, (forall f : A -> int, (@isum A (@set0 A) f) = (int_of_nat (NUMERAL O))) /\ (forall x : B, forall f : B -> int, forall s : B -> Prop, (@finite_set B s) -> (@isum B (@INSERT B x s) f) = (@COND int (@IN B x s) (@isum B s f) (addz (f x) (@isum B s f)))).
Axiom thm_nsum : forall {A : Type'}, (@nsum A) = (@iterate A nat addn).
Axiom thm_NEUTRAL_ADD : (@neutral nat addn) = (NUMERAL O).
Axiom thm_MONOIDAL_ADD : @monoidal nat addn.
Axiom thm_NSUM_DEGENERATE : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (~ (@finite_set A (@GSPEC A (fun GEN_PVAR_286 : A => exists x : A, @SETSPEC A GEN_PVAR_286 ((@IN A x s) /\ (~ ((f x) = (NUMERAL O)))) x)))) -> (@nsum A s f) = (NUMERAL O).
Axiom thm_NSUM_CLAUSES : forall {A B : Type'}, (forall f : A -> nat, (@nsum A (@set0 A) f) = (NUMERAL O)) /\ (forall x : B, forall f : B -> nat, forall s : B -> Prop, (@finite_set B s) -> (@nsum B (@INSERT B x s) f) = (@COND nat (@IN B x s) (@nsum B s f) (addn (f x) (@nsum B s f)))).
Axiom thm_NSUM_UNION : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (@DISJOINT A s t))) -> (@nsum A (@setU A s t) f) = (addn (@nsum A s f) (@nsum A t f)).
Axiom thm_NSUM_DIFF : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@subset A t s)) -> (@nsum A (@setD A s t) f) = (subn (@nsum A s f) (@nsum A t f)).
Axiom thm_NSUM_INCL_EXCL : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall f : A -> nat, ((@finite_set A s) /\ (@finite_set A t)) -> (addn (@nsum A s f) (@nsum A t f)) = (addn (@nsum A (@setU A s t) f) (@nsum A (@setI A s t) f)).
Axiom thm_NSUM_SUPPORT : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (@nsum A (@support A nat addn f s) f) = (@nsum A s f).
Axiom thm_NSUM_ADD : forall {A : Type'}, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, (@finite_set A s) -> (@nsum A s (fun x : A => addn (f x) (g x))) = (addn (@nsum A s f) (@nsum A s g)).
Axiom thm_NSUM_ADD_GEN : forall {A : Type'}, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((@finite_set A (@GSPEC A (fun GEN_PVAR_287 : A => exists x : A, @SETSPEC A GEN_PVAR_287 ((@IN A x s) /\ (~ ((f x) = (NUMERAL O)))) x))) /\ (@finite_set A (@GSPEC A (fun GEN_PVAR_288 : A => exists x : A, @SETSPEC A GEN_PVAR_288 ((@IN A x s) /\ (~ ((g x) = (NUMERAL O)))) x)))) -> (@nsum A s (fun x : A => addn (f x) (g x))) = (addn (@nsum A s f) (@nsum A s g)).
Axiom thm_NSUM_EQ_0 : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (NUMERAL O)) -> (@nsum A s f) = (NUMERAL O).
Axiom thm_NSUM_0 : forall {A : Type'}, forall s : A -> Prop, (@nsum A s (fun n : A => NUMERAL O)) = (NUMERAL O).
Axiom thm_NSUM_LMUL : forall {A : Type'}, forall f : A -> nat, forall c : nat, forall s : A -> Prop, (@nsum A s (fun x : A => muln c (f x))) = (muln c (@nsum A s f)).
Axiom thm_NSUM_RMUL : forall {A : Type'}, forall f : A -> nat, forall c : nat, forall s : A -> Prop, (@nsum A s (fun x : A => muln (f x) c)) = (muln (@nsum A s f) c).
Axiom thm_NSUM_LE : forall {A : Type'}, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> leqn (f x) (g x))) -> leqn (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_LT : forall {A : Type'}, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> leqn (f x) (g x)) /\ (exists x : A, (@IN A x s) /\ (ltn (f x) (g x))))) -> ltn (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_LT_ALL : forall {A : Type'}, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> ltn (f x) (g x)))) -> ltn (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_EQ : forall {A : Type'}, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (g x)) -> (@nsum A s f) = (@nsum A s g).
Axiom thm_NSUM_CONST : forall {A : Type'}, forall c : nat, forall s : A -> Prop, (@finite_set A s) -> (@nsum A s (fun n : A => c)) = (muln (@CARD A s) c).
Axiom thm_NSUM_POS_BOUND : forall {A : Type'}, forall f : A -> nat, forall b : nat, forall s : A -> Prop, ((@finite_set A s) /\ (leqn (@nsum A s f) b)) -> forall x : A, (@IN A x s) -> leqn (f x) b.
Axiom thm_NSUM_EQ_0_IFF : forall {A : Type'} (f : A -> nat), forall s : A -> Prop, (@finite_set A s) -> ((@nsum A s f) = (NUMERAL O)) = (forall x : A, (@IN A x s) -> (f x) = (NUMERAL O)).
Axiom thm_NSUM_POS_LT : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, ((@finite_set A s) /\ (exists x : A, (@IN A x s) /\ (ltn (NUMERAL O) (f x)))) -> ltn (NUMERAL O) (@nsum A s f).
Axiom thm_NSUM_POS_LT_ALL : forall {A : Type'}, forall s : A -> Prop, forall f : A -> nat, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall i : A, (@IN A i s) -> ltn (NUMERAL O) (f i)))) -> ltn (NUMERAL O) (@nsum A s f).
Axiom thm_NSUM_DELETE : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, forall a : A, ((@finite_set A s) /\ (@IN A a s)) -> (addn (f a) (@nsum A (@DELETE A s a) f)) = (@nsum A s f).
Axiom thm_NSUM_SING : forall {A : Type'}, forall f : A -> nat, forall x : A, (@nsum A (@INSERT A x (@set0 A)) f) = (f x).
Axiom thm_NSUM_DELTA : forall {A : Type'} (b : nat), forall s : A -> Prop, forall a : A, (@nsum A s (fun x : A => @COND nat (x = a) b (NUMERAL O))) = (@COND nat (@IN A a s) b (NUMERAL O)).
Axiom thm_NSUM_SWAP : forall {A B : Type'}, forall f : A -> B -> nat, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@nsum A s (fun i : A => @nsum B t (f i))) = (@nsum B t (fun j : B => @nsum A s (fun i : A => f i j))).
Axiom thm_NSUM_IMAGE : forall {A B : Type'}, forall f : A -> B, forall g : B -> nat, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@nsum B (@IMAGE A B f s) g) = (@nsum A s (@o A B nat g f)).
Axiom thm_NSUM_SUPERSET : forall {A : Type'}, forall f : A -> nat, forall u : A -> Prop, forall v : A -> Prop, ((@subset A u v) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (NUMERAL O))) -> (@nsum A v f) = (@nsum A u f).
Axiom thm_NSUM_UNIV : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (@subset A (@support A nat addn f (@setT A)) s) -> (@nsum A s f) = (@nsum A (@setT A) f).
Axiom thm_NSUM_UNION_RZERO : forall {A : Type'}, forall f : A -> nat, forall u : A -> Prop, forall v : A -> Prop, ((@finite_set A u) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (NUMERAL O))) -> (@nsum A (@setU A u v) f) = (@nsum A u f).
Axiom thm_NSUM_UNION_LZERO : forall {A : Type'}, forall f : A -> nat, forall u : A -> Prop, forall v : A -> Prop, ((@finite_set A v) /\ (forall x : A, ((@IN A x u) /\ (~ (@IN A x v))) -> (f x) = (NUMERAL O))) -> (@nsum A (@setU A u v) f) = (@nsum A v f).
Axiom thm_NSUM_RESTRICT : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (@finite_set A s) -> (@nsum A s (fun x : A => @COND nat (@IN A x s) (f x) (NUMERAL O))) = (@nsum A s f).
Axiom thm_NSUM_BOUND : forall {A : Type'}, forall s : A -> Prop, forall f : A -> nat, forall b : nat, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> leqn (f x) b)) -> leqn (@nsum A s f) (muln (@CARD A s) b).
Axiom thm_NSUM_BOUND_GEN : forall {A : Type'}, forall s : A -> Prop, forall f : A -> nat, forall b : nat, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> leqn (f x) (divn b (@CARD A s))))) -> leqn (@nsum A s f) b.
Axiom thm_NSUM_BOUND_LT : forall {A : Type'}, forall s : A -> Prop, forall f : A -> nat, forall b : nat, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> leqn (f x) b) /\ (exists x : A, (@IN A x s) /\ (ltn (f x) b)))) -> ltn (@nsum A s f) (muln (@CARD A s) b).
Axiom thm_NSUM_BOUND_LT_ALL : forall {A : Type'}, forall s : A -> Prop, forall f : A -> nat, forall b : nat, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> ltn (f x) b))) -> ltn (@nsum A s f) (muln (@CARD A s) b).
Axiom thm_NSUM_BOUND_LT_GEN : forall {A : Type'}, forall s : A -> Prop, forall f : A -> nat, forall b : nat, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> ltn (f x) (divn b (@CARD A s))))) -> ltn (@nsum A s f) b.
Axiom thm_NSUM_UNION_EQ : forall {A : Type'} (f : A -> nat), forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@finite_set A u) /\ (((@setI A s t) = (@set0 A)) /\ ((@setU A s t) = u))) -> (addn (@nsum A s f) (@nsum A t f)) = (@nsum A u f).
Axiom thm_NSUM_EQ_SUPERSET : forall {A : Type'} (g : A -> nat), forall f : A -> nat, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ ((@subset A t s) /\ ((forall x : A, (@IN A x t) -> (f x) = (g x)) /\ (forall x : A, ((@IN A x s) /\ (~ (@IN A x t))) -> (f x) = (NUMERAL O))))) -> (@nsum A s f) = (@nsum A t g).
Axiom thm_NSUM_RESTRICT_SET : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall f : A -> nat, (@nsum A (@GSPEC A (fun GEN_PVAR_289 : A => exists x : A, @SETSPEC A GEN_PVAR_289 ((@IN A x s) /\ (P x)) x)) f) = (@nsum A s (fun x : A => @COND nat (P x) (f x) (NUMERAL O))).
Axiom thm_NSUM_NSUM_RESTRICT : forall {A B : Type'}, forall R' : A -> B -> Prop, forall f : A -> B -> nat, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@nsum A s (fun x : A => @nsum B (@GSPEC B (fun GEN_PVAR_290 : B => exists y : B, @SETSPEC B GEN_PVAR_290 ((@IN B y t) /\ (R' x y)) y)) (fun y : B => f x y))) = (@nsum B t (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_291 : A => exists x : A, @SETSPEC A GEN_PVAR_291 ((@IN A x s) /\ (R' x y)) x)) (fun x : A => f x y))).
Axiom thm_CARD_EQ_NSUM : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (@CARD A s) = (@nsum A s (fun x : A => NUMERAL (BIT1 O))).
Axiom thm_NSUM_MULTICOUNT_GEN : forall {A B : Type'}, forall R' : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : B -> nat, ((@finite_set A s) /\ ((@finite_set B t) /\ (forall j : B, (@IN B j t) -> (@CARD A (@GSPEC A (fun GEN_PVAR_293 : A => exists i : A, @SETSPEC A GEN_PVAR_293 ((@IN A i s) /\ (R' i j)) i))) = (k j)))) -> (@nsum A s (fun i : A => @CARD B (@GSPEC B (fun GEN_PVAR_294 : B => exists j : B, @SETSPEC B GEN_PVAR_294 ((@IN B j t) /\ (R' i j)) j)))) = (@nsum B t (fun i : B => k i)).
Axiom thm_NSUM_MULTICOUNT : forall {A B : Type'}, forall R' : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : nat, ((@finite_set A s) /\ ((@finite_set B t) /\ (forall j : B, (@IN B j t) -> (@CARD A (@GSPEC A (fun GEN_PVAR_295 : A => exists i : A, @SETSPEC A GEN_PVAR_295 ((@IN A i s) /\ (R' i j)) i))) = k))) -> (@nsum A s (fun i : A => @CARD B (@GSPEC B (fun GEN_PVAR_296 : B => exists j : B, @SETSPEC B GEN_PVAR_296 ((@IN B j t) /\ (R' i j)) j)))) = (muln k (@CARD B t)).
Axiom thm_NSUM_IMAGE_GEN : forall {A B : Type'}, forall f : A -> B, forall g : A -> nat, forall s : A -> Prop, (@finite_set A s) -> (@nsum A s g) = (@nsum B (@IMAGE A B f s) (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_297 : A => exists x : A, @SETSPEC A GEN_PVAR_297 ((@IN A x s) /\ ((f x) = y)) x)) g)).
Axiom thm_NSUM_GROUP : forall {A B : Type'}, forall f : A -> B, forall g : A -> nat, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@subset B (@IMAGE A B f s) t)) -> (@nsum B t (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_298 : A => exists x : A, @SETSPEC A GEN_PVAR_298 ((@IN A x s) /\ ((f x) = y)) x)) g)) = (@nsum A s g).
Axiom thm_NSUM_GROUP_RELATION : forall {A B : Type'}, forall R' : A -> B -> Prop, forall g : A -> nat, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> @ex1 B (fun y : B => (@IN B y t) /\ (R' x y)))) -> (@nsum B t (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_299 : A => exists x : A, @SETSPEC A GEN_PVAR_299 ((@IN A x s) /\ (R' x y)) x)) g)) = (@nsum A s g).
Axiom thm_NSUM_SUBSET : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> nat, ((@finite_set A u) /\ ((@finite_set A v) /\ (forall x : A, (@IN A x (@setD A u v)) -> (f x) = (NUMERAL O)))) -> leqn (@nsum A u f) (@nsum A v f).
Axiom thm_NSUM_SUBSET_SIMPLE : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> nat, ((@finite_set A v) /\ (@subset A u v)) -> leqn (@nsum A u f) (@nsum A v f).
Axiom thm_NSUM_LE_GEN : forall {A : Type'}, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> leqn (f x) (g x)) /\ (@finite_set A (@GSPEC A (fun GEN_PVAR_301 : A => exists x : A, @SETSPEC A GEN_PVAR_301 ((@IN A x s) /\ (~ ((g x) = (NUMERAL O)))) x)))) -> leqn (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_MUL_BOUND : forall {A : Type'}, forall a : A -> nat, forall b : A -> nat, forall s : A -> Prop, (@finite_set A s) -> leqn (@nsum A s (fun i : A => muln (a i) (b i))) (muln (@nsum A s a) (@nsum A s b)).
Axiom thm_NSUM_IMAGE_NONZERO : forall {A B : Type'}, forall d : B -> nat, forall i : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((~ (x = y)) /\ ((i x) = (i y))))) -> (d (i x)) = (NUMERAL O))) -> (@nsum B (@IMAGE A B i s) d) = (@nsum A s (@o A B nat d i)).
Axiom thm_NSUM_BIJECTION : forall {A : Type'}, forall f : A -> nat, forall p : A -> A, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall y : A, (@IN A y s) -> @ex1 A (fun x : A => (@IN A x s) /\ ((p x) = y)))) -> (@nsum A s f) = (@nsum A s (@o A A nat f p)).
Axiom thm_NSUM_NSUM_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall x : A -> B -> nat, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> @finite_set B (t i))) -> (@nsum A s (fun i : A => @nsum B (t i) (x i))) = (@nsum (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_302 : prod A B => exists i : A, exists j : B, @SETSPEC (prod A B) GEN_PVAR_302 ((@IN A i s) /\ (@IN B j (t i))) (@pair A B i j))) (@GABS ((prod A B) -> nat) (fun f : (prod A B) -> nat => forall i : A, forall j : B, @eq nat (f (@pair A B i j)) (x i j)))).
Axiom thm_NSUM_EQ_GENERAL : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> nat, forall g : B -> nat, forall h : A -> B, ((forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((h x) = y))) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ ((g (h x)) = (f x)))) -> (@nsum A s f) = (@nsum B t g).
Axiom thm_NSUM_EQ_GENERAL_INVERSES : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> nat, forall g : B -> nat, forall h : A -> B, forall k : B -> A, ((forall y : B, (@IN B y t) -> (@IN A (k y) s) /\ ((h (k y)) = y)) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ (((k (h x)) = x) /\ ((g (h x)) = (f x))))) -> (@nsum A s f) = (@nsum B t g).
Axiom thm_NSUM_INJECTION : forall {A : Type'}, forall f : A -> nat, forall p : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((p x) = (p y)))) -> x = y))) -> (@nsum A s (@o A A nat f p)) = (@nsum A s f).
Axiom thm_NSUM_UNION_NONZERO : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (forall x : A, (@IN A x (@setI A s t)) -> (f x) = (NUMERAL O)))) -> (@nsum A (@setU A s t) f) = (addn (@nsum A s f) (@nsum A t f)).
Axiom thm_NSUM_UNIONS_NONZERO : forall {A : Type'}, forall f : A -> nat, forall s : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) s) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t) /\ (forall t1 : A -> Prop, forall t2 : A -> Prop, forall x : A, ((@IN (A -> Prop) t1 s) /\ ((@IN (A -> Prop) t2 s) /\ ((~ (t1 = t2)) /\ ((@IN A x t1) /\ (@IN A x t2))))) -> (f x) = (NUMERAL O)))) -> (@nsum A (@UNIONS A s) f) = (@nsum (A -> Prop) s (fun t : A -> Prop => @nsum A t f)).
Axiom thm_NSUM_CASES : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, forall f : A -> nat, forall g : A -> nat, (@finite_set A s) -> (@nsum A s (fun x : A => @COND nat (P x) (f x) (g x))) = (addn (@nsum A (@GSPEC A (fun GEN_PVAR_303 : A => exists x : A, @SETSPEC A GEN_PVAR_303 ((@IN A x s) /\ (P x)) x)) f) (@nsum A (@GSPEC A (fun GEN_PVAR_304 : A => exists x : A, @SETSPEC A GEN_PVAR_304 ((@IN A x s) /\ (~ (P x))) x)) g)).
Axiom thm_NSUM_CLOSED : forall {A : Type'}, forall P : nat -> Prop, forall f : A -> nat, forall s : A -> Prop, ((P (NUMERAL O)) /\ ((forall x : nat, forall y : nat, ((P x) /\ (P y)) -> P (addn x y)) /\ (forall a : A, (@IN A a s) -> P (f a)))) -> P (@nsum A s f).
Axiom thm_NSUM_RELATED : forall {A : Type'}, forall R' : nat -> nat -> Prop, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((R' (NUMERAL O) (NUMERAL O)) /\ ((forall m : nat, forall n : nat, forall m' : nat, forall n' : nat, ((R' m n) /\ (R' m' n')) -> R' (addn m m') (addn n n')) /\ ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))))) -> R' (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_CLOSED_NONEMPTY : forall {A : Type'}, forall P : nat -> Prop, forall f : A -> nat, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ ((forall x : nat, forall y : nat, ((P x) /\ (P y)) -> P (addn x y)) /\ (forall a : A, (@IN A a s) -> P (f a))))) -> P (@nsum A s f).
Axiom thm_NSUM_RELATED_NONEMPTY : forall {A : Type'}, forall R' : nat -> nat -> Prop, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((forall m : nat, forall n : nat, forall m' : nat, forall n' : nat, ((R' m n) /\ (R' m' n')) -> R' (addn m m') (addn n n')) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))))) -> R' (@nsum A s f) (@nsum A s g).
Axiom thm_NSUM_ADD_NUMSEG : forall f : nat -> nat, forall g : nat -> nat, forall m : nat, forall n : nat, (@nsum nat (dotdot m n) (fun i : nat => addn (f i) (g i))) = (addn (@nsum nat (dotdot m n) f) (@nsum nat (dotdot m n) g)).
Axiom thm_NSUM_LE_NUMSEG : forall f : nat -> nat, forall g : nat -> nat, forall m : nat, forall n : nat, (forall i : nat, ((leqn m i) /\ (leqn i n)) -> leqn (f i) (g i)) -> leqn (@nsum nat (dotdot m n) f) (@nsum nat (dotdot m n) g).
Axiom thm_NSUM_EQ_NUMSEG : forall f : nat -> nat, forall g : nat -> nat, forall m : nat, forall n : nat, (forall i : nat, ((leqn m i) /\ (leqn i n)) -> (f i) = (g i)) -> (@nsum nat (dotdot m n) f) = (@nsum nat (dotdot m n) g).
Axiom thm_NSUM_CONST_NUMSEG : forall c : nat, forall m : nat, forall n : nat, (@nsum nat (dotdot m n) (fun n' : nat => c)) = (muln (subn (addn n (NUMERAL (BIT1 O))) m) c).
Axiom thm_NSUM_EQ_0_NUMSEG : forall f : nat -> nat, forall m : nat, forall n : nat, (forall i : nat, ((leqn m i) /\ (leqn i n)) -> (f i) = (NUMERAL O)) -> (@nsum nat (dotdot m n) f) = (NUMERAL O).
Axiom thm_NSUM_EQ_0_IFF_NUMSEG : forall f : nat -> nat, forall m : nat, forall n : nat, ((@nsum nat (dotdot m n) f) = (NUMERAL O)) = (forall i : nat, ((leqn m i) /\ (leqn i n)) -> (f i) = (NUMERAL O)).
Axiom thm_NSUM_TRIV_NUMSEG : forall f : nat -> nat, forall m : nat, forall n : nat, (ltn n m) -> (@nsum nat (dotdot m n) f) = (NUMERAL O).
Axiom thm_NSUM_SING_NUMSEG : forall f : nat -> nat, forall n : nat, (@nsum nat (dotdot n n) f) = (f n).
Axiom thm_NSUM_CLAUSES_NUMSEG : forall (f : nat -> nat), (forall m : nat, (@nsum nat (dotdot m (NUMERAL O)) f) = (@COND nat (m = (NUMERAL O)) (f (NUMERAL O)) (NUMERAL O))) /\ (forall m : nat, forall n : nat, (@nsum nat (dotdot m (S n)) f) = (@COND nat (leqn m (S n)) (addn (@nsum nat (dotdot m n) f) (f (S n))) (@nsum nat (dotdot m n) f))).
Axiom thm_NSUM_CLAUSES_NUMSEG_LT : forall (f : nat -> nat), ((@nsum nat (@GSPEC nat (fun GEN_PVAR_305 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_305 (ltn i (NUMERAL O)) i)) f) = (NUMERAL O)) /\ (forall k : nat, (@nsum nat (@GSPEC nat (fun GEN_PVAR_306 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_306 (ltn i (S k)) i)) f) = (addn (@nsum nat (@GSPEC nat (fun GEN_PVAR_307 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_307 (ltn i k) i)) f) (f k))).
Axiom thm_NSUM_CLAUSES_NUMSEG_LE : forall (f : nat -> nat), ((@nsum nat (@GSPEC nat (fun GEN_PVAR_308 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_308 (leqn i (NUMERAL O)) i)) f) = (f (NUMERAL O))) /\ (forall k : nat, (@nsum nat (@GSPEC nat (fun GEN_PVAR_309 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_309 (leqn i (S k)) i)) f) = (addn (@nsum nat (@GSPEC nat (fun GEN_PVAR_310 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_310 (leqn i k) i)) f) (f (S k)))).
Axiom thm_NSUM_SWAP_NUMSEG : forall a : nat, forall b : nat, forall c : nat, forall d : nat, forall f : nat -> nat -> nat, (@nsum nat (dotdot a b) (fun i : nat => @nsum nat (dotdot c d) (f i))) = (@nsum nat (dotdot c d) (fun j : nat => @nsum nat (dotdot a b) (fun i : nat => f i j))).
Axiom thm_NSUM_ADD_SPLIT : forall f : nat -> nat, forall m : nat, forall n : nat, forall p : nat, (leqn m (addn n (NUMERAL (BIT1 O)))) -> (@nsum nat (dotdot m (addn n p)) f) = (addn (@nsum nat (dotdot m n) f) (@nsum nat (dotdot (addn n (NUMERAL (BIT1 O))) (addn n p)) f)).
Axiom thm_NSUM_OFFSET : forall p : nat, forall f : nat -> nat, forall m : nat, forall n : nat, (@nsum nat (dotdot (addn m p) (addn n p)) f) = (@nsum nat (dotdot m n) (fun i : nat => f (addn i p))).
Axiom thm_NSUM_OFFSET_0 : forall f : nat -> nat, forall m : nat, forall n : nat, (leqn m n) -> (@nsum nat (dotdot m n) f) = (@nsum nat (dotdot (NUMERAL O) (subn n m)) (fun i : nat => f (addn i m))).
Axiom thm_NSUM_CLAUSES_LEFT : forall f : nat -> nat, forall m : nat, forall n : nat, (leqn m n) -> (@nsum nat (dotdot m n) f) = (addn (f m) (@nsum nat (dotdot (addn m (NUMERAL (BIT1 O))) n) f)).
Axiom thm_NSUM_CLAUSES_RIGHT : forall f : nat -> nat, forall m : nat, forall n : nat, ((ltn (NUMERAL O) n) /\ (leqn m n)) -> (@nsum nat (dotdot m n) f) = (addn (@nsum nat (dotdot m (subn n (NUMERAL (BIT1 O)))) f) (f n)).
Axiom thm_NSUM_PAIR : forall f : nat -> nat, forall m : nat, forall n : nat, (@nsum nat (dotdot (muln (NUMERAL (BIT0 (BIT1 O))) m) (addn (muln (NUMERAL (BIT0 (BIT1 O))) n) (NUMERAL (BIT1 O)))) f) = (@nsum nat (dotdot m n) (fun i : nat => addn (f (muln (NUMERAL (BIT0 (BIT1 O))) i)) (f (addn (muln (NUMERAL (BIT0 (BIT1 O))) i) (NUMERAL (BIT1 O)))))).
Axiom thm_NSUM_REFLECT : forall x : nat -> nat, forall m : nat, forall n : nat, (@nsum nat (dotdot m n) x) = (@COND nat (ltn n m) (NUMERAL O) (@nsum nat (dotdot (NUMERAL O) (subn n m)) (fun i : nat => x (subn n i)))).
Axiom thm_MOD_NSUM_MOD : forall {A : Type'}, forall f : A -> nat, forall n : nat, forall s : A -> Prop, (@finite_set A s) -> (modn (@nsum A s f) n) = (modn (@nsum A s (fun i : A => modn (f i) n)) n).
Axiom thm_MOD_NSUM_MOD_NUMSEG : forall f : nat -> nat, forall a : nat, forall b : nat, forall n : nat, (modn (@nsum nat (dotdot a b) f) n) = (modn (@nsum nat (dotdot a b) (fun i : nat => modn (f i) n)) n).
Axiom thm_CONG_NSUM : forall {A : Type'}, forall n : nat, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> @eq2 nat (f x) (g x) (num_mod n))) -> @eq2 nat (@nsum A s f) (@nsum A s g) (num_mod n).
Axiom thm_CARD_UNIONS : forall {A : Type'}, forall s : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) s) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t) /\ (forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t s) /\ ((@IN (A -> Prop) u s) /\ (~ (t = u)))) -> (@setI A t u) = (@set0 A)))) -> (@CARD A (@UNIONS A s)) = (@nsum (A -> Prop) s (@CARD A)).
Axiom thm_sum : forall {A : Type'}, (@sum A) = (@iterate A R addr).
Axiom thm_NEUTRAL_REAL_ADD : (@neutral R addr) = (R_of_nat (NUMERAL O)).
Axiom thm_MONOIDAL_REAL_ADD : @monoidal R addr.
Axiom thm_SUM_DEGENERATE : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (~ (@finite_set A (@GSPEC A (fun GEN_PVAR_313 : A => exists x : A, @SETSPEC A GEN_PVAR_313 ((@IN A x s) /\ (~ ((f x) = (R_of_nat (NUMERAL O))))) x)))) -> (@sum A s f) = (R_of_nat (NUMERAL O)).
Axiom thm_SUM_CLAUSES : forall {A B : Type'}, (forall f : A -> R, (@sum A (@set0 A) f) = (R_of_nat (NUMERAL O))) /\ (forall x : B, forall f : B -> R, forall s : B -> Prop, (@finite_set B s) -> (@sum B (@INSERT B x s) f) = (@COND R (@IN B x s) (@sum B s f) (addr (f x) (@sum B s f)))).
Axiom thm_SUM_UNION : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (@DISJOINT A s t))) -> (@sum A (@setU A s t) f) = (addr (@sum A s f) (@sum A t f)).
Axiom thm_SUM_DIFF : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ (@subset A t s)) -> (@sum A (@setD A s t) f) = (subr (@sum A s f) (@sum A t f)).
Axiom thm_SUM_INCL_EXCL : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall f : A -> R, ((@finite_set A s) /\ (@finite_set A t)) -> (addr (@sum A s f) (@sum A t f)) = (addr (@sum A (@setU A s t) f) (@sum A (@setI A s t) f)).
Axiom thm_SUM_SUPPORT : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (@sum A (@support A R addr f s) f) = (@sum A s f).
Axiom thm_SUM_ADD : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, (@finite_set A s) -> (@sum A s (fun x : A => addr (f x) (g x))) = (addr (@sum A s f) (@sum A s g)).
Axiom thm_SUM_ADD_GEN : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((@finite_set A (@GSPEC A (fun GEN_PVAR_314 : A => exists x : A, @SETSPEC A GEN_PVAR_314 ((@IN A x s) /\ (~ ((f x) = (R_of_nat (NUMERAL O))))) x))) /\ (@finite_set A (@GSPEC A (fun GEN_PVAR_315 : A => exists x : A, @SETSPEC A GEN_PVAR_315 ((@IN A x s) /\ (~ ((g x) = (R_of_nat (NUMERAL O))))) x)))) -> (@sum A s (fun x : A => addr (f x) (g x))) = (addr (@sum A s f) (@sum A s g)).
Axiom thm_SUM_EQ_0 : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (R_of_nat (NUMERAL O))) -> (@sum A s f) = (R_of_nat (NUMERAL O)).
Axiom thm_SUM_0 : forall {A : Type'}, forall s : A -> Prop, (@sum A s (fun n : A => R_of_nat (NUMERAL O))) = (R_of_nat (NUMERAL O)).
Axiom thm_SUM_LMUL : forall {A : Type'}, forall f : A -> R, forall c : R, forall s : A -> Prop, (@sum A s (fun x : A => mulr c (f x))) = (mulr c (@sum A s f)).
Axiom thm_SUM_RMUL : forall {A : Type'}, forall f : A -> R, forall c : R, forall s : A -> Prop, (@sum A s (fun x : A => mulr (f x) c)) = (mulr (@sum A s f) c).
Axiom thm_SUM_NEG : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (@sum A s (fun x : A => oppr (f x))) = (oppr (@sum A s f)).
Axiom thm_SUM_SUB : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, (@finite_set A s) -> (@sum A s (fun x : A => subr (f x) (g x))) = (subr (@sum A s f) (@sum A s g)).
Axiom thm_SUM_LE : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> ler (f x) (g x))) -> ler (@sum A s f) (@sum A s g).
Axiom thm_SUM_LT : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> ler (f x) (g x)) /\ (exists x : A, (@IN A x s) /\ (ltr (f x) (g x))))) -> ltr (@sum A s f) (@sum A s g).
Axiom thm_SUM_LT_ALL : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> ltr (f x) (g x)))) -> ltr (@sum A s f) (@sum A s g).
Axiom thm_SUM_POS_LT : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> ler (R_of_nat (NUMERAL O)) (f x)) /\ (exists x : A, (@IN A x s) /\ (ltr (R_of_nat (NUMERAL O)) (f x))))) -> ltr (R_of_nat (NUMERAL O)) (@sum A s f).
Axiom thm_SUM_POS_LT_ALL : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall i : A, (@IN A i s) -> ltr (R_of_nat (NUMERAL O)) (f i)))) -> ltr (R_of_nat (NUMERAL O)) (@sum A s f).
Axiom thm_SUM_EQ : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (g x)) -> (@sum A s f) = (@sum A s g).
Axiom thm_SUM_ABS : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (@finite_set A s) -> ler (normr (@sum A s f)) (@sum A s (fun x : A => normr (f x))).
Axiom thm_SUM_ABS_LE : forall {A : Type'}, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> ler (normr (f x)) (g x))) -> ler (normr (@sum A s f)) (@sum A s g).
Axiom thm_SUM_CONST : forall {A : Type'}, forall c : R, forall s : A -> Prop, (@finite_set A s) -> (@sum A s (fun n : A => c)) = (mulr (R_of_nat (@CARD A s)) c).
Axiom thm_SUM_POS_LE : forall {A : Type'} (f : A -> R), forall s : A -> Prop, (forall x : A, (@IN A x s) -> ler (R_of_nat (NUMERAL O)) (f x)) -> ler (R_of_nat (NUMERAL O)) (@sum A s f).
Axiom thm_SUM_POS_BOUND : forall {A : Type'}, forall f : A -> R, forall b : R, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> ler (R_of_nat (NUMERAL O)) (f x)) /\ (ler (@sum A s f) b))) -> forall x : A, (@IN A x s) -> ler (f x) b.
Axiom thm_SUM_POS_EQ_0 : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> ler (R_of_nat (NUMERAL O)) (f x)) /\ ((@sum A s f) = (R_of_nat (NUMERAL O))))) -> forall x : A, (@IN A x s) -> (f x) = (R_of_nat (NUMERAL O)).
Axiom thm_SUM_ZERO_EXISTS : forall {A : Type'}, forall u : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((@sum A s u) = (R_of_nat (NUMERAL O)))) -> (forall i : A, (@IN A i s) -> (u i) = (R_of_nat (NUMERAL O))) \/ (exists j : A, exists k : A, (@IN A j s) /\ ((ltr (u j) (R_of_nat (NUMERAL O))) /\ ((@IN A k s) /\ (gtr (u k) (R_of_nat (NUMERAL O)))))).
Axiom thm_SUM_DELETE : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, forall a : A, ((@finite_set A s) /\ (@IN A a s)) -> (@sum A (@DELETE A s a) f) = (subr (@sum A s f) (f a)).
Axiom thm_SUM_DELETE_CASES : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, forall a : A, (@finite_set A s) -> (@sum A (@DELETE A s a) f) = (@COND R (@IN A a s) (subr (@sum A s f) (f a)) (@sum A s f)).
Axiom thm_SUM_SING : forall {A : Type'}, forall f : A -> R, forall x : A, (@sum A (@INSERT A x (@set0 A)) f) = (f x).
Axiom thm_SUM_DELTA : forall {A : Type'} (b : R), forall s : A -> Prop, forall a : A, (@sum A s (fun x : A => @COND R (x = a) b (R_of_nat (NUMERAL O)))) = (@COND R (@IN A a s) b (R_of_nat (NUMERAL O))).
Axiom thm_SUM_SWAP : forall {A B : Type'}, forall f : A -> B -> R, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@sum A s (fun i : A => @sum B t (f i))) = (@sum B t (fun j : B => @sum A s (fun i : A => f i j))).
Axiom thm_SUM_IMAGE : forall {A B : Type'}, forall f : A -> B, forall g : B -> R, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@sum B (@IMAGE A B f s) g) = (@sum A s (@o A B R g f)).
Axiom thm_SUM_SUPERSET : forall {A : Type'}, forall f : A -> R, forall u : A -> Prop, forall v : A -> Prop, ((@subset A u v) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (R_of_nat (NUMERAL O)))) -> (@sum A v f) = (@sum A u f).
Axiom thm_SUM_UNIV : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (@subset A (@support A R addr f (@setT A)) s) -> (@sum A s f) = (@sum A (@setT A) f).
Axiom thm_SUM_UNION_RZERO : forall {A : Type'}, forall f : A -> R, forall u : A -> Prop, forall v : A -> Prop, ((@finite_set A u) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (R_of_nat (NUMERAL O)))) -> (@sum A (@setU A u v) f) = (@sum A u f).
Axiom thm_SUM_UNION_LZERO : forall {A : Type'}, forall f : A -> R, forall u : A -> Prop, forall v : A -> Prop, ((@finite_set A v) /\ (forall x : A, ((@IN A x u) /\ (~ (@IN A x v))) -> (f x) = (R_of_nat (NUMERAL O)))) -> (@sum A (@setU A u v) f) = (@sum A v f).
Axiom thm_SUM_RESTRICT : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, (@finite_set A s) -> (@sum A s (fun x : A => @COND R (@IN A x s) (f x) (R_of_nat (NUMERAL O)))) = (@sum A s f).
Axiom thm_SUM_BOUND : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> ler (f x) b)) -> ler (@sum A s f) (mulr (R_of_nat (@CARD A s)) b).
Axiom thm_SUM_BOUND_GEN : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> ler (f x) (divr b (R_of_nat (@CARD A s)))))) -> ler (@sum A s f) b.
Axiom thm_SUM_ABS_BOUND : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> ler (normr (f x)) b)) -> ler (normr (@sum A s f)) (mulr (R_of_nat (@CARD A s)) b).
Axiom thm_SUM_BOUND_LT : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> ler (f x) b) /\ (exists x : A, (@IN A x s) /\ (ltr (f x) b)))) -> ltr (@sum A s f) (mulr (R_of_nat (@CARD A s)) b).
Axiom thm_SUM_BOUND_LT_ALL : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> ltr (f x) b))) -> ltr (@sum A s f) (mulr (R_of_nat (@CARD A s)) b).
Axiom thm_SUM_BOUND_LT_GEN : forall {A : Type'}, forall s : A -> Prop, forall f : A -> R, forall b : R, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> ltr (f x) (divr b (R_of_nat (@CARD A s)))))) -> ltr (@sum A s f) b.
Axiom thm_SUM_UNION_EQ : forall {A : Type'} (f : A -> R), forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@finite_set A u) /\ (((@setI A s t) = (@set0 A)) /\ ((@setU A s t) = u))) -> (addr (@sum A s f) (@sum A t f)) = (@sum A u f).
Axiom thm_SUM_EQ_SUPERSET : forall {A : Type'} (g : A -> R), forall f : A -> R, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A t) /\ ((@subset A t s) /\ ((forall x : A, (@IN A x t) -> (f x) = (g x)) /\ (forall x : A, ((@IN A x s) /\ (~ (@IN A x t))) -> (f x) = (R_of_nat (NUMERAL O)))))) -> (@sum A s f) = (@sum A t g).
Axiom thm_SUM_RESTRICT_SET : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall f : A -> R, (@sum A (@GSPEC A (fun GEN_PVAR_318 : A => exists x : A, @SETSPEC A GEN_PVAR_318 ((@IN A x s) /\ (P x)) x)) f) = (@sum A s (fun x : A => @COND R (P x) (f x) (R_of_nat (NUMERAL O)))).
Axiom thm_SUM_SUM_RESTRICT : forall {A B : Type'}, forall R' : A -> B -> Prop, forall f : A -> B -> R, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@finite_set B t)) -> (@sum A s (fun x : A => @sum B (@GSPEC B (fun GEN_PVAR_319 : B => exists y : B, @SETSPEC B GEN_PVAR_319 ((@IN B y t) /\ (R' x y)) y)) (fun y : B => f x y))) = (@sum B t (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_320 : A => exists x : A, @SETSPEC A GEN_PVAR_320 ((@IN A x s) /\ (R' x y)) x)) (fun x : A => f x y))).
Axiom thm_CARD_EQ_SUM : forall {A : Type'}, forall s : A -> Prop, (@finite_set A s) -> (R_of_nat (@CARD A s)) = (@sum A s (fun x : A => R_of_nat (NUMERAL (BIT1 O)))).
Axiom thm_SUM_MULTICOUNT_GEN : forall {A B : Type'}, forall R' : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : B -> nat, ((@finite_set A s) /\ ((@finite_set B t) /\ (forall j : B, (@IN B j t) -> (@CARD A (@GSPEC A (fun GEN_PVAR_322 : A => exists i : A, @SETSPEC A GEN_PVAR_322 ((@IN A i s) /\ (R' i j)) i))) = (k j)))) -> (@sum A s (fun i : A => R_of_nat (@CARD B (@GSPEC B (fun GEN_PVAR_323 : B => exists j : B, @SETSPEC B GEN_PVAR_323 ((@IN B j t) /\ (R' i j)) j))))) = (@sum B t (fun i : B => R_of_nat (k i))).
Axiom thm_SUM_MULTICOUNT : forall {A B : Type'}, forall R' : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : nat, ((@finite_set A s) /\ ((@finite_set B t) /\ (forall j : B, (@IN B j t) -> (@CARD A (@GSPEC A (fun GEN_PVAR_324 : A => exists i : A, @SETSPEC A GEN_PVAR_324 ((@IN A i s) /\ (R' i j)) i))) = k))) -> (@sum A s (fun i : A => R_of_nat (@CARD B (@GSPEC B (fun GEN_PVAR_325 : B => exists j : B, @SETSPEC B GEN_PVAR_325 ((@IN B j t) /\ (R' i j)) j))))) = (R_of_nat (muln k (@CARD B t))).
Axiom thm_SUM_IMAGE_GEN : forall {A B : Type'}, forall f : A -> B, forall g : A -> R, forall s : A -> Prop, (@finite_set A s) -> (@sum A s g) = (@sum B (@IMAGE A B f s) (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_326 : A => exists x : A, @SETSPEC A GEN_PVAR_326 ((@IN A x s) /\ ((f x) = y)) x)) g)).
Axiom thm_SUM_GROUP : forall {A B : Type'}, forall f : A -> B, forall g : A -> R, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (@subset B (@IMAGE A B f s) t)) -> (@sum B t (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_327 : A => exists x : A, @SETSPEC A GEN_PVAR_327 ((@IN A x s) /\ ((f x) = y)) x)) g)) = (@sum A s g).
Axiom thm_SUM_GROUP_RELATION : forall {A B : Type'}, forall R' : A -> B -> Prop, forall g : A -> R, forall s : A -> Prop, forall t : B -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> @ex1 B (fun y : B => (@IN B y t) /\ (R' x y)))) -> (@sum B t (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_328 : A => exists x : A, @SETSPEC A GEN_PVAR_328 ((@IN A x s) /\ (R' x y)) x)) g)) = (@sum A s g).
Axiom thm_REAL_OF_NUM_SUM : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (@finite_set A s) -> (R_of_nat (@nsum A s f)) = (@sum A s (fun x : A => R_of_nat (f x))).
Axiom thm_SUM_SUBSET : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> R, ((@finite_set A u) /\ ((@finite_set A v) /\ ((forall x : A, (@IN A x (@setD A u v)) -> ler (f x) (R_of_nat (NUMERAL O))) /\ (forall x : A, (@IN A x (@setD A v u)) -> ler (R_of_nat (NUMERAL O)) (f x))))) -> ler (@sum A u f) (@sum A v f).
Axiom thm_SUM_SUBSET_SIMPLE : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> R, ((@finite_set A v) /\ ((@subset A u v) /\ (forall x : A, (@IN A x (@setD A v u)) -> ler (R_of_nat (NUMERAL O)) (f x)))) -> ler (@sum A u f) (@sum A v f).
Axiom thm_SUM_MUL_BOUND : forall {A : Type'}, forall a : A -> R, forall b : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> (ler (R_of_nat (NUMERAL O)) (a i)) /\ (ler (R_of_nat (NUMERAL O)) (b i)))) -> ler (@sum A s (fun i : A => mulr (a i) (b i))) (mulr (@sum A s a) (@sum A s b)).
Axiom thm_SUM_IMAGE_NONZERO : forall {A B : Type'}, forall d : B -> R, forall i : A -> B, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((~ (x = y)) /\ ((i x) = (i y))))) -> (d (i x)) = (R_of_nat (NUMERAL O)))) -> (@sum B (@IMAGE A B i s) d) = (@sum A s (@o A B R d i)).
Axiom thm_SUM_BIJECTION : forall {A : Type'}, forall f : A -> R, forall p : A -> A, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall y : A, (@IN A y s) -> @ex1 A (fun x : A => (@IN A x s) /\ ((p x) = y)))) -> (@sum A s f) = (@sum A s (@o A A R f p)).
Axiom thm_SUM_SUM_PRODUCT : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall x : A -> B -> R, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> @finite_set B (t i))) -> (@sum A s (fun i : A => @sum B (t i) (x i))) = (@sum (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_329 : prod A B => exists i : A, exists j : B, @SETSPEC (prod A B) GEN_PVAR_329 ((@IN A i s) /\ (@IN B j (t i))) (@pair A B i j))) (@GABS ((prod A B) -> R) (fun f : (prod A B) -> R => forall i : A, forall j : B, @eq R (f (@pair A B i j)) (x i j)))).
Axiom thm_SUM_EQ_GENERAL : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> R, forall g : B -> R, forall h : A -> B, ((forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((h x) = y))) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ ((g (h x)) = (f x)))) -> (@sum A s f) = (@sum B t g).
Axiom thm_SUM_EQ_GENERAL_INVERSES : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall f : A -> R, forall g : B -> R, forall h : A -> B, forall k : B -> A, ((forall y : B, (@IN B y t) -> (@IN A (k y) s) /\ ((h (k y)) = y)) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ (((k (h x)) = x) /\ ((g (h x)) = (f x))))) -> (@sum A s f) = (@sum B t g).
Axiom thm_SUM_INJECTION : forall {A : Type'}, forall f : A -> R, forall p : A -> A, forall s : A -> Prop, ((@finite_set A s) /\ ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((p x) = (p y)))) -> x = y))) -> (@sum A s (@o A A R f p)) = (@sum A s f).
Axiom thm_SUM_UNION_NONZERO : forall {A : Type'}, forall f : A -> R, forall s : A -> Prop, forall t : A -> Prop, ((@finite_set A s) /\ ((@finite_set A t) /\ (forall x : A, (@IN A x (@setI A s t)) -> (f x) = (R_of_nat (NUMERAL O))))) -> (@sum A (@setU A s t) f) = (addr (@sum A s f) (@sum A t f)).
Axiom thm_SUM_UNIONS_NONZERO : forall {A : Type'}, forall f : A -> R, forall s : (A -> Prop) -> Prop, ((@finite_set (A -> Prop) s) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t s) -> @finite_set A t) /\ (forall t1 : A -> Prop, forall t2 : A -> Prop, forall x : A, ((@IN (A -> Prop) t1 s) /\ ((@IN (A -> Prop) t2 s) /\ ((~ (t1 = t2)) /\ ((@IN A x t1) /\ (@IN A x t2))))) -> (f x) = (R_of_nat (NUMERAL O))))) -> (@sum A (@UNIONS A s) f) = (@sum (A -> Prop) s (fun t : A -> Prop => @sum A t f)).
Axiom thm_SUM_CASES : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, forall f : A -> R, forall g : A -> R, (@finite_set A s) -> (@sum A s (fun x : A => @COND R (P x) (f x) (g x))) = (addr (@sum A (@GSPEC A (fun GEN_PVAR_330 : A => exists x : A, @SETSPEC A GEN_PVAR_330 ((@IN A x s) /\ (P x)) x)) f) (@sum A (@GSPEC A (fun GEN_PVAR_331 : A => exists x : A, @SETSPEC A GEN_PVAR_331 ((@IN A x s) /\ (~ (P x))) x)) g)).
Axiom thm_SUM_CASES_1 : forall {A : Type'} (y : R) (f : A -> R), forall s : A -> Prop, forall a : A, ((@finite_set A s) /\ (@IN A a s)) -> (@sum A s (fun x : A => @COND R (x = a) y (f x))) = (addr (@sum A s f) (subr y (f a))).
Axiom thm_SUM_LE_INCLUDED : forall {A B : Type'}, forall f : A -> R, forall g : B -> R, forall s : A -> Prop, forall t : B -> Prop, forall i : B -> A, ((@finite_set A s) /\ ((@finite_set B t) /\ ((forall y : B, (@IN B y t) -> ler (R_of_nat (NUMERAL O)) (g y)) /\ (forall x : A, (@IN A x s) -> exists y : B, (@IN B y t) /\ (((i y) = x) /\ (ler (f x) (g y))))))) -> ler (@sum A s f) (@sum B t g).
Axiom thm_SUM_IMAGE_LE : forall {A B : Type'}, forall f : A -> B, forall g : B -> R, forall s : A -> Prop, ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> ler (R_of_nat (NUMERAL O)) (g (f x)))) -> ler (@sum B (@IMAGE A B f s) g) (@sum A s (@o A B R g f)).
Axiom thm_SUM_CLOSED : forall {A : Type'}, forall P : R -> Prop, forall f : A -> R, forall s : A -> Prop, ((P (R_of_nat (NUMERAL O))) /\ ((forall x : R, forall y : R, ((P x) /\ (P y)) -> P (addr x y)) /\ (forall a : A, (@IN A a s) -> P (f a)))) -> P (@sum A s f).
Axiom thm_SUM_RELATED : forall {A : Type'}, forall R' : R -> R -> Prop, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((R' (R_of_nat (NUMERAL O)) (R_of_nat (NUMERAL O))) /\ ((forall m : R, forall n : R, forall m' : R, forall n' : R, ((R' m n) /\ (R' m' n')) -> R' (addr m m') (addr n n')) /\ ((@finite_set A s) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))))) -> R' (@sum A s f) (@sum A s g).
Axiom thm_SUM_CLOSED_NONEMPTY : forall {A : Type'}, forall P : R -> Prop, forall f : A -> R, forall s : A -> Prop, ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ ((forall x : R, forall y : R, ((P x) /\ (P y)) -> P (addr x y)) /\ (forall a : A, (@IN A a s) -> P (f a))))) -> P (@sum A s f).
Axiom thm_SUM_RELATED_NONEMPTY : forall {A : Type'}, forall R' : R -> R -> Prop, forall f : A -> R, forall g : A -> R, forall s : A -> Prop, ((forall m : R, forall n : R, forall m' : R, forall n' : R, ((R' m n) /\ (R' m' n')) -> R' (addr m m') (addr n n')) /\ ((@finite_set A s) /\ ((~ (s = (@set0 A))) /\ (forall x : A, (@IN A x s) -> R' (f x) (g x))))) -> R' (@sum A s f) (@sum A s g).
Axiom thm_REAL_OF_NUM_SUM_GEN : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (@finite_set A (@GSPEC A (fun GEN_PVAR_335 : A => exists i : A, @SETSPEC A GEN_PVAR_335 ((@IN A i s) /\ (~ ((f i) = (NUMERAL O)))) i))) -> (R_of_nat (@nsum A s f)) = (@sum A s (fun x : A => R_of_nat (f x))).
Axiom thm_SUM_ADD_NUMSEG : forall f : nat -> R, forall g : nat -> R, forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun i : nat => addr (f i) (g i))) = (addr (@sum nat (dotdot m n) f) (@sum nat (dotdot m n) g)).
Axiom thm_SUM_SUB_NUMSEG : forall f : nat -> R, forall g : nat -> R, forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun i : nat => subr (f i) (g i))) = (subr (@sum nat (dotdot m n) f) (@sum nat (dotdot m n) g)).
Axiom thm_SUM_LE_NUMSEG : forall f : nat -> R, forall g : nat -> R, forall m : nat, forall n : nat, (forall i : nat, ((leqn m i) /\ (leqn i n)) -> ler (f i) (g i)) -> ler (@sum nat (dotdot m n) f) (@sum nat (dotdot m n) g).
Axiom thm_SUM_EQ_NUMSEG : forall f : nat -> R, forall g : nat -> R, forall m : nat, forall n : nat, (forall i : nat, ((leqn m i) /\ (leqn i n)) -> (f i) = (g i)) -> (@sum nat (dotdot m n) f) = (@sum nat (dotdot m n) g).
Axiom thm_SUM_ABS_NUMSEG : forall f : nat -> R, forall m : nat, forall n : nat, ler (normr (@sum nat (dotdot m n) f)) (@sum nat (dotdot m n) (fun i : nat => normr (f i))).
Axiom thm_SUM_CONST_NUMSEG : forall c : R, forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun n' : nat => c)) = (mulr (R_of_nat (subn (addn n (NUMERAL (BIT1 O))) m)) c).
Axiom thm_SUM_EQ_0_NUMSEG : forall f : nat -> R, forall m : nat, forall n : nat, (forall i : nat, ((leqn m i) /\ (leqn i n)) -> (f i) = (R_of_nat (NUMERAL O))) -> (@sum nat (dotdot m n) f) = (R_of_nat (NUMERAL O)).
Axiom thm_SUM_TRIV_NUMSEG : forall f : nat -> R, forall m : nat, forall n : nat, (ltn n m) -> (@sum nat (dotdot m n) f) = (R_of_nat (NUMERAL O)).
Axiom thm_SUM_POS_LE_NUMSEG : forall m : nat, forall n : nat, forall f : nat -> R, (forall p : nat, ((leqn m p) /\ (leqn p n)) -> ler (R_of_nat (NUMERAL O)) (f p)) -> ler (R_of_nat (NUMERAL O)) (@sum nat (dotdot m n) f).
Axiom thm_SUM_POS_EQ_0_NUMSEG : forall f : nat -> R, forall m : nat, forall n : nat, ((forall p : nat, ((leqn m p) /\ (leqn p n)) -> ler (R_of_nat (NUMERAL O)) (f p)) /\ ((@sum nat (dotdot m n) f) = (R_of_nat (NUMERAL O)))) -> forall p : nat, ((leqn m p) /\ (leqn p n)) -> (f p) = (R_of_nat (NUMERAL O)).
Axiom thm_SUM_SING_NUMSEG : forall f : nat -> R, forall n : nat, (@sum nat (dotdot n n) f) = (f n).
Axiom thm_SUM_CLAUSES_NUMSEG : forall (f : nat -> R), (forall m : nat, (@sum nat (dotdot m (NUMERAL O)) f) = (@COND R (m = (NUMERAL O)) (f (NUMERAL O)) (R_of_nat (NUMERAL O)))) /\ (forall m : nat, forall n : nat, (@sum nat (dotdot m (S n)) f) = (@COND R (leqn m (S n)) (addr (@sum nat (dotdot m n) f) (f (S n))) (@sum nat (dotdot m n) f))).
Axiom thm_SUM_CLAUSES_NUMSEG_LT : forall (f : nat -> R), ((@sum nat (@GSPEC nat (fun GEN_PVAR_336 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_336 (ltn i (NUMERAL O)) i)) f) = (R_of_nat (NUMERAL O))) /\ (forall k : nat, (@sum nat (@GSPEC nat (fun GEN_PVAR_337 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_337 (ltn i (S k)) i)) f) = (addr (@sum nat (@GSPEC nat (fun GEN_PVAR_338 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_338 (ltn i k) i)) f) (f k))).
Axiom thm_SUM_CLAUSES_NUMSEG_LE : forall (f : nat -> R), ((@sum nat (@GSPEC nat (fun GEN_PVAR_339 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_339 (leqn i (NUMERAL O)) i)) f) = (f (NUMERAL O))) /\ (forall k : nat, (@sum nat (@GSPEC nat (fun GEN_PVAR_340 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_340 (leqn i (S k)) i)) f) = (addr (@sum nat (@GSPEC nat (fun GEN_PVAR_341 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_341 (leqn i k) i)) f) (f (S k)))).
Axiom thm_SUM_SWAP_NUMSEG : forall a : nat, forall b : nat, forall c : nat, forall d : nat, forall f : nat -> nat -> R, (@sum nat (dotdot a b) (fun i : nat => @sum nat (dotdot c d) (f i))) = (@sum nat (dotdot c d) (fun j : nat => @sum nat (dotdot a b) (fun i : nat => f i j))).
Axiom thm_SUM_ADD_SPLIT : forall f : nat -> R, forall m : nat, forall n : nat, forall p : nat, (leqn m (addn n (NUMERAL (BIT1 O)))) -> (@sum nat (dotdot m (addn n p)) f) = (addr (@sum nat (dotdot m n) f) (@sum nat (dotdot (addn n (NUMERAL (BIT1 O))) (addn n p)) f)).
Axiom thm_SUM_OFFSET : forall p : nat, forall f : nat -> R, forall m : nat, forall n : nat, (@sum nat (dotdot (addn m p) (addn n p)) f) = (@sum nat (dotdot m n) (fun i : nat => f (addn i p))).
Axiom thm_SUM_OFFSET_0 : forall f : nat -> R, forall m : nat, forall n : nat, (leqn m n) -> (@sum nat (dotdot m n) f) = (@sum nat (dotdot (NUMERAL O) (subn n m)) (fun i : nat => f (addn i m))).
Axiom thm_SUM_CLAUSES_LEFT : forall f : nat -> R, forall m : nat, forall n : nat, (leqn m n) -> (@sum nat (dotdot m n) f) = (addr (f m) (@sum nat (dotdot (addn m (NUMERAL (BIT1 O))) n) f)).
Axiom thm_SUM_CLAUSES_RIGHT : forall f : nat -> R, forall m : nat, forall n : nat, ((ltn (NUMERAL O) n) /\ (leqn m n)) -> (@sum nat (dotdot m n) f) = (addr (@sum nat (dotdot m (subn n (NUMERAL (BIT1 O)))) f) (f n)).
Axiom thm_SUM_PAIR : forall f : nat -> R, forall m : nat, forall n : nat, (@sum nat (dotdot (muln (NUMERAL (BIT0 (BIT1 O))) m) (addn (muln (NUMERAL (BIT0 (BIT1 O))) n) (NUMERAL (BIT1 O)))) f) = (@sum nat (dotdot m n) (fun i : nat => addr (f (muln (NUMERAL (BIT0 (BIT1 O))) i)) (f (addn (muln (NUMERAL (BIT0 (BIT1 O))) i) (NUMERAL (BIT1 O)))))).
Axiom thm_SUM_REFLECT : forall x : nat -> R, forall m : nat, forall n : nat, (@sum nat (dotdot m n) x) = (@COND R (ltn n m) (R_of_nat (NUMERAL O)) (@sum nat (dotdot (NUMERAL O) (subn n m)) (fun i : nat => x (subn n i)))).
Axiom thm_REAL_OF_NUM_SUM_NUMSEG : forall f : nat -> nat, forall m : nat, forall n : nat, (R_of_nat (@nsum nat (dotdot m n) f)) = (@sum nat (dotdot m n) (fun i : nat => R_of_nat (f i))).
Axiom thm_SUM_PARTIAL_SUC : forall f : nat -> R, forall g : nat -> R, forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun k : nat => mulr (f k) (subr (g (addn k (NUMERAL (BIT1 O)))) (g k)))) = (@COND R (leqn m n) (subr (subr (mulr (f (addn n (NUMERAL (BIT1 O)))) (g (addn n (NUMERAL (BIT1 O))))) (mulr (f m) (g m))) (@sum nat (dotdot m n) (fun k : nat => mulr (g (addn k (NUMERAL (BIT1 O)))) (subr (f (addn k (NUMERAL (BIT1 O)))) (f k))))) (R_of_nat (NUMERAL O))).
Axiom thm_SUM_PARTIAL_PRE : forall f : nat -> R, forall g : nat -> R, forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun k : nat => mulr (f k) (subr (g k) (g (subn k (NUMERAL (BIT1 O))))))) = (@COND R (leqn m n) (subr (subr (mulr (f (addn n (NUMERAL (BIT1 O)))) (g n)) (mulr (f m) (g (subn m (NUMERAL (BIT1 O)))))) (@sum nat (dotdot m n) (fun k : nat => mulr (g k) (subr (f (addn k (NUMERAL (BIT1 O)))) (f k))))) (R_of_nat (NUMERAL O))).
Axiom thm_SUM_DIFFS : forall (f : nat -> R), forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun k : nat => subr (f k) (f (addn k (NUMERAL (BIT1 O)))))) = (@COND R (leqn m n) (subr (f m) (f (addn n (NUMERAL (BIT1 O))))) (R_of_nat (NUMERAL O))).
Axiom thm_SUM_DIFFS_ALT : forall (f : nat -> R), forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun k : nat => subr (f (addn k (NUMERAL (BIT1 O)))) (f k))) = (@COND R (leqn m n) (subr (f (addn n (NUMERAL (BIT1 O)))) (f m)) (R_of_nat (NUMERAL O))).
Axiom thm_SUM_COMBINE_R : forall f : nat -> R, forall m : nat, forall n : nat, forall p : nat, ((leqn m (addn n (NUMERAL (BIT1 O)))) /\ (leqn n p)) -> (addr (@sum nat (dotdot m n) f) (@sum nat (dotdot (addn n (NUMERAL (BIT1 O))) p) f)) = (@sum nat (dotdot m p) f).
Axiom thm_SUM_COMBINE_L : forall f : nat -> R, forall m : nat, forall n : nat, forall p : nat, ((ltn (NUMERAL O) n) /\ ((leqn m n) /\ (leqn n (addn p (NUMERAL (BIT1 O)))))) -> (addr (@sum nat (dotdot m (subn n (NUMERAL (BIT1 O)))) f) (@sum nat (dotdot n p) f)) = (@sum nat (dotdot m p) f).
Axiom thm_REAL_SUB_POW : forall x : R, forall y : R, forall n : nat, (leqn (NUMERAL (BIT1 O)) n) -> (subr (expr x n) (expr y n)) = (mulr (subr x y) (@sum nat (dotdot (NUMERAL O) (subn n (NUMERAL (BIT1 O)))) (fun i : nat => mulr (expr x i) (expr y (subn (subn n (NUMERAL (BIT1 O))) i))))).
Axiom thm_REAL_SUB_POW_R1 : forall x : R, forall n : nat, (leqn (NUMERAL (BIT1 O)) n) -> (subr (expr x n) (R_of_nat (NUMERAL (BIT1 O)))) = (mulr (subr x (R_of_nat (NUMERAL (BIT1 O)))) (@sum nat (dotdot (NUMERAL O) (subn n (NUMERAL (BIT1 O)))) (fun i : nat => expr x i))).
Axiom thm_REAL_SUB_POW_L1 : forall x : R, forall n : nat, (leqn (NUMERAL (BIT1 O)) n) -> (subr (R_of_nat (NUMERAL (BIT1 O))) (expr x n)) = (mulr (subr (R_of_nat (NUMERAL (BIT1 O))) x) (@sum nat (dotdot (NUMERAL O) (subn n (NUMERAL (BIT1 O)))) (fun i : nat => expr x i))).
Axiom thm_REAL_SUB_POLYFUN : forall a : nat -> R, forall x : R, forall y : R, forall n : nat, (leqn (NUMERAL (BIT1 O)) n) -> (subr (@sum nat (dotdot (NUMERAL O) n) (fun i : nat => mulr (a i) (expr x i))) (@sum nat (dotdot (NUMERAL O) n) (fun i : nat => mulr (a i) (expr y i)))) = (mulr (subr x y) (@sum nat (dotdot (NUMERAL O) (subn n (NUMERAL (BIT1 O)))) (fun j : nat => mulr (@sum nat (dotdot (addn j (NUMERAL (BIT1 O))) n) (fun i : nat => mulr (a i) (expr y (subn (subn i j) (NUMERAL (BIT1 O)))))) (expr x j)))).
Axiom thm_REAL_SUB_POLYFUN_ALT : forall a : nat -> R, forall x : R, forall y : R, forall n : nat, (leqn (NUMERAL (BIT1 O)) n) -> (subr (@sum nat (dotdot (NUMERAL O) n) (fun i : nat => mulr (a i) (expr x i))) (@sum nat (dotdot (NUMERAL O) n) (fun i : nat => mulr (a i) (expr y i)))) = (mulr (subr x y) (@sum nat (dotdot (NUMERAL O) (subn n (NUMERAL (BIT1 O)))) (fun j : nat => mulr (@sum nat (dotdot (NUMERAL O) (subn (subn n j) (NUMERAL (BIT1 O)))) (fun k : nat => mulr (a (addn j (addn k (NUMERAL (BIT1 O))))) (expr y k))) (expr x j)))).
Axiom thm_REAL_POLYFUN_ROOTBOUND : forall n : nat, forall c : nat -> R, (~ (forall i : nat, (@IN nat i (dotdot (NUMERAL O) n)) -> (c i) = (R_of_nat (NUMERAL O)))) -> (@finite_set R (@GSPEC R (fun GEN_PVAR_347 : R => exists x : R, @SETSPEC R GEN_PVAR_347 ((@sum nat (dotdot (NUMERAL O) n) (fun i : nat => mulr (c i) (expr x i))) = (R_of_nat (NUMERAL O))) x))) /\ (leqn (@CARD R (@GSPEC R (fun GEN_PVAR_348 : R => exists x : R, @SETSPEC R GEN_PVAR_348 ((@sum nat (dotdot (NUMERAL O) n) (fun i : nat => mulr (c i) (expr x i))) = (R_of_nat (NUMERAL O))) x))) n).
Axiom thm_REAL_POLYFUN_FINITE_ROOTS : forall n : nat, forall c : nat -> R, (@finite_set R (@GSPEC R (fun GEN_PVAR_350 : R => exists x : R, @SETSPEC R GEN_PVAR_350 ((@sum nat (dotdot (NUMERAL O) n) (fun i : nat => mulr (c i) (expr x i))) = (R_of_nat (NUMERAL O))) x))) = (exists i : nat, (@IN nat i (dotdot (NUMERAL O) n)) /\ (~ ((c i) = (R_of_nat (NUMERAL O))))).
Axiom thm_REAL_POLYFUN_EQ_0 : forall n : nat, forall c : nat -> R, (forall x : R, (@sum nat (dotdot (NUMERAL O) n) (fun i : nat => mulr (c i) (expr x i))) = (R_of_nat (NUMERAL O))) = (forall i : nat, (@IN nat i (dotdot (NUMERAL O) n)) -> (c i) = (R_of_nat (NUMERAL O))).
Axiom thm_REAL_POLYFUN_EQ_CONST : forall n : nat, forall c : nat -> R, forall k : R, (forall x : R, (@sum nat (dotdot (NUMERAL O) n) (fun i : nat => mulr (c i) (expr x i))) = k) = (((c (NUMERAL O)) = k) /\ (forall i : nat, (@IN nat i (dotdot (NUMERAL (BIT1 O)) n)) -> (c i) = (R_of_nat (NUMERAL O)))).
Axiom thm_polynomial_function : forall p : R -> R, (polynomial_function p) = (exists m : nat, exists c : nat -> R, forall x : R, (p x) = (@sum nat (dotdot (NUMERAL O) m) (fun i : nat => mulr (c i) (expr x i)))).
Axiom thm_POLYNOMIAL_FUNCTION_CONST : forall c : R, polynomial_function (fun x : R => c).
Axiom thm_POLYNOMIAL_FUNCTION_ID : polynomial_function (fun x : R => x).
Axiom thm_POLYNOMIAL_FUNCTION_I : polynomial_function (@I R).
Axiom thm_POLYNOMIAL_FUNCTION_ADD : forall p : R -> R, forall q : R -> R, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (fun x : R => addr (p x) (q x)).
Axiom thm_POLYNOMIAL_FUNCTION_LMUL : forall p : R -> R, forall c : R, (polynomial_function p) -> polynomial_function (fun x : R => mulr c (p x)).
Axiom thm_POLYNOMIAL_FUNCTION_RMUL : forall p : R -> R, forall c : R, (polynomial_function p) -> polynomial_function (fun x : R => mulr (p x) c).
Axiom thm_POLYNOMIAL_FUNCTION_NEG : forall p : R -> R, (polynomial_function (fun x : R => oppr (p x))) = (polynomial_function p).
Axiom thm_POLYNOMIAL_FUNCTION_SUB : forall p : R -> R, forall q : R -> R, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (fun x : R => subr (p x) (q x)).
Axiom thm_POLYNOMIAL_FUNCTION_MUL : forall p : R -> R, forall q : R -> R, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (fun x : R => mulr (p x) (q x)).
Axiom thm_POLYNOMIAL_FUNCTION_SUM : forall {A : Type'}, forall s : A -> Prop, forall p : R -> A -> R, ((@finite_set A s) /\ (forall i : A, (@IN A i s) -> polynomial_function (fun x : R => p x i))) -> polynomial_function (fun x : R => @sum A s (p x)).
Axiom thm_POLYNOMIAL_FUNCTION_POW : forall p : R -> R, forall n : nat, (polynomial_function p) -> polynomial_function (fun x : R => expr (p x) n).
Axiom thm_POLYNOMIAL_FUNCTION_INDUCT : forall P : (R -> R) -> Prop, ((P (fun x : R => x)) /\ ((forall c : R, P (fun x : R => c)) /\ ((forall p : R -> R, forall q : R -> R, ((P p) /\ (P q)) -> P (fun x : R => addr (p x) (q x))) /\ (forall p : R -> R, forall q : R -> R, ((P p) /\ (P q)) -> P (fun x : R => mulr (p x) (q x)))))) -> forall p : R -> R, (polynomial_function p) -> P p.
Axiom thm_POLYNOMIAL_FUNCTION_o : forall p : R -> R, forall q : R -> R, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (@o R R R p q).
Axiom thm_POLYNOMIAL_FUNCTION_FINITE_ROOTS : forall p : R -> R, forall a : R, (polynomial_function p) -> (@finite_set R (@GSPEC R (fun GEN_PVAR_353 : R => exists x : R, @SETSPEC R GEN_PVAR_353 ((p x) = a) x))) = (~ (forall x : R, (p x) = a)).
Axiom thm_dimindex : forall {A : Type'}, forall s : A -> Prop, (@dimindex A s) = (@COND nat (@finite_set A (@setT A)) (@CARD A (@setT A)) (NUMERAL (BIT1 O))).
Axiom thm_DIMINDEX_NONZERO : forall {A : Type'}, forall s : A -> Prop, ~ ((@dimindex A s) = (NUMERAL O)).
Axiom thm_DIMINDEX_GE_1 : forall {A : Type'}, forall s : A -> Prop, leqn (NUMERAL (BIT1 O)) (@dimindex A s).
Axiom thm_DIMINDEX_UNIV : forall {A : Type'}, forall s : A -> Prop, (@dimindex A s) = (@dimindex A (@setT A)).
Axiom thm_DIMINDEX_UNIQUE : forall {A : Type'} (n : nat), (@HAS_SIZE A (@setT A) n) -> (@dimindex A (@setT A)) = n.
Axiom thm_UNIV_HAS_SIZE_DIMINDEX : forall {N' : Type'}, (@HAS_SIZE N' (@setT N') (@dimindex N' (@setT N'))) = (@finite_set N' (@setT N')).
Axiom thm_HAS_SIZE_1 : @HAS_SIZE unit (@setT unit) (NUMERAL (BIT1 O)).
Axiom thm_NUMSEG_LT_DIMINDEX : forall {N' : Type'}, (@GSPEC nat (fun GEN_PVAR_354 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_354 (ltn i (@dimindex N' (@setT N'))) i)) = (dotdot (NUMERAL O) (subn (@dimindex N' (@setT N')) (NUMERAL (BIT1 O)))).
Axiom thm_FINITE_IMAGE_IMAGE : forall {A : Type'}, (@setT (finite_image A)) = (@IMAGE nat (finite_image A) (@finite_index A) (dotdot (NUMERAL (BIT1 O)) (@dimindex A (@setT A)))).
Axiom thm_HAS_SIZE_FINITE_IMAGE : forall {A : Type'}, forall s : A -> Prop, @HAS_SIZE (finite_image A) (@setT (finite_image A)) (@dimindex A s).
Axiom thm_CARD_FINITE_IMAGE : forall {A : Type'}, forall s : A -> Prop, (@CARD (finite_image A) (@setT (finite_image A))) = (@dimindex A s).
Axiom thm_FINITE_FINITE_IMAGE : forall {A : Type'}, @finite_set (finite_image A) (@setT (finite_image A)).
Axiom thm_DIMINDEX_FINITE_IMAGE : forall {A : Type'}, forall s : (finite_image A) -> Prop, forall t : A -> Prop, (@dimindex (finite_image A) s) = (@dimindex A t).
Axiom thm_FINITE_INDEX_WORKS : forall {A : Type'}, forall i : finite_image A, @ex1 nat (fun n : nat => (leqn (NUMERAL (BIT1 O)) n) /\ ((leqn n (@dimindex A (@setT A))) /\ ((@finite_index A n) = i))).
Axiom thm_FINITE_INDEX_INJ : forall {A : Type'}, forall i : nat, forall j : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ ((leqn i (@dimindex A (@setT A))) /\ ((leqn (NUMERAL (BIT1 O)) j) /\ (leqn j (@dimindex A (@setT A)))))) -> ((@finite_index A i) = (@finite_index A j)) = (i = j).
Axiom thm_FORALL_FINITE_INDEX : forall {N' : Type'} (P : (finite_image N') -> Prop), (forall k : finite_image N', P k) = (forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex N' (@setT N')))) -> P (@finite_index N' i)).
Axiom thm_finite_index : forall {A N' : Type'}, forall x : cart A N', forall i : nat, (@dollar A N' x i) = (@dest_cart A N' x (@finite_index N' i)).
Axiom thm_CART_EQ : forall {A B : Type'}, forall x : cart A B, forall y : cart A B, (x = y) = (forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex B (@setT B)))) -> (@dollar A B x i) = (@dollar A B y i)).
Axiom thm_lambda : forall {A B : Type'}, forall g : nat -> A, (@lambda A B g) = (@ε (cart A B) (fun f : cart A B => forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (g i))).
Axiom thm_LAMBDA_BETA : forall {A B : Type'} (g : nat -> A), forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex B (@setT B)))) -> (@dollar A B (@lambda A B g) i) = (g i).
Axiom thm_LAMBDA_UNIQUE : forall {A B : Type'}, forall f : cart A B, forall g : nat -> A, (forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (g i)) = ((@lambda A B g) = f).
Axiom thm_LAMBDA_ETA : forall {A B : Type'}, forall g : cart A B, (@lambda A B (fun i : nat => @dollar A B g i)) = g.
Axiom thm_FINITE_INDEX_INRANGE : forall {A N' : Type'}, forall i : nat, exists k : nat, (leqn (NUMERAL (BIT1 O)) k) /\ ((leqn k (@dimindex N' (@setT N'))) /\ (forall x : cart A N', (@dollar A N' x i) = (@dollar A N' x k))).
Axiom thm_FINITE_INDEX_INRANGE_2 : forall {A B N' : Type'}, forall i : nat, exists k : nat, (leqn (NUMERAL (BIT1 O)) k) /\ ((leqn k (@dimindex N' (@setT N'))) /\ ((forall x : cart A N', (@dollar A N' x i) = (@dollar A N' x k)) /\ (forall y : cart B N', (@dollar B N' y i) = (@dollar B N' y k)))).
Axiom thm_CART_EQ_FULL : forall {A N' : Type'}, forall x : cart A N', forall y : cart A N', (x = y) = (forall i : nat, (@dollar A N' x i) = (@dollar A N' y i)).
Axiom thm_pastecart : forall {A M N' : Type'}, forall f : cart A M, forall g : cart A N', (@pastecart A M N' f g) = (@lambda A (finite_sum M N') (fun i : nat => @COND A (leqn i (@dimindex M (@setT M))) (@dollar A M f i) (@dollar A N' g (subn i (@dimindex M (@setT M)))))).
Axiom thm_fstcart : forall {A M N' : Type'}, forall f : cart A (finite_sum M N'), (@fstcart A M N' f) = (@lambda A M (fun i : nat => @dollar A (finite_sum M N') f i)).
Axiom thm_sndcart : forall {A M N' : Type'}, forall f : cart A (finite_sum M N'), (@sndcart A M N' f) = (@lambda A N' (fun i : nat => @dollar A (finite_sum M N') f (addn i (@dimindex M (@setT M))))).
Axiom thm_FINITE_SUM_IMAGE : forall {A B : Type'}, (@setT (finite_sum A B)) = (@IMAGE nat (finite_sum A B) (@mk_finite_sum A B) (dotdot (NUMERAL (BIT1 O)) (addn (@dimindex A (@setT A)) (@dimindex B (@setT B))))).
Axiom thm_DIMINDEX_HAS_SIZE_FINITE_SUM : forall {M N' : Type'}, @HAS_SIZE (finite_sum M N') (@setT (finite_sum M N')) (addn (@dimindex M (@setT M)) (@dimindex N' (@setT N'))).
Axiom thm_DIMINDEX_FINITE_SUM : forall {M N' : Type'}, (@dimindex (finite_sum M N') (@setT (finite_sum M N'))) = (addn (@dimindex M (@setT M)) (@dimindex N' (@setT N'))).
Axiom thm_FSTCART_PASTECART : forall {A M N' : Type'}, forall x : cart A M, forall y : cart A N', (@fstcart A M N' (@pastecart A M N' x y)) = x.
Axiom thm_SNDCART_PASTECART : forall {A M N' : Type'}, forall x : cart A M, forall y : cart A N', (@sndcart A M N' (@pastecart A M N' x y)) = y.
Axiom thm_PASTECART_FST_SND : forall {A M N' : Type'}, forall z : cart A (finite_sum M N'), (@pastecart A M N' (@fstcart A M N' z) (@sndcart A M N' z)) = z.
Axiom thm_PASTECART_EQ : forall {A M N' : Type'}, forall x : cart A (finite_sum M N'), forall y : cart A (finite_sum M N'), (x = y) = (((@fstcart A M N' x) = (@fstcart A M N' y)) /\ ((@sndcart A M N' x) = (@sndcart A M N' y))).
Axiom thm_FORALL_PASTECART : forall {A M N' : Type'} (P : (cart A (finite_sum M N')) -> Prop), (forall p : cart A (finite_sum M N'), P p) = (forall x : cart A M, forall y : cart A N', P (@pastecart A M N' x y)).
Axiom thm_EXISTS_PASTECART : forall {A M N' : Type'} (P : (cart A (finite_sum M N')) -> Prop), (exists p : cart A (finite_sum M N'), P p) = (exists x : cart A M, exists y : cart A N', P (@pastecart A M N' x y)).
Axiom thm_PASTECART_INJ : forall {A M N' : Type'}, forall x : cart A M, forall y : cart A N', forall w : cart A M, forall z : cart A N', ((@pastecart A M N' x y) = (@pastecart A M N' w z)) = ((x = w) /\ (y = z)).
Axiom thm_FSTCART_COMPONENT : forall {A M N' : Type'}, forall x : cart A (finite_sum M N'), forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex M (@setT M)))) -> (@dollar A M (@fstcart A M N' x) i) = (@dollar A (finite_sum M N') x i).
Axiom thm_SNDCART_COMPONENT : forall {A M N' : Type'}, forall x : cart A (finite_sum M N'), forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex N' (@setT N')))) -> (@dollar A N' (@sndcart A M N' x) i) = (@dollar A (finite_sum M N') x (addn i (@dimindex M (@setT M)))).
Axiom thm_PASTECART_COMPONENT : forall {A M N' : Type'}, (forall u : cart A M, forall v : cart A N', forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex M (@setT M)))) -> (@dollar A (finite_sum M N') (@pastecart A M N' u v) i) = (@dollar A M u i)) /\ (forall u : cart A M, forall v : cart A N', forall i : nat, ((leqn (addn (@dimindex M (@setT M)) (NUMERAL (BIT1 O))) i) /\ (leqn i (addn (@dimindex M (@setT M)) (@dimindex N' (@setT N'))))) -> (@dollar A (finite_sum M N') (@pastecart A M N' u v) i) = (@dollar A N' v (subn i (@dimindex M (@setT M))))).
Axiom thm_FINITE_DIFF_IMAGE : forall {A B : Type'}, (@setT (finite_diff A B)) = (@IMAGE nat (finite_diff A B) (@mk_finite_diff A B) (dotdot (NUMERAL (BIT1 O)) (@COND nat (ltn (@dimindex B (@setT B)) (@dimindex A (@setT A))) (subn (@dimindex A (@setT A)) (@dimindex B (@setT B))) (NUMERAL (BIT1 O))))).
Axiom thm_DIMINDEX_HAS_SIZE_FINITE_DIFF : forall {M N' : Type'}, @HAS_SIZE (finite_diff M N') (@setT (finite_diff M N')) (@COND nat (ltn (@dimindex N' (@setT N')) (@dimindex M (@setT M))) (subn (@dimindex M (@setT M)) (@dimindex N' (@setT N'))) (NUMERAL (BIT1 O))).
Axiom thm_DIMINDEX_FINITE_DIFF : forall {M N' : Type'}, (@dimindex (finite_diff M N') (@setT (finite_diff M N'))) = (@COND nat (ltn (@dimindex N' (@setT N')) (@dimindex M (@setT M))) (subn (@dimindex M (@setT M)) (@dimindex N' (@setT N'))) (NUMERAL (BIT1 O))).
Axiom thm_FINITE_PROD_IMAGE : forall {A B : Type'}, (@setT (finite_prod A B)) = (@IMAGE nat (finite_prod A B) (@mk_finite_prod A B) (dotdot (NUMERAL (BIT1 O)) (muln (@dimindex A (@setT A)) (@dimindex B (@setT B))))).
Axiom thm_DIMINDEX_HAS_SIZE_FINITE_PROD : forall {M N' : Type'}, @HAS_SIZE (finite_prod M N') (@setT (finite_prod M N')) (muln (@dimindex M (@setT M)) (@dimindex N' (@setT N'))).
Axiom thm_DIMINDEX_FINITE_PROD : forall {M N' : Type'}, (@dimindex (finite_prod M N') (@setT (finite_prod M N'))) = (muln (@dimindex M (@setT M)) (@dimindex N' (@setT N'))).
Axiom thm_tybit0_INDUCT : forall {A : Type'}, forall P : (tybit0 A) -> Prop, (forall a : finite_sum A A, P (@mktybit0 A a)) -> forall x : tybit0 A, P x.
Axiom thm_tybit0_RECURSION : forall {A Z' : Type'}, forall f : (finite_sum A A) -> Z', exists fn : (tybit0 A) -> Z', forall a : finite_sum A A, (fn (@mktybit0 A a)) = (f a).
Axiom thm_tybit1_INDUCT : forall {A : Type'}, forall P : (tybit1 A) -> Prop, (forall a : finite_sum (finite_sum A A) unit, P (@mktybit1 A a)) -> forall x : tybit1 A, P x.
Axiom thm_tybit1_RECURSION : forall {A Z' : Type'}, forall f : (finite_sum (finite_sum A A) unit) -> Z', exists fn : (tybit1 A) -> Z', forall a : finite_sum (finite_sum A A) unit, (fn (@mktybit1 A a)) = (f a).
Axiom thm_HAS_SIZE_TYBIT0 : forall {A : Type'}, @HAS_SIZE (tybit0 A) (@setT (tybit0 A)) (muln (NUMERAL (BIT0 (BIT1 O))) (@dimindex A (@setT A))).
Axiom thm_HAS_SIZE_TYBIT1 : forall {A : Type'}, @HAS_SIZE (tybit1 A) (@setT (tybit1 A)) (addn (muln (NUMERAL (BIT0 (BIT1 O))) (@dimindex A (@setT A))) (NUMERAL (BIT1 O))).
Axiom thm_DIMINDEX_TYBIT0 : forall {A : Type'}, (@dimindex (tybit0 A) (@setT (tybit0 A))) = (muln (NUMERAL (BIT0 (BIT1 O))) (@dimindex A (@setT A))).
Axiom thm_DIMINDEX_TYBIT1 : forall {A : Type'}, (@dimindex (tybit1 A) (@setT (tybit1 A))) = (addn (muln (NUMERAL (BIT0 (BIT1 O))) (@dimindex A (@setT A))) (NUMERAL (BIT1 O))).
Axiom thm_DIMINDEX_CLAUSES : forall {A : Type'}, ((@dimindex unit (@setT unit)) = (NUMERAL (BIT1 O))) /\ (((@dimindex (tybit0 A) (@setT (tybit0 A))) = (muln (NUMERAL (BIT0 (BIT1 O))) (@dimindex A (@setT A)))) /\ ((@dimindex (tybit1 A) (@setT (tybit1 A))) = (addn (muln (NUMERAL (BIT0 (BIT1 O))) (@dimindex A (@setT A))) (NUMERAL (BIT1 O))))).
Axiom thm_FINITE_1 : @finite_set unit (@setT unit).
Axiom thm_FINITE_TYBIT0 : forall {A : Type'}, @finite_set (tybit0 A) (@setT (tybit0 A)).
Axiom thm_FINITE_TYBIT1 : forall {A : Type'}, @finite_set (tybit1 A) (@setT (tybit1 A)).
Axiom thm_FINITE_CLAUSES : forall {A : Type'}, (@finite_set unit (@setT unit)) /\ ((@finite_set (tybit0 A) (@setT (tybit0 A))) /\ (@finite_set (tybit1 A) (@setT (tybit1 A)))).
Axiom thm_DIMINDEX_2 : (@dimindex (tybit0 unit) (@setT (tybit0 unit))) = (NUMERAL (BIT0 (BIT1 O))).
Axiom thm_DIMINDEX_3 : (@dimindex (tybit1 unit) (@setT (tybit1 unit))) = (NUMERAL (BIT1 (BIT1 O))).
Axiom thm_DIMINDEX_4 : (@dimindex (tybit0 (tybit0 unit)) (@setT (tybit0 (tybit0 unit)))) = (NUMERAL (BIT0 (BIT0 (BIT1 O)))).
Axiom thm_FINITE_CART : forall {A N' : Type'}, forall P : nat -> A -> Prop, (forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex N' (@setT N')))) -> @finite_set A (@GSPEC A (fun GEN_PVAR_360 : A => exists x : A, @SETSPEC A GEN_PVAR_360 (P i x) x))) -> @finite_set (cart A N') (@GSPEC (cart A N') (fun GEN_PVAR_361 : cart A N' => exists v : cart A N', @SETSPEC (cart A N') GEN_PVAR_361 (forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex N' (@setT N')))) -> P i (@dollar A N' v i)) v)).
Axiom thm_HAS_SIZE_CART_UNIV : forall {A N' : Type'}, forall m : nat, (@HAS_SIZE A (@setT A) m) -> @HAS_SIZE (cart A N') (@setT (cart A N')) (expn m (@dimindex N' (@setT N'))).
Axiom thm_CARD_CART_UNIV : forall {A N' : Type'}, (@finite_set A (@setT A)) -> (@CARD (cart A N') (@setT (cart A N'))) = (expn (@CARD A (@setT A)) (@dimindex N' (@setT N'))).
Axiom thm_FINITE_CART_UNIV : forall {A N' : Type'}, (@finite_set A (@setT A)) -> @finite_set (cart A N') (@setT (cart A N')).
Axiom thm_vector : forall {A N' : Type'}, forall l : seq A, (@vector A N' l) = (@lambda A N' (fun i : nat => @EL A (subn i (NUMERAL (BIT1 O))) l)).
Axiom thm_IN_ELIM_PASTECART_THM : forall {A M N' : Type'}, forall P : (cart A M) -> (cart A N') -> Prop, forall a : cart A M, forall b : cart A N', (@IN (cart A (finite_sum M N')) (@pastecart A M N' a b) (@GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_362 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_362 (P x y) (@pastecart A M N' x y)))) = (P a b).
Axiom thm_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, (@PCROSS A M N' s t) = (@GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x s) /\ (@IN (cart A N') y t)) (@pastecart A M N' x y))).
Axiom thm_FORALL_IN_PCROSS : forall {A M N' : Type'} (s : (cart A M) -> Prop) (t : (cart A N') -> Prop) (P : (cart A (finite_sum M N')) -> Prop), (forall z : cart A (finite_sum M N'), (@IN (cart A (finite_sum M N')) z (@PCROSS A M N' s t)) -> P z) = (forall x : cart A M, forall y : cart A N', ((@IN (cart A M) x s) /\ (@IN (cart A N') y t)) -> P (@pastecart A M N' x y)).
Axiom thm_EXISTS_IN_PCROSS : forall {A M N' : Type'} (s : (cart A M) -> Prop) (t : (cart A N') -> Prop) (P : (cart A (finite_sum M N')) -> Prop), (exists z : cart A (finite_sum M N'), (@IN (cart A (finite_sum M N')) z (@PCROSS A M N' s t)) /\ (P z)) = (exists x : cart A M, exists y : cart A N', (@IN (cart A M) x s) /\ ((@IN (cart A N') y t) /\ (P (@pastecart A M N' x y)))).
Axiom thm_PASTECART_IN_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall x : cart A M, forall y : cart A N', (@IN (cart A (finite_sum M N')) (@pastecart A M N' x y) (@PCROSS A M N' s t)) = ((@IN (cart A M) x s) /\ (@IN (cart A N') y t)).
Axiom thm_PCROSS_EQ_EMPTY : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, ((@PCROSS A M N' s t) = (@set0 (cart A (finite_sum M N')))) = ((s = (@set0 (cart A M))) \/ (t = (@set0 (cart A N')))).
Axiom thm_PCROSS_EMPTY : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, (@PCROSS A M N' s (@set0 (cart A N'))) = (@set0 (cart A (finite_sum M N')))) /\ (forall t : (cart A N') -> Prop, (@PCROSS A M N' (@set0 (cart A M)) t) = (@set0 (cart A (finite_sum M N')))).
Axiom thm_PCROSS_SING : forall {A M N' : Type'}, forall x : cart A M, forall y : cart A N', (@PCROSS A M N' (@INSERT (cart A M) x (@set0 (cart A M))) (@INSERT (cart A N') y (@set0 (cart A N')))) = (@INSERT (cart A (finite_sum M N')) (@pastecart A M N' x y) (@set0 (cart A (finite_sum M N')))).
Axiom thm_SUBSET_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall s' : (cart A M) -> Prop, forall t' : (cart A N') -> Prop, (@subset (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s' t')) = ((s = (@set0 (cart A M))) \/ ((t = (@set0 (cart A N'))) \/ ((@subset (cart A M) s s') /\ (@subset (cart A N') t t')))).
Axiom thm_PCROSS_MONO : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall s' : (cart A M) -> Prop, forall t' : (cart A N') -> Prop, ((@subset (cart A M) s s') /\ (@subset (cart A N') t t')) -> @subset (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s' t').
Axiom thm_PCROSS_EQ : forall {M N' : Type'}, forall s : (cart R M) -> Prop, forall s' : (cart R M) -> Prop, forall t : (cart R N') -> Prop, forall t' : (cart R N') -> Prop, ((@PCROSS R M N' s t) = (@PCROSS R M N' s' t')) = ((((s = (@set0 (cart R M))) \/ (t = (@set0 (cart R N')))) /\ ((s' = (@set0 (cart R M))) \/ (t' = (@set0 (cart R N'))))) \/ ((s = s') /\ (t = t'))).
Axiom thm_UNIV_PCROSS_UNIV : forall {A M N' : Type'}, (@PCROSS A M N' (@setT (cart A M)) (@setT (cart A N'))) = (@setT (cart A (finite_sum M N'))).
Axiom thm_HAS_SIZE_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE (cart A M) s m) /\ (@HAS_SIZE (cart A N') t n)) -> @HAS_SIZE (cart A (finite_sum M N')) (@PCROSS A M N' s t) (muln m n).
Axiom thm_FINITE_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, ((@finite_set (cart A M) s) /\ (@finite_set (cart A N') t)) -> @finite_set (cart A (finite_sum M N')) (@PCROSS A M N' s t).
Axiom thm_FINITE_PCROSS_EQ : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, (@finite_set (cart A (finite_sum M N')) (@PCROSS A M N' s t)) = ((s = (@set0 (cart A M))) \/ ((t = (@set0 (cart A N'))) \/ ((@finite_set (cart A M) s) /\ (@finite_set (cart A N') t)))).
Axiom thm_IMAGE_FSTCART_PCROSS : forall {M N' : Type'}, forall s : (cart R M) -> Prop, forall t : (cart R N') -> Prop, (@IMAGE (cart R (finite_sum M N')) (cart R M) (@fstcart R M N') (@PCROSS R M N' s t)) = (@COND ((cart R M) -> Prop) (t = (@set0 (cart R N'))) (@set0 (cart R M)) s).
Axiom thm_IMAGE_SNDCART_PCROSS : forall {M N' : Type'}, forall s : (cart R M) -> Prop, forall t : (cart R N') -> Prop, (@IMAGE (cart R (finite_sum M N')) (cart R N') (@sndcart R M N') (@PCROSS R M N' s t)) = (@COND ((cart R N') -> Prop) (s = (@set0 (cart R M))) (@set0 (cart R N')) t).
Axiom thm_PCROSS_INTER : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' s (@setI (cart A N') t u)) = (@setI (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s u))) /\ (forall s : (cart A M) -> Prop, forall t : (cart A M) -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' (@setI (cart A M) s t) u) = (@setI (cart A (finite_sum M N')) (@PCROSS A M N' s u) (@PCROSS A M N' t u))).
Axiom thm_PCROSS_UNION : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' s (@setU (cart A N') t u)) = (@setU (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s u))) /\ (forall s : (cart A M) -> Prop, forall t : (cart A M) -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' (@setU (cart A M) s t) u) = (@setU (cart A (finite_sum M N')) (@PCROSS A M N' s u) (@PCROSS A M N' t u))).
Axiom thm_PCROSS_DIFF : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' s (@setD (cart A N') t u)) = (@setD (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s u))) /\ (forall s : (cart A M) -> Prop, forall t : (cart A M) -> Prop, forall u : (cart A N') -> Prop, (@PCROSS A M N' (@setD (cart A M) s t) u) = (@setD (cart A (finite_sum M N')) (@PCROSS A M N' s u) (@PCROSS A M N' t u))).
Axiom thm_INTER_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall s' : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall t' : (cart A N') -> Prop, (@setI (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s' t')) = (@PCROSS A M N' (@setI (cart A M) s s') (@setI (cart A N') t t')).
Axiom thm_PCROSS_UNIONS : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall f : ((cart A N') -> Prop) -> Prop, (@PCROSS A M N' s (@UNIONS (cart A N') f)) = (@UNIONS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_365 : (cart A (finite_sum M N')) -> Prop => exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_365 (@IN ((cart A N') -> Prop) t f) (@PCROSS A M N' s t))))) /\ (forall f : ((cart A M) -> Prop) -> Prop, forall t : (cart A N') -> Prop, (@PCROSS A M N' (@UNIONS (cart A M) f) t) = (@UNIONS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_366 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_366 (@IN ((cart A M) -> Prop) s f) (@PCROSS A M N' s t))))).
Axiom thm_PCROSS_UNIONS_UNIONS : forall {A M N' : Type'}, forall f : ((cart A M) -> Prop) -> Prop, forall g : ((cart A N') -> Prop) -> Prop, (@PCROSS A M N' (@UNIONS (cart A M) f) (@UNIONS (cart A N') g)) = (@UNIONS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_364 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_364 ((@IN ((cart A M) -> Prop) s f) /\ (@IN ((cart A N') -> Prop) t g)) (@PCROSS A M N' s t)))).
Axiom thm_PCROSS_INTERS : forall {A M N' : Type'}, (forall s : (cart A M) -> Prop, forall f : ((cart A N') -> Prop) -> Prop, (@PCROSS A M N' s (@INTERS (cart A N') f)) = (@COND ((cart A (finite_sum M N')) -> Prop) (f = (@set0 ((cart A N') -> Prop))) (@PCROSS A M N' s (@setT (cart A N'))) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_370 : (cart A (finite_sum M N')) -> Prop => exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_370 (@IN ((cart A N') -> Prop) t f) (@PCROSS A M N' s t)))))) /\ (forall f : ((cart A M) -> Prop) -> Prop, forall t : (cart A N') -> Prop, (@PCROSS A M N' (@INTERS (cart A M) f) t) = (@COND ((cart A (finite_sum M N')) -> Prop) (f = (@set0 ((cart A M) -> Prop))) (@PCROSS A M N' (@setT (cart A M)) t) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_371 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_371 (@IN ((cart A M) -> Prop) s f) (@PCROSS A M N' s t)))))).
Axiom thm_PCROSS_INTERS_INTERS : forall {A M N' : Type'}, forall f : ((cart A M) -> Prop) -> Prop, forall g : ((cart A N') -> Prop) -> Prop, (@PCROSS A M N' (@INTERS (cart A M) f) (@INTERS (cart A N') g)) = (@COND ((cart A (finite_sum M N')) -> Prop) (f = (@set0 ((cart A M) -> Prop))) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_367 : (cart A (finite_sum M N')) -> Prop => exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_367 (@IN ((cart A N') -> Prop) t g) (@PCROSS A M N' (@setT (cart A M)) t)))) (@COND ((cart A (finite_sum M N')) -> Prop) (g = (@set0 ((cart A N') -> Prop))) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_368 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_368 (@IN ((cart A M) -> Prop) s f) (@PCROSS A M N' s (@setT (cart A N')))))) (@INTERS (cart A (finite_sum M N')) (@GSPEC ((cart A (finite_sum M N')) -> Prop) (fun GEN_PVAR_369 : (cart A (finite_sum M N')) -> Prop => exists s : (cart A M) -> Prop, exists t : (cart A N') -> Prop, @SETSPEC ((cart A (finite_sum M N')) -> Prop) GEN_PVAR_369 ((@IN ((cart A M) -> Prop) s f) /\ (@IN ((cart A N') -> Prop) t g)) (@PCROSS A M N' s t)))))).
Axiom thm_DISJOINT_PCROSS : forall {A M N' : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N') -> Prop, forall s' : (cart A M) -> Prop, forall t' : (cart A N') -> Prop, (@DISJOINT (cart A (finite_sum M N')) (@PCROSS A M N' s t) (@PCROSS A M N' s' t')) = ((@DISJOINT (cart A M) s s') \/ (@DISJOINT (cart A N') t t')).
Axiom thm_CASEWISE_DEF : forall {_138002 _138038 _138042 _138043 : Type'} (h : prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) (t : seq (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) (f : _138043) (x : _138042), ((@CASEWISE _138002 _138038 _138042 _138043 (@nil (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) f x) = (@ε _138002 (fun y : _138002 => True))) /\ ((@CASEWISE _138002 _138038 _138042 _138043 (@cons (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) h t) f x) = (@COND _138002 (exists y : _138038, (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x) (@snd (_138038 -> _138042) (_138043 -> _138038 -> _138002) h f (@ε _138038 (fun y : _138038 => (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x))) (@CASEWISE _138002 _138038 _138042 _138043 t f x))).
Axiom thm_CASEWISE : forall {_138054 _138062 _138063 _138102 _138103 _138105 : Type'} (t : _138103 -> _138105 -> _138063) (s : _138105 -> _138102) (clauses : seq (prod (_138105 -> _138102) (_138103 -> _138105 -> _138063))) (f : _138103) (x : _138102), ((@CASEWISE _138062 _138054 _138102 _138103 (@nil (prod (_138054 -> _138102) (_138103 -> _138054 -> _138062))) f x) = (@ε _138062 (fun y : _138062 => True))) /\ ((@CASEWISE _138063 _138105 _138102 _138103 (@cons (prod (_138105 -> _138102) (_138103 -> _138105 -> _138063)) (@pair (_138105 -> _138102) (_138103 -> _138105 -> _138063) s t) clauses) f x) = (@COND _138063 (exists y : _138105, (s y) = x) (t f (@ε _138105 (fun y : _138105 => (s y) = x))) (@CASEWISE _138063 _138105 _138102 _138103 clauses f x))).
Axiom thm_CASEWISE_CASES : forall {_138194 _138195 _138197 _138204 : Type'}, forall clauses : seq (prod (_138197 -> _138194) (_138195 -> _138197 -> _138204)), forall c : _138195, forall x : _138194, (exists s : _138197 -> _138194, exists t : _138195 -> _138197 -> _138204, exists a : _138197, (@MEM (prod (_138197 -> _138194) (_138195 -> _138197 -> _138204)) (@pair (_138197 -> _138194) (_138195 -> _138197 -> _138204) s t) clauses) /\ (((s a) = x) /\ ((@CASEWISE _138204 _138197 _138194 _138195 clauses c x) = (t c a)))) \/ ((~ (exists s : _138197 -> _138194, exists t : _138195 -> _138197 -> _138204, exists a : _138197, (@MEM (prod (_138197 -> _138194) (_138195 -> _138197 -> _138204)) (@pair (_138197 -> _138194) (_138195 -> _138197 -> _138204) s t) clauses) /\ ((s a) = x))) /\ ((@CASEWISE _138204 _138197 _138194 _138195 clauses c x) = (@ε _138204 (fun y : _138204 => True)))).
Axiom thm_CASEWISE_WORKS : forall {A B C P : Type'}, forall clauses : seq (prod (P -> A) (C -> P -> B)), forall c : C, (forall s : P -> A, forall t : C -> P -> B, forall s' : P -> A, forall t' : C -> P -> B, forall x : P, forall y : P, ((@MEM (prod (P -> A) (C -> P -> B)) (@pair (P -> A) (C -> P -> B) s t) clauses) /\ ((@MEM (prod (P -> A) (C -> P -> B)) (@pair (P -> A) (C -> P -> B) s' t') clauses) /\ ((s x) = (s' y)))) -> (t c x) = (t' c y)) -> @ALL (prod (P -> A) (C -> P -> B)) (@GABS ((prod (P -> A) (C -> P -> B)) -> Prop) (fun f : (prod (P -> A) (C -> P -> B)) -> Prop => forall s : P -> A, forall t : C -> P -> B, @eq Prop (f (@pair (P -> A) (C -> P -> B) s t)) (forall x : P, (@CASEWISE B P A C clauses c (s x)) = (t c x)))) clauses.
Axiom thm_admissible : forall {_138333 _138336 _138340 _138341 _138346 : Type'}, forall p : (_138340 -> _138336) -> _138346 -> Prop, forall lt2 : _138340 -> _138333 -> Prop, forall s : _138346 -> _138333, forall t : (_138340 -> _138336) -> _138346 -> _138341, (@admissible _138333 _138336 _138340 _138341 _138346 lt2 p s t) = (forall f : _138340 -> _138336, forall g : _138340 -> _138336, forall a : _138346, ((p f a) /\ ((p g a) /\ (forall z : _138340, (lt2 z (s a)) -> (f z) = (g z)))) -> (t f a) = (t g a)).
Axiom thm_tailadmissible : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall s : P -> A, forall p : (A -> B) -> P -> Prop, forall t : (A -> B) -> P -> B, (@tailadmissible A B P lt2 p s t) = (exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (lt2 y (G f a))) -> lt2 y (s a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (lt2 z (s a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (p f a) -> (t f a) = (@COND B (P' f a) (f (G f a)) (H f a))))).
Axiom thm_superadmissible : forall {_138490 _138492 _138498 : Type'}, forall lt2 : _138490 -> _138490 -> Prop, forall p : (_138490 -> _138492) -> _138498 -> Prop, forall s : _138498 -> _138490, forall t : (_138490 -> _138492) -> _138498 -> _138492, (@superadmissible _138490 _138492 _138498 lt2 p s t) = ((@admissible _138490 _138492 _138490 Prop _138498 lt2 (fun f : _138490 -> _138492 => fun a : _138498 => True) s p) -> @tailadmissible _138490 _138492 _138498 lt2 p s t).
Axiom thm_MATCH_SEQPATTERN : forall {_138526 _138533 : Type'} (r : _138533 -> _138526 -> Prop) (x : _138533) (s : _138533 -> _138526 -> Prop), (@_MATCH _138533 _138526 x (@_SEQPATTERN _138533 _138526 r s)) = (@COND _138526 (exists y : _138526, r x y) (@_MATCH _138533 _138526 x r) (@_MATCH _138533 _138526 x s)).
Axiom thm_ADMISSIBLE_CONST : forall {_138553 _138554 _138555 _138556 _138557 : Type'} (lt2 : _138554 -> _138553 -> Prop), forall p : (_138554 -> _138555) -> _138556 -> Prop, forall s : _138556 -> _138553, forall c : _138556 -> _138557, @admissible _138553 _138555 _138554 _138557 _138556 lt2 p s (fun f : _138554 -> _138555 => c).
Axiom thm_ADMISSIBLE_BASE : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : P -> A, (forall f : A -> B, forall a : P, (p f a) -> lt2 (t a) (s a)) -> @admissible A B A B P lt2 p s (fun f : A -> B => fun x : P => f (t x)).
Axiom thm_ADMISSIBLE_COMB : forall {A B C D P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall g : (A -> B) -> P -> C -> D, forall y : (A -> B) -> P -> C, ((@admissible A B A (C -> D) P lt2 p s g) /\ (@admissible A B A C P lt2 p s y)) -> @admissible A B A D P lt2 p s (fun f : A -> B => fun x : P => g f x (y f x)).
Axiom thm_ADMISSIBLE_RAND : forall {A B C D P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall g : P -> C -> D, forall y : (A -> B) -> P -> C, (@admissible A B A C P lt2 p s y) -> @admissible A B A D P lt2 p s (fun f : A -> B => fun x : P => g x (y f x)).
Axiom thm_ADMISSIBLE_LAMBDA : forall {A B C P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> C -> P -> Prop, (@admissible A B A Prop (prod C P) lt2 (fun f : A -> B => @GABS ((prod C P) -> Prop) (fun f' : (prod C P) -> Prop => forall u : C, forall x : P, @eq Prop (f' (@pair C P u x)) (p f x))) (@GABS ((prod C P) -> A) (fun f : (prod C P) -> A => forall u : C, forall x : P, @eq A (f (@pair C P u x)) (s x))) (fun f : A -> B => @GABS ((prod C P) -> Prop) (fun f' : (prod C P) -> Prop => forall u : C, forall x : P, @eq Prop (f' (@pair C P u x)) (t f u x)))) -> @admissible A B A (C -> Prop) P lt2 p s (fun f : A -> B => fun x : P => fun u : C => t f u x).
Axiom thm_ADMISSIBLE_NEST : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> P -> A, ((@admissible A B A A P lt2 p s t) /\ (forall f : A -> B, forall a : P, (p f a) -> lt2 (t f a) (s a))) -> @admissible A B A B P lt2 p s (fun f : A -> B => fun x : P => f (t f x)).
Axiom thm_ADMISSIBLE_COND : forall {_138890 _138891 _138922 _138947 P : Type'}, forall lt2 : _138891 -> _138890 -> Prop, forall p : (_138891 -> _138922) -> P -> Prop, forall P' : (_138891 -> _138922) -> P -> Prop, forall s : P -> _138890, forall h : (_138891 -> _138922) -> P -> _138947, forall k : (_138891 -> _138922) -> P -> _138947, ((@admissible _138890 _138922 _138891 Prop P lt2 p s P') /\ ((@admissible _138890 _138922 _138891 _138947 P lt2 (fun f : _138891 -> _138922 => fun x : P => (p f x) /\ (P' f x)) s h) /\ (@admissible _138890 _138922 _138891 _138947 P lt2 (fun f : _138891 -> _138922 => fun x : P => (p f x) /\ (~ (P' f x))) s k))) -> @admissible _138890 _138922 _138891 _138947 P lt2 p s (fun f : _138891 -> _138922 => fun x : P => @COND _138947 (P' f x) (h f x) (k f x)).
Axiom thm_ADMISSIBLE_MATCH : forall {_138988 _138989 _138990 _139022 _139025 P : Type'}, forall lt2 : _138989 -> _138988 -> Prop, forall p : (_138989 -> _138990) -> P -> Prop, forall s : P -> _138988, forall e : (_138989 -> _138990) -> P -> _139025, forall c : (_138989 -> _138990) -> P -> _139025 -> _139022 -> Prop, ((@admissible _138988 _138990 _138989 _139025 P lt2 p s e) /\ (@admissible _138988 _138990 _138989 (_139022 -> Prop) P lt2 p s (fun f : _138989 -> _138990 => fun x : P => c f x (e f x)))) -> @admissible _138988 _138990 _138989 _139022 P lt2 p s (fun f : _138989 -> _138990 => fun x : P => @_MATCH _139025 _139022 (e f x) (c f x)).
Axiom thm_ADMISSIBLE_SEQPATTERN : forall {_139065 _139066 _139128 _139144 _139154 P : Type'}, forall lt2 : _139066 -> _139065 -> Prop, forall p : (_139066 -> _139128) -> P -> Prop, forall s : P -> _139065, forall c1 : (_139066 -> _139128) -> P -> _139154 -> _139144 -> Prop, forall c2 : (_139066 -> _139128) -> P -> _139154 -> _139144 -> Prop, forall e : (_139066 -> _139128) -> P -> _139154, ((@admissible _139065 _139128 _139066 Prop P lt2 p s (fun f : _139066 -> _139128 => fun x : P => exists y : _139144, c1 f x (e f x) y)) /\ ((@admissible _139065 _139128 _139066 (_139144 -> Prop) P lt2 (fun f : _139066 -> _139128 => fun x : P => (p f x) /\ (exists y : _139144, c1 f x (e f x) y)) s (fun f : _139066 -> _139128 => fun x : P => c1 f x (e f x))) /\ (@admissible _139065 _139128 _139066 (_139144 -> Prop) P lt2 (fun f : _139066 -> _139128 => fun x : P => (p f x) /\ (~ (exists y : _139144, c1 f x (e f x) y))) s (fun f : _139066 -> _139128 => fun x : P => c2 f x (e f x))))) -> @admissible _139065 _139128 _139066 (_139144 -> Prop) P lt2 p s (fun f : _139066 -> _139128 => fun x : P => @_SEQPATTERN _139154 _139144 (c1 f x) (c2 f x) (e f x)).
Axiom thm_ADMISSIBLE_UNGUARDED_PATTERN : forall {_139239 _139240 _139287 _139320 _139327 P : Type'}, forall lt2 : _139240 -> _139239 -> Prop, forall p : (_139240 -> _139287) -> P -> Prop, forall s : P -> _139239, forall pat : (_139240 -> _139287) -> P -> _139320, forall e : (_139240 -> _139287) -> P -> _139320, forall t : (_139240 -> _139287) -> P -> _139327, forall y : (_139240 -> _139287) -> P -> _139327, ((@admissible _139239 _139287 _139240 _139320 P lt2 p s pat) /\ ((@admissible _139239 _139287 _139240 _139320 P lt2 p s e) /\ ((@admissible _139239 _139287 _139240 _139327 P lt2 (fun f : _139240 -> _139287 => fun x : P => (p f x) /\ ((pat f x) = (e f x))) s t) /\ (@admissible _139239 _139287 _139240 _139327 P lt2 (fun f : _139240 -> _139287 => fun x : P => (p f x) /\ ((pat f x) = (e f x))) s y)))) -> @admissible _139239 _139287 _139240 Prop P lt2 p s (fun f : _139240 -> _139287 => fun x : P => _UNGUARDED_PATTERN (@eq _139320 (pat f x) (e f x)) (@eq _139327 (t f x) (y f x))).
Axiom thm_ADMISSIBLE_GUARDED_PATTERN : forall {_139413 _139414 _139491 _139529 _139538 P : Type'}, forall lt2 : _139414 -> _139413 -> Prop, forall p : (_139414 -> _139491) -> P -> Prop, forall s : P -> _139413, forall pat : (_139414 -> _139491) -> P -> _139529, forall q : (_139414 -> _139491) -> P -> Prop, forall e : (_139414 -> _139491) -> P -> _139529, forall t : (_139414 -> _139491) -> P -> _139538, forall y : (_139414 -> _139491) -> P -> _139538, ((@admissible _139413 _139491 _139414 _139529 P lt2 p s pat) /\ ((@admissible _139413 _139491 _139414 _139529 P lt2 p s e) /\ ((@admissible _139413 _139491 _139414 _139538 P lt2 (fun f : _139414 -> _139491 => fun x : P => (p f x) /\ (((pat f x) = (e f x)) /\ (q f x))) s t) /\ ((@admissible _139413 _139491 _139414 Prop P lt2 (fun f : _139414 -> _139491 => fun x : P => (p f x) /\ ((pat f x) = (e f x))) s q) /\ (@admissible _139413 _139491 _139414 _139538 P lt2 (fun f : _139414 -> _139491 => fun x : P => (p f x) /\ (((pat f x) = (e f x)) /\ (q f x))) s y))))) -> @admissible _139413 _139491 _139414 Prop P lt2 p s (fun f : _139414 -> _139491 => fun x : P => _GUARDED_PATTERN (@eq _139529 (pat f x) (e f x)) (q f x) (@eq _139538 (t f x) (y f x))).
Axiom thm_ADMISSIBLE_NSUM : forall {A B C P : Type'}, forall lt2 : B -> A -> Prop, forall p : (B -> C) -> P -> Prop, forall s : P -> A, forall h : (B -> C) -> P -> nat -> nat, forall a : P -> nat, forall b : P -> nat, (@admissible A C B nat (prod nat P) lt2 (fun f : B -> C => @GABS ((prod nat P) -> Prop) (fun f' : (prod nat P) -> Prop => forall k : nat, forall x : P, @eq Prop (f' (@pair nat P k x)) ((leqn (a x) k) /\ ((leqn k (b x)) /\ (p f x))))) (@GABS ((prod nat P) -> A) (fun f : (prod nat P) -> A => forall k : nat, forall x : P, @eq A (f (@pair nat P k x)) (s x))) (fun f : B -> C => @GABS ((prod nat P) -> nat) (fun f' : (prod nat P) -> nat => forall k : nat, forall x : P, @eq nat (f' (@pair nat P k x)) (h f x k)))) -> @admissible A C B nat P lt2 p s (fun f : B -> C => fun x : P => @nsum nat (dotdot (a x) (b x)) (h f x)).
Axiom thm_ADMISSIBLE_SUM : forall {A B C P : Type'}, forall lt2 : B -> A -> Prop, forall p : (B -> C) -> P -> Prop, forall s : P -> A, forall h : (B -> C) -> P -> nat -> R, forall a : P -> nat, forall b : P -> nat, (@admissible A C B R (prod nat P) lt2 (fun f : B -> C => @GABS ((prod nat P) -> Prop) (fun f' : (prod nat P) -> Prop => forall k : nat, forall x : P, @eq Prop (f' (@pair nat P k x)) ((leqn (a x) k) /\ ((leqn k (b x)) /\ (p f x))))) (@GABS ((prod nat P) -> A) (fun f : (prod nat P) -> A => forall k : nat, forall x : P, @eq A (f (@pair nat P k x)) (s x))) (fun f : B -> C => @GABS ((prod nat P) -> R) (fun f' : (prod nat P) -> R => forall k : nat, forall x : P, @eq R (f' (@pair nat P k x)) (h f x k)))) -> @admissible A C B R P lt2 p s (fun f : B -> C => fun x : P => @sum nat (dotdot (a x) (b x)) (h f x)).
Axiom thm_ADMISSIBLE_MAP : forall {_139831 _139840 _139846 A B P : Type'}, forall lt2 : A -> _139831 -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> _139831, forall h : (A -> B) -> P -> _139846 -> _139840, forall l : (A -> B) -> P -> seq _139846, ((@admissible _139831 B A (seq _139846) P lt2 p s l) /\ (@admissible _139831 B A _139840 (prod _139846 P) lt2 (fun f : A -> B => @GABS ((prod _139846 P) -> Prop) (fun f' : (prod _139846 P) -> Prop => forall y : _139846, forall x : P, @eq Prop (f' (@pair _139846 P y x)) ((p f x) /\ (@MEM _139846 y (l f x))))) (@GABS ((prod _139846 P) -> _139831) (fun f : (prod _139846 P) -> _139831 => forall y : _139846, forall x : P, @eq _139831 (f (@pair _139846 P y x)) (s x))) (fun f : A -> B => @GABS ((prod _139846 P) -> _139840) (fun f' : (prod _139846 P) -> _139840 => forall y : _139846, forall x : P, @eq _139840 (f' (@pair _139846 P y x)) (h f x y))))) -> @admissible _139831 B A (seq _139840) P lt2 p s (fun f : A -> B => fun x : P => @map _139846 _139840 (h f x) (l f x)).
Axiom thm_ADMISSIBLE_MATCH_SEQPATTERN : forall {_139903 _139904 _139969 _139993 _140024 P : Type'}, forall lt2 : _139904 -> _139903 -> Prop, forall p : (_139904 -> _139969) -> P -> Prop, forall s : P -> _139903, forall c1 : (_139904 -> _139969) -> P -> _140024 -> _139993 -> Prop, forall c2 : (_139904 -> _139969) -> P -> _140024 -> _139993 -> Prop, forall e : (_139904 -> _139969) -> P -> _140024, ((@admissible _139903 _139969 _139904 Prop P lt2 p s (fun f : _139904 -> _139969 => fun x : P => exists y : _139993, c1 f x (e f x) y)) /\ ((@admissible _139903 _139969 _139904 _139993 P lt2 (fun f : _139904 -> _139969 => fun x : P => (p f x) /\ (exists y : _139993, c1 f x (e f x) y)) s (fun f : _139904 -> _139969 => fun x : P => @_MATCH _140024 _139993 (e f x) (c1 f x))) /\ (@admissible _139903 _139969 _139904 _139993 P lt2 (fun f : _139904 -> _139969 => fun x : P => (p f x) /\ (~ (exists y : _139993, c1 f x (e f x) y))) s (fun f : _139904 -> _139969 => fun x : P => @_MATCH _140024 _139993 (e f x) (c2 f x))))) -> @admissible _139903 _139969 _139904 _139993 P lt2 p s (fun f : _139904 -> _139969 => fun x : P => @_MATCH _140024 _139993 (e f x) (@_SEQPATTERN _140024 _139993 (c1 f x) (c2 f x))).
Axiom thm_ADMISSIBLE_IMP_SUPERADMISSIBLE : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> P -> B, (@admissible A B A B P lt2 p s t) -> @superadmissible A B P lt2 p s t.
Axiom thm_SUPERADMISSIBLE_CONST : forall {_140103 _140104 _140105 : Type'} (lt2 : _140103 -> _140103 -> Prop), forall p : (_140103 -> _140105) -> _140104 -> Prop, forall s : _140104 -> _140103, forall c : _140104 -> _140105, @superadmissible _140103 _140105 _140104 lt2 p s (fun f : _140103 -> _140105 => c).
Axiom thm_SUPERADMISSIBLE_TAIL : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> P -> A, ((@admissible A B A A P lt2 p s t) /\ (forall f : A -> B, forall a : P, (p f a) -> forall y : A, (lt2 y (t f a)) -> lt2 y (s a))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => f (t f x)).
Axiom thm_SUPERADMISSIBLE_COND : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall P' : (A -> B) -> P -> Prop, forall s : P -> A, forall h : (A -> B) -> P -> B, forall k : (A -> B) -> P -> B, ((@admissible A B A Prop P lt2 p s P') /\ ((@superadmissible A B P lt2 (fun f : A -> B => fun x : P => (p f x) /\ (P' f x)) s h) /\ (@superadmissible A B P lt2 (fun f : A -> B => fun x : P => (p f x) /\ (~ (P' f x))) s k))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => @COND B (P' f x) (h f x) (k f x)).
Axiom thm_SUPERADMISSIBLE_MATCH_SEQPATTERN : forall {_140424 _140539 _140540 P : Type'}, forall lt2 : _140424 -> _140424 -> Prop, forall p : (_140424 -> _140540) -> P -> Prop, forall s : P -> _140424, forall c1 : (_140424 -> _140540) -> P -> _140539 -> _140540 -> Prop, forall c2 : (_140424 -> _140540) -> P -> _140539 -> _140540 -> Prop, forall e : (_140424 -> _140540) -> P -> _140539, ((@admissible _140424 _140540 _140424 Prop P lt2 p s (fun f : _140424 -> _140540 => fun x : P => exists y : _140540, c1 f x (e f x) y)) /\ ((@superadmissible _140424 _140540 P lt2 (fun f : _140424 -> _140540 => fun x : P => (p f x) /\ (exists y : _140540, c1 f x (e f x) y)) s (fun f : _140424 -> _140540 => fun x : P => @_MATCH _140539 _140540 (e f x) (c1 f x))) /\ (@superadmissible _140424 _140540 P lt2 (fun f : _140424 -> _140540 => fun x : P => (p f x) /\ (~ (exists y : _140540, c1 f x (e f x) y))) s (fun f : _140424 -> _140540 => fun x : P => @_MATCH _140539 _140540 (e f x) (c2 f x))))) -> @superadmissible _140424 _140540 P lt2 p s (fun f : _140424 -> _140540 => fun x : P => @_MATCH _140539 _140540 (e f x) (@_SEQPATTERN _140539 _140540 (c1 f x) (c2 f x))).
Axiom thm_SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN : forall {A B D P Q : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall e : P -> D, forall pat : Q -> D, forall arg : P -> Q -> A, ((forall f : A -> B, forall a : P, forall t : Q, forall u : Q, ((p f a) /\ (((pat t) = (e a)) /\ ((pat u) = (e a)))) -> (arg a t) = (arg a u)) /\ (forall f : A -> B, forall a : P, forall t : Q, ((p f a) /\ ((pat t) = (e a))) -> forall y : A, (lt2 y (arg a t)) -> lt2 y (s a))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => @_MATCH D B (e x) (fun u : D => fun v : B => exists t : Q, _UNGUARDED_PATTERN (@eq D (pat t) u) (@eq B (f (arg x t)) v))).
Axiom thm_SUPERADMISSIBLE_MATCH_GUARDED_PATTERN : forall {A B D P Q : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall e : P -> D, forall pat : Q -> D, forall q : P -> Q -> Prop, forall arg : P -> Q -> A, ((forall f : A -> B, forall a : P, forall t : Q, forall u : Q, ((p f a) /\ (((pat t) = (e a)) /\ ((q a t) /\ (((pat u) = (e a)) /\ (q a u))))) -> (arg a t) = (arg a u)) /\ (forall f : A -> B, forall a : P, forall t : Q, ((p f a) /\ ((q a t) /\ ((pat t) = (e a)))) -> forall y : A, (lt2 y (arg a t)) -> lt2 y (s a))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => @_MATCH D B (e x) (fun u : D => fun v : B => exists t : Q, _GUARDED_PATTERN (@eq D (pat t) u) (q x t) (@eq B (f (arg x t)) v))).
Axiom thm_WF_REC_CASES : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall clauses : seq (prod (P -> A) ((A -> B) -> P -> B)), ((@well_founded A lt2) /\ (@ALL (prod (P -> A) ((A -> B) -> P -> B)) (@GABS ((prod (P -> A) ((A -> B) -> P -> B)) -> Prop) (fun f : (prod (P -> A) ((A -> B) -> P -> B)) -> Prop => forall s : P -> A, forall t : (A -> B) -> P -> B, @eq Prop (f (@pair (P -> A) ((A -> B) -> P -> B) s t)) (exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f' : A -> B, forall a : P, forall y : A, ((P' f' a) /\ (lt2 y (G f' a))) -> lt2 y (s a)) /\ ((forall f' : A -> B, forall g : A -> B, forall a : P, (forall z : A, (lt2 z (s a)) -> (f' z) = (g z)) -> ((P' f' a) = (P' g a)) /\ (((G f' a) = (G g a)) /\ ((H f' a) = (H g a)))) /\ (forall f' : A -> B, forall a : P, (t f' a) = (@COND B (P' f' a) (f' (G f' a)) (H f' a))))))) clauses)) -> exists f : A -> B, forall x : A, (f x) = (@CASEWISE B P A (A -> B) clauses f x).
Axiom thm_RECURSION_CASEWISE : forall {A B P : Type'}, forall clauses : seq (prod (P -> A) ((A -> B) -> P -> B)), ((exists lt2 : A -> A -> Prop, (@well_founded A lt2) /\ (@ALL (prod (P -> A) ((A -> B) -> P -> B)) (@GABS ((prod (P -> A) ((A -> B) -> P -> B)) -> Prop) (fun f : (prod (P -> A) ((A -> B) -> P -> B)) -> Prop => forall s : P -> A, forall t : (A -> B) -> P -> B, @eq Prop (f (@pair (P -> A) ((A -> B) -> P -> B) s t)) (@tailadmissible A B P lt2 (fun f' : A -> B => fun a : P => True) s t))) clauses)) /\ (forall s : P -> A, forall t : (A -> B) -> P -> B, forall s' : P -> A, forall t' : (A -> B) -> P -> B, forall f : A -> B, forall x : P, forall y : P, ((@MEM (prod (P -> A) ((A -> B) -> P -> B)) (@pair (P -> A) ((A -> B) -> P -> B) s t) clauses) /\ (@MEM (prod (P -> A) ((A -> B) -> P -> B)) (@pair (P -> A) ((A -> B) -> P -> B) s' t') clauses)) -> ((s x) = (s' y)) -> (t f x) = (t' f y))) -> exists f : A -> B, @ALL (prod (P -> A) ((A -> B) -> P -> B)) (@GABS ((prod (P -> A) ((A -> B) -> P -> B)) -> Prop) (fun f' : (prod (P -> A) ((A -> B) -> P -> B)) -> Prop => forall s : P -> A, forall t : (A -> B) -> P -> B, @eq Prop (f' (@pair (P -> A) ((A -> B) -> P -> B) s t)) (forall x : P, (f (s x)) = (t f x)))) clauses.
Axiom thm_RECURSION_CASEWISE_PAIRWISE : forall {_141763 _141779 _141783 : Type'}, forall clauses : seq (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)), ((exists lt2 : _141763 -> _141763 -> Prop, (@well_founded _141763 lt2) /\ (@ALL (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) (@GABS ((prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop) (fun f : (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop => forall s : _141783 -> _141763, forall t : (_141763 -> _141779) -> _141783 -> _141779, @eq Prop (f (@pair (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779) s t)) (@tailadmissible _141763 _141779 _141783 lt2 (fun f' : _141763 -> _141779 => fun a : _141783 => True) s t))) clauses)) /\ ((@ALL (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) (@GABS ((prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop) (fun f : (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop => forall s : _141783 -> _141763, forall t : (_141763 -> _141779) -> _141783 -> _141779, @eq Prop (f (@pair (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779) s t)) (forall f' : _141763 -> _141779, forall x : _141783, forall y : _141783, ((s x) = (s y)) -> (t f' x) = (t f' y)))) clauses) /\ (@PAIRWISE (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) (@GABS ((prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop) (fun f : (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop => forall s : _141783 -> _141763, forall t : (_141763 -> _141779) -> _141783 -> _141779, @eq ((prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop) (f (@pair (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779) s t)) (@GABS ((prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop) (fun f' : (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop => forall s' : _141783 -> _141763, forall t' : (_141763 -> _141779) -> _141783 -> _141779, @eq Prop (f' (@pair (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779) s' t')) (forall f'' : _141763 -> _141779, forall x : _141783, forall y : _141783, ((s x) = (s' y)) -> (t f'' x) = (t' f'' y)))))) clauses))) -> exists f : _141763 -> _141779, @ALL (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) (@GABS ((prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop) (fun f' : (prod (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779)) -> Prop => forall s : _141783 -> _141763, forall t : (_141763 -> _141779) -> _141783 -> _141779, @eq Prop (f' (@pair (_141783 -> _141763) ((_141763 -> _141779) -> _141783 -> _141779) s t)) (forall x : _141783, (f (s x)) = (t f x)))) clauses.
Axiom thm_SUPERADMISSIBLE_T : forall {_141893 _141895 _141899 : Type'} (lt2 : _141893 -> _141893 -> Prop) (s : _141899 -> _141893) (t : (_141893 -> _141895) -> _141899 -> _141895), (@superadmissible _141893 _141895 _141899 lt2 (fun f : _141893 -> _141895 => fun x : _141899 => True) s t) = (@tailadmissible _141893 _141895 _141899 lt2 (fun f : _141893 -> _141895 => fun x : _141899 => True) s t).
