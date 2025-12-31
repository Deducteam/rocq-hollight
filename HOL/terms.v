Require Import Stdlib.Reals.Reals mathcomp.boot.ssrnat mathcomp.boot.div mathcomp.boot.seq mathcomp.algebra.ssrint mathcomp.algebra.intdiv mathcomp.classical.classical_sets mathcomp.classical.cardinality mathcomp.analysis_stdlib.Rstruct_topology HOLLight.HOL.mappings.
Definition _FALSITY_ : Prop := False.
Lemma _FALSITY__def : _FALSITY_ = False.
Proof. exact (REFL _FALSITY_). Qed.
Definition o {A B C : Type'} : (B -> C) -> (A -> B) -> A -> C := fun f : B -> C => fun g : A -> B => fun x : A => f (g x).
Lemma o_def {A B C : Type'} : (@o A B C) = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)).
Proof. exact (REFL (@o A B C)). Qed.
Definition I {A : Type'} : A -> A := fun x : A => x.
Lemma I_def {A : Type'} : (@I A) = (fun x : A => x).
Proof. exact (REFL (@I A)). Qed.
Definition hashek : Prop := True.
Lemma hashek_def : hashek = True.
Proof. exact (REFL hashek). Qed.
Definition LET {A B : Type'} : (A -> B) -> A -> B := fun f : A -> B => fun x : A => f x.
Lemma LET_def {A B : Type'} : (@LET A B) = (fun f : A -> B => fun x : A => f x).
Proof. exact (REFL (@LET A B)). Qed.
Definition LET_END {A : Type'} : A -> A := fun t : A => t.
Lemma LET_END_def {A : Type'} : (@LET_END A) = (fun t : A => t).
Proof. exact (REFL (@LET_END A)). Qed.
Definition GABS {A : Type'} : (A -> Prop) -> A := fun P : A -> Prop => @ε A P.
Lemma GABS_def {A : Type'} : (@GABS A) = (fun P : A -> Prop => @ε A P).
Proof. exact (REFL (@GABS A)). Qed.
Definition _SEQPATTERN {A B : Type'} : (A -> B -> Prop) -> (A -> B -> Prop) -> A -> B -> Prop := fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x).
Lemma _SEQPATTERN_def {A B : Type'} : (@_SEQPATTERN A B) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x)).
Proof. exact (REFL (@_SEQPATTERN A B)). Qed.
Definition _UNGUARDED_PATTERN : Prop -> Prop -> Prop := fun p : Prop => fun r : Prop => p /\ r.
Lemma _UNGUARDED_PATTERN_def : _UNGUARDED_PATTERN = (fun p : Prop => fun r : Prop => p /\ r).
Proof. exact (REFL _UNGUARDED_PATTERN). Qed.
Definition _GUARDED_PATTERN : Prop -> Prop -> Prop -> Prop := fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r).
Lemma _GUARDED_PATTERN_def : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)).
Proof. exact (REFL _GUARDED_PATTERN). Qed.
Definition _MATCH {A B : Type'} : A -> (A -> B -> Prop) -> B := fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False)).
Lemma _MATCH_def {A B : Type'} : (@_MATCH A B) = (fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False))).
Proof. exact (REFL (@_MATCH A B)). Qed.
Definition _FUNCTION {A B : Type'} : (A -> B -> Prop) -> A -> B := fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False)).
Lemma _FUNCTION_def {A B : Type'} : (@_FUNCTION A B) = (fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False))).
Proof. exact (REFL (@_FUNCTION A B)). Qed.
Definition CURRY {A B C : Type'} : ((prod A B) -> C) -> A -> B -> C := fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285).
Lemma CURRY_def {A B C : Type'} : (@CURRY A B C) = (fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285)).
Proof. exact (REFL (@CURRY A B C)). Qed.
Definition UNCURRY {A B C : Type'} : (A -> B -> C) -> (prod A B) -> C := fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305).
Lemma UNCURRY_def {A B C : Type'} : (@UNCURRY A B C) = (fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305)).
Proof. exact (REFL (@UNCURRY A B C)). Qed.
Definition PASSOC {A B C D : Type'} : ((prod (prod A B) C) -> D) -> (prod A (prod B C)) -> D := fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322))).
Lemma PASSOC_def {A B C D : Type'} : (@PASSOC A B C D) = (fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322)))).
Proof. exact (REFL (@PASSOC A B C D)). Qed.
Definition minimal : (nat -> Prop) -> nat := fun _6536 : nat -> Prop => @ε nat (fun n : nat => (_6536 n) /\ (forall m : nat, (ltn m n) -> ~ (_6536 m))).
Lemma minimal_def : minimal = (fun _6536 : nat -> Prop => @ε nat (fun n : nat => (_6536 n) /\ (forall m : nat, (ltn m n) -> ~ (_6536 m)))).
Proof. exact (REFL minimal). Qed.
Definition MEASURE {A : Type'} : (A -> nat) -> A -> A -> Prop := fun _8094 : A -> nat => fun x : A => fun y : A => ltn (_8094 x) (_8094 y).
Lemma MEASURE_def {A : Type'} : (@MEASURE A) = (fun _8094 : A -> nat => fun x : A => fun y : A => ltn (_8094 x) (_8094 y)).
Proof. exact (REFL (@MEASURE A)). Qed.
Definition NUMPAIR : nat -> nat -> nat := fun _17487 : nat => fun _17488 : nat => muln (expn (NUMERAL (BIT0 (BIT1 O))) _17487) (addn (muln (NUMERAL (BIT0 (BIT1 O))) _17488) (NUMERAL (BIT1 O))).
Lemma NUMPAIR_def : NUMPAIR = (fun _17487 : nat => fun _17488 : nat => muln (expn (NUMERAL (BIT0 (BIT1 O))) _17487) (addn (muln (NUMERAL (BIT0 (BIT1 O))) _17488) (NUMERAL (BIT1 O)))).
Proof. exact (REFL NUMPAIR). Qed.
Definition NUMFST : nat -> nat := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun X : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17503 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), exists Y : nat -> nat, forall x : nat, forall y : nat, ((X _17503 (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O))))))))))))).
Lemma NUMFST_def : NUMFST = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun X : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17503 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), exists Y : nat -> nat, forall x : nat, forall y : nat, ((X _17503 (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))))))))).
Proof. exact (REFL NUMFST). Qed.
Definition NUMSND : nat -> nat := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun Y : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17504 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), forall x : nat, forall y : nat, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y _17504 (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O))))))))))))).
Lemma NUMSND_def : NUMSND = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun Y : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17504 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), forall x : nat, forall y : nat, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y _17504 (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))))))))).
Proof. exact (REFL NUMSND). Qed.
Definition NUMSUM : Prop -> nat -> nat := fun _17505 : Prop => fun _17506 : nat => @COND nat _17505 (S (muln (NUMERAL (BIT0 (BIT1 O))) _17506)) (muln (NUMERAL (BIT0 (BIT1 O))) _17506).
Lemma NUMSUM_def : NUMSUM = (fun _17505 : Prop => fun _17506 : nat => @COND nat _17505 (S (muln (NUMERAL (BIT0 (BIT1 O))) _17506)) (muln (NUMERAL (BIT0 (BIT1 O))) _17506)).
Proof. exact (REFL NUMSUM). Qed.
Definition INJN {A : Type'} : nat -> nat -> A -> Prop := fun _17537 : nat => fun n : nat => fun a : A => n = _17537.
Lemma INJN_def {A : Type'} : (@INJN A) = (fun _17537 : nat => fun n : nat => fun a : A => n = _17537).
Proof. exact (REFL (@INJN A)). Qed.
Definition INJA {A : Type'} : A -> nat -> A -> Prop := fun _17542 : A => fun n : nat => fun b : A => b = _17542.
Lemma INJA_def {A : Type'} : (@INJA A) = (fun _17542 : A => fun n : nat => fun b : A => b = _17542).
Proof. exact (REFL (@INJA A)). Qed.
Definition INJF {A : Type'} : (nat -> nat -> A -> Prop) -> nat -> A -> Prop := fun _17549 : nat -> nat -> A -> Prop => fun n : nat => _17549 (NUMFST n) (NUMSND n).
Lemma INJF_def {A : Type'} : (@INJF A) = (fun _17549 : nat -> nat -> A -> Prop => fun n : nat => _17549 (NUMFST n) (NUMSND n)).
Proof. exact (REFL (@INJF A)). Qed.
Definition INJP {A : Type'} : (nat -> A -> Prop) -> (nat -> A -> Prop) -> nat -> A -> Prop := fun _17554 : nat -> A -> Prop => fun _17555 : nat -> A -> Prop => fun n : nat => fun a : A => @COND Prop (NUMLEFT n) (_17554 (NUMRIGHT n) a) (_17555 (NUMRIGHT n) a).
Lemma INJP_def {A : Type'} : (@INJP A) = (fun _17554 : nat -> A -> Prop => fun _17555 : nat -> A -> Prop => fun n : nat => fun a : A => @COND Prop (NUMLEFT n) (_17554 (NUMRIGHT n) a) (_17555 (NUMRIGHT n) a)).
Proof. exact (REFL (@INJP A)). Qed.
Definition ZCONSTR {A : Type'} : nat -> A -> (nat -> nat -> A -> Prop) -> nat -> A -> Prop := fun _17566 : nat => fun _17567 : A => fun _17568 : nat -> nat -> A -> Prop => @INJP A (@INJN A (S _17566)) (@INJP A (@INJA A _17567) (@INJF A _17568)).
Lemma ZCONSTR_def {A : Type'} : (@ZCONSTR A) = (fun _17566 : nat => fun _17567 : A => fun _17568 : nat -> nat -> A -> Prop => @INJP A (@INJN A (S _17566)) (@INJP A (@INJA A _17567) (@INJF A _17568))).
Proof. exact (REFL (@ZCONSTR A)). Qed.
Definition ZBOT {A : Type'} : nat -> A -> Prop := @INJP A (@INJN A (NUMERAL O)) (@ε (nat -> A -> Prop) (fun z : nat -> A -> Prop => True)).
Lemma ZBOT_def {A : Type'} : (@ZBOT A) = (@INJP A (@INJN A (NUMERAL O)) (@ε (nat -> A -> Prop) (fun z : nat -> A -> Prop => True))).
Proof. exact (REFL (@ZBOT A)). Qed.
Definition FNIL {A : Type'} : nat -> A := fun _17624 : nat => @ε A (fun x : A => True).
Lemma FNIL_def {A : Type'} : (@FNIL A) = (fun _17624 : nat => @ε A (fun x : A => True)).
Proof. exact (REFL (@FNIL A)). Qed.
Definition OUTL {A B : Type'} : (Datatypes.sum A B) -> A := @ε ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A => forall _17649 : prod nat (prod nat (prod nat nat)), forall x : A, (OUTL' _17649 (@inl A B x)) = x) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O))))))))))).
Lemma OUTL_def {A B : Type'} : (@OUTL A B) = (@ε ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A => forall _17649 : prod nat (prod nat (prod nat nat)), forall x : A, (OUTL' _17649 (@inl A B x)) = x) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))))))).
Proof. exact (REFL (@OUTL A B)). Qed.
Definition OUTR {A B : Type'} : (Datatypes.sum A B) -> B := @ε ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B => forall _17651 : prod nat (prod nat (prod nat nat)), forall y : B, (OUTR' _17651 (@inr A B y)) = y) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O))))))))))).
Lemma OUTR_def {A B : Type'} : (@OUTR A B) = (@ε ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B => forall _17651 : prod nat (prod nat (prod nat nat)), forall y : B, (OUTR' _17651 (@inr A B y)) = y) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))))))).
Proof. exact (REFL (@OUTR A B)). Qed.
Definition _22943 : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii := fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL O) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7).
Lemma _22943_def : _22943 = (fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL O) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)).
Proof. exact (REFL _22943). Qed.
Definition ASCII : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii := _22943.
Lemma ASCII_def : ASCII = _22943.
Proof. exact (REFL ASCII). Qed.
Definition DECIMAL : nat -> nat -> R := fun _27914 : nat => fun _27915 : nat => divr (R_of_nat _27914) (R_of_nat _27915).
Lemma DECIMAL_def : DECIMAL = (fun _27914 : nat => fun _27915 : nat => divr (R_of_nat _27914) (R_of_nat _27915)).
Proof. exact (REFL DECIMAL). Qed.
Definition eq2 {A : Type'} : A -> A -> (A -> A -> Prop) -> Prop := fun _29688 : A => fun _29689 : A => fun _29690 : A -> A -> Prop => _29690 _29688 _29689.
Lemma eq2_def {A : Type'} : (@eq2 A) = (fun _29688 : A => fun _29689 : A => fun _29690 : A -> A -> Prop => _29690 _29688 _29689).
Proof. exact (REFL (@eq2 A)). Qed.
Definition int_mod : int -> int -> int -> Prop := fun _29750 : int => fun _29751 : int => fun _29752 : int => dividez _29750 (subz _29751 _29752).
Lemma int_mod_def : int_mod = (fun _29750 : int => fun _29751 : int => fun _29752 : int => dividez _29750 (subz _29751 _29752)).
Proof. exact (REFL int_mod). Qed.
Definition num_of_int : int -> nat := fun _31320 : int => @ε nat (fun n : nat => (int_of_nat n) = _31320).
Lemma num_of_int_def : num_of_int = (fun _31320 : int => @ε nat (fun n : nat => (int_of_nat n) = _31320)).
Proof. exact (REFL num_of_int). Qed.
Definition num_divides : nat -> nat -> Prop := fun _31352 : nat => fun _31353 : nat => dividez (int_of_nat _31352) (int_of_nat _31353).
Lemma num_divides_def : num_divides = (fun _31352 : nat => fun _31353 : nat => dividez (int_of_nat _31352) (int_of_nat _31353)).
Proof. exact (REFL num_divides). Qed.
Definition num_mod : nat -> nat -> nat -> Prop := fun _31364 : nat => fun _31365 : nat => fun _31366 : nat => int_mod (int_of_nat _31364) (int_of_nat _31365) (int_of_nat _31366).
Lemma num_mod_def : num_mod = (fun _31364 : nat => fun _31365 : nat => fun _31366 : nat => int_mod (int_of_nat _31364) (int_of_nat _31365) (int_of_nat _31366)).
Proof. exact (REFL num_mod). Qed.
Definition num_coprime : (prod nat nat) -> Prop := fun _31385 : prod nat nat => pair_coprimez (@pair int int (int_of_nat (@fst nat nat _31385)) (int_of_nat (@snd nat nat _31385))).
Lemma num_coprime_def : num_coprime = (fun _31385 : prod nat nat => pair_coprimez (@pair int int (int_of_nat (@fst nat nat _31385)) (int_of_nat (@snd nat nat _31385)))).
Proof. exact (REFL num_coprime). Qed.
Definition num_gcd : (prod nat nat) -> nat := fun _31394 : prod nat nat => num_of_int (pair_gcdz (@pair int int (int_of_nat (@fst nat nat _31394)) (int_of_nat (@snd nat nat _31394)))).
Lemma num_gcd_def : num_gcd = (fun _31394 : prod nat nat => num_of_int (pair_gcdz (@pair int int (int_of_nat (@fst nat nat _31394)) (int_of_nat (@snd nat nat _31394))))).
Proof. exact (REFL num_gcd). Qed.
Definition num_lcm : (prod nat nat) -> nat := fun _31403 : prod nat nat => num_of_int (pair_lcmz (@pair int int (int_of_nat (@fst nat nat _31403)) (int_of_nat (@snd nat nat _31403)))).
Lemma num_lcm_def : num_lcm = (fun _31403 : prod nat nat => num_of_int (pair_lcmz (@pair int int (int_of_nat (@fst nat nat _31403)) (int_of_nat (@snd nat nat _31403))))).
Proof. exact (REFL num_lcm). Qed.
Definition prime : nat -> Prop := fun _32188 : nat => (~ (_32188 = (NUMERAL (BIT1 O)))) /\ (forall x : nat, (num_divides x _32188) -> (x = (NUMERAL (BIT1 O))) \/ (x = _32188)).
Lemma prime_def : prime = (fun _32188 : nat => (~ (_32188 = (NUMERAL (BIT1 O)))) /\ (forall x : nat, (num_divides x _32188) -> (x = (NUMERAL (BIT1 O))) \/ (x = _32188))).
Proof. exact (REFL prime). Qed.
Definition real_zpow : R -> int -> R := fun _32346 : R => fun _32347 : int => @COND R (lez (int_of_nat (NUMERAL O)) _32347) (expr _32346 (num_of_int _32347)) (invr (expr _32346 (num_of_int (oppz _32347)))).
Lemma real_zpow_def : real_zpow = (fun _32346 : R => fun _32347 : int => @COND R (lez (int_of_nat (NUMERAL O)) _32347) (expr _32346 (num_of_int _32347)) (invr (expr _32346 (num_of_int (oppz _32347))))).
Proof. exact (REFL real_zpow). Qed.
Definition INFINITE {A : Type'} : (A -> Prop) -> Prop := fun _32574 : A -> Prop => ~ (@finite_set A _32574).
Lemma INFINITE_def {A : Type'} : (@INFINITE A) = (fun _32574 : A -> Prop => ~ (@finite_set A _32574)).
Proof. exact (REFL (@INFINITE A)). Qed.
Definition INJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32591 : A -> B => fun _32592 : A -> Prop => fun _32593 : B -> Prop => (forall x : A, (@IN A x _32592) -> @IN B (_32591 x) _32593) /\ (forall x : A, forall y : A, ((@IN A x _32592) /\ ((@IN A y _32592) /\ ((_32591 x) = (_32591 y)))) -> x = y).
Lemma INJ_def {A B : Type'} : (@INJ A B) = (fun _32591 : A -> B => fun _32592 : A -> Prop => fun _32593 : B -> Prop => (forall x : A, (@IN A x _32592) -> @IN B (_32591 x) _32593) /\ (forall x : A, forall y : A, ((@IN A x _32592) /\ ((@IN A y _32592) /\ ((_32591 x) = (_32591 y)))) -> x = y)).
Proof. exact (REFL (@INJ A B)). Qed.
Definition SURJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32612 : A -> B => fun _32613 : A -> Prop => fun _32614 : B -> Prop => (forall x : A, (@IN A x _32613) -> @IN B (_32612 x) _32614) /\ (forall x : B, (@IN B x _32614) -> exists y : A, (@IN A y _32613) /\ ((_32612 y) = x)).
Lemma SURJ_def {A B : Type'} : (@SURJ A B) = (fun _32612 : A -> B => fun _32613 : A -> Prop => fun _32614 : B -> Prop => (forall x : A, (@IN A x _32613) -> @IN B (_32612 x) _32614) /\ (forall x : B, (@IN B x _32614) -> exists y : A, (@IN A y _32613) /\ ((_32612 y) = x))).
Proof. exact (REFL (@SURJ A B)). Qed.
Definition BIJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32633 : A -> B => fun _32634 : A -> Prop => fun _32635 : B -> Prop => (@INJ A B _32633 _32634 _32635) /\ (@SURJ A B _32633 _32634 _32635).
Lemma BIJ_def {A B : Type'} : (@BIJ A B) = (fun _32633 : A -> B => fun _32634 : A -> Prop => fun _32635 : B -> Prop => (@INJ A B _32633 _32634 _32635) /\ (@SURJ A B _32633 _32634 _32635)).
Proof. exact (REFL (@BIJ A B)). Qed.
Definition CHOICE {A : Type'} : (A -> Prop) -> A := fun _32654 : A -> Prop => @ε A (fun x : A => @IN A x _32654).
Lemma CHOICE_def {A : Type'} : (@CHOICE A) = (fun _32654 : A -> Prop => @ε A (fun x : A => @IN A x _32654)).
Proof. exact (REFL (@CHOICE A)). Qed.
Definition REST {A : Type'} : (A -> Prop) -> A -> Prop := fun _32659 : A -> Prop => @DELETE A _32659 (@CHOICE A _32659).
Lemma REST_def {A : Type'} : (@REST A) = (fun _32659 : A -> Prop => @DELETE A _32659 (@CHOICE A _32659)).
Proof. exact (REFL (@REST A)). Qed.
Definition FINREC {A B : Type'} : (A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop) (fun FINREC' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop => forall _42261 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall f : A -> B -> B, forall s : A -> Prop, forall a : B, forall b : B, (FINREC' _42261 f b s a (NUMERAL O)) = ((s = (@set0 A)) /\ (a = b))) /\ (forall b : B, forall s : A -> Prop, forall n : nat, forall a : B, forall f : A -> B -> B, (FINREC' _42261 f b s a (S n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((FINREC' _42261 f b (@DELETE A s x) c n) /\ (a = (f x c)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 O))))))))))))).
Lemma FINREC_def {A B : Type'} : (@FINREC A B) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop) (fun FINREC' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop => forall _42261 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall f : A -> B -> B, forall s : A -> Prop, forall a : B, forall b : B, (FINREC' _42261 f b s a (NUMERAL O)) = ((s = (@set0 A)) /\ (a = b))) /\ (forall b : B, forall s : A -> Prop, forall n : nat, forall a : B, forall f : A -> B -> B, (FINREC' _42261 f b s a (S n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((FINREC' _42261 f b (@DELETE A s x) c n) /\ (a = (f x c)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))))))))).
Proof. exact (REFL (@FINREC A B)). Qed.
Definition HAS_SIZE {A : Type'} : (A -> Prop) -> nat -> Prop := fun _43489 : A -> Prop => fun _43490 : nat => (@finite_set A _43489) /\ ((@CARD A _43489) = _43490).
Lemma HAS_SIZE_def {A : Type'} : (@HAS_SIZE A) = (fun _43489 : A -> Prop => fun _43490 : nat => (@finite_set A _43489) /\ ((@CARD A _43489) = _43490)).
Proof. exact (REFL (@HAS_SIZE A)). Qed.
Definition CROSS {A B : Type'} : (A -> Prop) -> (B -> Prop) -> (prod A B) -> Prop := fun _47408 : A -> Prop => fun _47409 : B -> Prop => @GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x _47408) /\ (@IN B y _47409)) (@pair A B x y)).
Lemma CROSS_def {A B : Type'} : (@CROSS A B) = (fun _47408 : A -> Prop => fun _47409 : B -> Prop => @GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x _47408) /\ (@IN B y _47409)) (@pair A B x y))).
Proof. exact (REFL (@CROSS A B)). Qed.
Definition ARB {A : Type'} : A := @ε A (fun x : A => False).
Lemma ARB_def {A : Type'} : (@ARB A) = (@ε A (fun x : A => False)).
Proof. exact (REFL (@ARB A)). Qed.
Definition EXTENSIONAL {A B : Type'} : (A -> Prop) -> (A -> B) -> Prop := fun _48182 : A -> Prop => @GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x _48182)) -> (f x) = (@ARB B)) f).
Lemma EXTENSIONAL_def {A B : Type'} : (@EXTENSIONAL A B) = (fun _48182 : A -> Prop => @GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x _48182)) -> (f x) = (@ARB B)) f)).
Proof. exact (REFL (@EXTENSIONAL A B)). Qed.
Definition RESTRICTION {A B : Type'} : (A -> Prop) -> (A -> B) -> A -> B := fun _48234 : A -> Prop => fun _48235 : A -> B => fun _48236 : A => @COND B (@IN A _48236 _48234) (_48235 _48236) (@ARB B).
Lemma RESTRICTION_def {A B : Type'} : (@RESTRICTION A B) = (fun _48234 : A -> Prop => fun _48235 : A -> B => fun _48236 : A => @COND B (@IN A _48236 _48234) (_48235 _48236) (@ARB B)).
Proof. exact (REFL (@RESTRICTION A B)). Qed.
Definition cartesian_product {A K : Type'} : (K -> Prop) -> (K -> A -> Prop) -> (K -> A) -> Prop := fun _48429 : K -> Prop => fun _48430 : K -> A -> Prop => @GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A _48429 f) /\ (forall i : K, (@IN K i _48429) -> @IN A (f i) (_48430 i))) f).
Lemma cartesian_product_def {A K : Type'} : (@cartesian_product A K) = (fun _48429 : K -> Prop => fun _48430 : K -> A -> Prop => @GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A _48429 f) /\ (forall i : K, (@IN K i _48429) -> @IN A (f i) (_48430 i))) f)).
Proof. exact (REFL (@cartesian_product A K)). Qed.
Definition product_map {A B K : Type'} : (K -> Prop) -> (K -> A -> B) -> (K -> A) -> K -> B := fun _49478 : K -> Prop => fun _49479 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _49478 (fun i : K => _49479 i (x i)).
Lemma product_map_def {A B K : Type'} : (@product_map A B K) = (fun _49478 : K -> Prop => fun _49479 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _49478 (fun i : K => _49479 i (x i))).
Proof. exact (REFL (@product_map A B K)). Qed.
Definition disjoint_union {A K : Type'} : (K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop := fun _49614 : K -> Prop => fun _49615 : K -> A -> Prop => @GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i _49614) /\ (@IN A x (_49615 i))) (@pair K A i x)).
Lemma disjoint_union_def {A K : Type'} : (@disjoint_union A K) = (fun _49614 : K -> Prop => fun _49615 : K -> A -> Prop => @GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i _49614) /\ (@IN A x (_49615 i))) (@pair K A i x))).
Proof. exact (REFL (@disjoint_union A K)). Qed.
Definition pairwise {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _56702 : A -> A -> Prop => fun _56703 : A -> Prop => forall x : A, forall y : A, ((@IN A x _56703) /\ ((@IN A y _56703) /\ (~ (x = y)))) -> _56702 x y.
Lemma pairwise_def {A : Type'} : (@pairwise A) = (fun _56702 : A -> A -> Prop => fun _56703 : A -> Prop => forall x : A, forall y : A, ((@IN A x _56703) /\ ((@IN A y _56703) /\ (~ (x = y)))) -> _56702 x y).
Proof. exact (REFL (@pairwise A)). Qed.
Definition UNION_OF {A : Type'} : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57415 : ((A -> Prop) -> Prop) -> Prop => fun _57416 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57415 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57416 c) /\ ((@UNIONS A u) = s)).
Lemma UNION_OF_def {A : Type'} : (@UNION_OF A) = (fun _57415 : ((A -> Prop) -> Prop) -> Prop => fun _57416 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57415 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57416 c) /\ ((@UNIONS A u) = s))).
Proof. exact (REFL (@UNION_OF A)). Qed.
Definition INTERSECTION_OF {A : Type'} : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57427 : ((A -> Prop) -> Prop) -> Prop => fun _57428 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57427 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57428 c) /\ ((@INTERS A u) = s)).
Lemma INTERSECTION_OF_def {A : Type'} : (@INTERSECTION_OF A) = (fun _57427 : ((A -> Prop) -> Prop) -> Prop => fun _57428 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57427 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57428 c) /\ ((@INTERS A u) = s))).
Proof. exact (REFL (@INTERSECTION_OF A)). Qed.
Definition ARBITRARY {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _57563 : (A -> Prop) -> Prop => True.
Lemma ARBITRARY_def {A : Type'} : (@ARBITRARY A) = (fun _57563 : (A -> Prop) -> Prop => True).
Proof. exact (REFL (@ARBITRARY A)). Qed.
Definition le_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64157 : A -> Prop => fun _64158 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64157) -> @IN B (f x) _64158) /\ (forall x : A, forall y : A, ((@IN A x _64157) /\ ((@IN A y _64157) /\ ((f x) = (f y)))) -> x = y).
Lemma le_c_def {A B : Type'} : (@le_c A B) = (fun _64157 : A -> Prop => fun _64158 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64157) -> @IN B (f x) _64158) /\ (forall x : A, forall y : A, ((@IN A x _64157) /\ ((@IN A y _64157) /\ ((f x) = (f y)))) -> x = y)).
Proof. exact (REFL (@le_c A B)). Qed.
Definition lt_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64169 : A -> Prop => fun _64170 : B -> Prop => (@le_c A B _64169 _64170) /\ (~ (@le_c B A _64170 _64169)).
Lemma lt_c_def {A B : Type'} : (@lt_c A B) = (fun _64169 : A -> Prop => fun _64170 : B -> Prop => (@le_c A B _64169 _64170) /\ (~ (@le_c B A _64170 _64169))).
Proof. exact (REFL (@lt_c A B)). Qed.
Definition eq_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64181 : A -> Prop => fun _64182 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64181) -> @IN B (f x) _64182) /\ (forall y : B, (@IN B y _64182) -> @ex1 A (fun x : A => (@IN A x _64181) /\ ((f x) = y))).
Lemma eq_c_def {A B : Type'} : (@eq_c A B) = (fun _64181 : A -> Prop => fun _64182 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64181) -> @IN B (f x) _64182) /\ (forall y : B, (@IN B y _64182) -> @ex1 A (fun x : A => (@IN A x _64181) /\ ((f x) = y)))).
Proof. exact (REFL (@eq_c A B)). Qed.
Definition ge_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64193 : A -> Prop => fun _64194 : B -> Prop => @le_c B A _64194 _64193.
Lemma ge_c_def {A B : Type'} : (@ge_c A B) = (fun _64193 : A -> Prop => fun _64194 : B -> Prop => @le_c B A _64194 _64193).
Proof. exact (REFL (@ge_c A B)). Qed.
Definition gt_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64205 : A -> Prop => fun _64206 : B -> Prop => @lt_c B A _64206 _64205.
Lemma gt_c_def {A B : Type'} : (@gt_c A B) = (fun _64205 : A -> Prop => fun _64206 : B -> Prop => @lt_c B A _64206 _64205).
Proof. exact (REFL (@gt_c A B)). Qed.
Definition COUNTABLE {A : Type'} : (A -> Prop) -> Prop := fun _64356 : A -> Prop => @ge_c nat A (@setT nat) _64356.
Lemma COUNTABLE_def {A : Type'} : (@COUNTABLE A) = (fun _64356 : A -> Prop => @ge_c nat A (@setT nat) _64356).
Proof. exact (REFL (@COUNTABLE A)). Qed.
Definition sup : (R -> Prop) -> R := fun _64361 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _64361) -> ler x a) /\ (forall b : R, (forall x : R, (@IN R x _64361) -> ler x b) -> ler a b)).
Lemma sup_def : sup = (fun _64361 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _64361) -> ler x a) /\ (forall b : R, (forall x : R, (@IN R x _64361) -> ler x b) -> ler a b))).
Proof. exact (REFL sup). Qed.
Definition inf : (R -> Prop) -> R := fun _65220 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _65220) -> ler a x) /\ (forall b : R, (forall x : R, (@IN R x _65220) -> ler b x) -> ler b a)).
Lemma inf_def : inf = (fun _65220 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _65220) -> ler a x) /\ (forall b : R, (forall x : R, (@IN R x _65220) -> ler b x) -> ler b a))).
Proof. exact (REFL inf). Qed.
Definition has_inf : (R -> Prop) -> R -> Prop := fun _66570 : R -> Prop => fun _66571 : R => forall c : R, (forall x : R, (@IN R x _66570) -> ler c x) = (ler c _66571).
Lemma has_inf_def : has_inf = (fun _66570 : R -> Prop => fun _66571 : R => forall c : R, (forall x : R, (@IN R x _66570) -> ler c x) = (ler c _66571)).
Proof. exact (REFL has_inf). Qed.
Definition has_sup : (R -> Prop) -> R -> Prop := fun _66582 : R -> Prop => fun _66583 : R => forall c : R, (forall x : R, (@IN R x _66582) -> ler x c) = (ler _66583 c).
Lemma has_sup_def : has_sup = (fun _66582 : R -> Prop => fun _66583 : R => forall c : R, (forall x : R, (@IN R x _66582) -> ler x c) = (ler _66583 c)).
Proof. exact (REFL has_sup). Qed.
Definition monoidal {A : Type'} : (A -> A -> A) -> Prop := fun _68925 : A -> A -> A => (forall x : A, forall y : A, (_68925 x y) = (_68925 y x)) /\ ((forall x : A, forall y : A, forall z : A, (_68925 x (_68925 y z)) = (_68925 (_68925 x y) z)) /\ (forall x : A, (_68925 (@neutral A _68925) x) = x)).
Lemma monoidal_def {A : Type'} : (@monoidal A) = (fun _68925 : A -> A -> A => (forall x : A, forall y : A, (_68925 x y) = (_68925 y x)) /\ ((forall x : A, forall y : A, forall z : A, (_68925 x (_68925 y z)) = (_68925 (_68925 x y) z)) /\ (forall x : A, (_68925 (@neutral A _68925) x) = x))).
Proof. exact (REFL (@monoidal A)). Qed.
Definition iterato {A K : Type'} : (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) (fun itty : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => forall _76787 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (itty _76787 dom neut op ltle k f) = (@COND A ((@finite_set K (@GSPEC K (fun GEN_PVAR_265 : K => exists i : K, @SETSPEC K GEN_PVAR_265 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_266 : K => exists i : K, @SETSPEC K GEN_PVAR_266 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) (@LET K A (fun i : K => @LET_END A (op (f i) (itty _76787 dom neut op ltle (@GSPEC K (fun GEN_PVAR_267 : K => exists j : K, @SETSPEC K GEN_PVAR_267 ((@IN K j (@DELETE K k i)) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j)) f))) (@COND K (exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) (@ε K (fun i : K => (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i)))) (@ε K (fun i : K => (@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))))))) neut)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))))))))).
Lemma iterato_def {A K : Type'} : (@iterato A K) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) (fun itty : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => forall _76787 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (itty _76787 dom neut op ltle k f) = (@COND A ((@finite_set K (@GSPEC K (fun GEN_PVAR_265 : K => exists i : K, @SETSPEC K GEN_PVAR_265 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_266 : K => exists i : K, @SETSPEC K GEN_PVAR_266 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) (@LET K A (fun i : K => @LET_END A (op (f i) (itty _76787 dom neut op ltle (@GSPEC K (fun GEN_PVAR_267 : K => exists j : K, @SETSPEC K GEN_PVAR_267 ((@IN K j (@DELETE K k i)) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j)) f))) (@COND K (exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) (@ε K (fun i : K => (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i)))) (@ε K (fun i : K => (@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))))))) neut)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O))))))))))))))).
Proof. exact (REFL (@iterato A K)). Qed.
Definition nproduct {A : Type'} : (A -> Prop) -> (A -> nat) -> nat := @iterate A nat muln.
Lemma nproduct_def {A : Type'} : (@nproduct A) = (@iterate A nat muln).
Proof. exact (REFL (@nproduct A)). Qed.
Definition iproduct {A : Type'} : (A -> Prop) -> (A -> int) -> int := @iterate A int mulz.
Lemma iproduct_def {A : Type'} : (@iproduct A) = (@iterate A int mulz).
Proof. exact (REFL (@iproduct A)). Qed.
Definition product {A : Type'} : (A -> Prop) -> (A -> R) -> R := @iterate A R mulr.
Lemma product_def {A : Type'} : (@product A) = (@iterate A R mulr).
Proof. exact (REFL (@product A)). Qed.
Definition isum {A : Type'} : (A -> Prop) -> (A -> int) -> int := @iterate A int addz.
Lemma isum_def {A : Type'} : (@isum A) = (@iterate A int addz).
Proof. exact (REFL (@isum A)). Qed.
Definition nsum {A : Type'} : (A -> Prop) -> (A -> nat) -> nat := @iterate A nat addn.
Lemma nsum_def {A : Type'} : (@nsum A) = (@iterate A nat addn).
Proof. exact (REFL (@nsum A)). Qed.
Definition polynomial_function : (R -> R) -> Prop := fun _94200 : R -> R => exists m : nat, exists c : nat -> R, forall x : R, (_94200 x) = (@sum nat (dotdot (NUMERAL O) m) (fun i : nat => mulr (c i) (expr x i))).
Lemma polynomial_function_def : polynomial_function = (fun _94200 : R -> R => exists m : nat, exists c : nat -> R, forall x : R, (_94200 x) = (@sum nat (dotdot (NUMERAL O) m) (fun i : nat => mulr (c i) (expr x i)))).
Proof. exact (REFL polynomial_function). Qed.
Definition lambda {A B : Type'} : (nat -> A) -> cart A B := fun _94688 : nat -> A => @ε (cart A B) (fun f : cart A B => forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94688 i)).
Lemma lambda_def {A B : Type'} : (@lambda A B) = (fun _94688 : nat -> A => @ε (cart A B) (fun f : cart A B => forall i : nat, ((leqn (NUMERAL (BIT1 O)) i) /\ (leqn i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94688 i))).
Proof. exact (REFL (@lambda A B)). Qed.
Definition pastecart {A M N' : Type'} : (cart A M) -> (cart A N') -> cart A (finite_sum M N') := fun _94979 : cart A M => fun _94980 : cart A N' => @lambda A (finite_sum M N') (fun i : nat => @COND A (leqn i (@dimindex M (@setT M))) (@dollar A M _94979 i) (@dollar A N' _94980 (subn i (@dimindex M (@setT M))))).
Lemma pastecart_def {A M N' : Type'} : (@pastecart A M N') = (fun _94979 : cart A M => fun _94980 : cart A N' => @lambda A (finite_sum M N') (fun i : nat => @COND A (leqn i (@dimindex M (@setT M))) (@dollar A M _94979 i) (@dollar A N' _94980 (subn i (@dimindex M (@setT M)))))).
Proof. exact (REFL (@pastecart A M N')). Qed.
Definition fstcart {A M N' : Type'} : (cart A (finite_sum M N')) -> cart A M := fun _94991 : cart A (finite_sum M N') => @lambda A M (fun i : nat => @dollar A (finite_sum M N') _94991 i).
Lemma fstcart_def {A M N' : Type'} : (@fstcart A M N') = (fun _94991 : cart A (finite_sum M N') => @lambda A M (fun i : nat => @dollar A (finite_sum M N') _94991 i)).
Proof. exact (REFL (@fstcart A M N')). Qed.
Definition sndcart {A M N' : Type'} : (cart A (finite_sum M N')) -> cart A N' := fun _94996 : cart A (finite_sum M N') => @lambda A N' (fun i : nat => @dollar A (finite_sum M N') _94996 (addn i (@dimindex M (@setT M)))).
Lemma sndcart_def {A M N' : Type'} : (@sndcart A M N') = (fun _94996 : cart A (finite_sum M N') => @lambda A N' (fun i : nat => @dollar A (finite_sum M N') _94996 (addn i (@dimindex M (@setT M))))).
Proof. exact (REFL (@sndcart A M N')). Qed.
Definition _100406 {A : Type'} : (finite_sum A A) -> tybit0 A := fun a : finite_sum A A => @_mk_tybit0 A ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL O) a' (fun n : nat => @BOTTOM (finite_sum A A))) a).
Lemma _100406_def {A : Type'} : (@_100406 A) = (fun a : finite_sum A A => @_mk_tybit0 A ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL O) a' (fun n : nat => @BOTTOM (finite_sum A A))) a)).
Proof. exact (REFL (@_100406 A)). Qed.
Definition mktybit0 {A : Type'} : (finite_sum A A) -> tybit0 A := @_100406 A.
Lemma mktybit0_def {A : Type'} : (@mktybit0 A) = (@_100406 A).
Proof. exact (REFL (@mktybit0 A)). Qed.
Definition _100425 {A : Type'} : (finite_sum (finite_sum A A) unit) -> tybit1 A := fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL O) a' (fun n : nat => @BOTTOM (finite_sum (finite_sum A A) unit))) a).
Lemma _100425_def {A : Type'} : (@_100425 A) = (fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL O) a' (fun n : nat => @BOTTOM (finite_sum (finite_sum A A) unit))) a)).
Proof. exact (REFL (@_100425 A)). Qed.
Definition mktybit1 {A : Type'} : (finite_sum (finite_sum A A) unit) -> tybit1 A := @_100425 A.
Lemma mktybit1_def {A : Type'} : (@mktybit1 A) = (@_100425 A).
Proof. exact (REFL (@mktybit1 A)). Qed.
Definition vector {A N' : Type'} : (seq A) -> cart A N' := fun _102119 : seq A => @lambda A N' (fun i : nat => @EL A (subn i (NUMERAL (BIT1 O))) _102119).
Lemma vector_def {A N' : Type'} : (@vector A N') = (fun _102119 : seq A => @lambda A N' (fun i : nat => @EL A (subn i (NUMERAL (BIT1 O))) _102119)).
Proof. exact (REFL (@vector A N')). Qed.
Definition PCROSS {A M N' : Type'} : ((cart A M) -> Prop) -> ((cart A N') -> Prop) -> (cart A (finite_sum M N')) -> Prop := fun _102146 : (cart A M) -> Prop => fun _102147 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x _102146) /\ (@IN (cart A N') y _102147)) (@pastecart A M N' x y)).
Lemma PCROSS_def {A M N' : Type'} : (@PCROSS A M N') = (fun _102146 : (cart A M) -> Prop => fun _102147 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x _102146) /\ (@IN (cart A N') y _102147)) (@pastecart A M N' x y))).
Proof. exact (REFL (@PCROSS A M N')). Qed.
Definition CASEWISE {_138002 _138038 _138042 _138043 : Type'} : (seq (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (seq (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002) (fun CASEWISE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (seq (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 => forall _102751 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall f : _138043, forall x : _138042, (CASEWISE' _102751 (@nil (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) f x) = (@ε _138002 (fun y : _138002 => True))) /\ (forall h : prod (_138038 -> _138042) (_138043 -> _138038 -> _138002), forall t : seq (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)), forall f : _138043, forall x : _138042, (CASEWISE' _102751 (@cons (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) h t) f x) = (@COND _138002 (exists y : _138038, (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x) (@snd (_138038 -> _138042) (_138043 -> _138038 -> _138002) h f (@ε _138038 (fun y : _138038 => (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x))) (CASEWISE' _102751 t f x)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O))))))))))))))).
Lemma CASEWISE_def {_138002 _138038 _138042 _138043 : Type'} : (@CASEWISE _138002 _138038 _138042 _138043) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (seq (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002) (fun CASEWISE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (seq (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 => forall _102751 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall f : _138043, forall x : _138042, (CASEWISE' _102751 (@nil (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) f x) = (@ε _138002 (fun y : _138002 => True))) /\ (forall h : prod (_138038 -> _138042) (_138043 -> _138038 -> _138002), forall t : seq (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)), forall f : _138043, forall x : _138042, (CASEWISE' _102751 (@cons (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) h t) f x) = (@COND _138002 (exists y : _138038, (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x) (@snd (_138038 -> _138042) (_138043 -> _138038 -> _138002) h f (@ε _138038 (fun y : _138038 => (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x))) (CASEWISE' _102751 t f x)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 O)))))))))))))))).
Proof. exact (REFL (@CASEWISE _138002 _138038 _138042 _138043)). Qed.
Definition admissible {_138333 _138336 _138340 _138341 _138346 : Type'} : (_138340 -> _138333 -> Prop) -> ((_138340 -> _138336) -> _138346 -> Prop) -> (_138346 -> _138333) -> ((_138340 -> _138336) -> _138346 -> _138341) -> Prop := fun _103818 : _138340 -> _138333 -> Prop => fun _103819 : (_138340 -> _138336) -> _138346 -> Prop => fun _103820 : _138346 -> _138333 => fun _103821 : (_138340 -> _138336) -> _138346 -> _138341 => forall f : _138340 -> _138336, forall g : _138340 -> _138336, forall a : _138346, ((_103819 f a) /\ ((_103819 g a) /\ (forall z : _138340, (_103818 z (_103820 a)) -> (f z) = (g z)))) -> (_103821 f a) = (_103821 g a).
Lemma admissible_def {_138333 _138336 _138340 _138341 _138346 : Type'} : (@admissible _138333 _138336 _138340 _138341 _138346) = (fun _103818 : _138340 -> _138333 -> Prop => fun _103819 : (_138340 -> _138336) -> _138346 -> Prop => fun _103820 : _138346 -> _138333 => fun _103821 : (_138340 -> _138336) -> _138346 -> _138341 => forall f : _138340 -> _138336, forall g : _138340 -> _138336, forall a : _138346, ((_103819 f a) /\ ((_103819 g a) /\ (forall z : _138340, (_103818 z (_103820 a)) -> (f z) = (g z)))) -> (_103821 f a) = (_103821 g a)).
Proof. exact (REFL (@admissible _138333 _138336 _138340 _138341 _138346)). Qed.
Definition tailadmissible {A B P : Type'} : (A -> A -> Prop) -> ((A -> B) -> P -> Prop) -> (P -> A) -> ((A -> B) -> P -> B) -> Prop := fun _103850 : A -> A -> Prop => fun _103851 : (A -> B) -> P -> Prop => fun _103852 : P -> A => fun _103853 : (A -> B) -> P -> B => exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (_103850 y (G f a))) -> _103850 y (_103852 a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (_103850 z (_103852 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (_103851 f a) -> (_103853 f a) = (@COND B (P' f a) (f (G f a)) (H f a)))).
Lemma tailadmissible_def {A B P : Type'} : (@tailadmissible A B P) = (fun _103850 : A -> A -> Prop => fun _103851 : (A -> B) -> P -> Prop => fun _103852 : P -> A => fun _103853 : (A -> B) -> P -> B => exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (_103850 y (G f a))) -> _103850 y (_103852 a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (_103850 z (_103852 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (_103851 f a) -> (_103853 f a) = (@COND B (P' f a) (f (G f a)) (H f a))))).
Proof. exact (REFL (@tailadmissible A B P)). Qed.
Definition superadmissible {_138490 _138492 _138498 : Type'} : (_138490 -> _138490 -> Prop) -> ((_138490 -> _138492) -> _138498 -> Prop) -> (_138498 -> _138490) -> ((_138490 -> _138492) -> _138498 -> _138492) -> Prop := fun _103882 : _138490 -> _138490 -> Prop => fun _103883 : (_138490 -> _138492) -> _138498 -> Prop => fun _103884 : _138498 -> _138490 => fun _103885 : (_138490 -> _138492) -> _138498 -> _138492 => (@admissible _138490 _138492 _138490 Prop _138498 _103882 (fun f : _138490 -> _138492 => fun a : _138498 => True) _103884 _103883) -> @tailadmissible _138490 _138492 _138498 _103882 _103883 _103884 _103885.
Lemma superadmissible_def {_138490 _138492 _138498 : Type'} : (@superadmissible _138490 _138492 _138498) = (fun _103882 : _138490 -> _138490 -> Prop => fun _103883 : (_138490 -> _138492) -> _138498 -> Prop => fun _103884 : _138498 -> _138490 => fun _103885 : (_138490 -> _138492) -> _138498 -> _138492 => (@admissible _138490 _138492 _138490 Prop _138498 _103882 (fun f : _138490 -> _138492 => fun a : _138498 => True) _103884 _103883) -> @tailadmissible _138490 _138492 _138498 _103882 _103883 _103884 _103885).
Proof. exact (REFL (@superadmissible _138490 _138492 _138498)). Qed.
