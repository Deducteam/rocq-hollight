From HB Require Import structures.
From mathcomp Require Import eqtype choice nmodule classical_sets.

(* To be imported before pseudometric_structure.v from mathcomp analysis.
   More general than the instance defined there *)
HB.instance Definition _ (G : Algebra.ChoiceBaseAddUMagma.type) :=
  isPointed.Build G 0%R.

(* To use for Types that can be infered as ChoiceBaseAddUMagmas.
   For example, G : zmodType cannot be infered as Type', but G%' can. *)
Notation "T '%' '":= (T : Algebra.ChoiceBaseAddUMagma.type) (format "T '%' '").