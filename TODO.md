# TODO
## When rocq-fourcolor is updated (Doesn't support rocq >= 9.2 / mathcomp >= 2.6, see [this rocq-fourcolor issue](https://github.com/rocq-community/fourcolor/issues/79)):
- In automatically generated files, rename mathcomp.algebra.ssralg to mathcomp.algebra.algebraic_hierarchy.ssralg (alternatively, it is already possible to instead use From mathcomp Require Import ssralg, but this would change the automatically generated structure)
- Replace "Notation" with "Abbreviation" when possible (or when support is dropped)
- Watch out for the progress on automatically generated inductive schemes. For now, Rocq 9.2.0 issues warning about the necessary schemes for list and List.Forall/List.Forall2 not being registered, But one would assume they will be registered in corelib/stdlib
## When rocq 9.3.0 is released
- Replace ssreflect's rewrite with rw (or when support is dropped)