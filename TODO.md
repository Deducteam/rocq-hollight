# TODO
## When mathcomp-algebra 2.6.0 is released:
- In automatically generated files, rename mathcomp.algebra.ssralg to mathcomp.algebra.alg.ssralg (alternatively, it is already possible to instead use From mathcomp Require Import ssralg, but this would change the automatically generated structure)
## When mathcomp-classical 1.16.0 is released
- Add support for Rocq 9.1.0 (in particular in CI)
## When Rocq 9.2.0 is released
- Replace "Notation" with "Abbreviation" when possible
- Watch out for the progress on automatically generated inductive schemes. For now, Rocq 9.2.0 issues warning about the necessary schemes for list and List.Forall/List.Forall2 not being registered, But one would assume they will be registered in corelib/stdlib
