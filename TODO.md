# TODO
## When rocq-fourcolor is updated (doesn't support rocq >= 9.2 / mathcomp >= 2.6 ):
- In automatically generated files, rename mathcomp.algebra.ssralg to mathcomp.algebra.alg.ssralg (alternatively, it is already possible to instead use From mathcomp Require Import ssralg, but this would change the automatically generated structure)
- Replace "Notation" with "Abbreviation" when possible
- Watch out for the progress on automatically generated inductive schemes. For now, Rocq 9.2.0 issues warning about the necessary schemes for list and List.Forall/List.Forall2 not being registered, But one would assume they will be registered in corelib/stdlib
## When rocq 9.3.0 is released
- Replace ssreflect's rewrite with rw (deprecated)
- Check for potential proofscripts failing due to rewrite/rw goal order changing.
  + For example, change tactic if_triv and variants.
  + Alternatively, add "Set SsrOldRewriteGoalsOrder." at the start of files. 