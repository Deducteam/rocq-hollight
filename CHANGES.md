All notable changes to this project are documented in this file.
The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## 1.0.0 (2026-09-08)

First release. This new package regroups in a single one [coq-hol-light-real-with-nat](https://github.com/Deducteam/coq-hol-light-real-with-nat), [coq-hol-light-real-with-N](https://github.com/Deducteam/coq-hol-light-real-with-N) and [coq-hol-light](https://github.com/Deducteam/coq-hol-light), following the structure of the HOL-Light repository. It also includes the newly translated Logic library. We now align the basic data structures (integers, lists, real numbers) and their basic operations with the ones in Mathcomp rather than with the ones in the Rocq standard library. This allows us to align more complex objects that are present in Mathcomp but not in the Rocq standard library.

<!--------------------------------------------------------------------------->
# Previous changes in [coq-hol-light-real-with-nat](https://github.com/Deducteam/coq-hol-light-real-with-nat)

AUTHORS:
- [Frédéric Blanqui](https://blanqui.gitlabpages.inria.fr/)
- [Anthony Bordg](https://sites.google.com/site/anthonybordg/) for the alignmen
t of the types sum, list, option
- Amal Makni for the alignment of subtypes, quotient types and part of the type
 of real numbers

## Unreleased

- renamings of HOLLight_Real into mappings, erasing.lp into mappings.lp
- section Mappings.Quotient: remove Local Definition of a
- hol_upto_real.ml: update wrt HOL-Light 3.0
- mappings.lp: update wrt https://github.com/Deducteam/hol2dk/pull/161 and http
s://github.com/Deducteam/hol2dk/pull/149
- reproduce: update hollight, hol2dk and lambdapi versions
- reproduce: add stage mechanism to run reproduce again by skipping stages that
 succeeded
- add file mappings.mk for the local dependencies of mappings.v

## 1.0.0 (2024-11-03)

First release.

<!--------------------------------------------------------------------------->
# Previous changes in [coq-hol-light-real-with-N](https://github.com/Deducteam/coq-hol-light-real-with-N)

AUTHORS:
- [Frédéric Blanqui](https://blanqui.gitlabpages.inria.fr/) for the alignment o
f unary and binary natural numbers, and real numbers
- [Anthony Bordg](https://sites.google.com/site/anthonybordg/) for the alignmen
t of the types sum, list, option
- Amal Makni for the alignment of subtypes, quotient types and part of the type
 of real numbers
- [Théo Winterhalter](https://theowinterhalter.github.io/) for the tactic align
_ε
- [Jérémy Dubut](https://jeremydubut.com/) for the alignment of EVEN, ODD, WF
- Antoine Gontard for the tactics to automatically align inductive types and re
cursive functions

## 2.0.0 (2025-07-11)

- add tactics to automatically prove the correctness of alignments of inductive types or recursive functions

## 1.2.0 (2025-03-13)

- update mappings following https://github.com/Deducteam/hol2dk/pull/176
- move definition of Type' in type.v
- remove NUMERAL in terms.v and theorems.v

## 1.1.0 (2025-02-19)

- add tactics to handle functional extensionality and ε (Théo Winterhalter)
- add mappings for EVEN, ODD, WF (Jérémy Dubut)
- add mapping for FACT
- reformat proofs using bullets (Jérémy Dubut)

## 1.0.0 (2025-01-20)

First release.

<!--------------------------------------------------------------------------->
# Previous changes in [coq-hol-light](https://github.com/Deducteam/coq-hol-light)

AUTHORS:
- [Frédéric Blanqui](https://blanqui.gitlabpages.inria.fr/)
- [Théo Winterhalter](https://theowinterhalter.github.io/) for the alignment of
 various functions and predicates on integers
- [Alessio Coltellacci](https://github.com/notbad4u) for the alignment of lcm

## 3.1.0 (2025-03-13)

- add mappings for various integer functions and predicates (Théo Winterhalter)
- add mapping for int_lcm (Alessio Coltellacci and Théo Winterhalter)

## 3.0.0 (2025-01-21)

- add HOL-Light library Multivariate/make_complex.ml (~17,500 theorems)
- rename HOLLight.v into With_N.v
- use coq-hol-light-real-with-N

## 2.0.0 (2024-12-17)

All HOL-Light base library lib_hol.ml with alignement of real numbers.

## 1.0.0 (2024-02-24)

HOL-Light base library up to lists.ml.

## 0.0.0 (2023-11-06)

HOL-Light base library up to arith.ml.
