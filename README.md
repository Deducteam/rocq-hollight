HOL-Light libraries in Rocq
---------------------------

This [Rocq](https://coq.inria.fr/) library contains an automatic translation of the [HOL-Light](https://github.com/jrh13/hol-light) libraries [Multivariate/make_complex.ml](https://github.com/jrh13/hol-light/blob/master/Multivariate/make_complex.ml) and [Logic/make.ml](https://github.com/jrh13/hol-light/blob/master/Logic/make.ml) with various HOL-Light types and functions [mapped](https://github.com/Deducteam/rocq-hollight/blob/main/Multivariate/mappings.lp) to the corresponding types and functions of the Rocq standard or mathcomp library so that, for instance, a HOL-Light theorem on HOL-Light real numbers is translated to a Rocq theorem on Rocq real numbers. The provided theorems can therefore be readily used within other Rocq developments based on the Rocq mathcomp library. More types and functions need to be aligned though (see below how to contribute). The translation has been done using [hol2dk](https://github.com/Deducteam/hol2dk) to extract and translate HOL-Light proofs to Lambdapi files, and [lambdapi](https://github.com/Deducteam/lambdapi) to translate Lambdapi files to Rocq files.

It contains more than 20,000 theorems on arithmetic, wellfounded relations,
lists, real numbers, integers, basic set theory, permutations, group
theory, matroids, metric spaces, homology, vectors, determinants,
topology, convex sets and functions, paths, polytopes, Brouwer degree,
derivatives, Clifford algebra, integration, measure theory, complex
numbers and analysis, transcendental numbers, real analysis, complex
line integrals, etc. See HOL-Light files for more details.

**Reproducibility**

The translated theorems are provided as axioms in order to have a fast Require because the proofs currently extracted from HOL-Light are very big (91 Gb) and not very informative for they are low level (the translation is done at the kernel level, not at the source level). If you are skeptical, you can however generate and check them again by using the script [reproduce](https://github.com/Deducteam/rocq-hollight/blob/main/reproduce).  
This script:
- sets up a local opam switch with all the dependencies (which takes more than 30 minutes, and even more depending on computer specs)
- generates the translated proofs and theorems (which, depending on the choice of library to generate proofs for, takes between 5 minutes and more than an hour with 32 processors Intel Core i9-13950HX and 128 Gb RAM)
- checks the proofs (which, depending on the choice of library, takes between 10 minutes and over 50 hours with 32 processors Intel Core i9-13950HX and 128 Gb RAM).  

If everything works well, the proofs will be in the directory `tmp/output`.  
It is possible to execute only parts of it, more details are displayed when running the script with no argument:
```
./reproduce
```
**Definition alignments**

The types and functions currently [aligned](https://github.com/Deducteam/rocq-hollight/blob/main/Multivariate/mappings.lp) are:
- types: unit, prod, list, option, sum, ascii, N, R, Z
- functions on N: pred, add, mul, pow, le, lt, ge, gt, max, min, sub, div, modulo, even, odd, factorial
- functions on Z: IZR, le, lt, ge, gt, opp, add, sub, mul, abs, sgn, max, min, pow, div, rem, divide, coprime, gcd, lcm
- functions on list: app, rev, map, removelast, In, hd, tl
- functions on R: Rle, Rplus, Rmult, Rinv, Ropp, Rabs, Rdiv, Rminus, Rge, Rgt, Rlt, Rmax, Rmin, IZR, Rsgn, Rmod_eq, Rpow

Your help is welcome to align more functions!

**How to contribute?**

The following instructions are for Multivariate translation/subfolder, but can be transposed for other subfolders.

You can easily contribute by proving the correctness of more mappings in Rocq:

- Look in [Multivariate/terms.v](https://github.com/Deducteam/rocq-hollight/blob/main/Multivariate/terms.v) for the definition of a function symbol, say f, that you want to replace; note that it is followed by a lemma f_DEF stating what f is equal to.

- Copy and paste in [Multivariate/mappings.v](https://github.com/Deducteam/rocq-hollight/blob/main/Multivariate/mappings.v) the lemma f_DEF, and try to prove it if f is replaced by your own function.
  + If the function comes from a file outside the Multivariate library (e.g. in one of the files from the base HOL-Light library or from HOL-Light's Library/analysis.ml file), you could also try to put the lemma in an earlier file (e.g. [HOL/mappings.v](https://github.com/Deducteam/rocq-hollight/blob/main/HOL/mappings.v) or [Library/analysis.v](https://github.com/Deducteam/rocq-hollight/blob/main/Library/analysis.v))
  + A wide set of helper tactics is available in [init.v](https://github.com/Deducteam/rocq-hollight/blob/main/init.v#L478) that are made for working with HOL-Light functions and could be worth looking up.

- Create a [pull request](https://github.com/Deducteam/coq-hol-light/pulls).

You can also propose to change the mapping of some type in one of the mappings files. Every HOL-Light type `A` is axiomatized as being isomorphic to the subset of elements `x` of some already defined type `B` that satisfies some property `p:B->Prop`. `A` can always be mapped to the Rocq type `{x:B|p(x)}` (see [init.v](https://github.com/Deducteam/rocq-hollight/blob/main/init.v#L306)) but it is possible to map it to some more convenient type `A'` by defining two functions:

- `mk:B->A'`

- `dest:A'->B`

and proving two lemmas:

- `mk_dest x: mk (dest x) = x`

- `dest_mk x: P x = (dest (mk x) = x)`

showing that `A'` is isomorphic to `{x:B|p(x)}`.

**Axioms used**

As HOL-Light is based on classical higher-order logic with choice, this library uses the following standard set of axioms in Rocq:

```
Axiom constructive_indefinite_description : forall (A : Type) (P : A->Prop), (exists x, P x) -> { x : A | P x }.
Axiom fun_ext : forall {A B : Type} {f g : A -> B}, (forall x, (f x) = (g x)) -> f = g.
Axiom prop_ext : forall {P Q : Prop}, (P -> Q) -> (Q -> P) -> P = Q.
```
They allow deriving the following properties which are often used as axioms as well:

```
Lemma classic : forall P:Prop, P \/ ~ P.
Lemma Prop_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
```

**Installation using [opam](https://opam.ocaml.org/)**

Dependencies: [rocq-equations](https://github.com/rocq-prover/equations), [rocq-mathcomp-analysis-stdlib](https://github.com/math-comp/analysis/tree/master/reals_stdlib), [coq-mathcomp-zify](https://github.com/math-comp/mczify), [coq-fourcolor-reals](https://github.com/coq-community/fourcolor)

For now, the package can be installed by cloning the repository, as such:

```
git clone https://github.com/Deducteam/rocq-hollight.git
cd rocq-hollight
opam install .
```

**Usage in a Rocq file**

```
Require Import HOLLight.Multivariate.theorems.
Check thm_DIV_DIV.
```

**Bibliography**

- [Translating HOL-Light proofs to Coq](https://doi.org/10.29007/6k4x), Frédéric Blanqui, 25th International Conference on Logic for Programming, Artificial Intelligence and Reasoning (LPAR), 2024.
- [Aligning HOL-Light and Rocq libraries formally](https://files.inria.fr/blanqui/align.pdf), Frédéric Blanqui and Antoine Gontard, to be published in the 27th International Conference on Logic for Programming, Artificial Intelligence and Reasoning (LPAR), 2026.
