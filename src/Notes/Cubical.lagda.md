```
module Notes.Cubical where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Cubical.Core.Primitives
```

CTT provides a formalism for HoTT with computational univalence and paths.

In HoTT we have the univalence axiom. However that univalence axiom
doesn't have computational content. Higher inductive types are also
added axiomatically without reduction rules.

CTT 'constructivizes' HoTT making the following changes:
- Replaces identity types with a geometric notion of paths along an
  interval.
- Internalizes homotopies as actual terms.

CTT provides a model for HoTT that is computational. 

'diagonal operation' - for higher inductive types.

Agda uses CCHM type theory [@cchm2016].

CCHM type theory refers to the variant of cubical type theory
introduced by Cyril Cohen, Thierry Coquand, Simon Huber, and Anders
Mörtberg. This system is often called the CCHM cubical type theory and
is notable for providing a constructive interpretation of the
univalence axiom—a central feature of homotopy type theory—using a
geometric and computational approach based on cubical sets.

## Path types

There is a single inteval 'pseudotype', `𝕀`, which acts like a type
but can't be considered a full type. `𝕀` is a free de Morgan algebra.

Path abstraction defines the following notions:

Abstraction: For $i : 𝕀; t, u : A$,

```agda-sketch
⟨ i ⟩ t : Path A t u
```

Substitutions: $(i/r)$. $i0$ and $i1$ are special endpoint values.

There is an additional algebra called the 'face lattice'. This is a restirction of the cubical space to just (hyper) faces/edges/points. By substituting an endpoint to an axis variable.

These can be combined into sets of faces/edges. Every path in cubical Agda originates from some face algebra.

## Comp operator

The comp operator operates in a fixed h-level and is written:

```agda-sketch
compⁱ A \left[ φ ↦ u \right] a₀
```

Here $u$ is a system of extents given by a face algebra.

"The composition operation expresses that being extensible is preserved along paths: if
a partial path is extensible at 0, then it is extensible at 1." [@cchm2016]



```bibtex
@article{cchm2016,
  title={Cubical type theory: a constructive interpretation of the univalence axiom},
  author={Cohen, Cyril and Coquand, Thierry and Huber, Simon and M{\"o}rtberg, Anders},
  journal={arXiv preprint arXiv:1611.02108},
  year={2016},
  url={https://arxiv.org/pdf/1611.02108}
}
```
