<!--
```
module Dissertation.Intro where
```
-->

\begin{verbatim}[hide]
module DissertationTex.Intro where
\end{verbatim}


The formalization was performed in Cubical Agda. This chapter
documents the development of the formalization, building up from basic
lemmas to more complex results. It is generated from type-checked
literate Agda files, allowing formal verifications of the definitions
included.

There are three main approaches I tried:

- `SumTree`: based representations of finite sets.
- `InjFun`: Dependent sum representation of injective functions.
- `Inj`: Inductive representation of finite sets.

The tree-based representation comes from the intuition that we want to
have tensor product, which must have an *associator*, which is a
natural isomorphism with certain coherence conditions. These coherence
conditions can be thought about as rebalancing of a tree and would
become obvious if we had, say, that the semantic object of any `SumTree`
is isomorphic to that of any other `SumTree`.

It became apparent early in the project that the tree-based
representations weren't leading anywhere, so it was abandoned. You can
find it in the source code (CITE repo). It is omitted from this report
because it wasn't used to develop any significant result. 

The `InjFun` approach uses the standard definition of injective function: a
function paired with a proof of injectivity. This approach made
associativity relatively simple, but caused problems with formally
defining a trace operator. This is because there's no natural way to
talk about the individual edges of the function's graph. Additionally,
my approach of chaining injective functions preserved injectivity but
lost information about the order of the elements, which is crucial to
define the trace operator.

Finally, my last representation, `Inj`, uses an inductive definition of
injective function, which has the drawback of obscuring somewhat the
function, but has the benefit of keeping the order of elements fixed
between operations, and has a relatively intuitive representation of
the trace operator.
