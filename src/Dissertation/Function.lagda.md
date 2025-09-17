<!--
```
module Dissertation.Function where

open import Cubical.Core.Primitives
open import Cubical.Data.Empty
open import Cubical.Data.Equality.Base using (id)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import VSet.Function.Iso using (_≅_; linv; rinv)
open import VSet.Function.Injection
open import VSet.Prelude
open import VSet.Data.Sum.Properties

private
  variable
    a b c d : Level
    A : Type a
    B : Type b
    C : Type c
    D : Type d
```
-->

\begin{verbatim}[hide]
module DissertationTex.Function where

open import Cubical.Core.Primitives
open import Cubical.Data.Empty
open import Cubical.Data.Equality.Base using (id)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import VSet.Function.Iso using (_≅_; linv; rinv)
open import VSet.Function.Injection
open import VSet.Prelude
open import VSet.Data.Sum.Properties

private
  variable
    a b c d : Level
    A : Type a
    B : Type b
    C : Type c
    D : Type d
\end{verbatim}

# Function Definitions for `InjFun`

To define the category of injective functions, we must 

