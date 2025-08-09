```
module Notes.Loose where
```

Given the complexity, I'm not sure that defining my morphism equality
to be based on dependent paths was the best decision. It seemed
natural to pick dependent paths in cubical agda becauase they're one
of the main benefits that is given by cubical type theory, and they
are very elegant in theory. Neither library provided satisfactory
tooling to reason with dependent paths. That being said, the whole
thing would be obviated if I switched to classical agda, as `x ≡ y`
means that `a : Fin x` automatically gives that `a : Fin y` whenever
the path can be computed.
