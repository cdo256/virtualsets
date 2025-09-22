# Toward a Formally Verified Implementation of "Virtual Sets"

The majority of this work was carried out in a single Git repository
hosted on [GitHub](https://github.com/cdo256/virtualsets). Is is
implemented in cubical Agda using the cubical Agda standard library.
Originally I started working in the Agda standard library however it was
suggested by Thorsten that I should switch to a cubical library, to
avoid \"setoid hell\" (cf. Altenkirch 2017 , more generally, Allais et.
al 2025), suggesting 1Lab library . I moved my definitions over to 1Lab
but there were some akward definitions, which were slowing me down. Most
notably the definition of finite sets (`Fin`), which used a quotient
(truncation) type . I eventially settled on the standard cubical library
.

The work is fully reproducible for its Git repository, using Nix flakes,
and include all of depdencies all of the lemmas I have completed. It
even include the list of dependencies and python script for building the
report. The code is structured modularly and designed intentionally for
ease of further development.

The layout of the repository is as follows:

```text
 build.py.
 flake.lock.
 flake.nix.
 justfile.
 latex.
     agda.sty.
     chapters.
         conclusion.tex.
         formalization.tex.
         introduction.tex.
         lit-reivew.tex.
         prelim.tex.
     main.tex.
     preamble.tex.
     report.bib.
 libraries.
 nix.
     args.nix.
     packages.nix.
     shells.nix.
 postprocess-latex.pl.
 src.
     Compat.
         1Lab.
         1Lab.agda.
     Dissertation.
     DissertationTex.
     Notes.
     VSet.
         All.agda.
         Cat.
             Inj.agda.
             InjFun.agda.
             Trace.agda.
         Data.
             Fin.
             Fin.agda.
             HITTree.
             Inj.
             InjFun.
             Maybe.agda.
             Nat.
             Nat.agda.
             NatPlus.
             Sum.
             SumTree.
             Tree.
             VecFun.
         Function.
             Base.agda.
             Injection.agda.
             Iso.agda.
             Properties.agda.
         Path.agda.
         Prelude.agda.
         Relation.
             Definitions.agda.
             WellFounded.
         Transform.
             Inj.
                 Compose.
                 Elementary.
                 Inverse.
                 Tensor.
                 Trace.
             InjFun.
                 Compose.agda.
                 Flattern.agda.
                 Inflate.agda.
                 Pred.agda.
                 Properties.agda.
                 Sub.agda.
                 Tensor.agda.
                 Unused.agda.
 virtual-set.agda-lib.
```

There are 3 main top-level directories for different purposes:

`./latex/` defines the parts of this dissertation that are written in
_TeX_ or an ajacent language, such as _BibTeX_. These are assembled by
'./build.py' with the sections of the dissertation written in literate
Agda (with markdown), to produce the final PDF file. Everything in
`./src/Dissertation/` is converted into TeX with Pandoc, in order to
process the embedded TeX commands, then Agda type checks the file,
before adding syntax hylighting and references before inserting it into
`./latex/generated/`, where it in turn is referred to by
`./latex/chapters/formalization.tex`. This circuitous route was required
as to date, Agda does not currently have a markdown-to-latex backed.

`./nix/` together with `./flake.nix` and `./flake.lock`.

Finally all of the Agda source is contained in `./src`. Compat contains
functions that allow the use the functions of other libraries, such as
1Lab. These are not source I have developed myself, but they are
functions copied into the repo to enable use of certain functions from
other libraries. Normally libraries can't be mixed, because it can
result in mismatch of primitive definitions, meaning you have to convert
between these definitions manually every time you want to use a function
from a foreign library. `./src/Dissertation/` and
`./src/DissertationTex/` contins the files to generate the formalization
chapter.

The bulk of the source is in `./src/VSet/`:

- is a list of all files to type check to ensure the repository is
  still valid. I run this regularly to ensure I haven't broken
  anything.

- : This contains category definitions and category constructions.
  Inj.agda and InjFun.agda are the two category constructions for the
  two ways to define injective maps explored in this work.

- : This directory contains various definitions and properties of Data
  types. Most properties of data types are defined here, except the
  main development for Inj and InjFun is performed inside
  `./src/VSet/Transform`.

- define basic properties of functions and paths, for use elsewhere.

- defines basic properties of functions and paths, for use elsewhere.

- defiens transformations of injective functions, such as
  inserting/removing links up to describing a trace function. This is
  where the majority of the development is situated.
