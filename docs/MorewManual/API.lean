import VersoManual

open Verso.Genre Manual

#doc (Manual) "API index" =>
%%%
tag := "api-index"
file := "api-index"
htmlSplit := .never
%%%

The [complete API reference](api/) includes declaration types, docstrings,
search, and links to source files in the Morew repository.

- [Core](api/Morew/Core.html): optimization problems, feasible points, and global equivalence.
- [Functions](api/Morew/Fn.html): vector norms, powers, exponential functions, and matrix functions.
- [Affine maps](api/Morew/Affine.html): affine expressions on vector and matrix spaces.
- [Transformations](api/Morew/Transform.html): epigraphs, substitutions, constraint changes, and restrictions.
- [Substitution](api/Morew/Substitution.html): coordinate parameterizations and their range conditions.
- [Representations](api/Morew/Rewrite/Basic.html): graph, epigraph, hypograph, and constraint equivalences.
- [Conic programs](api/Morew/Conic/Basic.html): cone constraints, target data, and `IsConic`.
- [Smooth nonlinear programs](api/Morew/NLP/Basic.html): residuals, domains, target data, and `IsSmoothNLP`.
- [Commands](api/Morew/Elab/Reformulation/Syntax.html): reformulation syntax and selectors.

The [problem syntax](api/Morew/Syntax.html) and
[reformulation command](api/Morew/Elab/Reformulation/Command.html) are starting
points for studying parsing, elaboration, and certificate generation.

The command entry points are
[Basic](api/Morew/Reformulation/Basic.html),
[Conic](api/Morew/Reformulation/Conic.html), and
[NLP](api/Morew/Reformulation/NLP.html).
