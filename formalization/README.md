## Formalizations for "Signatures and Induction Principles for Higher Inductive-Inductive Types"

Usage and installation: this folder has been checked with Agda 2.5.4.1. An Agda standard library
is also required, see https://agda.readthedocs.io/en/v2.5.4.2/tools/package-system.html for how
to setup a library. We used 0.16.1 version of the stdlib, which is available from here:
https://github.com/agda/agda-stdlib/releases

There are two formalizations, a shallow and a deeper one.

- The **shallow** one can be found in [Shallow.agda](Shallow.agda). This formalisation embeds both source and target syntax in Agda shallowly.

- The **deep** one embeds the external target syntax shallowly in Agda, but
  represents the source syntax as a quotient inductive-inductive type. It has
  just transport instead of J and J-beta, because we have found it quite
  difficult to just define the substitution rule for J in the syntax (certainly
  possible though, and someone willing to expend the effort should do it at some
  point). The definition of the source syntax is in
  [DeepSourceSyntax.agda](DeepSourceSyntax.agda), simply as a number of
  postulated constants. We can give a _model_ of the syntax by creating a file
  which contains names with the same types as in the syntax, but with every name
  defined instead of postulated (i.e. we give an algebra). Then, we could
  postulate a morphism from the syntax to the model, consisting of all recursors
  and beta-rules, and use Agda REWRITE pragmas to get some computational
  behavior. In the current formalization, we only give the A, D, M and S
  translations in a single model in [DeepADMS.agda](DeepADMS.agda), so we don't
  need to postulate recursion. In Agda, such postulated recursion for intrinsic
  TT-in-TT is not particularly useful for doing small example
  computations. That's because even the simplest examples (you can find some in
  [DeepCodeExamples.agda](DeepCodeExamples.agda)) contain transports over
  equality constructors, but Agda computation always gets stuck on these, and
  it's not feasible to get around this with more rewrite rules. Such computation
  would require something an type theory with computing transports, like
  cubical or observational type theory.
