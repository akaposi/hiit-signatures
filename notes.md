

New references:
  - For higher inductive integer example (Nicolai et al. free omega groups?)
  - Borrow new references from CQIIT paper, add also Harper-Cavallo POPL
  - Maybe reflexive graph for logrel part

Presentation:
  - we should leave syntax presentation as it is
  - Rename to alg./disp alg/morphism/section
  - 2-tiered colored syntax for signatures is also OK
  - rename things to algebras, morphisms, displayed algebras, sections
  - worked computational example?

Updates for Agda formalization and Haskell demo
  - Haskell demo: rename stuff in output
  - (extra: type equalities, logrel model)


1. Intro

  HIIT intro

  Related work

  Overview

2. Theory of signatures

  - Motivation: features, dependencies
  - External type motivation two layer. Description of target type theory
  - Theory of signatures, examples

3. General definition of induction and recursion (overview of the ADMS model using Nat)

4. Coherence, syntactic translations
  (MERGE here: syntactic translation section)

  - Open problem: interpreting an internal syntax of type theory in HoTT or UIP-free
    TT.

  - Preterms: irrelevant conversion proofs
     - interpret normal forms? Öhman, Abel, Vezzosi: decidable conversion without UIP,
	   but still far from solution
     - View syntax as initial structured category (well-typed syntax).
	   Problem: set-truncation. Untruncated syntax is not a set, has undecidable conversion.
	   Higher syntax and models of type theory.

  - Solution: instead of interpreting the syntax into an UIP-free metatheory, we translate
    from the syntax to the syntax of an UIP-free theory.
	- etc.

5. Algebras

6. From logical relations to morphisms

    Logical relation model: present only part (U, El, Pi)
      maybe present Pi without positivity restriction

    Hint: Reddy: functional logical relations are homomorphisms
      interpret U as function space

    Spos function space:
      - definition can be strictified along singleton contraction
      - This gives us the usual notion of homomorphism


7. Displayed algebras
  Logical predicates

8. Sections of displayed algebras
  Dependent homomorphisms

9. Strictness problems for id, composition

10. Formalization and implementation

11. Conclusions and further work



  <!-- Intro -->
  <!--   Motivation for HIITs -->
  <!-- 	  - HoTT motivation, TT/real/surreal/ordinal numbers for inductive-inductive -->
  <!-- 	    motivation. -->
  <!-- 	  - In this paper: signatures, algebra, displayed algebra, homomorphism, section -->
  <!-- 	                   of displayed algebra -->
  <!--       - this is enough to state notions of: induction + homotopy initiality -->
  <!-- 		- Haskell program can typecheck signatures and print out these notions -->
  <!-- 		- no category of algebras -->
  <!-- 		- no initial algebras -->


  <!-- Type constructor equalities: -->
  <!--   - extend everything with this -->
  <!-- 	- integer example: (ℤ : U, zero : El ℤ, sp : ℤ = ℤ) -->


  <!-- Formal syntax, models and coherence problems -->
  <!--   - Motivation: -->
  <!-- 	  - we want to compute notions of algebras / induction principles -->
  <!-- 	    in a setting without UIP (HoTT-compatible) setting. -->
  <!--     - we want to have feasible machine-checked formalization -->

  <!--   - Formal syntax: presyntax + relations, vs. structured categories -->
  <!-- 	  (Example: standard model of TT from CwF QIIT) -->

  <!--   - Standard model for presyntactic presentation is not controversial, -->
  <!-- 	  but it is very complicated formally (initiality conjecture for type theories). -->

  <!--   - Coherence issue arises in both categorical (CwF) and presyntactic presentation: -->
  <!-- 	  CwF:       set-truncation -->
  <!-- 	  presyntax: irrelevant derivation of conversion and typing -->

  <!--   - Models : Set-truncated CwF only has standard model with UIP -->
  <!-- 	           Untruncated CwF is not the notion of syntax we want: -->
  <!-- 			     - if we add any base type, then it is not a set, and -->
  <!-- 				   hence has undecidable equality -->

  <!--   - Syntactic models: -->
  <!-- 	  - a model in the syntax of some type theory (possibly the same -->
  <!-- 	    theory as the source). -->
  <!--     - Definitionally equal source terms must be mapped to equal target terms. -->
  <!-- 	    Equality in target syntax coincides with target definitional equality. -->
  <!-- 		Hence: we have strict models: definitionally equal terms must be mapped to -->
  <!-- 		definitionally equal terms. -->
  <!-- 		(Remark: strong equality reflection makes strictness -->
  <!-- 		issues go away, but it's of cource UA-incompatible) -->

  <!--     - Contrast metatheoretic models. Example: a model of TT where syntactic functions -->
  <!-- 	    are interpreted as metatheoretic functions. Then, if there is funext in metatheory, -->
  <!-- 		we can appeal to it when proving preservation of definitional equality. -->


  <!-- Logical relations and homomorphisms: -->
  <!--   - graph model: logrel over std model -->
  <!-- 	- Uday Reddy: homomorphism is functional logrel for groups -->
  <!-- 	- change definition of U to function space, notice that inductive function interpretation -->
  <!-- 	  has a stricter equivalent definition -->
  <!--   - (? homomorphism for non-strictly positive signatures ?) -->
  <!--   - homomorphisms (question: should we discuss transpᴹ and Jᴹ at this point, in which case we need -->
  <!-- 	  to add them to formalizations) -->

  <!-- Notion of homotopy initiality: contractible space of morphisms -->

  <!-- Displayed algebras: exactly logical predicate over std model -->


  <!-- Why not categories? -->
  <!--   - Identity, composition, etc. -->
  <!--   - Syntactic model: strict preservation of definitional equalities -->
  <!-- 	- Identity and composition are not syntactic models, they preserve definitional -->
  <!-- 	  equality only up to propositional equality in target syntax. -->
  <!--     - Example: U[] in the identity translation -->
  <!--   - "Proper" semantics in (ω,1)-categories. "Homotopy initiality ~ induction" seems to be -->
  <!-- 	  provable on the level of "wild categories", see Sojakova. -->
