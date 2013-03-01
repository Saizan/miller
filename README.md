Higher-Order Pattern Unification in Agda
========================================

Higher-order unification problems can have multiple incompatible solutions, a challenge for many applications which can't afford to enumerate nor to guess, like type inference. A good strategy is instead to defer any decision except for the cases that fall into the pattern fragment, a subset which guarantees unique solutions.

This repo provides a formalization in Agda of higher-order pattern unification as defined by Miller in ["A Logic Programming Language with Lambda-Abstraction, Function Variables, and Simple Unification"](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.54.8958).

The code has been tested with [Agda-2.3.2](http://hackage.haskell.org/package/Agda-2.3.2) using [The Agda standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary), if reloading you get an error related to "refl\`" you need to invalidate the interface file for `Support.Equality' because of [this bug](http://code.google.com/p/agda/issues/detail?id=756) with pattern synonyms.

The presentation is greatly influenced both by ["Higher-Order Dynamic Pattern Unification for Dependent Types and Records"](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.190.4789) and ["First-Order Unification by Structural Recursion"](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.1516) but neither are required to follow the work.

["A tutorial implementation of dynamic pattern unification"](https://personal.cis.strath.ac.uk/adam.gundry/pattern-unify/) using Haskell and tackling a much more general version of the problem is a great introduction to the field.


The key to read the present work is to identify argument lists satisfying the pattern condition with injective renamings, this point of view and the richly typed structures make it very natural to apply concepts from category theory to organize the algorithm and its proof of correctness.

### Overview of the modules
<pre>
- Definitions and Theorems from Category Theory.
 Category - monos, equalizers, pullbacks

- Variable Names as Typed de Bruijn Indexes.
 Vars            - `Γ ∋ τ'
   Vars.MatchTwo - matching against two names in one go
   Vars.SumIso   - `(Γ ++ Δ) ∋ τ' ≈ `Γ ∋ τ ⊎ Δ ∋ τ'

- Injective Renamings as a first-order datatype.
 Injections 
   Injections.Type - `Inj Γ Δ' ≈ injective `∀ τ → Γ ∋ τ → Δ ∋ τ'
   Injections.Sum  - `Inj Γ (Γ ++ Δ)' and `Inj Δ (Γ ++ Δ)'  

- Meta-Renamings send meta-vars to meta-vars applied to an injective renaming.
 MetaRens - MetaRen Γ Δ 

- Lambda Calculus Terms with and without the Pattern condition. 
 Syntax
   Syntax.Type             - `Tm< pat? > Σ Γ Δ τ', `ren' applies renamings `Inj Δ₀ Δ₁`
   Syntax.NbE              - Normalization by Evaluation
     Syntax.NbE.Properties
   Syntax.Sub              - `sub' applies meta-substitutions `Sub< pat? > Σ Γ₀ Γ₁`
   Syntax.Equality         - structural term equality, useful for recursing over its proofs
   Syntax.RenOrn           - `i ⁻¹ t' ≈ `∃ λ s → ren i s ≡ t' as an inductive type
   Syntax.OneHoleContext   - `wrap C t` plugs the term t into the hole of the context C 
   Syntax.No-Cycle         - `¬ ren i t ≡ wrap (d ∷ ds) (ren j t)' i.e. you can't go down 
                              a non-empty context and find the same term you started with

- Higher-Order Pattern Unification by Structural Recursion (well, almost).
 Unification                            - `Unify : (s t : Tm Sg G D T) → ∃σ-pat Max (Unifies s t) ⊎ ¬ ∃σ Unifies s t`
   Unification.Specification            - `Max (Unifies s t) σ` ≈ σ is the most general unifier of s and t
     Unification.Specification.Decr-Sub - `DSub Σ Γ Δ' ≈ substitutions decreasing the size of the context, or isomorphisms
   Unification.Injections               - equalizers and pullbacks
   Unification.MetaRens                 - coproducts, coequalizers and pushouts
   Unification.Pruning                  - solving for `ρ` in `ren i z ≡ sub ρ t`
     Unification.Pruning.Epi-Decr       - epic `MetaRen's, like `ρ' above, won't enlarge the context
   Unification.Inversion                - solving for `z` in `ren i z ≡ sub ρ t`
   Unification.OccursCheck              - checking whether a meta-var occurs in a term

- Wrappers around the Agda Standard Library.
 Support.Product
 Support.List
 Support.Equality
 Support.EqReasoning
</pre>
