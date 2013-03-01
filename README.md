### Modules
<pre>
- Definitions and Theorems from Category Theory  
 Category - monos, equalizers, pullbacks

- Variable Names as Typed de Bruijn Indexes
 Vars            - `Γ ∋ τ'
   Vars.MatchTwo - matching against two names in one go
   Vars.SumIso   - `(Γ ++ Δ) ∋ τ' ≈ `Γ ∋ τ ⊎ Δ ∋ τ'

- Injective Renamings as a first-order datatype
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

- Wrappers around the Agda Standard Library
 Support.Product
 Support.List
 Support.Equality
 Support.EqReasoning
</pre>