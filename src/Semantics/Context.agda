
{- Denotational semantics of the contexts in the category of temporal types. -}
module Semantics.Context where

open import CategoryTheory.Instances.Reactive
open import TemporalOps.Box
open import TemporalOps.Diamond
open import Syntax.Context
open import Semantics.Types

open import Data.Product using (_×_)

-- Denotation of reactive contexts as a finite product of temporal types.
⟦_⟧ᵣ : Context -> τ
⟦ ∙ ⟧ᵣ = ⊤
⟦ Γ , A ⟧ᵣ = ⟦ Γ ⟧ᵣ ⊗ ⟦ A ⟧ₜ

-- Denotation of stable contexts which don't change with time.
⟦_⟧ₛ : Context -> τ
⟦ ∙ ⟧ₛ = ⊤
⟦ Δ , S ⟧ₛ = λ _ → (∀ n -> ⟦ Δ ⟧ₛ n) × (∀ n -> ⟦ S ⟧ₜ n)

-- Denotation of an environment (dual context)
⟦_⟧ₑ : Environment -> τ
⟦ Δ ⁏ Γ ⟧ₑ = ⟦ Δ ⟧ₛ ⊗ ⟦ Γ ⟧ᵣ

-- Stable contexts don't change types with time.
stable : ∀(Δ : Context){n : ℕ} -> ⟦ Δ ⟧ₛ n -> (k : ℕ) -> ⟦ Δ ⟧ₛ k
stable ∙ d k = top.tt
stable (Δ , x) d k = d
