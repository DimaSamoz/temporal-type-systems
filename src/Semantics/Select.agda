
-- Semantic lemmas related to the select operator
module Semantics.Select where

open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Types

open import Semantics.Types
open import Semantics.Context

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive
open Category ℝeactive
open import TemporalOps.Diamond using (◇-select ; ◇_)

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl)


-- Handle all three possibilities of event ordering by selecting
-- the correct continuation
⟦select⟧ : ∀ Γ A B C -> (n : ℕ) -> (⟦ Γ ⟧ₓ n)
          -> (⟦C₁⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ◇ ⟦ B ⟧ₜ ⊗ ⟦ A ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ)
          -> (⟦C₂⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ◇ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ)
          -> (⟦C₃⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ)
          -> (  ⟦ A ⟧ₜ ⊗ ◇ ⟦ B ⟧ₜ)
           ⊕ (◇ ⟦ A ⟧ₜ ⊗   ⟦ B ⟧ₜ)
           ⊕ (  ⟦ A ⟧ₜ ⊗   ⟦ B ⟧ₜ) ⇴ ◇ ⟦ C ⟧ₜ
⟦select⟧ Γ _ _ _ n env ⟦C₁⟧ _ _ k (inj₁ (inj₁ (⟦A⟧ , ⟦◇B⟧))) = ⟦C₁⟧ k ((⟦ Γ ⟧ˢₓ n env k , ⟦◇B⟧) , ⟦A⟧)
⟦select⟧ Γ _ _ _ n env _ ⟦C₂⟧ _ k (inj₁ (inj₂ (⟦◇A⟧ , ⟦B⟧))) = ⟦C₂⟧ k ((⟦ Γ ⟧ˢₓ n env k , ⟦◇A⟧) , ⟦B⟧)
⟦select⟧ Γ _ _ _ n env _ _ ⟦C₃⟧ k (inj₂ (⟦A⟧ , ⟦B⟧))         = ⟦C₃⟧ k ((⟦ Γ ⟧ˢₓ n env k , ⟦A⟧)  , ⟦B⟧)

open ≡.≡-Reasoning

-- The denotation of select and OPEs can be commuted
⟦select⟧-⟦⟧⊆-comm : ∀ {Γ Δ C} A B
          -> ∀(n k : ℕ) -> (c : (⟦ A ⟧ₜ ⊗ ◇ ⟦ B ⟧ₜ ⊕ ◇ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⊕ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ) k)
          -> (s : Γ ⊆ Δ) -> (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
          -> {⟦C₁⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ◇ ⟦ B ⟧ₜ ⊗ ⟦ A ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
          -> {⟦C₂⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ◇ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
          -> {⟦C₃⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
          -> ⟦select⟧ Δ A B C n ⟦Δ⟧
                (⟦C₁⟧ ∘ ⟦ keep {A = A now} (keep {A = (Event B) now} (ˢ-⊆-monotone s)) ⟧⊆)
                (⟦C₂⟧ ∘ ⟦ keep {A = B now} (keep {A = (Event A) now} (ˢ-⊆-monotone s)) ⟧⊆)
                (⟦C₃⟧ ∘ ⟦ keep {A = B now} (keep {A = A now} (ˢ-⊆-monotone s)) ⟧⊆) k c
           ≡ ⟦select⟧ Γ A B C n (⟦ s ⟧⊆ n ⟦Δ⟧) ⟦C₁⟧ ⟦C₂⟧ ⟦C₃⟧ k c
⟦select⟧-⟦⟧⊆-comm _ _ n k (inj₁ (inj₁ (⟦A⟧ , ⟦◇B⟧))) s ⟦Δ⟧ rewrite ⟦⟧ˢₓ-⟦⟧⊆-comm n k s ⟦Δ⟧ = refl
⟦select⟧-⟦⟧⊆-comm _ _ n k (inj₁ (inj₂ (⟦◇A⟧ , ⟦B⟧))) s ⟦Δ⟧ rewrite ⟦⟧ˢₓ-⟦⟧⊆-comm n k s ⟦Δ⟧ = refl
⟦select⟧-⟦⟧⊆-comm _ _ n k (inj₂ (⟦A⟧ , ⟦B⟧)) s ⟦Δ⟧ rewrite ⟦⟧ˢₓ-⟦⟧⊆-comm n k s ⟦Δ⟧ = refl
