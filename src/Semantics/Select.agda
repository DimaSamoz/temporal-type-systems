
-- Semantic lemmas related to the select operator
module Semantics.Select where

open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Types

open import Semantics.Types
open import Semantics.Context

open import CategoryTheory.Instances.Reactive
open import TemporalOps.Diamond using (◇-select ; ◇_)

open import Data.Product
open import Data.Sum


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
