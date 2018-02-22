
{- Denotational semantics of the types in the category of temporal types. -}
module Semantics.Types where

open import Syntax.Types
open import CategoryTheory.Instances.Reactive
open import TemporalOps.Box
open import TemporalOps.Diamond

-- Denotation of types
⟦_⟧ₜ : Type -> τ
⟦ Unit     ⟧ₜ = ⊤
⟦ A & B    ⟧ₜ = ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ
⟦ A + B    ⟧ₜ = ⟦ A ⟧ₜ ⊕ ⟦ B ⟧ₜ
⟦ A => B   ⟧ₜ = ⟦ A ⟧ₜ ⇒ ⟦ B ⟧ₜ
⟦ Event A  ⟧ₜ = ◇ ⟦ A ⟧ₜ
⟦ Signal A ⟧ₜ = □ ⟦ A ⟧ₜ
