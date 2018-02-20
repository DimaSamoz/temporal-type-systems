
{- Denotational semantics of the types in the category of temporal types. -}
module Semantics where

open import Types
open import CategoryTheory.Instances.Reactive
open import TemporalOps.Box
open import TemporalOps.Diamond

-- Denotation of types
⟦_⟧ : Type -> τ
⟦ Unit ⟧     = ⊤
⟦ A & B ⟧    = ⟦ A ⟧ ⊗ ⟦ B ⟧
⟦ A + B ⟧    = ⟦ A ⟧ ⊕ ⟦ B ⟧
⟦ A => B ⟧   = ⟦ A ⟧ ⇒ ⟦ B ⟧
⟦ Event A ⟧  = ◇ ⟦ A ⟧
⟦ Signal A ⟧ = □ ⟦ A ⟧
