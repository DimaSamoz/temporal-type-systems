
{- Denotational semantics of the types in the category of temporal types. -}
module Semantics where

open import Types
open import Category
open import TemporalOps

-- Denotation of types
⟦_⟧ : Type -> τ
⟦ Unit ⟧        = ⊤
⟦ A & B ⟧       = ⟦ A ⟧ ⊗ ⟦ B ⟧
⟦ A => B ⟧      = ⟦ A ⟧ ⇒ ⟦ B ⟧
⟦ Next A ⟧      = ▹ ⟦ A ⟧
⟦ Event A ⟧     = ◇ ⟦ A ⟧
⟦ Behaviour A ⟧ = □ ⟦ A ⟧
