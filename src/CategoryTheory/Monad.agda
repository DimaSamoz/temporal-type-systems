
{- Type class for monads. -}
module CategoryTheory.Monad where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans

-- A monad on a category
record Monad {n} (ℂ : Category n) : Set (lsuc n) where
    open Category ℂ
    field
        -- Underlying endofunctor
        T : Endofunctor ℂ
    open Functor T

    field
        -- || Definitions
        -- Unit / return
        η : I ⟹ T
        -- Multiplication / join
        μ : (T ²) ⟹ T

    module η = _⟹_ η
    module μ = _⟹_ μ
    field
        -- || Laws
        -- Unit on both sides is cancelled by multiplication (unit)
        η-unit1 : ∀ {A : obj} -> (μ.at A) ∘ (η.at (omap A)) ≈ id
        η-unit2 : ∀ {A : obj} -> (μ.at A) ∘ (fmap (η.at A)) ≈ id

        -- Multiplication can be performed on both sides (associativity)
        μ-assoc : ∀ {A : obj} -> (μ.at A) ∘ (μ.at (omap A))
                               ≈ (μ.at A) ∘ (fmap (μ.at A))
