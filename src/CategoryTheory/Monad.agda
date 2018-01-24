
{- Type class for monads. -}
module CategoryTheory.Monad where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open CategoryTheory.Categories.Category using (obj)

-- A monad on a category
record Monad (ℂ : Category) : Set₁ where
    private module ℂ = Category ℂ
    field
        -- Underlying endofunctor
        T : Endofunctor ℂ
    private module T = Functor T

    field
        -- || Definitions
        -- Unit / return
        η : I ⟹ T
        -- Multiplication / join
        μ : (T ²) ⟹ T

    private module η = _⟹_ η
    private module μ = _⟹_ μ
    field
        -- || Laws
        -- Unit on both sides is cancelled by multiplication (unit)
        η-unit1 : ∀ {A : obj ℂ} -> (μ.at A) ℂ.∘ (η.at (T.omap A)) ℂ.≈ ℂ.id
        η-unit2 : ∀ {A : obj ℂ} -> (μ.at A) ℂ.∘ (T.fmap (η.at A)) ℂ.≈ ℂ.id

        -- Multiplication can be performed on both sides (associativity)
        μ-assoc : ∀ {A : obj ℂ} -> (μ.at A) ℂ.∘ (μ.at (T.omap A))
                               ℂ.≈ (μ.at A) ℂ.∘ (T.fmap (μ.at A))
