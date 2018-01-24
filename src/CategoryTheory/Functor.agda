
{- Type class for functors. -}
module CategoryTheory.Functor where

open import CategoryTheory.Categories
open CategoryTheory.Categories.Category using (obj)
import Relation.Binary.PropositionalEquality as R
open import Relation.Binary

-- Functor between two categories
record Functor (ℂ : Category) (𝔻 : Category) : Set₁ where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    field
        -- || Definitions
        -- Object map
        omap : obj ℂ -> obj 𝔻
        -- Arrow map
        fmap : ∀{A B : obj ℂ} -> (A ℂ.~> B) -> (omap A 𝔻.~> omap B)

        -- || Laws
        -- Functor preseres identities
        fmap-id   : ∀{A : obj ℂ} -> fmap (ℂ.id {A}) 𝔻.≈ 𝔻.id
        -- Functor preserves composition
        fmap-∘    : ∀{A B C : obj ℂ} {g : B ℂ.~> C} {f : A ℂ.~> B}
                 -> fmap (g ℂ.∘ f) 𝔻.≈ fmap g 𝔻.∘ fmap f
        -- Congruence of equality and fmap
        fmap-cong : ∀{A B : obj ℂ} {f f′ : A ℂ.~> B}
                -> f ℂ.≈ f′ -> fmap f 𝔻.≈ fmap f′

-- Endofunctor on a category
record Endofunctor (ℂ : Category) : Set₁ where
    field
        functor : Functor ℂ ℂ
