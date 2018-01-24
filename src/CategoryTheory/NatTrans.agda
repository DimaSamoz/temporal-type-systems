
{- Type class for natural transformations. -}
module CategoryTheory.NatTrans where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open CategoryTheory.Categories.Category using (obj)
open import Relation.Binary.PropositionalEquality

infixr 25 _⟹_

-- Natural transformation between two functors
record _⟹_ {ℂ 𝔻 : Category} (F : Functor ℂ 𝔻) (G : Functor ℂ 𝔻) : Set₁ where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    private module F = Functor F
    private module G = Functor G
    field
        -- || Definitions
        -- One component of the natural transformations.
        at : ∀(A : obj ℂ) -> (F.omap A) 𝔻.~> (G.omap A)

        -- || Laws
        -- Naturality condition
        nat-cond : ∀{A B : obj ℂ} {f : A ℂ.~> B}
                -> (G.fmap f 𝔻.∘ at A) 𝔻.≈ (at B 𝔻.∘ F.fmap f)
                
