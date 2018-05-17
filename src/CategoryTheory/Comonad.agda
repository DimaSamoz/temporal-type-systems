
{- Type class for comonads. -}
module CategoryTheory.Comonad where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans

-- A comonad on a category
record Comonad {n} (ℂ : Category n) : Set (lsuc n) where
    open Category ℂ
    field
        -- Underlying endofunctor
        W : Endofunctor ℂ
    open Functor W

    field
        -- || Definitions
        -- Counit / extract
        ε : W ⟹ I
        -- Comultiplication / duplicate
        δ : W ⟹ (W ²)

    module ε = _⟹_ ε
    module δ = _⟹_ δ
    field
        -- || Laws
        -- Duplication is cancelled by extraction on both sides (counit)
        ε-unit1 : ∀ {A : obj} -> (ε.at (omap A)) ∘ (δ.at A) ≈ id
        ε-unit2 : ∀ {A : obj} -> (fmap (ε.at A)) ∘ (δ.at A) ≈ id

        -- Duplication can be performed on both sides (coassociativity)
        δ-assoc : ∀ {A : obj} -> (δ.at (omap A)) ∘ (δ.at A)
                               ≈ (fmap (δ.at A)) ∘ (δ.at A)
