
{- Type class for comonads. -}
module CategoryTheory.Comonad where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans

-- A comonad on a category
record Comonad {n} (ℂ : Category n) : Set (lsuc n) where
    private module ℂ = Category ℂ
    field
        -- Underlying endofunctor
        W : Endofunctor ℂ
    private module W = Functor W

    field
        -- || Definitions
        -- Counit / extract
        ε : W ⟹ I
        -- Comultiplication / duplicate
        δ : W ⟹ (W ²)

    private module ε = _⟹_ ε
    private module δ = _⟹_ δ
    field
        -- || Laws
        -- Duplication is cancelled by extraction on both sides (counit)
        ε-unit1 : ∀ {A : ℂ.obj} -> (ε.at (W.omap A)) ℂ.∘ (δ.at A) ℂ.≈ ℂ.id
        ε-unit2 : ∀ {A : ℂ.obj} -> (W.fmap (ε.at A)) ℂ.∘ (δ.at A) ℂ.≈ ℂ.id

        -- Duplication can be performed on both sides (coassociativity)
        δ-assoc : ∀ {A : ℂ.obj} -> (δ.at (W.omap A)) ℂ.∘ (δ.at A)
                               ℂ.≈ (W.fmap (δ.at A)) ℂ.∘ (δ.at A)
