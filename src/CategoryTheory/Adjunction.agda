
{- Type class for adjoint functors -}
module CategoryTheory.Adjunction where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans

-- Adjunction between two functors
record _⊣_ {n} {ℂ 𝔻 : Category n} (F : Functor ℂ 𝔻) (G : Functor 𝔻 ℂ) : Set (lsuc n) where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    private module F = Functor F
    private module G = Functor G
    field
        -- || Definitions
        -- Unit
        η : I ⟹ G ◯ F
        -- Counit
        ε : F ◯ G ⟹ I

    private module η = _⟹_ η
    private module ε = _⟹_ ε

    field
        -- || Laws
        -- First triangle identity: εF ∘ Fη = ιd
        tri1 : ∀ {A : ℂ.obj} -> ε.at (F.omap A) 𝔻.∘ F.fmap (η.at A) 𝔻.≈ 𝔻.id
        -- Second triangle inequality: Gε ∘ ηG = ιd
        tri2 : ∀ {B : 𝔻.obj} -> G.fmap (ε.at B) ℂ.∘ η.at (G.omap B) ℂ.≈ ℂ.id
