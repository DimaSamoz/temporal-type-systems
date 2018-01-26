
{- Type class for natural transformations. -}
module CategoryTheory.NatTrans where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open CategoryTheory.Categories.Category using (obj)
open import Relation.Binary.PropositionalEquality

infixr 25 _⟹_

-- Natural transformation between two functors
record _⟹_ {n} {ℂ 𝔻 : Category n} (F : Functor ℂ 𝔻) (G : Functor ℂ 𝔻) : Set (lsuc n) where
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

-- Natural isomorphism between two functors
record _⟺_  {n} {ℂ 𝔻 : Category n} (F : Functor ℂ 𝔻) (G : Functor ℂ 𝔻) : Set (lsuc n) where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    private module F = Functor F
    private module G = Functor G
    field
        -- || Definitions
        -- NT from F to G
        to   : F ⟹ G
        -- NT from G to F
        from : G ⟹ F

    private module to   = _⟹_ to
    private module from = _⟹_ from

    field
        -- || Isomorphism laws
        iso1 : ∀{A : obj ℂ} -> (from.at A) 𝔻.∘ (to.at A)   𝔻.≈ 𝔻.id
        iso2 : ∀{A : obj ℂ} -> (to.at A)   𝔻.∘ (from.at A) 𝔻.≈ 𝔻.id
