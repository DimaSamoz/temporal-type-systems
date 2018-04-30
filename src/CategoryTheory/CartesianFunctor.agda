
module CategoryTheory.CartesianFunctor where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.BCCCs.Cartesian

-- Type class for Cartesian functors
record CartesianFunctor {n}
        {ℂ : Category n} {𝔻 : Category n} (Fn : Functor ℂ 𝔻)
        (ℂ-cart : Cartesian ℂ) (𝔻-cart : Cartesian 𝔻) : Set (lsuc n) where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    open Category 𝔻
    open Functor Fn renaming (omap to F)
    open Cartesian ℂ-cart renaming
        ( ⊤ to ⊤ᶜ ; _⊗_ to _⊗ᶜ_ ; _*_ to _*ᶜ_ ; assoc-right to αᶜ
        ; unit-left to λᶜ ; unit-right to ρᶜ)
    open Cartesian 𝔻-cart renaming
        ( ⊤ to ⊤ᵈ ; _⊗_ to _⊗ᵈ_ ; _*_ to _*ᵈ_; assoc-right to αᵈ
        ; unit-left to λᵈ ; unit-right to ρᵈ)

    field
        -- | Data
        -- F preserves terminal objects (0-ary products)
        u : ⊤ᵈ ~> F ⊤ᶜ
        -- F preserves binary products
        m : ∀(A B : ℂ.obj) -> F A ⊗ᵈ F B ~> F (A ⊗ᶜ B)

        -- | Laws
        associative : ∀{A B C : ℂ.obj} ->
              m A (B ⊗ᶜ C) ∘ (id *ᵈ m B C) ∘ αᵈ
            ≈ fmap αᶜ ∘ m (A ⊗ᶜ B) C ∘ (m A B *ᵈ id)
        unital-right : ∀{A : ℂ.obj} ->
            fmap ρᶜ ∘ m A ⊤ᶜ ∘ (id *ᵈ u) ≈ ρᵈ
        unital-left : ∀{B : ℂ.obj} ->
            fmap λᶜ ∘ m ⊤ᶜ B ∘ (u *ᵈ id) ≈ λᵈ
