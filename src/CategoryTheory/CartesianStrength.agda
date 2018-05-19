
module CategoryTheory.CartesianStrength where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.BCCCs.Cartesian
open import CategoryTheory.Monad
open import CategoryTheory.Comonad

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

    -- Canonical distribution morphism
    m⁻¹ : ∀(A B : ℂ.obj) -> F (A ⊗ᶜ B) ~> F A ⊗ᵈ F B
    m⁻¹ A B = Cartesian.⟨_,_⟩ 𝔻-cart (fmap (Cartesian.π₁ ℂ-cart))
                                     (fmap (Cartesian.π₂ ℂ-cart))

-- Type class for Cartesian comonads
record CartesianComonad {n}
        {ℂ : Category n} (C : Comonad ℂ)
        (ℂ-cart : Cartesian ℂ) : Set (lsuc n) where
    open Category ℂ
    open Comonad C
    open Functor W renaming (omap to F)
    open Cartesian ℂ-cart

    field
        -- Cartesian comonads are Cartesian functors
        cart-fun : CartesianFunctor W ℂ-cart ℂ-cart
    open CartesianFunctor cart-fun
    field
        -- | Laws
        u-ε : u ∘ ε.at ⊤ ≈ id
        u-δ : δ.at ⊤ ∘ u ≈ fmap u ∘ u
        m-ε : ∀{A B : obj} -> ε.at (A ⊗ B) ∘ m A B ≈ ε.at A * ε.at B
        m-δ : ∀{A B : obj} -> fmap (m A B) ∘ m (F A) (F B) ∘ δ.at A * δ.at B
                            ≈ δ.at (A ⊗ B) ∘ m A B

record WStrongMonad {n}
        {ℂ : Category n} {Co : Comonad ℂ} (Mo : Monad ℂ)
        (ℂ-cart : Cartesian ℂ) (W-cart-com : CartesianComonad Co ℂ-cart)
        : Set (lsuc n) where
    open Category ℂ
    open Comonad Co
    open Monad Mo
    open Functor W renaming (omap to C ; fmap to C-f)
    open Functor T renaming (omap to M ; fmap to M-f)
    open Cartesian ℂ-cart
    open CartesianComonad W-cart-com
    open CartesianFunctor cart-fun

    λᶜ : ∀(A : obj) -> C ⊤ ⊗ A ~> A
    λᶜ _ = π₂

    αᶜ : ∀(A B D : obj) -> (C (A ⊗ B) ⊗ D) ~> (C A ⊗ (C B ⊗ D))
    αᶜ A B D = assoc-right ∘ m⁻¹ A B * id

    field
        -- C-tensorial strength
        st : ∀(A B : obj) -> C A ⊗ M B ~> M (C A ⊗ B)

        -- | Laws
        -- Naturality conditions
        st-nat₁ : ∀{A B D : obj} (f : A ~> B)
               -> M-f (id * f) ∘ st D A ≈ st D B ∘ id * M-f f
        st-nat₂ : ∀{A B D : obj} (f : A ~> B)
               -> M-f (C-f f * id) ∘ st A D ≈ st B D ∘ C-f f * id

        -- Strength and left unit
        st-λ : ∀{A} -> M-f (λᶜ A) ∘ st ⊤ A ≈ λᶜ (M A)
        -- Strength and associativity
        st-α : ∀{A B D} -> st A (C B ⊗ D) ∘ id * st B D ∘ αᶜ A B (M D)
                         ≈ M-f (αᶜ A B D) ∘ st (A ⊗ B) D
        -- Strength and unit
        st-η : ∀{A B} -> st A B ∘ id * η.at B ≈ η.at (C A ⊗ B)
        -- Strength and multiplication
        st-μ : ∀{A B} -> μ.at (C A ⊗ B) ∘ M-f (st A B) ∘ st A (M B)
                       ≈ st A B ∘ (id * μ.at B)
