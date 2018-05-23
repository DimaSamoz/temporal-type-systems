
module CategoryTheory.Linear where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.BCCCs
open import CategoryTheory.Monad
open import CategoryTheory.Instances.Kleisli

module L {n} {ℂ : Category n} (ℂ-BCCC : BicartesianClosed ℂ) (Mo : Monad ℂ) where
    open Category ℂ
    open BicartesianClosed ℂ-BCCC
    open Monad Mo
    open Functor T renaming (omap to M ; fmap to M-f)
    Kl : Category n
    Kl = Kleisli ℂ Mo

    -- Linear product of two objects
    _⊛_ : (A B : obj) -> obj
    A ⊛ B = (A ⊗ M B) ⊕ (M A ⊗ B) ⊕ (A ⊗ B)

    -- First projection from linear product
    *π₁ : ∀{A B} -> A ⊛ B ~> M A
    *π₁ {A}{B} = [ η.at A ∘ π₁ ⁏ π₁ ⁏ η.at A ∘ π₁ ]

    -- Second projection from linear product
    *π₂ : ∀{A B} -> A ⊛ B ~> M B
    *π₂ {A}{B} = [ π₂ ⁏ η.at B ∘ π₂ ⁏ η.at B ∘ π₂ ]


    -- Type class for linear products of type A ⊛ B. Need to provide
    -- linear product of morphisms and product laws in order to establish
    -- that the linear product is a product in the Kleisli category of the monad.
    record LinearProduct (A B : obj) : Set (lsuc n) where
        infix 10 ⟪_,_⟫
        field
            -- | Data
            -- Linear product
            ⟪_,_⟫ : ∀{L} -> (L ~> M A) -> (L ~> M B) -> (L ~> M (A ⊛ B))

            -- | Laws
            *π₁-comm : ∀{L} -> {l₁ : L ~> M A} {l₂ : L ~> M B}
                   -> (μ.at A ∘ M-f *π₁) ∘ ⟪ l₁ , l₂ ⟫ ≈ l₁
            *π₂-comm : ∀{L} -> {l₁ : L ~> M A} {l₂ : L ~> M B}
                   -> (μ.at B ∘ M-f *π₂) ∘ ⟪ l₁ , l₂ ⟫ ≈ l₂
            ⊛-unique : ∀{P} {p₁ : P ~> M A} {p₂ : P ~> M B} {m : P ~> M A⊕B}
                    -> (μ.at A ∘ M-f *π₁) ∘ m ≈ p₁ -> (μ.at B ∘ M-f *π₂) ∘ m ≈ p₂
                    -> ⟪ p₁ , p₂ ⟫ ≈ m

        Kl-⊛ : Product Kl A B
        Kl-⊛ = record
            { A⊗B = A ⊛ B
            ; π₁ = *π₁
            ; π₂ = *π₂
            ; ⟨_,_⟩ = ⟪_,_⟫
            ; π₁-comm = *π₁-comm
            ; π₂-comm = *π₂-comm
            ; ⊗-unique = ⊛-unique
            }

-- Type class for linear categories
record Linear {n} {ℂ : Category n}
              (ℂ-BCCC : BicartesianClosed ℂ) (Mo : Monad ℂ) : Set (lsuc n) where
    open Category ℂ
    open L ℂ-BCCC Mo

    field
        linprod : ∀(A B : obj) -> LinearProduct A B
