
-- Exponentials and closed categories
module CategoryTheory.BCCCs.Closed where
open import CategoryTheory.Categories
open import CategoryTheory.BCCCs.Cartesian


module _ {n} {ℂ : Category n} (Cℂ : Cartesian ℂ) where

    open Category ℂ
    open Cartesian Cℂ

    -- Exponential from two objects
    record Exponential (A B : obj) : Set (lsuc n) where
        field
            -- | Data
            -- Exponential object
            A⇒B : obj
            -- Evaluation map
            eval : A⇒B ⊗ A ~> B
            -- Canonical transposition morphism (currying)
            Λ : ∀{E} -> (E ⊗ A ~> B) -> (E ~> A⇒B)

            -- | Laws
            Λ-comm : ∀{E} -> {e : E ⊗ A ~> B}
                  -> eval ∘ (Λ e * id) ≈ e
            Λ-unique : ∀{E} -> {e : E ⊗ A ~> B} {m : E ~> A⇒B}
                  -> eval ∘ (m * id) ≈ e -> Λ e ≈ m

-- Type class for closed categories
-- definition using exponentials
record Closed {n} {ℂ : Category n} (Cℂ : Cartesian ℂ) : Set (lsuc n) where
    open Category ℂ
    open Exponential
    field
        -- Exponential object for each pair of objects
        exp : ∀(A B : obj) -> Exponential Cℂ A B

    -- Shorthand for exponential object
    infixr 70 _⇒_
    _⇒_ : (A B : obj) -> obj
    _⇒_ A B = A⇒B (exp A B)
