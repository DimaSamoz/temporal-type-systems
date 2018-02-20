
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
            ƛ : ∀{E} -> (E ⊗ A ~> B) -> (E ~> A⇒B)

            -- | Laws
            comm-ƛ : ∀{E} -> {e : E ⊗ A ~> B}
                  -> eval ∘ (ƛ e * id) ≈ e
            unique : ∀{E} -> {e : E ⊗ A ~> B} {m : E ~> A⇒B}
                  -> eval ∘ (m * id) ≈ e -> ƛ e ≈ m

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

𝕊et-Closed : Closed (𝕊et-Cartesian)
𝕊et-Closed = record
    { exp = λ A B → record
        { A⇒B = A -> B
        ; eval = λ fa → proj₁ fa (proj₂ fa)
        ; ƛ = λ f a b → f (a , b)
        ; comm-ƛ = refl
        ; unique = λ pr → λ {a} ->  unique-𝕊et (ext λ x → pr {x})
        }
    }
    where
    open Cartesian
    open Category 𝕊et
    unique-𝕊et : ∀{A B E : Set}{a}
              -> {e : E × A -> B} {m : E -> (A -> B)}
              -> (λ fa → proj₁ fa (proj₂ fa)) ∘ < m ∘ proj₁ , proj₂ > ≡ e
              -> (λ b → e (a , b)) ≡ m a
    unique-𝕊et refl = refl
