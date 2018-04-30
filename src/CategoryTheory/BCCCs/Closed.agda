
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
            Λ-cong : ∀{E} {f g : E ⊗ A ~> B}
                  -> f ≈ g -> Λ f ≈ Λ g

        -- Currying identity
        Λ-*id : ∀{D E} {f : E ⊗ A ~> B} {g : D ~> E}
             -> Λ (f ∘ (g * id)) ≈ Λ f ∘ g
        Λ-*id {D}{E}{f}{g} =
            begin
                Λ (f ∘ (g * id))
            ≈⟨ Λ-cong (≈-cong-left (Λ-comm [sym]) ≈> ∘-assoc) ⟩
                Λ (eval ∘ (Λ f * id) ∘ (g * id))
            ≈⟨ Λ-cong (≈-cong-right (*-idemp-dist-∘ id-left)) ⟩
                Λ (eval ∘ (Λ f ∘ g) * id)
            ≈⟨ Λ-unique r≈ ⟩
                Λ f ∘ g
            ∎

-- Type class for closed categories
-- definition using exponentials
record Closed {n} {ℂ : Category n} (Cℂ : Cartesian ℂ) : Set (lsuc n) where
    open Category ℂ
    field
        -- Exponential object for each pair of objects
        exp : ∀(A B : obj) -> Exponential Cℂ A B

    open module E {A} {B} = Exponential (exp A B) public

    -- Shorthand for exponential object
    infixr 20 _⇒_
    _⇒_ : (A B : obj) -> obj
    A ⇒ B = A⇒B {A} {B}
