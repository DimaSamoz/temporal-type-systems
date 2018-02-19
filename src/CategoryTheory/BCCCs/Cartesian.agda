
-- Products and Cartesian categories
module CategoryTheory.BCCCs.Cartesian where

open import CategoryTheory.Categories
open import Relation.Binary using (IsEquivalence)
import Function as F using (_∘_)

module _ {n} (ℂ : Category n) where

    open Category ℂ

    -- Terminal object in a category
    record TerminalObj : Set (lsuc n) where
        field
            -- | Data
            -- The terminal object
            ⊤ : obj
            -- Canonical morphism
            ! : {A : obj} -> (A ~> ⊤)

            -- | Laws
            -- Need to show that the canonical morphism ! is unique
            unique : {A : obj} -> (m : A ~> ⊤)
                  -> m ≈ !

    -- Product of two objects
    -- Based on github.com/copumpkin/categories
    record Product (A B : obj) : Set (lsuc n) where
        infix 10 ⟨_,_⟩
        field
            -- | Data
            -- Product of A and B
            A⊗B : obj
            -- First projection
            π₁ : A⊗B ~> A
            -- Second projection
            π₂ : A⊗B ~> B
            -- Canonical mediator
            ⟨_,_⟩ : ∀{P} -> (P ~> A) -> (P ~> B) -> (P ~> A⊗B)

            -- | Laws
            -- ⟨_,_⟩ expresses that given another candidate product C
            -- and candidate projections to A and B there is a morphism
            -- from P to A⊗B. We need to check that this mediator makes
            -- the product diagram commute and is unique.

            comm-π₁ : ∀{P} -> {p₁ : P ~> A} {p₂ : P ~> B}
                   -> π₁ ∘ ⟨ p₁ , p₂ ⟩ ≈ p₁
            comm-π₂ : ∀{P} -> {p₁ : P ~> A} {p₂ : P ~> B}
                   -> π₂ ∘ ⟨ p₁ , p₂ ⟩ ≈ p₂
            unique  : ∀{P} -> {p₁ : P ~> A} {p₂ : P ~> B} {m : P ~> A⊗B}
                   -> π₁ ∘ m ≈ p₁ -> π₂ ∘ m ≈ p₂ -> ⟨ p₁ , p₂ ⟩ ≈ m

        ⊗-η-exp : ∀{P} -> {m : P ~> A⊗B}
               -> ⟨ π₁ ∘ m , π₂ ∘ m ⟩ ≈ m
        ⊗-η-exp = unique (IsEquivalence.refl ≈-equiv) (IsEquivalence.refl ≈-equiv)

        ⊗-η-id : ⟨ π₁ , π₂ ⟩ ≈ id
        ⊗-η-id = unique id-right id-right

        ⟨,⟩-cong : ∀{P} -> {p₁ q₁ : P ~> A} {p₂ q₂ : P ~> B}
               -> p₁ ≈ q₁ -> p₂ ≈ q₂
               -> ⟨ p₁ , p₂ ⟩ ≈ ⟨ q₁ , q₂ ⟩
        ⟨,⟩-cong pr1 pr2 = unique (comm-π₁ ≈> pr1 [sym]) (comm-π₂ ≈> pr2 [sym])

-- Type class for Cartesian categories
record Cartesian {n} (ℂ : Category n) : Set (lsuc n) where
    open Category ℂ
    field
        -- | Data
        -- Terminal object
        ⊤ : TerminalObj ℂ
        -- Binary products for all pairs of objects
        _⊗_ : ∀(A B : obj) -> Product ℂ A B


𝕊et-Cartesian : Cartesian 𝕊et
𝕊et-Cartesian = record
    { ⊤ = record
        { ⊤ = top
        ; ! = λ {A} _ → top.tt
        ; unique = λ m → refl
        }
    ; _⊗_ = λ A B → record
        { A⊗B = A × B
        ; π₁ = proj₁
        ; π₂ = proj₂
        ; ⟨_,_⟩ = <_,_>
        ; comm-π₁ = refl
        ; comm-π₂ = refl
        ; unique = λ pr1 pr2 → unique-𝕊et (ext λ x → pr1 {x}) (ext λ x → pr2 {x})
        }
    }
    where
    unique-𝕊et : ∀{A B P : Set}{a}
              -> {p₁ : P -> A} {p₂ : P -> B} {m : P -> A × B}
              -> proj₁ F.∘ m ≡ p₁ -> proj₂ F.∘ m ≡ p₂
              -> < p₁ , p₂ > a ≡ m a
    unique-𝕊et refl refl = refl
