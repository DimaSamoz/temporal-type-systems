
-- Products and Cartesian categories
module CategoryTheory.BCCCs.Cartesian where

open import CategoryTheory.Categories

open import Relation.Binary using (IsEquivalence)

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

        -- η-expansion of function pairs (via morphisms)
        ⊗-η-exp : ∀{P} -> {m : P ~> A⊗B}
               -> ⟨ π₁ ∘ m , π₂ ∘ m ⟩ ≈ m
        ⊗-η-exp = unique r≈ r≈

        -- Pairing of projection functions is the identity
        ⊗-η-id : ⟨ π₁ , π₂ ⟩ ≈ id
        ⊗-η-id = unique id-right id-right

        -- Congruence over function pairing
        ⟨,⟩-cong : ∀{P} -> {p₁ q₁ : P ~> A} {p₂ q₂ : P ~> B}
               -> p₁ ≈ q₁ -> p₂ ≈ q₂
               -> ⟨ p₁ , p₂ ⟩ ≈ ⟨ q₁ , q₂ ⟩
        ⟨,⟩-cong pr1 pr2 = unique (comm-π₁ ≈> pr1 [sym]) (comm-π₂ ≈> pr2 [sym])

-- Type class for Cartesian categories
record Cartesian {n} (ℂ : Category n) : Set (lsuc n) where
    open Category ℂ
    open Product hiding (⟨_,_⟩)
    field
        -- | Data
        -- Terminal object
        term : TerminalObj ℂ
        -- Binary products for all pairs of objects
        prod : ∀(A B : obj) -> Product ℂ A B

    -- Shorthand for terminal object
    ⊤ : obj
    ⊤ = TerminalObj.⊤ term

    -- Shorthand for product object
    infixr 70 _⊗_
    _⊗_ : (A B : obj) -> obj
    _⊗_ A B = A⊗B (prod A B)

    -- Parallel product of morphisms
    _*_ : {A B P Q : obj} -> (A ~> P) -> (B ~> Q)
       -> (A ⊗ B ~> P ⊗ Q)
    _*_ {A} {B} {P} {Q} f g = ⟨ f ∘ π₁ (prod A B) , g ∘ π₂ (prod A B) ⟩
        where
        open Product (prod P Q) using (⟨_,_⟩)
