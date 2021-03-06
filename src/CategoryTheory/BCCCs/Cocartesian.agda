
-- Sums and cocartesian categories
module CategoryTheory.BCCCs.Cocartesian where

open import CategoryTheory.Categories

open import Relation.Binary using (IsEquivalence)

module _ {n} (ℂ : Category n) where

    open Category ℂ

    -- Initial object in a category
    record InitialObj : Set (lsuc n) where
        field
            -- | Data
            -- The initial object
            ⊥ : obj
            -- Canonical morphism
            ¡ : {A : obj} -> (⊥ ~> A)

            -- | Laws
            -- Need to show that the canonical morphism ! is unique
            ¡-unique : {A : obj} -> (m : ⊥ ~> A)
                  -> m ≈ ¡

    -- Sum of two objects
    -- Based on github.com/copumpkin/categories
    record Sum (A B : obj) : Set (lsuc n) where
        infix 10 [_⁏_]
        field
            -- | Data
            -- Sum of A and B
            A⊕B : obj
            -- First injection
            ι₁ : A ~> A⊕B
            -- Second injection
            ι₂ : B ~> A⊕B
            -- Canonical mediator
            [_⁏_] : ∀{S} -> (A ~> S) -> (B ~> S) -> (A⊕B ~> S)

            -- | Laws
            -- [_⁏_] expresses that given another candidate sum S
            -- and candidate injections to A and B there is a morphism
            -- from A⊕B to S. We need to check that this mediator makes
            -- the sum diagram commute and is unique.

            ι₁-comm : ∀{S} -> {i₁ : A ~> S} {i₂ : B ~> S}
                   -> [ i₁ ⁏ i₂ ] ∘ ι₁ ≈ i₁
            ι₂-comm : ∀{S} -> {i₁ : A ~> S} {i₂ : B ~> S}
                   -> [ i₁ ⁏ i₂ ] ∘ ι₂ ≈ i₂
            ⊕-unique  : ∀{S} -> {i₁ : A ~> S} {i₂ : B ~> S} {m : A⊕B ~> S}
                   -> m ∘ ι₁ ≈ i₁ -> m ∘ ι₂ ≈ i₂ -> [ i₁ ⁏ i₂ ] ≈ m

        -- η-expansion of function sums (via morphisms)
        ⊕-η-exp : ∀{S} -> {m : A⊕B ~> S}
               -> [ m ∘ ι₁ ⁏ m ∘ ι₂ ] ≈ m
        ⊕-η-exp = ⊕-unique r≈ r≈

        -- Summing of injection functions is the identity
        ⊕-η-id : [ ι₁ ⁏ ι₂ ] ≈ id
        ⊕-η-id = ⊕-unique id-left id-left

        -- Congruence over function summing
        [⁏]-cong : ∀{S} -> {i₁ j₁ : A ~> S} {i₂ j₂ : B ~> S}
               -> i₁ ≈ j₁ -> i₂ ≈ j₂
               -> [ i₁ ⁏ i₂ ] ≈ [ j₁ ⁏ j₂ ]
        [⁏]-cong pr1 pr2 = ⊕-unique (ι₁-comm ≈> pr1 [sym]) (ι₂-comm ≈> pr2 [sym])

-- Type class for cocartesian categories
record Cocartesian {n} (ℂ : Category n) : Set (lsuc n) where
    open Category ℂ
    field
        -- | Data
        -- Initial object
        init : InitialObj ℂ
        -- Binary sums for all pairs of objects
        sum : ∀(A B : obj) -> Sum ℂ A B

    open InitialObj init public
    open module S {A} {B} = Sum (sum A B) public

    -- Shorthand for sum object
    infixl 22 _⊕_
    _⊕_ : (A B : obj) -> obj
    A ⊕ B = A⊕B {A} {B}

    -- Parallel sum of morphisms
    infixl 65 _⊹_
    _⊹_ : {A B P Q : obj} -> (A ~> P) -> (B ~> Q)
       -> (A ⊕ B ~> P ⊕ Q)
    _⊹_ {A} {B} {P} {Q} f g = [ ι₁ ∘ f ⁏ ι₂ ∘ g ]

    -- Sum of three morphisms
    [_⁏_⁏_] : ∀{S A B C : obj} -> (A ~> S) -> (B ~> S) -> (C ~> S) -> (A ⊕ B ⊕ C ~> S)
    [ f ⁏ g ⁏ h ] = [ [ f ⁏ g ] ⁏ h ]
