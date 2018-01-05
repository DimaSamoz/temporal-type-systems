
{- Type classes and instances for categories. -}
module CategoryTheory.Categories where

open import Data.Nat public
open import Relation.Binary.PropositionalEquality public
open import Data.Unit using () renaming (⊤ to top) public
open import Data.Empty using () renaming (⊥ to bot) public
open import Data.Product public
open import Data.Sum renaming (_⊎_ to _∨_)
open import Relation.Binary using (IsEquivalence ; Reflexive ; Symmetric ; Transitive)

-- Type class for categories.
-- Based on https://github.com/UlfNorell/category-theory-experiments
record Category : Set₂ where
    infixr 50 _~>_
    infixl 40 _≈_
    infix 60 _∘_
    field
        -- || Data
        -- Objects
        obj  : Set₁
        -- Arrows
        _~>_ : obj -> obj -> Set

        -- || Operations
        -- Identity arrow
        id   : {A : obj} -> A ~> A
        -- Composition of arrows
        _∘_  : {A B C : obj} -> (B ~> C) -> (A ~> B) -> (A ~> C)
        -- Equality of arrows (as we don't have function extensionality)
        _≈_  : {A B : obj} -> (A ~> B) -> (A ~> B) -> Set

        -- || Laws
        -- Left identity
        id-left  : {x y : obj} {f : x ~> y} -> id ∘ f ≈ f
        -- Right identity
        id-right : {x y : obj} {f : x ~> y} -> f ∘ id ≈ f
        -- Associativity of composition
        ∘-assoc  : {x y z w : obj} {f : z ~> w} {g : y ~> z} {h : x ~> y}
                -> (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
        ≈-equiv  : ∀{A B : obj} -> IsEquivalence (_≈_ {A} {B})
open Category

-- Category of sets.
instance
    𝕊et : Category
    𝕊et = record
        { obj      = Set
        ; _~>_     = λ a b   -> (a -> b)
        ; id       = λ a     -> a
        ; _∘_      = λ g f a -> g (f a)
        ; _≈_      = λ f g   -> ∀ {a} -> f a ≡ g a
        ; id-left  = refl
        ; id-right = refl
        ; ∘-assoc  = refl
        ; ≈-equiv  = record { refl = refl
                            ; sym = λ p → sym p
                            ; trans = λ p q → trans p q }
        }

-- || Reactive types

-- Time-indexed types.
τ : Set₁
τ = ℕ -> Set

-- Time-indexed functions.
_⇴_ : τ -> τ -> Set
A ⇴ B = ∀(n : ℕ) -> A n -> B n
infixr 30 _⇴_

-- Category of reactive types
instance
    ℝeactive : Category
    ℝeactive = record
             { obj      = τ
             ; _~>_     = _⇴_
             ; id       = λ n a -> a
             ; _∘_      = λ g f -> λ n a -> g n (f n a)
             ; _≈_      = λ f g -> ∀ {n : ℕ} {a} -> f n a ≡ g n a
             ; id-left  = refl
             ; id-right = refl
             ; ∘-assoc  = refl
             ; ≈-equiv  = record { refl = refl
                                 ; sym = λ x → sym x
                                 ; trans = λ p q → trans p q }
             }



-- || Cartesian, cocartesian, exponential structure

-- Final object
⊤ : τ
⊤ n = top

-- Products
_⊗_ : τ -> τ -> τ
(A ⊗ B) n = A n × B n
infixl 60 _⊗_

-- Initial object
⊥ : τ
⊥ n = bot

-- Products
_⊕_ : τ -> τ -> τ
(A ⊕ B) n = A n ∨ B n
infixl 55 _⊕_

-- Exponentials
_⇒_ : τ -> τ -> τ
(A ⇒ B) n = A n -> B n
infixr 50 _⇒_
