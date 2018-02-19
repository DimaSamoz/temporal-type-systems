
{- Type classes and instances for categories. -}
module CategoryTheory.Categories where

open import Data.Nat using (ℕ ; zero ; suc ; _+_) public
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; subst ; cong) public
open import Data.Unit using () renaming (⊤ to top) public
open import Data.Empty using () renaming (⊥ to bot) public
open import Data.Product public
open import Data.Sum renaming (_⊎_ to _∨_)
open import Relation.Binary using (IsEquivalence)
open import Agda.Primitive using (Level ; _⊔_ ; lzero ; lsuc) public
open import Relation.Binary.PropositionalEquality

-- Function extensionality
postulate
    ext : ∀{a b} -> Extensionality a b


-- Type class for categories.
-- Based on https://github.com/UlfNorell/category-theory-experiments
record Category (n : Level) : Set (lsuc (lsuc n)) where
    infixr 50 _~>_
    infixl 40 _≈_
    infix 60 _∘_
    field
        -- || Data
        -- Objects
        obj  : Set (lsuc n)
        -- Arrows
        _~>_ : obj -> obj -> Set n

        -- || Operations
        -- Identity arrow
        id   : {A : obj} -> A ~> A
        -- Composition of arrows
        _∘_  : {A B C : obj} -> (B ~> C) -> (A ~> B) -> (A ~> C)
        -- Equality of arrows (as we don't have function extensionality)
        _≈_  : {A B : obj} -> (A ~> B) -> (A ~> B) -> Set n

        -- || Laws
        -- Left identity
        id-left  : {A B : obj} {f : A ~> B} -> id ∘ f ≈ f
        -- Right identity
        id-right : {A B : obj} {f : A ~> B} -> f ∘ id ≈ f
        -- Associativity of composition
        ∘-assoc  : {A B C D : obj} {f : C ~> D} {g : B ~> C} {h : A ~> B}
                -> (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
        -- Arrow equality is an equivalence relation
        ≈-equiv  : ∀{A B : obj} -> IsEquivalence (_≈_ {A} {B})
        -- Congruence of equality and composition
        ≈-cong   : ∀{A B C : obj} {f f′ : A ~> B} {g g′ : B ~> C}
                -> f ≈ f′ -> g ≈ g′ -> g ∘ f ≈ g′ ∘ f′

    -- Equational reasoning for ≈ (based on the standard library definitions)
    infix  3 _∎
    infixr 2 _≈⟨⟩_ _≈⟨_⟩_
    infix  1 begin_
    infixl 20 _[sym]
    infixr 15 _≈>_

    begin_ : ∀{A B : obj} {x y : A ~> B} → x ≈ y → x ≈ y
    begin_ x≈y = x≈y

    _≈⟨⟩_ : ∀{A B : obj} (x {y} : A ~> B) → x ≈ y → x ≈ y
    _ ≈⟨⟩ x≈y = x≈y

    _≈⟨_⟩_ : ∀{A B : obj} (x {y z} : A ~> B) → x ≈ y → y ≈ z → x ≈ z
    _ ≈⟨ x≈y ⟩ y≈z = IsEquivalence.trans ≈-equiv x≈y y≈z

    _∎ : ∀{A B : obj} (x : A ~> B) → x ≈ x
    _∎ _ = IsEquivalence.refl ≈-equiv

    _[sym] : ∀{A B : obj} {x y : A ~> B} → x ≈ y → y ≈ x
    p [sym] = IsEquivalence.sym ≈-equiv p

    _≈>_ : ∀{A B : obj} {x y z : A ~> B} → x ≈ y → y ≈ z → x ≈ z
    p1 ≈> p2 = IsEquivalence.trans ≈-equiv p1 p2

    id-comm : {A B : obj} {f : A ~> B} -> f ∘ id ≈ id ∘ f
    id-comm = id-right ≈> id-left [sym]

    -- Derived congruence properties
    ≈-cong-left : ∀{A B C : obj} {f : A ~> B} {g g′ : B ~> C}
            -> g ≈ g′ -> g ∘ f ≈ g′ ∘ f
    ≈-cong-left e = ≈-cong (IsEquivalence.refl ≈-equiv) e
    ≈-cong-right : ∀{A B C : obj} {g : B ~> C} {f f′ : A ~> B}
            -> f ≈ f′ -> g ∘ f ≈ g ∘ f′
    ≈-cong-right e = ≈-cong e (IsEquivalence.refl ≈-equiv)
open Category

-- Category of sets.
𝕊et : Category lzero
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
    ; ≈-cong   = ≈-cong-𝕊
    }
    where
    ≈-cong-𝕊 : ∀{A B C : Set} {f f′ : A -> B} {g g′ : B -> C}
            -> (∀ {a} -> f a ≡ f′ a)
            -> (∀ {b} -> g b ≡ g′ b)
            -> (∀ {a} -> g (f a) ≡ g′ (f′ a))
    ≈-cong-𝕊 {f′ = f′} fe ge {a′} rewrite fe {a′} | ge {f′ a′} = refl

-- || Reactive types

-- Time-indexed types.
τ : Set₁
τ = ℕ -> Set

-- Time-indexed functions.
_⇴_ : τ -> τ -> Set
A ⇴ B = ∀(n : ℕ) -> A n -> B n
infixr 30 _⇴_

-- Category of reactive types
ℝeactive : Category lzero
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
         ; ≈-cong   = ≈-cong-ℝ
         }
         where
         ≈-cong-ℝ : ∀{A B C : τ} {f f′ : A ⇴ B} {g g′ : B ⇴ C}
                 -> (∀ {n a} -> f n a ≡ f′ n a)
                 -> (∀ {n b} -> g n b ≡ g′ n b)
                 -> (∀ {n a} -> g n (f n a) ≡ g′ n (f′ n a))
         ≈-cong-ℝ {f′ = f′} fe ge {n} {a′}
                rewrite fe {n} {a′}
                      | ge {n} {f′ n a′} = refl


