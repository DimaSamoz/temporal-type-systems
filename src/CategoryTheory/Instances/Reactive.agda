
{- Category of reactive types -}
module CategoryTheory.Instances.Reactive where

open import CategoryTheory.Categories


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
