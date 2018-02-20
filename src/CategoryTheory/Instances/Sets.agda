
{- Category of sets -}
module CategoryTheory.Instances.Sets where

open import CategoryTheory.Categories

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
