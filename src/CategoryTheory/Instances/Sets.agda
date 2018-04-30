
{- Category of sets -}
module CategoryTheory.Instances.Sets where

open import CategoryTheory.Categories
open import CategoryTheory.BCCCs

import Function as F using (_∘_)
open import Data.Unit using () renaming (⊤ to top) public
open import Data.Product public
open import Data.Empty using (⊥-elim) renaming (⊥ to bot) public
open import Data.Sum

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

-- Bicartesian closed structure
𝕊et-BCCC : BicartesianClosed 𝕊et
𝕊et-BCCC = record
    { cart = record
        { term = record
            { ⊤ = top
            ; ! = λ {A} _ → top.tt
            ; !-unique = λ m → refl
            }
        ; prod = λ A B → record
            { A⊗B = A × B
            ; π₁ = proj₁
            ; π₂ = proj₂
            ; ⟨_,_⟩ = <_,_>
            ; π₁-comm = refl
            ; π₂-comm = refl
            ; ⊗-unique = λ pr1 pr2 → unique-cart (ext λ x → pr1 {x}) (ext λ x → pr2 {x})
            }
        }
    ; cocart = record
        { init = record
            { ⊥ = bot
            ; ¡ = ⊥-elim
            ; ¡-unique = λ {A} m → λ {}
            }
        ; sum = λ A B → record
            { A⊕B = A ⊎ B
            ; ι₁ = inj₁
            ; ι₂ = inj₂
            ; [_⁏_] = [_,_]
            ; ι₁-comm = λ {S} {i₁} {i₂} {a} → refl
            ; ι₂-comm = λ {S} {i₁} {i₂} {a} → refl
            ; ⊕-unique = λ {S} {i₁} {i₂} {m} pr1 pr2
                      -> unique-cocart {m = m} (ext λ x → pr1 {x}) (ext λ x → pr2 {x})
            }
        }
    ; closed = record
        { exp = λ A B → record
            { A⇒B = A -> B
            ; eval = λ fa → proj₁ fa (proj₂ fa)
            ; Λ = λ f a b → f (a , b)
            ; Λ-comm = refl
            ; Λ-unique = λ pr → λ {a} ->  unique-closed (ext λ x → pr {x})
            }
        }
    }
    where
    unique-cart : ∀{A B P : Set}{a}
              -> {p₁ : P -> A} {p₂ : P -> B} {m : P -> A × B}
              -> proj₁ F.∘ m ≡ p₁ -> proj₂ F.∘ m ≡ p₂
              -> < p₁ , p₂ > a ≡ m a
    unique-cart refl refl = refl
    unique-cocart : ∀{A B S : Set}{a}
              -> {i₁ : A -> S} {i₂ : B -> S} {m : A ⊎ B -> S}
              -> m F.∘ inj₁ ≡ i₁ -> m F.∘ inj₂ ≡ i₂
              -> [ i₁ , i₂ ] a ≡ m a
    unique-cocart {a = inj₁ x} refl refl = refl
    unique-cocart {a = inj₂ y} refl refl = refl
    open Category 𝕊et
    unique-closed : ∀{A B E : Set}{a}
              -> {e : E × A -> B} {m : E -> (A -> B)}
              -> (λ fa → proj₁ fa (proj₂ fa)) ∘ < m ∘ proj₁ , proj₂ > ≡ e
              -> (λ b → e (a , b)) ≡ m a
    unique-closed refl = refl
