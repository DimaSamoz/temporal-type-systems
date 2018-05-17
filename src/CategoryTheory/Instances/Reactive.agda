
{- Category of reactive types -}
module CategoryTheory.Instances.Reactive where

open import CategoryTheory.Categories
open import CategoryTheory.BCCCs

open import Data.Nat using (ℕ ; zero ; suc ; _+_) public
open import Data.Unit using () renaming (⊤ to top) public
open import Data.Product
open import Data.Empty using (⊥-elim) renaming (⊥ to bot) public
open import Data.Sum renaming ([_,_] to ⟦_,_⟧)
import Function as F using (_∘_)

-- || Reactive types

-- Time-indexed types.
τ : Set₁
τ = ℕ -> Set

-- Time-indexed functions.
_⇴_ : τ -> τ -> Set
A ⇴ B = ∀(n : ℕ) -> A n -> B n
infixr 10 _⇴_

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

-- Bicartesian closed structure for reactive types
ℝeactive-BCCC : BicartesianClosed ℝeactive
ℝeactive-BCCC = record
    { cart = record
        { term = record
            { ⊤ = λ n → top
            ; ! = λ n _ → top.tt
            ; !-unique = λ m → refl
            }
        ; prod = λ A B → record
            { A⊗B = λ n → A n × B n
            ; π₁ = λ n → proj₁
            ; π₂ = λ n → proj₂
            ; ⟨_,_⟩ = λ f g n a → (f n a , g n a)
            ; π₁-comm = λ {P} {p₁} {p₂} {n} {a} → refl
            ; π₂-comm = λ {P} {p₁} {p₂} {n} {a} → refl
            ; ⊗-unique = λ pr1 pr2 → unique-cart (ext λ a → ext λ n → pr1 {a} {n})
                                               (ext λ a → ext λ n → pr2 {a} {n})
            }
        }
    ; cocart = record
        { init = record
            { ⊥ = λ n → bot
            ; ¡ = λ {A} n → λ ()
            ; ¡-unique = λ {A} m {n} → λ {}
            }
        ; sum = λ A B → record
            { A⊕B = λ n → A n ⊎ B n
            ; ι₁ = λ n → inj₁
            ; ι₂ = λ n → inj₂
            ; [_⁏_] = sum
            ; ι₁-comm = λ {S} {i₁} {i₂} {n} {a} → refl
            ; ι₂-comm = λ {S} {i₁} {i₂} {n} {a} → refl
            ; ⊕-unique = λ {S} {i₁} {i₂} {m} pr1 pr2 →
                        unique-cocart {m = m} (ext λ a → ext λ n → pr1 {a} {n})
                                      (ext λ a → ext λ n → pr2 {a} {n})
            }
        }
    ; closed = record
        { exp = λ A B → record
            { A⇒B = λ n → A n -> B n
            ; eval = λ n z → proj₁ z (proj₂ z)
            ; Λ = λ  f n a b → f n (a , b)
            ; Λ-comm = refl
            ; Λ-unique = λ pr → unique-closed (ext λ n → ext λ a → pr {n} {a})
            ; Λ-cong = λ pr → ext λ _ → pr
            }
        }
    }
    where
    open Category ℝeactive
    unique-cart : ∀{A B P : τ}
              -> {p₁ : P ⇴ A} {p₂ : P ⇴ B} {m : P ⇴ (λ n -> A n × B n)}
              -> (λ _ → proj₁) ∘ m ≡ p₁ -> (λ _ → proj₂) ∘ m ≡ p₂
              -> ∀{n : ℕ}{a : P n} -> (p₁ n a , p₂ n a) ≡ m n a
    unique-cart refl refl = refl
    sum : {A B S : obj} → A ⇴ S → B ⇴ S → (λ n → A n ⊎ B n) ⇴ S
    sum f g n (inj₁ x) = f n x
    sum f g n (inj₂ y) = g n y
    unique-cocart : ∀{A B S : τ}
              -> {i₁ : A ⇴ S} {i₂ : B ⇴ S} {m : (λ n -> A n ⊎ B n) ⇴ S}
              -> m ∘ (λ _ -> inj₁) ≡ i₁ -> m ∘ (λ _ -> inj₂) ≡ i₂
              -> ∀{n : ℕ}{a : A n ⊎ B n} -> sum i₁ i₂ n a ≡ m n a
    unique-cocart refl refl {n} {inj₁ x} = refl
    unique-cocart refl refl {n} {inj₂ y} = refl
    unique-closed : ∀{A B E : τ}
              -> {e : (λ n -> E n × A n) ⇴ B} {m : E ⇴ (λ n -> A n -> B n)}
              -> (λ n fa → proj₁ fa (proj₂ fa)) ∘ ((λ n (a : E n × A n) -> ( (m n F.∘ proj₁) a , proj₂ a ))) ≡ e
              -> ∀{n}{a : E n} -> (λ b → e n (a , b)) ≡ m n a
    unique-closed refl = refl


-- | Top-level shorthands for distinguished BCCC objects and morphisms
open BicartesianClosed ℝeactive-BCCC
open Category ℝeactive hiding (begin_ ; _∎) public

open Cartesian cart public
open Cocartesian cocart public
open Closed closed public

ℝeactive-cart : Cartesian ℝeactive
ℝeactive-cart = cart

-- Sum of three morphisms
[_⁏_⁏_] : ∀{S A B C : τ} -> (A ⇴ S) -> (B ⇴ S) -> (C ⇴ S) -> (A ⊕ B ⊕ C ⇴ S)
[ f ⁏ g ⁏ h ] = [ [ f ⁏ g ] ⁏ h ]

-- Non-canonical distribution morphism
dist : ∀{A B C : τ} ->  A ⊗ (B ⊕ C) ⇴ (A ⊗ B) ⊕ (A ⊗ C)
dist n (a , inj₁ b) = inj₁ (a , b)
dist n (a , inj₂ c) = inj₂ (a , c)

dist2 : ∀{A B C D : τ} ->  A ⊗ (B ⊕ C ⊕ D) ⇴ (A ⊗ B) ⊕ (A ⊗ C) ⊕ (A ⊗ D)
dist2 n (a , inj₁ (inj₁ b)) = inj₁ (inj₁ (a , b))
dist2 n (a , inj₁ (inj₂ c)) = inj₁ (inj₂ (a , c))
dist2 n (a , inj₂ d) = inj₂ (a , d)

-- ℝeactive is distributive
dist-ℝ : ∀{A B C : τ} -> (A ⊗ B) ⊕ (A ⊗ C) <~> A ⊗ (B ⊕ C)
dist-ℝ = record
    { iso~> = [ id * ι₁ ⁏ id * ι₂ ]
    ; iso<~ = dist
    ; iso-id₁ = dist-iso-id₁
    ; iso-id₂ = dist-iso-id₂
    }
    where
    dist-iso-id₁ : ∀{A B C : τ} -> dist {A}{B}{C} ∘ [ id * ι₁ ⁏ id * ι₂ ] ≈ id
    dist-iso-id₁ {n = n} {inj₁ (a , b)} = refl
    dist-iso-id₁ {n = n} {inj₂ (a , c)} = refl

    dist-iso-id₂ : ∀{A B C : τ} -> [ id * ι₁ ⁏ id * ι₂ ] ∘ dist {A}{B}{C} ≈ id
    dist-iso-id₂ {n = n} {a , inj₁ b} = refl
    dist-iso-id₂ {n = n} {a , inj₂ c} = refl
