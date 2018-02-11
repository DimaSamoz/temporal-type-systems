
{- Box operator. -}
module TemporalOps.Box where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import TemporalOps.Common

open import Relation.Binary.PropositionalEquality

-- Function extensionality
postulate
    ext : ∀{a b} -> Extensionality a b

-- The box operator can be derived as a comonad from an adjunction K ⊣ G

K : Functor 𝕊et ℝeactive
K = record
  { omap = λ A -> (λ n -> A)
  ; fmap = λ f -> (λ n -> λ x -> f x)
  ; fmap-id = refl
  ; fmap-∘ = refl
  ; fmap-cong = λ z → z
  }

G : Functor ℝeactive 𝕊et
G = record
  { omap = λ A -> (∀(n : ℕ) -> A n)
  ; fmap = λ f -> λ a -> (λ n -> f n (a n))
  ; fmap-id = refl
  ; fmap-∘ = refl
  ; fmap-cong = λ pf → ext (λ n → pf)
  }

-- Box operator
□_ : τ -> τ
(□ A) n = (k : ℕ) -> A k
infixr 65 □_

-- Functor instance for □
F-□ : Endofunctor ℝeactive
F-□ = record
    { omap = □_
    ; fmap = fmap-□
    ; fmap-id = refl
    ; fmap-∘ = refl
    ; fmap-cong = fmap-□-cong
    }
    where
    -- Lifting of □
    fmap-□ : {A B : τ} -> A ⇴ B -> □ A ⇴ □ B
    fmap-□ f n a = λ k → f k (a k)

    fmap-□-cong : {A B : τ} {f f′ : A ⇴ B}
               -> (∀{n : ℕ} {a : A at n} -> f n a ≡ f′ n a)
               -> (∀{n : ℕ} {a : □ A at n} -> fmap-□ f n a ≡ fmap-□ f′ n a)
    fmap-□-cong {A} {B} {f} {f′} p {n} {a} = ext (λ n → p)
