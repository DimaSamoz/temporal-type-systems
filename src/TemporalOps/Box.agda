
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
(□_ A) n = (n : ℕ) -> A n
infixr 65 □_

-- □ instances
instance
    F-□ : Functor ℝeactive ℝeactive
    F-□ = record
        { omap = □_
        ; fmap = fmap-□
        ; fmap-id = refl
        ; fmap-∘ = refl
        }
        where
        -- Lifting of □
        fmap-□ : {A B : τ} -> A ⇴ B -> □ A ⇴ □ B
        fmap-□ f n a = λ k → f k (a k)

    EF-□ : Endofunctor ℝeactive
    EF-□ = record { functor = F-□ }
