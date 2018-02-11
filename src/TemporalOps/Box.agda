
{- Box operator. -}
module TemporalOps.Box where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Adjunction
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
K⊣G : K ⊣ G
K⊣G = record
    { η = record
        { at = λ A x n → x
        ; nat-cond = λ {A} {B} {f} {a} → refl }
    ; ε = record
        { at = λ A n z → z n
        ; nat-cond = λ {A} {B} {f} {n} {a} → refl }
    ; tri1 = λ {A} {n} {a} → refl
    ; tri2 = λ {B} {a} → refl
    }

-- | Box operator

-- Comonad instance from adjunction
W-□ : Comonad ℝeactive
W-□ = AdjComonad K⊣G

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
