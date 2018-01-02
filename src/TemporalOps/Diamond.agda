
{- Diamond operator. -}
module TemporalOps.Diamond where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import TemporalOps.Common
open import TemporalOps.Next
open import TemporalOps.Delay
open CategoryTheory.Categories.Category {{...}}

-- Arbitrary delay
◇_ : τ -> τ
(◇_ A) n = Σ ℕ (λ k -> delay A by k at n)
infixr 65 ◇_

-- ◇ instances
instance
    F-◇ : Functor ℝeactive ℝeactive
    F-◇ = record
        { omap = ◇_
        ; fmap = fmap-◇
        ; fmap-id = fmap-◇-id
        ; fmap-∘ = fmap-◇-∘
        }
        where
        -- Lifting of ◇
        fmap-◇ : {A B : τ} -> A ⇴ B -> ◇ A ⇴ ◇ B
        fmap-◇ f n (k , v) = k , (Functor.fmap (F-delay k) f at n) v
        -- ◇ preserves identities
        fmap-◇-id : ∀ {A : τ} {n : ℕ} {a : (◇ A) n}
                 -> (fmap-◇ (id {A}) at n) a ≡ a
        fmap-◇-id {A} {n} {zero , v} = refl
        fmap-◇-id {A} {zero} {suc k , v} = refl
        fmap-◇-id {A} {suc n} {suc k , v}
            rewrite delay-plus {A} 1 k n
                  | Functor.fmap-id (F-delay (suc k)) {A} {suc n} {v}
            = refl
        -- ◇ preserves composition
        fmap-◇-∘ : ∀ {A B C : τ} {g : B ⇴ C} {f : A ⇴ B} {n : ℕ} {a : (◇ A) n}
                -> (fmap-◇ (g ∘ f) at n) a ≡ (fmap-◇ g ∘ fmap-◇ f at n) a
        fmap-◇-∘ {n = n} {zero , v} = refl
        fmap-◇-∘ {n = zero} {suc k , v} = refl
        fmap-◇-∘ {A} {B} {C} {g} {f} {suc n} {suc k , v}
            rewrite delay-plus {A} 1 k n
                  | Functor.fmap-∘ (F-delay (suc k)) {A} {B} {C} {g} {f} {suc n} {v}
            = refl

    EF-◇ : Endofunctor ℝeactive F-◇
    EF-◇ = record {}
