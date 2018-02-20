
{- Diamond operator. -}
module TemporalOps.Diamond.Functor where

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import TemporalOps.Common
open import TemporalOps.Next
open import TemporalOps.Delay

open Category ℝeactive hiding (begin_ ; _∎) public

-- Arbitrary delay
◇_ : τ -> τ
(◇ A) n = Σ[ k ∈ ℕ ] (delay A by k at n)
infixr 65 ◇_

-- ◇ instances
F-◇ : Endofunctor ℝeactive
F-◇ = record
    { omap      = ◇_
    ; fmap      = fmap-◇
    ; fmap-id   = fmap-◇-id
    ; fmap-∘    = fmap-◇-∘
    ; fmap-cong = fmap-◇-cong
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
        rewrite delay-+ {A} 1 k n
              | Functor.fmap-id (F-delay (suc k)) {A} {suc n} {v}
        = refl
    -- ◇ preserves composition
    fmap-◇-∘ : ∀ {A B C : τ} {g : B ⇴ C} {f : A ⇴ B} {n : ℕ} {a : (◇ A) n}
            -> (fmap-◇ (g ∘ f) at n) a ≡ (fmap-◇ g ∘ fmap-◇ f at n) a
    fmap-◇-∘ {n = n} {zero , v} = refl
    fmap-◇-∘ {n = zero} {suc k , v} = refl
    fmap-◇-∘ {A} {B} {C} {g} {f} {suc n} {suc k , v}
        rewrite delay-+ {A} 1 k n
              | Functor.fmap-∘ (F-delay (suc k)) {A} {B} {C} {g} {f} {suc n} {v}
        = refl
    -- ▹ is congruent
    fmap-◇-cong : ∀{A B : τ} {f f′ : A ⇴ B}
            -> ({n : ℕ} {a : A at n}   -> f n a ≡ f′ n a)
            -> ({n : ℕ} {a : ◇ A at n} -> (fmap-◇ f at n) a
                                        ≡ (fmap-◇ f′ at n) a)
    fmap-◇-cong {A} e {n} {zero , a}
        rewrite delay-+-left0 {A} 0 n
              | e {n} {a} = refl
    fmap-◇-cong e {zero} {suc k , a} = refl
    fmap-◇-cong {A} {B} {f} {f′} e {suc n} {suc k , a}
        rewrite delay-+ {A} 1 k n
              | Functor.fmap-cong (F-delay (suc k)) {A} {B} {f} {f′} e {suc n} {a}
              = refl
