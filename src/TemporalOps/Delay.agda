
{- Delay operator. -}
module TemporalOps.Delay where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import TemporalOps.Common
open import TemporalOps.Next
open CategoryTheory.Categories.Category {{...}}

-- General iteration
-- iter f n v = fⁿ(v)
iter : (τ -> τ) -> ℕ -> τ -> τ
iter F zero    A = A
iter F (suc n) A = F (iter F n A)

-- Multi-step delay
delay_by_ : τ -> ℕ -> τ
delay A by n = iter ▹_ n A
infix 67 delay_by_

-- || Lemmas for the delay operator

-- Extra delay is cancelled out by extra waiting.
delay-plus : ∀{A} -> (n l k : ℕ)
          -> delay A by (n + l) at (n + k) ≡ delay A by l at k
delay-plus zero l k = refl
delay-plus (suc n) = delay-plus n

-- || Derived lemmas - they can all be expressed in terms of delay-plus,
-- || but they are given explicitly for simplicity.

-- Delay by n is cancelled out by waiting n extra steps.
delay-plus-left0 : ∀{A} -> (n k : ℕ)
              -> delay A by n at (n + k) ≡ A at k
delay-plus-left0 zero k = refl
delay-plus-left0 (suc n) k = delay-plus-left0 n k

-- Extra delay by n steps is cancelled out by waiting for n steps.
delay-plus-right0 : ∀{A} -> (n l : ℕ)
              -> delay A by (n + l) at n ≡ delay A by l at 0
delay-plus-right0 zero l = refl
delay-plus-right0 (suc n) l = delay-plus-right0 n l


-- Delay instances
instance
    F-delay : ℕ -> Functor ℝeactive ℝeactive
    F-delay k = record
        { omap = delay_by k
        ; fmap = fmap-delay k
        ; fmap-id = λ {_ n a} -> fmap-delay-id k {_} {n} {a}
        ; fmap-∘ = fmap-delay-∘ k
        }
        where
        -- Lifting of delay
        fmap-delay : {A B : τ} -> (k : ℕ) -> A ⇴ B -> delay A by k ⇴ delay B by k
        fmap-delay zero    f = f
        fmap-delay (suc k) f = Functor.fmap F-▹ (fmap-delay k f)
        -- Delay preserves identities
        fmap-delay-id : ∀ (k : ℕ) {A : τ} {n : ℕ} {a : (delay A by k) n}
                 -> (fmap-delay k (id {A}) at n) a ≡ a
        fmap-delay-id zero = refl
        fmap-delay-id (suc k) {A} {zero} = refl
        fmap-delay-id (suc k) {A} {suc n} = fmap-delay-id k {A} {n}
        -- Delay preserves composition
        fmap-delay-∘ : ∀ (k : ℕ) {A B C : τ} {g : B ⇴ C} {f : A ⇴ B} {n : ℕ} {a : (delay A by k) n}
                -> (fmap-delay k (g ∘ f) at n) a ≡ (fmap-delay k g ∘ fmap-delay k f at n) a
        fmap-delay-∘ zero = refl
        fmap-delay-∘ (suc k) {n = zero} = refl
        fmap-delay-∘ (suc k) {n = suc n} = fmap-delay-∘ k {n = n}

    EF-delay : (k : ℕ) -> Endofunctor ℝeactive
    EF-delay k = record { functor = F-delay k }
