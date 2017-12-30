
{- Temporal operations. -}

module TemporalOps where

open import Types
open import Category

open import Data.Nat
open import Data.Product

-- Box operator
□_ : τ -> τ
(□_ A) n = (n : ℕ) -> A n
infixr 65 □_

-- || Delay and iteration

-- One-step delay operator
▹_ : τ -> τ
▹_ A zero    = ⊤ zero
▹_ A (suc n) = A n
infixr 70 ▹_

-- Time indexing (for clarity, synonym of function appliation at any level)
_at_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f at n = f n
infixl 45 _at_

-- General iteration
-- iter f n v = fⁿ(v)
iter : (τ -> τ) -> ℕ -> τ -> τ
iter F zero    A = A
iter F (suc n) A = F (iter F n A)

-- Multi-step delay
delay_by_ : τ -> ℕ -> τ
delay A by n = iter ▹_ n A
infix 67 delay_by_

-- Arbitrary delay
◇_ : τ -> τ
(◇_ A) n = Σ ℕ (λ k -> delay A by k at n)
infixr 65 ◇_

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
