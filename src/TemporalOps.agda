
{- Temporal operations. -}

module TemporalOps where

open import Types
open import Category

open import Data.Nat
open import Data.Product

infixr 70 ◇_

-- || Delay and iteration

-- One-step delay operator
▹ : τ -> τ
▹ A zero    = ⊤ zero
▹ A (suc n) = A n

-- General iteration
-- iter f n v = fⁿ(v)
iter : (τ -> τ) -> ℕ -> τ -> τ
iter F zero    A = A
iter F (suc n) A = F (iter F n A)

-- Multi-step delay
delay_by_ : τ -> ℕ -> τ
delay A by n = iter ▹ n A

-- Arbitrary delay
◇_ : τ -> τ
(◇_ A) n = Σ ℕ (λ k -> (delay A by k) n)
