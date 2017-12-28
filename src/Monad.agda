
{- Monadic structure of the diamond operator. -}
module Monad where

open import Category
open import Functor
open import TemporalOps

open import Data.Nat.Properties using (+-suc; +-comm; +-right-identity; +-assoc)
open import Function using (_∋_)

-- (Very verbose) cmparison view
-- Like 'compare', but only distinguishes ≤ or >.
data LeqOrdering : ℕ -> ℕ -> Set where
    fst==suc[_+_] : ∀ k l → LeqOrdering (k + suc l) k
    snd==[_+_]    : ∀ k l → LeqOrdering k           (k + l)

compareLeq : ∀ n k -> LeqOrdering n k
compareLeq zero               k    = snd==[ zero + k ]
compareLeq (suc n)            zero = fst==suc[ zero + n ]
compareLeq (suc n)            (suc k) with compareLeq n k
compareLeq (suc .(k + suc l)) (suc k)        | fst==suc[ .k + l ] =
    fst==suc[ suc k + l ]
compareLeq (suc n)            (suc .(n + l)) | snd==[ .n + l ] =
    snd==[ suc n + l ]


-- Unit for ◇.
η : {A : τ} -> A ⇴ ◇ A
η n a = 0 , a

-- Join for ◇.
μ : {A : τ} -> ◇ ◇ A ⇴ ◇ A
μ n (k , v) with compareLeq k n
μ {A} .(k + l) (k , v)       | snd==[ .k + l ]
    rewrite sym (+-right-identity k)
          | +-assoc k 0 l
          | delay-plus {λ n → Σ ℕ (λ m → delay A by m at n)} k 0 (0 + l)
    with v
...       | j , y
    rewrite sym (delay-plus {A} k j l)
          | +-comm k j
          = j + k , y
μ {A} n (.(n + suc l) , v) | fst==suc[ .n + l ]
    rewrite sym (+-right-identity n)
          | +-assoc n 0 (suc l)
          | delay-plus {λ k → Σ ℕ (λ m → delay A by m at k)} n (0 + suc l) 0
          | sym (delay-plus {A} n (suc l) 0)
          = n + suc l , v
