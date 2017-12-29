
{- Monadic structure of the diamond operator. -}
module Monad where

open import Category
open import Functor
open import TemporalOps

open import Data.Nat.Properties using (+-suc; +-comm; +-right-identity; +-assoc)

-- (Very verbose) comparison view
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
    rewrite delay-plus-left0 {λ n → Σ ℕ (λ m → delay A by m at n)} k l
    with v
... | j , y
    rewrite sym (delay-plus {A} k j l)
    = k + j , y
μ {A} n (.(n + suc l) , v) | fst==suc[ .n + l ]
    rewrite delay-plus-right0 {λ k → Σ ℕ (λ m → delay A by m at k)} n (suc l)
          | sym (delay-plus-right0 {A} n (suc l))
    = n + suc l , v

-- || Monad laws

-- Left identity
μ-left-id : ∀{A : τ} {n : ℕ} {a : ◇ A at n}
               -> (μ {A} ∘ fmap-◇ {A} {◇ A} η at n) a ≡ (μ ∘ η at n) a
μ-left-id {A} {n} {k , v} with compareLeq k n
μ-left-id {A} {.k} {.(k + suc l) , v} | fst==suc[ k + l ]
    = {!   !}
    where open ≡-Reasoning
μ-left-id {A} {.(k + l)} {k , v}      | snd==[ .k + l ] = {!   !}


-- join . fmap join = join . join
-- join . fmap return = join . return = id
