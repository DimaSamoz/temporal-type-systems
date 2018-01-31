
{- Auxiliary functions for temporal operators. -}
module TemporalOps.Common where

open import CategoryTheory.Categories

-- open import Relation.Binary.PropositionalEquality using (_≡_)

-- Time indexing (for clarity, synonym of function appliation at any level)
_at_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f at n = f n
infixl 45 _at_

-- Substitution with identity predicate – explicit rewriting
rew : ∀{x y : Set} -> x ≡ y -> x -> y
rew p x = subst (λ a -> a) p x

-- (Very verbose) comparison view
-- Like 'compare', but only distinguishes ≤ or >.
data LeqOrdering : ℕ -> ℕ -> Set where
    snd==[_+_]    : ∀ k l → LeqOrdering k           (k + l)
    fst==suc[_+_] : ∀ k l → LeqOrdering (k + suc l) k

compareLeq : ∀ n k -> LeqOrdering n k
compareLeq zero               k    = snd==[ zero + k ]
compareLeq (suc n)            zero = fst==suc[ zero + n ]
compareLeq (suc n)            (suc k) with compareLeq n k
compareLeq (suc n)            (suc .(n + l)) | snd==[ .n + l ] =
    snd==[ suc n + l ]
compareLeq (suc .(k + suc l)) (suc k)        | fst==suc[ .k + l ] =
    fst==suc[ suc k + l ]
