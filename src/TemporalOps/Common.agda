
{- Auxiliary functions for temporal operators. -}
module TemporalOps.Common where

open import CategoryTheory.Categories
open import Relation.Binary.HeterogeneousEquality
    using (_≅_)

-- open import Relation.Binary.PropositionalEquality using (_≡_)

-- Time indexing (for clarity, synonym of function appliation at any level)
_at_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f at n = f n
infixl 45 _at_

-- Substitution with identity predicate – explicit rewriting
rew : ∀{ℓ}{x y : Set ℓ} -> x ≡ y -> x -> y
rew p x = subst (λ a -> a) p x

-- Rewriting preserves heterogeneous equality
rew-to-≅ : ∀{ℓ}{x y : Set ℓ}{v : x} -> (p : x ≡ y) -> v ≅ rew p v
rew-to-≅ {x = x} {.x} {v} refl = _≅_.refl

-- Heterogenous equality can be converted to homogeneous equality via rewriting
≅-to-rew-≡ : ∀ {P Q : Set} {x : P} {y : Q}
            -> (p : x ≅ y) -> (e : P ≡ Q)
            -> rew e x ≡ y
≅-to-rew-≡ _≅_.refl refl = refl

-- (Very verbose) comparison view
-- Like 'compare', but only distinguishes ≤ or >.
data LeqOrdering : ℕ -> ℕ -> Set where
    snd==[_+_]    : ∀ k l → LeqOrdering k           (k + l)
    fst==suc[_+_] : ∀ k l → LeqOrdering (k + suc l) k

-- Auxiliary function to compareLeq
compareLeq-suc : ∀ n k -> LeqOrdering n k -> LeqOrdering (suc n) (suc k)
compareLeq-suc n .(n + l)     snd==[ .n + l ]    = snd==[ suc n + l ]
compareLeq-suc .(k + suc l) k fst==suc[ .k + l ] = fst==suc[ suc k + l ]

compareLeq : ∀ n k -> LeqOrdering n k
compareLeq zero k          = snd==[ zero + k ]
compareLeq (suc n) zero    = fst==suc[ zero + n ]
compareLeq (suc n) (suc k) = compareLeq-suc n k (compareLeq n k)

-- Inspect idiom
data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl
