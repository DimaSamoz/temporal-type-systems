
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

-- Inspect idiom
data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl


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

-- Lemmas for compareLeq

-- Comparing n and (n + k) always gives snd==[ n + k ]
compare-snd : ∀ (n k : ℕ) -> compareLeq n (n + k) ≡ snd==[ n + k ]
compare-snd zero k = refl
compare-snd (suc n) k rewrite compare-snd n k = refl

-- If n ≤ n + k, then l + n  ≤ (l + n) + k
compare-snd-+ : ∀ (n k l : ℕ) -> compareLeq n (n + k) ≡ snd==[ n + k ]
             -> compareLeq (l + n) ((l + n) + k) ≡ snd==[ (l + n) + k ]
compare-snd-+ n k zero pf = pf
compare-snd-+ zero k (suc l) pf rewrite +-identityʳ l = compare-snd (suc l) k
compare-snd-+ (suc n) k (suc l) pf
    rewrite +-suc l n | compare-snd (l + n) k = refl

-- Heterogeneous version of compare-snd-+ with associativity
compare-snd-+-assoc : ∀ (n k l : ℕ) -> compareLeq n (n + k) ≡ snd==[ n + k ]
                   -> compareLeq (l + n) (l + (n + k)) ≅ snd==[ (l + n) + k ]
compare-snd-+-assoc n k l pf =
    begin
        compareLeq (l + n) (l + (n + k))
    ≅⟨ ≅.cong (λ x → compareLeq (l + n) x) (≡-to-≅ (sym (+-assoc l n k))) ⟩
        compareLeq (l + n) ((l + n) + k)
    ≅⟨ ≡-to-≅ (compare-snd-+ n k l pf) ⟩
        snd==[ (l + n) + k ]
    ∎
    where
    open ≅.≅-Reasoning

-- Comparing (n + suc k and n always gives fst==suc[ n + k ]
compare-fst : ∀ (n k : ℕ) -> compareLeq (n + suc k) n ≡ fst==suc[ n + k ]
compare-fst zero k = refl
compare-fst (suc n) k rewrite compare-fst n k = refl

-- If n + suc k > n, then (l + n) + suc k  > l + n
compare-fst-+ : ∀ (n k l : ℕ) -> compareLeq (n + suc k) n ≡ fst==suc[ n + k ]
             -> compareLeq ((l + n) + suc k) (l + n) ≡ fst==suc[ (l + n) + k ]
compare-fst-+ n k zero pf = pf
compare-fst-+ zero k (suc l) pf rewrite +-identityʳ l = compare-fst (suc l) k
compare-fst-+ (suc n) k (suc l) pf
    rewrite +-suc l n | compare-fst (l + n) k = refl

-- Heterogeneous version of compare-fst-+ with associativity
compare-fst-+-assoc : ∀ (n k l : ℕ) -> compareLeq (n + suc k) n ≡ fst==suc[ n + k ]
                   -> compareLeq (l + (n + suc k)) (l + n) ≅ fst==suc[ (l + n) + k ]
compare-fst-+-assoc n k l pf =
    begin
        compareLeq (l + (n + suc k)) (l + n)
    ≅⟨ ≅.cong (λ x → compareLeq x (l + n)) (≡-to-≅ (sym (+-assoc l n (suc k)))) ⟩
        compareLeq ((l + n) + suc k) (l + n)
    ≅⟨ ≡-to-≅ (compare-fst-+ n k l pf) ⟩
        fst==suc[ (l + n) + k ]
    ∎
    where
    open ≅.≅-Reasoning
