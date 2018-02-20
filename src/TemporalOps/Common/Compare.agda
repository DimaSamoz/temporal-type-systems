
{- Comparison view and associated lemmas -}
module TemporalOps.Common.Compare where

open import CategoryTheory.Categories
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.HeterogeneousEquality as ≅
open import Data.Nat.Properties using (+-identityʳ ; +-assoc ; +-suc)
open import Data.Nat using (ℕ ; zero ; suc ; _+_) public

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
    ≅⟨ ≅.cong (λ x → compareLeq (l + n) x) (≡-to-≅ (≡.sym (+-assoc l n k))) ⟩
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
    ≅⟨ ≅.cong (λ x → compareLeq x (l + n)) (≡-to-≅ (≡.sym (+-assoc l n (suc k)))) ⟩
        compareLeq ((l + n) + suc k) (l + n)
    ≅⟨ ≡-to-≅ (compare-fst-+ n k l pf) ⟩
        fst==suc[ (l + n) + k ]
    ∎
    where
    open ≅.≅-Reasoning
