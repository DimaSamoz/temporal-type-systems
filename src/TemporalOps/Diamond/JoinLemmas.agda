
{- Definition of join for ◇ and associated lemmas. -}
module TemporalOps.Diamond.JoinLemmas where

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import TemporalOps.Common
open import TemporalOps.Next
open import TemporalOps.Delay
open import TemporalOps.Diamond.Functor
open import TemporalOps.Diamond.Join

import Relation.Binary.PropositionalEquality as ≡
open import Data.Product
open import Relation.Binary.HeterogeneousEquality as ≅
            using (_≅_ ; ≅-to-≡ ; ≡-to-≅ ; cong₂)
open import Data.Nat.Properties
            using (+-identityʳ ; +-comm ; +-suc ; +-assoc)

-- | Auxiliary lemmas

-- Equality of two delayed values
◇-≅ : ∀{A : τ}{n n′ k k′ : ℕ}
          -> {v : delay A by k at n} {v′ : delay A by k′ at n′}
          -> (pk : k ≡ k′) (pn : n ≡ n′)
          -> v ≅ v′
          -> _≅_ {A = ◇ A at n} (k , v)
                 {B = ◇ A at n′} (k′ , v′)
◇-≅ refl refl ≅.refl = ≅.refl

-- | Lemmas involving μ

-- Two consecutive shifts can be composed
μ-shift-comp : ∀{A} {n k l : ℕ} {a : ◇ A at n}
            -> μ-shift l (k + n) (μ-shift {A} k n a)
             ≅ μ-shift {A} (l + k) n a
μ-shift-comp {A} {n} {k} {l} {j , v} =
    begin
        μ-shift l (k + n) (μ-shift k n (j , v))
    ≡⟨⟩
        μ-shift l (k + n) (k + j , v′)
    ≡⟨⟩
        l + (k + j) , rew (sym (delay-+ l (k + j) (k + n))) v′
    ≅⟨ ◇-≅ (sym (+-assoc l k j)) ((sym (+-assoc l k n))) pr ⟩
        (l + k) + j , rew (sym (delay-+ (l + k) j n)) v
    ≡⟨⟩
        μ-shift (l + k) n (j , v)
    ∎
    where
    open ≅.≅-Reasoning
    v′ : delay A by (k + j) at (k + n)
    v′ = rew (sym (delay-+ k j n)) v
    v≅v′ : v ≅ v′
    v≅v′ = rew-to-≅ (sym (delay-+ k j n))
    pr : rew (sym (delay-+ l (k + j) (k + n))) v′
        ≅ rew (sym (delay-+ (l + k) j n)) v
    pr = delay-assoc-sym l k j n v′ v (≅.sym v≅v′)

private module μ = _⟹_ μ-◇
open ≅.≅-Reasoning

-- Shift and multiplication can be interchanged
μ-interchange : ∀{A}{n k : ℕ}{a : ◇ ◇ A at n}
             -> μ.at A (k + n) (μ-shift k n a)
              ≅ μ-shift k n (μ.at A n a)
μ-interchange {A} {n} {k} {l , y} with inspect (compareLeq l n)
μ-interchange {A} {.(l + m)} {k} {l , v} | snd==[ .l + m ] with≡ pf =
    begin
        μ.at A (k + (l + m)) (μ-shift k (l + m) (l , v))
    ≡⟨⟩
        μ.at A (k + (l + m)) (k + l , rew (sym (delay-+ k l (l + m))) v)
    ≡⟨⟩
        μ-compare A (k + (l + m)) (k + l) v′ (compareLeq (k + l) (k + (l + m)))
    ≅⟨
        ≅-cong₃ (λ x y z → μ-compare A x (k + l) y z)
            (≡-to-≅ (sym (+-assoc k l m))) v′≅v″ (compare-snd-+-assoc l m k pf)
     ⟩
        μ-compare A ((k + l) + m) (k + l) v″ (snd==[ (k + l) + m ])
    ≡⟨⟩
        μ-shift (k + l) m (rew (delay-+-left0 (k + l) m) v″)
    ≡⟨ cong (λ x → μ-shift (k + l) m x) (pr k l m v″ v v″≅v) ⟩
        μ-shift (k + l) m (rew (delay-+-left0 l m) v)
    ≅⟨ ≅.sym ( μ-shift-comp {A} {m} {l} {k} {(rew (delay-+-left0 l m) v)} ) ⟩
        μ-shift k (l + m) (μ-shift l m (rew (delay-+-left0 l m) v))
    ≡⟨⟩
        μ-shift k (l + m) (μ-compare A (l + m) l v (snd==[ l + m ]))
    ≡⟨ cong (λ x → μ-shift k (l + m) (μ-compare A (l + m) l v x)) (sym pf) ⟩
        μ-shift k (l + m) (μ-compare A (l + m) l v (compareLeq l (l + m)))
    ≡⟨⟩
        μ-shift k (l + m) (μ.at A (l + m) (l , v))
    ∎
    where
    v′ : delay ◇ A by (k + l) at (k + (l + m))
    v′ = rew (sym (delay-+ k l (l + m))) v
    v≅v′ : v ≅ v′
    v≅v′ = rew-to-≅ (sym (delay-+ k l (l + m)))
    lemma-assoc : ∀{A : τ} -> (a b c : ℕ)
              -> delay ◇ A by (a + b) at (a + (b + c))
               ≡ delay ◇ A by (a + b) at ((a + b) + c)
    lemma-assoc a b c rewrite sym (+-assoc a b c) = refl
    v″ : delay ◇ A by (k + l) at ((k + l) + m)
    v″ = (rew (lemma-assoc k l m) v′)
    v′≅v″ : v′ ≅ v″
    v′≅v″ = rew-to-≅ (lemma-assoc k l m)
    v″≅v : v″ ≅ v
    v″≅v = ≅.trans (≅.sym v′≅v″) (≅.sym v≅v′)
    pr : ∀{A} (k l m : ℕ) -> Proof-≡ (delay-+-left0 {A} (k + l) m)
                                     (delay-+-left0 {A} l m)
    pr zero l m v .v ≅.refl = refl
    pr (suc k) l m = pr k l m

-- l = n + suc j
μ-interchange {A} {.n} {k} {.(n + suc l) , v} | fst==suc[ n + l ] with≡ pf =
    begin
        μ.at A (k + n) (μ-shift k n (n + suc l , v))
    ≡⟨⟩
        μ.at A (k + n) (k + (n + suc l) , rew (sym (delay-+ k (n + suc l) n)) v)
    ≡⟨⟩
        μ-compare A (k + n) (k + (n + suc l)) v′ (compareLeq (k + (n + suc l)) (k + n))
    ≅⟨ ≅-cong₃ ((λ x y z → μ-compare A (k + n) x y z))
            (≡-to-≅ (sym (+-assoc k n (suc l)))) v′≅v″ (compare-fst-+-assoc n l k pf) ⟩
        μ-compare A (k + n) ((k + n) + suc l) v″ fst==suc[ (k + n) + l ]
    ≡⟨⟩
        (k + n) + suc l , rew (delay-⊤ (k + n) l) top.tt
    ≅⟨ ◇-≅ (+-assoc k n (suc l)) refl (pr n k l) ⟩
        k + (n + suc l) , rew (sym (delay-+ k (n + suc l) n)) (rew (delay-⊤ n l) top.tt)
    ≡⟨⟩
        μ-shift k n (n + suc l , rew (delay-⊤ n l) top.tt)
    ≡⟨⟩
        μ-shift k n (μ-compare A n (n + suc l) v (fst==suc[ n + l ]))
    ≡⟨ cong (λ x → μ-shift k n (μ-compare A n (n + suc l) v x)) (sym pf) ⟩
        μ-shift k n (μ-compare A n (n + suc l) v (compareLeq (n + suc l) n))
    ≡⟨⟩
        μ-shift k n (μ.at A n (n + suc l , v))
    ∎
    where
    v′ : delay ◇ A by (k + (n + suc l)) at (k + n)
    v′ = (rew (sym (delay-+ k (n + suc l) n)) v)
    lemma-assoc : ∀{A : τ} -> (a b c : ℕ)
              -> delay ◇ A by (a + (b + c)) at (a + b)
               ≡ delay ◇ A by ((a + b) + c) at (a + b)
    lemma-assoc {A} a b c rewrite sym (+-assoc a b c) = refl
    v″ : delay ◇ A by ((k + n) + suc l) at (k + n)
    v″ = (rew (lemma-assoc k n (suc l)) v′)
    v′≅v″ : v′ ≅ v″
    v′≅v″ = rew-to-≅ (lemma-assoc k n (suc l))
    pr : ∀{A} (n k l : ℕ)
      -> rew (delay-⊤ {A} (k + n) l) top.tt
       ≅ rew (sym (delay-+ {A} k (n + suc l) n)) (rew (delay-⊤ n l) top.tt)
    pr n zero l = ≅.refl
    pr n (suc k) l = pr n k l
