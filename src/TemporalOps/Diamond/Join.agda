
{- Definition of join for ◇ and associated lemmas. -}
module TemporalOps.Diamond.Join where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import TemporalOps.Common
open import TemporalOps.Next
open import TemporalOps.Delay
open import TemporalOps.Diamond.Functor

import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.HeterogeneousEquality as ≅
            using (_≅_ ; ≅-to-≡ ; ≡-to-≅ ; cong₂)
open import Data.Nat.Properties
            using (+-identityʳ ; +-comm ; +-suc ; +-assoc)


-- | Auxiliary definitions for μ

-- Shifting an event by some interval
μ-shift : {A : τ} -> (k n : ℕ) -> ◇ A at n -> ◇ A at (k + n)
μ-shift {A} k n (l , v) = k + l , rew (sym (delay-+ k l n)) v

-- Auxiliary function for μ, taking the comparison of the delay and
-- time index as an argument
μ-compare : (A : τ) -> (n k : ℕ) -> (v : delay ◇ A by k at n)
         -> LeqOrdering k n -> ◇ A at n
μ-compare A .(k + l) k  v snd==[ .k + l ] =
        μ-shift k l (rew (delay-+-left0 k l) v)
μ-compare A n .(n + suc l) v fst==suc[ .n + l ] =
        n + suc l , rew (delay-⊤ n l) top.tt

private module F-◇ = Functor F-◇


-- Join for ◇
μ-◇ : (F-◇ ²) ⟹ F-◇
μ-◇ = record
    { at = μ-◇-at
    ; nat-cond = λ {A} {B} {f} {n} {a}
                -> μ-◇-nat-cond {A} {B} {f} {n} {a}
    }
    where
    open Functor
    private module F-▹ = Functor F-▹
    open ≡.≡-Reasoning

    -- The order of mapping and shifting of events can be interchanged
    μ-shift-fmap : {A B : τ} {f : A ~> B} {k l : ℕ} {a : ◇ A at l}
                -> F-◇.fmap f (k + l) (μ-shift {A} k l a)
                 ≡ μ-shift {B} k l (F-◇.fmap f l a)
    μ-shift-fmap {A} {B} {f} {zero} {l} {j , y} = refl
    μ-shift-fmap {A} {B} {f} {suc k} {l} {j , y}
        rewrite μ-shift-fmap {A} {B} {f} {k} {l} {j , y}
        = cong (λ x → suc k + j , x) (fmap-delay-+-k k j l y)

    -- Join for ◇
    μ-◇-at : (A : τ) -> ◇ ◇ A ⇴ ◇ A
    μ-◇-at A n (k , v) = μ-compare A n k v (compareLeq k n)

    -- Naturality proof
    μ-◇-nat-cond : ∀{A B : τ} {f : A ⇴ B} {n : ℕ} {a : ◇ ◇ A at n}
                -> F-◇.fmap f n (μ-◇-at A n a)
                 ≡ μ-◇-at B n (Functor.fmap (F-◇ ²) f n a)
    μ-◇-nat-cond {A} {B} {f} {n} {k , v} with inspect (compareLeq k n)
    -- n = k + l
    μ-◇-nat-cond {A} {B} {f} {.(k + l)} {k , v} | snd==[ .k + l ] with≡ pf =
        begin
            F-◇.fmap f (k + l) (μ-◇-at A (k + l) (k , v))
        ≡⟨⟩ -- Def. of μ-◇-at
            F-◇.fmap f (k + l) (μ-compare A (k + l) k v (compareLeq k (k + l)))
        ≡⟨ cong (λ x → F-◇.fmap f (k + l) (μ-compare A (k + l) k v x)) pf ⟩
            F-◇.fmap f (k + l) (μ-shift k l (rew (delay-+-left0 k l) v))
        ≡⟨ μ-shift-fmap {_}{_}{_}{k}{l}{(rew (delay-+-left0 k l) v)} ⟩
            μ-shift k l (F-◇.fmap f l (rew (delay-+-left0 k l) v))
        ≡⟨ cong (λ x → μ-shift k l (F-◇.fmap f l x)) (≅-to-≡ (delay-+-left0-eq k l v v′ v≅v′)) ⟩
            μ-shift k l (F-◇.fmap f l (rew (delay-+ k 0 l) v′))
        ≡⟨⟩ -- Def. of (F-delay 0).fmap
            μ-shift k l ((Functor.fmap (F-delay 0) (F-◇.fmap f) at l) (rew (delay-+ k 0 l) v′))
        ≡⟨ cong (λ x → μ-shift k l x) (sym (fmap-delay-+-n+k k 0 l v′)) ⟩
            μ-shift k l (rew (delay-+ k 0 l) ((Functor.fmap (F-delay (k + 0)) (F-◇.fmap f) at (k + l)) v′))
        ≡⟨ cong (λ x → μ-shift k l x)
            (sym (≅-to-≡ (delay-+-left0-eq k l ((Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v)
                                               ((Functor.fmap (F-delay (k + 0)) (F-◇.fmap f) at (k + l)) v′) pr)))
         ⟩
            μ-shift k l (rew (delay-+-left0 k l) ((Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v))
        ≡⟨⟩ -- Def. of μ-compare
            μ-compare B (k + l) k ((Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v) (snd==[ k + l ])
        ≡⟨ cong (λ x → μ-compare B (k + l) k ((Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v) x) (sym pf) ⟩
            μ-compare B (k + l) k ((Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v) (compareLeq k (k + l))
        ≡⟨⟩ -- Folding definitions
            μ-◇-at B (k + l) (fmap (F-◇ ²) f (k + l) (k , v))
        ∎
        where
        v′ : delay (◇ A) by (k + 0) at (k + l)
        v′ = rew (delay-+0-left k (k + l)) v
        v≅v′ : v ≅ v′
        v≅v′ = rew-to-≅ (delay-+0-left k (k + l))
        pr : (Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v
           ≅ (Functor.fmap (F-delay (k + 0)) (F-◇.fmap f) at (k + l)) v′
        pr = cong₂ (λ x y → (Functor.fmap (F-delay x) (F-◇.fmap f) at (k + l)) y) (≡-to-≅ (sym (+-identityʳ k))) v≅v′

    -- k = suc n + l
    μ-◇-nat-cond {A} {B} {f} {.n} {.(n + suc l) , v} | fst==suc[ n + l ] with≡ pf =
        begin
            F-◇.fmap f n (μ-◇-at A n (n + suc l , v))
        ≡⟨⟩ -- Def. of μ-◇-at
            F-◇.fmap f n (μ-compare A n (n + suc l) v (compareLeq (n + suc l) n))
        ≡⟨ cong (λ x → F-◇.fmap f n (μ-compare A n (n + suc l) v x)) pf ⟩
            F-◇.fmap f n (n + suc l , rew (delay-⊤ n l) top.tt)
        ≡⟨⟩ -- Def. of F-◇.fmap
            n + suc l , (Functor.fmap (F-delay (n + suc l)) f at n) (rew (delay-⊤ n l) top.tt)
        ≡⟨ cong (λ x → n + suc l , x) (eq n l) ⟩
            n + suc l , rew (delay-⊤ n l) top.tt
        ≡⟨⟩ -- Def. of μ-compare
            μ-compare B n (n + suc l) ((Functor.fmap (F-delay ((n + suc l))) (F-◇.fmap f) at n) v) (fst==suc[ n + l ])
        ≡⟨ cong (λ x → μ-compare B n (n + suc l) ((Functor.fmap (F-delay (n + suc l)) (F-◇.fmap f) at n) v) x) (sym pf) ⟩
            μ-compare B n (n + suc l) ((Functor.fmap (F-delay (n + suc l)) (F-◇.fmap f) at n) v) (compareLeq (n + suc l) n)
        ≡⟨⟩ -- Def. of μ-◇-at
            μ-◇-at B n (Functor.fmap (F-◇ ²) f n (n + suc l , v))
        ∎
        where
        eq : ∀ (n l : ℕ)
          -> (Functor.fmap (F-delay (n + suc l)) f at n) (rew (delay-⊤ n l) top.tt)
           ≡ rew (delay-⊤ n l) top.tt
        eq zero l = refl
        eq (suc n) l = eq n l
