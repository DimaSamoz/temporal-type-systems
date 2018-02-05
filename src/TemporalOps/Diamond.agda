
{- Diamond operator. -}
module TemporalOps.Diamond where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import TemporalOps.Common
open import TemporalOps.Next
open import TemporalOps.Delay

open import Data.Nat.Properties using (+-identityʳ ; +-comm)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; ≅-to-≡ ; ≡-to-≅ )

open Category ℝeactive

-- Arbitrary delay
◇_ : τ -> τ
(◇ A) n = Σ ℕ (λ k -> delay A by k at n)
infixr 65 ◇_

-- ◇ instances
F-◇ : Endofunctor ℝeactive
F-◇ = record
    { omap = ◇_
    ; fmap = fmap-◇
    ; fmap-id = fmap-◇-id
    ; fmap-∘ = fmap-◇-∘
    ; fmap-cong = fmap-◇-cong
    }
    where
    -- Lifting of ◇
    fmap-◇ : {A B : τ} -> A ⇴ B -> ◇ A ⇴ ◇ B
    fmap-◇ f n (k , v) = k , (Functor.fmap (F-delay k) f at n) v
    -- ◇ preserves identities
    fmap-◇-id : ∀ {A : τ} {n : ℕ} {a : (◇ A) n}
             -> (fmap-◇ (id {A}) at n) a ≡ a
    fmap-◇-id {A} {n} {zero , v} = refl
    fmap-◇-id {A} {zero} {suc k , v} = refl
    fmap-◇-id {A} {suc n} {suc k , v}
        rewrite delay-+ {A} 1 k n
              | Functor.fmap-id (F-delay (suc k)) {A} {suc n} {v}
        = refl
    -- ◇ preserves composition
    fmap-◇-∘ : ∀ {A B C : τ} {g : B ⇴ C} {f : A ⇴ B} {n : ℕ} {a : (◇ A) n}
            -> (fmap-◇ (g ∘ f) at n) a ≡ (fmap-◇ g ∘ fmap-◇ f at n) a
    fmap-◇-∘ {n = n} {zero , v} = refl
    fmap-◇-∘ {n = zero} {suc k , v} = refl
    fmap-◇-∘ {A} {B} {C} {g} {f} {suc n} {suc k , v}
        rewrite delay-+ {A} 1 k n
              | Functor.fmap-∘ (F-delay (suc k)) {A} {B} {C} {g} {f} {suc n} {v}
        = refl
    -- ▹ is congruent
    fmap-◇-cong : ∀{A B : τ} {f f′ : A ⇴ B}
            -> ({n : ℕ} {a : A at n}   -> f n a ≡ f′ n a)
            -> ({n : ℕ} {a : ◇ A at n} -> (fmap-◇ f at n) a
                                        ≡ (fmap-◇ f′ at n) a)
    fmap-◇-cong {A} e {n} {zero , a}
        rewrite delay-+-left0 {A} 0 n
              | e {n} {a} = refl
    fmap-◇-cong e {zero} {suc k , a} = refl
    fmap-◇-cong {A} {B} {f} {f′} e {suc n} {suc k , a}
        rewrite delay-+ {A} 1 k n
              | Functor.fmap-cong (F-delay (suc k)) {A} {B} {f} {f′} e {suc n} {a}
              = refl

M-◇ : Monad ℝeactive
M-◇ = record
    { T = F-◇
    ; η = η-◇
    ; μ = μ-◇
    ; η-unit1 = refl
    ; η-unit2 = {!   !}
    ; μ-assoc = {!   !} }
    where
    η-◇ : I ⟹ F-◇
    η-◇ = record
        { at = λ A n x -> 0 , x
        ; nat-cond = λ {A} {B} {f} {n} {a} → refl }

    μ-◇ : (F-◇ ²) ⟹ F-◇
    μ-◇ = record
        { at = μ-◇-at
        ; nat-cond = λ {A} {B} {f} {n} {a}
                    -> μ-◇-nat-cond {A} {B} {f} {n} {a}
        }
        where
        open ≡.≡-Reasoning
        open Functor
        private module F-▹ = Functor F-▹
        private module F-◇ = Functor F-◇

        -- || Multiplication definition
        -- Shifting an event by some interval
        μ-shift : {A : τ} -> (k l : ℕ) -> ◇ A at l -> ◇ A at (k + l)
        μ-shift {A} k l (j , y) = k + j , rew (sym (delay-+ k j l)) y

        μ-shift-fmap : {A B : τ} {f : A ~> B} {k l : ℕ} {a : ◇ A at l}
                    -> F-◇.fmap f (k + l) (μ-shift {A} k l a)
                     ≡ μ-shift {B} k l (F-◇.fmap f l a)
        μ-shift-fmap {A} {B} {f} {zero} {l} {j , y} = refl
        μ-shift-fmap {A} {B} {f} {suc k} {l} {j , y}
            rewrite μ-shift-fmap {A} {B} {f} {k} {l} {j , y}
            = cong (λ x → suc k + j , x) (fmap-delay-+-k k j l y)

        -- Auxiliary function for μ, taking the comparison of the delay and
        -- time index as an argument
        μ-compare : (A : τ) -> (n k : ℕ) -> (v : delay ◇ A by k at n)
                 -> LeqOrdering k n -> ◇ A at n
        μ-compare A .(k + l) k  v snd==[ .k + l ] =
            μ-shift k l (rew (delay-+-left0 k l) v)

        μ-compare A n .(n + suc l) v fst==suc[ .n + l ] =
            let eq : delay ◇ A by (n + suc l) at n
                   ≡ delay A by (n + suc l) at n
                eq = trans (delay-+-right0 n (suc l))
                           (sym (delay-+-right0 n (suc l)))
            in (n + suc l) , rew eq v

        -- Join for ◇
        μ-◇-at : (A : τ) -> ◇ ◇ A ⇴ ◇ A
        μ-◇-at A n (k , v) = μ-compare A n k v (compareLeq k n)

        -- Naturality proof

        foo : ∀(k n : ℕ) -> Σ (LeqOrdering k n) (λ y -> y ≡ compareLeq k n)
        foo k n = compareLeq k n , refl

        μ-◇-nat-cond : ∀{A B : τ} {f : A ⇴ B} {n : ℕ} {a : ◇ ◇ A at n}
                    -> Functor.fmap F-◇ f n (μ-◇-at A n a)
                     ≡ μ-◇-at B n (Functor.fmap (F-◇ ²) f n a)
        -- μ-◇-nat-cond {A} {B} {f} {n} {k , v} = {!   !}
        μ-◇-nat-cond {A} {B} {f} {n} {k , v}  with inspect (compareLeq k n)
        μ-◇-nat-cond {A} {B} {f} {.(k + l)} {k , v} | snd==[ .k + l ] with≡ pf =
            ≡.≡-Reasoning.begin
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
                                                      ((Functor.fmap (F-delay (k + 0)) (F-◇.fmap f) at (k + l)) v′) pr))) ⟩
                μ-shift k l (rew (delay-+-left0 k l) ((Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v))
            ≡⟨⟩ -- Def. of μ-compare
                μ-compare B (k + l) k ((Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v) (snd==[ k + l ])
            ≡⟨ cong (λ x → μ-compare B (k + l) k ((Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v) x) (sym pf) ⟩
                μ-compare B (k + l) k ((Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v) (compareLeq k (k + l))
            ≡⟨⟩ -- Folding definitions
                μ-◇-at B (k + l) (fmap (F-◇ ²) f (k + l) (k , v))
            ≡.≡-Reasoning.∎
            where
            private module ≅ = Relation.Binary.HeterogeneousEquality
            v′ : delay (◇ A) by (k + 0) at (k + l)
            v′ = rew (delay-+0-left k (k + l)) v
            v≅v′ : v ≅ v′
            v≅v′ = rew-to-≅ (delay-+0-left k (k + l))
            pr : (Functor.fmap (F-delay k) (F-◇.fmap f) at (k + l)) v
              ≅ (Functor.fmap (F-delay (k + 0)) (F-◇.fmap f) at (k + l)) v′
            pr = ≅.cong₂ (λ x y → (Functor.fmap (F-delay x) (F-◇.fmap f) at (k + l)) y) (≡-to-≅ (sym (+-identityʳ k))) v≅v′

        μ-◇-nat-cond {A} {B} {f} {.k} {.(k + suc l) , v} | fst==suc[ k + l ] with≡ x = {!   !}
