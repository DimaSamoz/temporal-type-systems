
{- Diamond operator. -}
module TemporalOps.Diamond where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import TemporalOps.Common
open import TemporalOps.Next
open import TemporalOps.Delay

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Category ℝeactive

-- Arbitrary delay
◇_ : τ -> τ
(◇ A) n = Σ ℕ (λ k -> delay A by k at n)
infixr 65 ◇_

-- ◇ instances
instance
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
            rewrite delay-plus {A} 1 k n
                  | Functor.fmap-id (F-delay (suc k)) {A} {suc n} {v}
            = refl
        -- ◇ preserves composition
        fmap-◇-∘ : ∀ {A B C : τ} {g : B ⇴ C} {f : A ⇴ B} {n : ℕ} {a : (◇ A) n}
                -> (fmap-◇ (g ∘ f) at n) a ≡ (fmap-◇ g ∘ fmap-◇ f at n) a
        fmap-◇-∘ {n = n} {zero , v} = refl
        fmap-◇-∘ {n = zero} {suc k , v} = refl
        fmap-◇-∘ {A} {B} {C} {g} {f} {suc n} {suc k , v}
            rewrite delay-plus {A} 1 k n
                  | Functor.fmap-∘ (F-delay (suc k)) {A} {B} {C} {g} {f} {suc n} {v}
            = refl
        -- ▹ is congruent
        fmap-◇-cong : ∀{A B : τ} {f f′ : A ⇴ B}
                -> ({n : ℕ} {a : A at n}   -> f n a ≡ f′ n a)
                -> ({n : ℕ} {a : ◇ A at n} -> (fmap-◇ f at n) a
                                            ≡ (fmap-◇ f′ at n) a)
        fmap-◇-cong {A} e {n} {zero , a}
            rewrite delay-plus-left0 {A} 0 n
                  | e {n} {a} = refl
        fmap-◇-cong e {zero} {suc k , a} = refl
        fmap-◇-cong {A} {B} {f} {f′} e {suc n} {suc k , a}
            rewrite delay-plus {A} 1 k n
                  | Functor.fmap-cong (F-delay (suc k)) {A} {B} {f} {f′} e {suc n} {a}
                  = refl

instance
    M-◇ : Monad ℝeactive
    M-◇ = record
        { T = F-◇
        ; η = η-◇
        ; μ = {!   !}
        ; η-unit1 = {!   !}
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
            ; nat-cond = {!   !} }
            where
            μ-compare : (A : τ) -> (n : ℕ) -> (a : ◇ ◇ A at n) -> LeqOrdering (proj₁ a) n -> ◇ A at n
            μ-compare A .(k + l) (k , v) snd==[ .k + l ] =
                μ-split (rew (delay-plus-left0 k l) v)
                where
                μ-split : ◇ A at l ->  ◇ A at (k + l)
                μ-split (j , y) = k + j , rew (sym (delay-plus k j l)) y
            μ-compare A n (.(n + suc l) , v) fst==suc[ .n + l ] =
                (n + suc l) , rew eq v
                where
                eq : delay ◇ A by (n + suc l) at n
                   ≡ delay A by (n + suc l) at n
                eq = trans (delay-plus-right0 n (suc l))
                           (sym (delay-plus-right0 n (suc l)))

            μ-◇-at : (A : τ) -> ◇ ◇ A ⇴ ◇ A
            μ-◇-at A n a@(k , v) = μ-compare A n a (compareLeq k n)

            μ-◇-nat-cond : ∀{A B : τ} {f : A ⇴ B} {n : ℕ} {a : ◇ ◇ A at n}
                        -> Functor.fmap F-◇ f n (μ-◇-at A n a)
                         ≡ μ-◇-at B n (Functor.fmap (F-◇ ²) f n a)
            μ-◇-nat-cond {A} {B} {f} {n} {k , v} with compareLeq k n
            μ-◇-nat-cond {A} {B} {f} {.(k + l)} {k , v} | snd==[ .k + l ]
                = ≡.≡-Reasoning.begin
                    {!   !}
                ≡⟨ {!   !} ⟩
                    {!   !}
                ≡.≡-Reasoning.∎
                where open ≡.≡-Reasoning
            μ-◇-nat-cond {A} {B} {f} {.k} {.(k + suc l) , v} | fst==suc[ k + l ] = {!   !}
