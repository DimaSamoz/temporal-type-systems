
{- Next step operator. -}
module TemporalOps.Next where

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import TemporalOps.Common

open import Data.Product
open import Data.Sum

-- One-step delay operator.
▹_ : τ -> τ
(▹ A) zero    = ⊤ zero
(▹ A) (suc n) = A n
infixr 70 ▹_


-- Functor instance for ▹
F-▹ : Endofunctor ℝeactive
F-▹ = record
    { omap      = ▹_
    ; fmap      = fmap-▹
    ; fmap-id   = λ {_ n} -> fmap-▹-id {n = n}
    ; fmap-∘    = λ {_ _ _ _ _ n} -> fmap-▹-∘ {n = n}
    ; fmap-cong = fmap-▹-cong
    }
    where
    -- Lifting of ▹
    fmap-▹ : {A B : τ} -> A ⇴ B -> ▹ A ⇴ ▹ B
    fmap-▹ f zero =  λ _ → top.tt
    fmap-▹ f (suc n) = f n
    -- ▹ preserves identities
    fmap-▹-id : ∀ {A : τ} {n : ℕ} {a : ▹ A at n}
             -> (fmap-▹ id at n) a ≡ a
    fmap-▹-id {n = zero} = refl
    fmap-▹-id {n = suc n} = refl
    -- ▹ preserves composition
    fmap-▹-∘ : ∀ {A B C : τ} {g : B ⇴ C} {f : A ⇴ B} {n : ℕ} {a : ▹ A at n}
            -> (fmap-▹ (g ∘ f) at n) a ≡ (fmap-▹ g ∘ fmap-▹ f at n) a
    fmap-▹-∘ {n = zero}  = refl
    fmap-▹-∘ {n = suc n} = refl
    -- ▹ is congruent
    fmap-▹-cong : ∀{A B : τ} {f f′ : A ⇴ B}
            -> ({n : ℕ} {a : A at n}   -> f n a ≡ f′ n a)
            -> ({n : ℕ} {a : ▹ A at n} -> (fmap-▹ f at n) a
                                        ≡ (fmap-▹ f′ at n) a)
    fmap-▹-cong e {zero} = refl
    fmap-▹-cong e {suc n} = e

-- ▹ preserves products
pair-▹ : ∀{A B : τ} -> (▹ A ⊗ ▹ B) ⇴ ▹ (A ⊗ B)
pair-▹ {A} {B} zero (▹A , ▹B) = top.tt
pair-▹ {A} {B} (suc n) (▹A , ▹B) = ▹A , ▹B

-- ▹ preserves coproducts
sum-▹ : ∀{A B : τ} -> (▹ A ⊕ ▹ B) ⇴ ▹ (A ⊕ B)
sum-▹ zero v = top.tt
sum-▹ (suc n) v = v
