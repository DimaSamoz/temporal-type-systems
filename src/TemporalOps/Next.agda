
{- Next step operator. -}
module TemporalOps.Next where

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import CategoryTheory.CartesianStrength
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

-- ▹ is a Cartesian functor
F-cart-▹ : CartesianFunctor F-▹ ℝeactive-cart ℝeactive-cart
F-cart-▹ = record
    { u = u-▹
    ; m = m-▹
    ; m-nat₁ = m-nat₁-▹
    ; m-nat₂ = m-nat₂-▹
    ; associative = λ {A}{B}{C}{n}{a} -> assoc-▹ {A}{B}{C}{n}{a}
    ; unital-right = λ {A}{n}{a} -> unit-right-▹ {A}{n}{a}
    ; unital-left = λ {A}{n}{a} -> unit-left-▹ {A}{n}{a}
    }
    where
    open Functor F-▹

    u-▹ : ⊤ ⇴ ▹ ⊤
    u-▹ zero t = top.tt
    u-▹ (suc n) t = top.tt

    m-▹ : ∀(A B : τ) -> ▹ A ⊗ ▹ B ⇴ ▹ (A ⊗ B)
    m-▹ A B zero _ = top.tt
    m-▹ A B (suc n) p = p

    m-nat₁-▹ : ∀{A B C : τ} (f : A ⇴ B)
          -> fmap (f * id) ∘ m-▹ A C ≈ m-▹ B C ∘ fmap f * id
    m-nat₁-▹ f {zero} {a} = refl
    m-nat₁-▹ f {suc n} {a} = refl

    m-nat₂-▹ : ∀{A B C : τ} (f : A ⇴ B)
          -> fmap (id * f) ∘ m-▹ C A ≈ m-▹ C B ∘ id * fmap f
    m-nat₂-▹ f {zero} {a} = refl
    m-nat₂-▹ f {suc n} {a} = refl

    assoc-▹ : ∀{A B C : τ}
           -> m-▹ A (B ⊗ C) ∘ id * m-▹ B C ∘ assoc-right
            ≈ fmap assoc-right ∘ m-▹ (A ⊗ B) C ∘ m-▹ A B * id
    assoc-▹ {A} {B} {C} {zero} {a} = refl
    assoc-▹ {A} {B} {C} {suc n} {(▹A , ▹B) , ▹C} = refl

    unit-right-▹ : ∀{A : τ} ->
        fmap unit-right ∘ m-▹ A ⊤ ∘ (id * u-▹) ≈ unit-right
    unit-right-▹ {A} {zero} {a} = refl
    unit-right-▹ {A} {suc n} {a} = refl

    unit-left-▹ : ∀{A : τ} ->
        fmap unit-left ∘ m-▹ ⊤ A ∘ (u-▹ * id) ≈ unit-left
    unit-left-▹ {A} {zero} {a} = refl
    unit-left-▹ {A} {suc n} {a} = refl

-- ▹ preserves coproducts
sum-▹ : ∀{A B : τ} -> (▹ A ⊕ ▹ B) ⇴ ▹ (A ⊕ B)
sum-▹ zero v = top.tt
sum-▹ (suc n) v = v
