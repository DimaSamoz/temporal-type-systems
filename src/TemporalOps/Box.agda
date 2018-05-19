
{- Box operator. -}
module TemporalOps.Box where

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Sets
open import CategoryTheory.Instances.Reactive
open import CategoryTheory.BCCCs
open import CategoryTheory.Functor
open import CategoryTheory.CartesianStrength
open import CategoryTheory.NatTrans
open import CategoryTheory.Adjunction
open import CategoryTheory.Comonad
open import TemporalOps.Common

-- The box operator can be derived as a comonad from an adjunction K ⊣ G

K : Functor 𝕊et ℝeactive
K = record
  { omap = λ A -> (λ n -> A)
  ; fmap = λ f -> (λ n -> λ x -> f x)
  ; fmap-id = refl
  ; fmap-∘ = refl
  ; fmap-cong = λ z → z
  }

G : Functor ℝeactive 𝕊et
G = record
  { omap = λ A -> (∀(n : ℕ) -> A n)
  ; fmap = λ f -> λ a -> (λ n -> f n (a n))
  ; fmap-id = refl
  ; fmap-∘ = refl
  ; fmap-cong = λ pf → ext (λ n → pf)
  }

K⊣G : K ⊣ G
K⊣G = record
    { η = record
        { at = λ A x n → x
        ; nat-cond = refl }
    ; ε = record
        { at = λ A n a → a n
        ; nat-cond = refl }
    ; tri1 = refl
    ; tri2 = refl
    }

-- | Box operator

-- Comonad instance from adjunction
W-□ : Comonad ℝeactive
W-□ = AdjComonad K⊣G

-- Endofunctor from comonad
F-□ : Endofunctor ℝeactive
F-□ = Comonad.W W-□

-- Operator from functor
□_ : τ -> τ
□_ = Functor.omap (Comonad.W W-□)
infixr 65 □_

-- Extensional equality for boxed values
□-≡ : ∀{A} n l {v : (□ A) n}{w : (□ A) l}
   -> v ≡ w
   -> ∀ m -> v m ≡ w m
□-≡ n l refl m = refl

-- □ is a Cartesian functor
F-cart-□ : CartesianFunctor F-□ ℝeactive-cart ℝeactive-cart
F-cart-□ = record
    { u = λ n a _ → a
    ; m = m-□
    ; associative = refl
    ; unital-right = refl
    ; unital-left = refl
    }
    where
    m-□ : ∀(A B : τ) -> □ A ⊗ □ B ⇴ □ (A ⊗ B)
    m-□ A B n (a , b) = λ k → a k , b k

open CartesianFunctor F-cart-□ public

-- □ is a Cartesian comonad
W-cart-□ : CartesianComonad W-□ ℝeactive-cart
W-cart-□ = record { cart-fun = F-cart-□ ; u-ε = refl ; u-δ = refl
                                        ; m-ε = refl ; m-δ = refl }

open CartesianComonad W-cart-□ public
