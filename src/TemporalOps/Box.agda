
{- Box operator. -}
module TemporalOps.Box where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import TemporalOps.Common

-- Box operator
□_ : τ -> τ
(□_ A) n = (n : ℕ) -> A n
infixr 65 □_

-- □ instances
instance
    F-□ : Functor ℝeactive ℝeactive
    F-□ = record
        { omap = □_
        ; fmap = fmap-□
        ; fmap-id = refl
        ; fmap-∘ = refl
        }
        where
        -- Lifting of □
        fmap-□ : {A B : τ} -> A ⇴ B -> □ A ⇴ □ B
        fmap-□ f n a = λ k → f k (a k)

    EF-□ : Endofunctor ℝeactive
    EF-□ = record { functor = F-□ }
