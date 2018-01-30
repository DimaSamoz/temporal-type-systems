
{- Next step operator. -}
module TemporalOps.Next where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import TemporalOps.Common

-- One-step delay operator.
▹_ : τ -> τ
▹_ A zero    = ⊤ zero
▹_ A (suc n) = A n
infixr 70 ▹_


open CategoryTheory.Categories.Category {{...}}


-- || Functor and endofunctor instances

-- ▹ instances
instance
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
        fmap-▹-id : ∀ {A : τ} {n : ℕ} {a : (▹ A) n}
                 -> (fmap-▹ (id {A}) at n) a ≡ a
        fmap-▹-id {n = zero} = refl
        fmap-▹-id {n = suc n} = refl
        -- ▹ preserves composition
        fmap-▹-∘ : ∀ {A B C : τ} {g : B ⇴ C} {f : A ⇴ B} {n : ℕ} {a : (▹ A) n}
                -> (fmap-▹ (g ∘ f) at n) a ≡ (fmap-▹ g ∘ fmap-▹ f at n) a
        fmap-▹-∘ {n = zero} = refl
        fmap-▹-∘ {n = suc n} = refl
        -- ▹ is congruent
        fmap-▹-cong : ∀{A B : τ} {f f′ : A ⇴ B}
                -> ({n : ℕ} {a : A at n}     -> f n a ≡ f′ n a)
                -> ({n : ℕ} {a : ▹ A at n} -> (fmap-▹ f at n) a
                                          ≡ (fmap-▹ f′ at n) a)
        fmap-▹-cong e {zero} = refl
        fmap-▹-cong e {suc n} = e
