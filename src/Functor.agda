
{- Functoriality of temporal operators -}
module Functor where

open import Categories
open Categories.Category using (obj)
-- open Category.Category {{...}}
open import TemporalOps
open import Relation.Binary.PropositionalEquality

-- || Functoriality of ◇

-- Lifting of ◇
fmap-◇ : {A B : τ} -> A ⇴ B -> ◇ A ⇴ ◇ B
fmap-◇ f n (k , v) = k , (fmap-delay k f at n) v

-- ◇ preserves identities
fmap-◇-id : ∀{A : τ} {n : ℕ} {a : (◇ A) n}
         -> (fmap-◇ id at n) a ≡ (id {◇ A} at n) a
fmap-◇-id {A} {n} {zero , v} = refl
fmap-◇-id {A} {zero} {suc k , v} = refl
fmap-◇-id {A} {suc n} {suc k , v}
    rewrite delay-plus {A} 1 k n
          | fmap-delay-id {A} {n} {k} = refl

-- ◇ preserves composition
fmap-◇-∘ : ∀ {A B C : τ} {n : ℕ} {a : (◇ A) n} {g : B ⇴ C} {f : A ⇴ B}
        -> (fmap-◇ (g ∘ f) at n) a ≡ (fmap-◇ g ∘ fmap-◇ f at n) a
fmap-◇-∘ {n = n} {zero , v} = refl
fmap-◇-∘ {n = zero} {suc k , v} = refl
fmap-◇-∘ {A} {B} {C} {n = suc n} {suc k , v} {g} {f}
    rewrite delay-plus {A} 1 k n
          | fmap-delay-∘ {A} {B} {C} {n} {k} {g} {f} = refl

-- || Functoriality of □

-- Lifting of □
fmap-□ : {A B : τ} -> A ⇴ B -> □ A ⇴ □ B
fmap-□ f n a = λ k → f k (a k)

-- □ preserves identities
fmap-□-id : ∀{A : τ}
         -> fmap-□ id ≡ id {□ A}
fmap-□-id = refl

-- □ preserves composition
fmap-□-∘ : ∀ {A B C : τ} {g : B ⇴ C} {f : A ⇴ B}
        -> fmap-□ (g ∘ f) ≡ fmap-□ g ∘ fmap-□ f
fmap-□-∘ = refl
-- Functor between two categories
record Functor (ℂ : Category) (𝔻 : Category) : Set₁ where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    field
        -- || Definitions
        -- Object map
        omap : obj ℂ -> obj 𝔻
        -- Arrow map
        fmap : ∀{A B : obj ℂ} -> (A ℂ.~> B) -> (omap A 𝔻.~> omap B)

        -- || Laws
        -- Functor preseres identities
        fmap-id : ∀{A : obj ℂ} -> fmap (ℂ.id {A}) 𝔻.≈ 𝔻.id
        -- Functor preserves composition
        fmap-∘ : ∀{A B C : obj ℂ} {g : B ℂ.~> C} {f : A ℂ.~> B}
              -> fmap (g ℂ.∘ f) 𝔻.≈ fmap g 𝔻.∘ fmap f

-- Endofunctor on a category
record Endofunctor (ℂ : Category) : Set₁ where
    field
        {{functor}} : Functor ℂ ℂ

open Categories.Category {{...}}


-- || Functor and endofunctor instances for temporal operators

-- ▹ instances
instance
    F-▹ : Functor ℝeactive ℝeactive
    F-▹ = record
        { omap = ▹_
        ; fmap = fmap-▹
        ; fmap-id = λ {_ n a} -> fmap-▹-id {_} {n} {a}
        ; fmap-∘ = λ {_ _ _ _ _ n} -> fmap-▹-∘ {n = n}
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

    EF-▹ : Endofunctor ℝeactive
    EF-▹ = record {}

-- Delay instances
instance
    F-delay : ℕ -> Functor ℝeactive ℝeactive
    F-delay k = record
        { omap = delay_by k
        ; fmap = fmap-delay k
        ; fmap-id = λ {_ n a} -> fmap-delay-id k {_} {n} {a}
        ; fmap-∘ = fmap-delay-∘ k
        }
        where
        -- Lifting of delay
        fmap-delay : {A B : τ} -> (k : ℕ) -> A ⇴ B -> delay A by k ⇴ delay B by k
        fmap-delay zero    f = f
        fmap-delay (suc k) f = Functor.fmap F-▹ (fmap-delay k f)
        -- Delay preserves identities
        fmap-delay-id : ∀ (k : ℕ) {A : τ} {n : ℕ} {a : (delay A by k) n}
                 -> (fmap-delay k (id {A}) at n) a ≡ a
        fmap-delay-id zero = refl
        fmap-delay-id (suc k) {A} {zero} = refl
        fmap-delay-id (suc k) {A} {suc n} = fmap-delay-id k {A} {n}
        -- Delay preserves composition
        fmap-delay-∘ : ∀ (k : ℕ) {A B C : τ} {g : B ⇴ C} {f : A ⇴ B} {n : ℕ} {a : (delay A by k) n}
                -> (fmap-delay k (g ∘ f) at n) a ≡ (fmap-delay k g ∘ fmap-delay k f at n) a
        fmap-delay-∘ zero = refl
        fmap-delay-∘ (suc k) {n = zero} = refl
        fmap-delay-∘ (suc k) {n = suc n} = fmap-delay-∘ k {n = n}

    EF-delay : Endofunctor ℝeactive
    EF-delay = record {}


