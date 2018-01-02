
{- Functoriality of temporal operators -}
module Functor where

open import Categories
open Categories.Category using (obj)
-- open Category.Category {{...}}
open import TemporalOps
open import Relation.Binary.PropositionalEquality

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
record Endofunctor (ℂ : Category) (f : Functor ℂ ℂ): Set₁ where
    functor : Functor ℂ ℂ
    functor = f

open Categories.Category {{...}}


-- || Functor and endofunctor instances for temporal operators

-- ▹ instances
instance
    F-▹ : Functor ℝeactive ℝeactive
    F-▹ = record
        { omap = ▹_
        ; fmap = fmap-▹
        ; fmap-id = λ {_ n} -> fmap-▹-id {n = n}
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

    EF-▹ : Endofunctor ℝeactive F-▹
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

    EF-delay : (k : ℕ) -> Endofunctor ℝeactive (F-delay k)
    EF-delay = λ _ → record {}


-- ◇ instances
instance
    F-◇ : Functor ℝeactive ℝeactive
    F-◇ = record
        { omap = ◇_
        ; fmap = fmap-◇
        ; fmap-id = fmap-◇-id
        ; fmap-∘ = fmap-◇-∘
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

    EF-◇ : Endofunctor ℝeactive F-◇
    EF-◇ = record {}

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

    EF-□ : Endofunctor ℝeactive F-□
    EF-□ = record {}
