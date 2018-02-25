
{- Kleisli category for a monad. -}
module CategoryTheory.Instances.Kleisli where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad

open Category

-- Kleisli category from a category ℂ and a monad on ℂ
Kleisli : ∀{n} -> (ℂ : Category n) -> Monad ℂ -> Category n
Kleisli ℂ M = record
    { obj = ℂ.obj
    ; _~>_ = λ A B → A ℂ.~> T B
    ; id = λ {A} → η.at A
    ; _∘_ = λ {A}{B}{C} g f → (μ.at C ℂ.∘ fmap g) ℂ.∘ f
    ; _≈_ = ℂ._≈_
    ; id-left = λ {A} {B} {f} → ℂ.≈-cong-left (η-unit2 {B}) ℂ.≈> ℂ.id-left
    ; id-right = id-right-K
    ; ∘-assoc = ∘-assoc-K
    ; ≈-equiv = ℂ.≈-equiv
    ; ≈-cong = λ p1 p2 → ℂ.≈-cong-right p1 ℂ.≈> ℂ.≈-cong-left (ℂ.≈-cong-right (fmap-cong p2))
    }
    where
    private module ℂ = Category ℂ
    open Monad M renaming (T to F)
    open Functor F renaming (omap to T)
    private module μ = _⟹_ μ
    private module η = _⟹_ η
    id-right-K : {A B : ℂ.obj} {f : A ℂ.~> T B} → (μ.at B ℂ.∘ fmap f) ℂ.∘ η.at A ℂ.≈ f
    id-right-K {A}{B}{f}=
        ℂ.begin
            (μ.at B ℂ.∘ fmap f) ℂ.∘ η.at A
        ℂ.≈⟨ ℂ.∘-assoc ⟩
            μ.at B ℂ.∘ (fmap f ℂ.∘ η.at A)
        ℂ.≈⟨ ℂ.≈-cong-right η.nat-cond ℂ.≈> ℂ.∘-assoc ℂ.[sym] ⟩
            (μ.at B ℂ.∘ η.at (T B)) ℂ.∘ f
        ℂ.≈⟨ ℂ.≈-cong-left (η-unit1) ℂ.≈> ℂ.id-left ⟩
            f
        ℂ.∎
    ∘-assoc-K : {A B C D : ℂ.obj} {f : C ℂ.~> T D} {g : B ℂ.~> T C} {h : A ℂ.~> T B} →
          (μ.at D ℂ.∘ fmap ((μ.at D ℂ.∘ fmap f) ℂ.∘ g)) ℂ.∘ h ℂ.≈
          (μ.at D ℂ.∘ fmap f) ℂ.∘ ((μ.at C ℂ.∘ fmap g) ℂ.∘ h)
    ∘-assoc-K {A}{B}{C}{D}{f}{g}{h} =
        ℂ.begin
            (μ.at D ℂ.∘ fmap ((μ.at D ℂ.∘ fmap f) ℂ.∘ g)) ℂ.∘ h
        ℂ.≈⟨ ℂ.≈-cong-left (ℂ.≈-cong-right fmap-∘) ⟩
            (μ.at D ℂ.∘ (fmap (μ.at D ℂ.∘ fmap f) ℂ.∘ fmap g)) ℂ.∘ h
        ℂ.≈⟨ ℂ.≈-cong-left (ℂ.≈-cong-right (ℂ.≈-cong-left fmap-∘)) ⟩
            (μ.at D ℂ.∘ ((fmap (μ.at D) ℂ.∘ fmap (fmap f)) ℂ.∘ fmap g)) ℂ.∘ h
        ℂ.≈⟨ ℂ.≈-cong-left (ℂ.∘-assoc ℂ.[sym]) ℂ.≈> ℂ.≈-cong-left (ℂ.≈-cong-left (ℂ.∘-assoc ℂ.[sym])) ⟩
            (((μ.at D ℂ.∘ fmap (μ.at D)) ℂ.∘ fmap (fmap f)) ℂ.∘ fmap g) ℂ.∘ h
        ℂ.≈⟨ ℂ.≈-cong-left (ℂ.≈-cong-left (ℂ.≈-cong-left (μ-assoc ℂ.[sym]))) ⟩
            (((μ.at D ℂ.∘ μ.at (T D)) ℂ.∘ fmap (fmap f)) ℂ.∘ fmap g) ℂ.∘ h
        ℂ.≈⟨ ℂ.≈-cong-left (ℂ.≈-cong-left (ℂ.∘-assoc)) ⟩
            ((μ.at D ℂ.∘ (μ.at (T D) ℂ.∘ fmap (fmap f))) ℂ.∘ fmap g) ℂ.∘ h
        ℂ.≈⟨ ℂ.≈-cong-left (ℂ.≈-cong-left (ℂ.≈-cong-right (μ.nat-cond ℂ.[sym]))) ⟩
            ((μ.at D ℂ.∘ (fmap f ℂ.∘ μ.at C)) ℂ.∘ fmap g) ℂ.∘ h
        ℂ.≈⟨ ℂ.≈-cong-left (ℂ.≈-cong-left (ℂ.∘-assoc ℂ.[sym])) ⟩
            (((μ.at D ℂ.∘ fmap f) ℂ.∘ μ.at C) ℂ.∘ fmap g) ℂ.∘ h
        ℂ.≈⟨ ℂ.≈-cong-left (ℂ.∘-assoc) ℂ.≈> ℂ.∘-assoc ⟩
            (μ.at D ℂ.∘ fmap f) ℂ.∘ ((μ.at C ℂ.∘ fmap g) ℂ.∘ h)
        ℂ.∎
