
{- Type class for functors. -}
module CategoryTheory.Functor where

open import CategoryTheory.Categories
open CategoryTheory.Categories.Category using (obj)
import Relation.Binary.PropositionalEquality as R
open import Relation.Binary

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
        fmap-id   : ∀{A : obj ℂ} -> fmap (ℂ.id {A}) 𝔻.≈ 𝔻.id
        -- Functor preserves composition
        fmap-∘    : ∀{A B C : obj ℂ} {g : B ℂ.~> C} {f : A ℂ.~> B}
                 -> fmap (g ℂ.∘ f) 𝔻.≈ fmap g 𝔻.∘ fmap f
        -- Congruence of equality and fmap
        fmap-cong : ∀{A B : obj ℂ} {f f′ : A ℂ.~> B}
                -> f ℂ.≈ f′ -> fmap f 𝔻.≈ fmap f′

-- Endofunctor on a category
record Endofunctor (ℂ : Category) : Set₁ where
    field
        functor : Functor ℂ ℂ

open Functor {{...}}

open CategoryTheory.Categories.Category {{...}}


-- Identity functor
instance
    I : ∀{ℂ} -> Endofunctor ℂ
    I {ℂ} = record { functor =
            record { omap = λ a → a
                   ; fmap = λ a → a
                   ; fmap-id = IsEquivalence.refl (Category.≈-equiv ℂ)
                   ; fmap-∘ =  IsEquivalence.refl (Category.≈-equiv ℂ)
                   ; fmap-cong = λ p → p }
        }

-- Functors are closed under composition.
instance
    _◯_ : ∀{𝔸 𝔹 ℂ} -> Functor 𝔹 ℂ -> Functor 𝔸 𝔹 -> Functor 𝔸 ℂ
    _◯_ {𝔸} {𝔹} {ℂ} G F =
        record { omap = λ a → G.omap (F.omap a)
               ; fmap = λ f → G.fmap (F.fmap f)
               ; fmap-id = fmap-◯-id
               ; fmap-∘ = fmap-◯-∘
               ; fmap-cong = λ p → G.fmap-cong (F.fmap-cong p)}
        where private module F = Functor F
              private module G = Functor G
              private module 𝔸 = Category 𝔸
              private module 𝔹 = Category 𝔹
              private module ℂ = Category ℂ

              fmap-◯-id : ∀{A : obj 𝔸} -> G.fmap (F.fmap (𝔸.id {A})) ℂ.≈ ℂ.id
              fmap-◯-id {A} =
                    ℂ.begin
                        G.fmap (F.fmap (𝔸.id))
                    ℂ.≈⟨ G.fmap-cong (F.fmap-id) ⟩
                        G.fmap (𝔹.id)
                    ℂ.≈⟨ G.fmap-id ⟩
                        ℂ.id
                    ℂ.∎
              fmap-◯-∘ : ∀{A B C : obj 𝔸} {g : B 𝔸.~> C} {f : A 𝔸.~> B}
                       -> G.fmap (F.fmap (g 𝔸.∘ f)) ℂ.≈
                          G.fmap (F.fmap g) ℂ.∘ G.fmap (F.fmap f)
              fmap-◯-∘ {A} {g = g} {f = f} =
                    ℂ.begin
                        G.fmap (F.fmap (g 𝔸.∘ f))
                    ℂ.≈⟨ G.fmap-cong (F.fmap-∘) ⟩
                        G.fmap ((F.fmap g) 𝔹.∘ (F.fmap f))
                    ℂ.≈⟨ G.fmap-∘ ⟩
                        G.fmap (F.fmap g) ℂ.∘ G.fmap (F.fmap f)
                    ℂ.∎

