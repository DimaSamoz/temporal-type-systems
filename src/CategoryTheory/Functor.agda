
{- Type class for functors. -}
module CategoryTheory.Functor where

open import CategoryTheory.Categories
open import Relation.Binary

-- Functor between two categories
record Functor {n} (ℂ : Category n) (𝔻 : Category n) : Set (lsuc n) where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    field
        -- || Definitions
        -- Object map
        omap : ℂ.obj -> 𝔻.obj
        -- Arrow map
        fmap : ∀{A B : ℂ.obj} -> (A ℂ.~> B) -> (omap A 𝔻.~> omap B)

        -- || Laws
        -- Functor preseres identities
        fmap-id   : ∀{A : ℂ.obj} -> fmap (ℂ.id {A}) 𝔻.≈ 𝔻.id
        -- Functor preserves composition
        fmap-∘    : ∀{A B C : ℂ.obj} {g : B ℂ.~> C} {f : A ℂ.~> B}
                 -> fmap (g ℂ.∘ f) 𝔻.≈ fmap g 𝔻.∘ fmap f
        -- Congruence of equality and fmap
        fmap-cong : ∀{A B : ℂ.obj} {f f′ : A ℂ.~> B}
                -> f ℂ.≈ f′ -> fmap f 𝔻.≈ fmap f′

-- Type synonym for endofunctors
Endofunctor : ∀{n} -> Category n -> Set (lsuc n)
Endofunctor ℂ = Functor ℂ ℂ


-- Identity functor
I : ∀ {n} {ℂ : Category n} -> Endofunctor ℂ
I {n} {ℂ} = record { omap = λ a → a
               ; fmap = λ a → a
               ; fmap-id = IsEquivalence.refl (Category.≈-equiv ℂ)
               ; fmap-∘ =  IsEquivalence.refl (Category.≈-equiv ℂ)
               ; fmap-cong = λ p → p }


-- Functors are closed under composition.
infixl 40 _◯_
_◯_ : ∀ {n} {𝔸 𝔹 ℂ : Category n} -> Functor 𝔹 ℂ -> Functor 𝔸 𝔹 -> Functor 𝔸 ℂ
_◯_ {n} {𝔸} {𝔹} {ℂ} G F =
    record { omap = λ a → G.omap (F.omap a)
           ; fmap = λ f → G.fmap (F.fmap f)
           ; fmap-id = fmap-◯-id
           ; fmap-∘ = fmap-◯-∘
           ; fmap-cong = λ p → G.fmap-cong (F.fmap-cong p)}
    where private module F = Functor F
          private module G = Functor G
          private module 𝔸 = Category 𝔸
          private module 𝔹 = Category 𝔹
          open Category ℂ

          fmap-◯-id : ∀{A : 𝔸.obj} -> G.fmap (F.fmap (𝔸.id {A})) ≈ id
          fmap-◯-id {A} =
                begin
                    G.fmap (F.fmap (𝔸.id))
                ≈⟨ G.fmap-cong (F.fmap-id) ⟩
                    G.fmap (𝔹.id)
                ≈⟨ G.fmap-id ⟩
                    id
                ∎
          fmap-◯-∘ : ∀{A B C : 𝔸.obj} {g : B 𝔸.~> C} {f : A 𝔸.~> B}
                   -> G.fmap (F.fmap (g 𝔸.∘ f)) ≈
                      G.fmap (F.fmap g) ∘ G.fmap (F.fmap f)
          fmap-◯-∘ {A} {g = g} {f = f} =
                begin
                    G.fmap (F.fmap (g 𝔸.∘ f))
                ≈⟨ G.fmap-cong (F.fmap-∘) ⟩
                    G.fmap ((F.fmap g) 𝔹.∘ (F.fmap f))
                ≈⟨ G.fmap-∘ ⟩
                    G.fmap (F.fmap g) ∘ G.fmap (F.fmap f)
                ∎

-- Endofunctor tensor product
infixl 40 _⨂_
_⨂_ : ∀ {n} {ℂ : Category n} -> Endofunctor ℂ -> Endofunctor ℂ -> Endofunctor ℂ
(T ⨂ S) = T ◯ S

-- Square and cube of an endofunctor
_² : ∀ {n} {ℂ : Category n} -> Endofunctor ℂ -> Endofunctor ℂ
F ² = F ⨂ F

_³ : ∀ {n} {ℂ : Category n} -> Endofunctor ℂ -> Endofunctor ℂ
F ³ = F ⨂ F ⨂ F
