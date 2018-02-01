
{- Type class for adjoint functors -}
module CategoryTheory.Adjunction where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Comonad

-- Adjunction between two functors
record _⊣_ {n} {ℂ 𝔻 : Category n} (F : Functor ℂ 𝔻) (G : Functor 𝔻 ℂ) : Set (lsuc n) where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    private module F = Functor F
    private module G = Functor G
    field
        -- || Definitions
        -- Unit
        η : I ⟹ G ◯ F
        -- Counit
        ε : F ◯ G ⟹ I

    private module η = _⟹_ η
    private module ε = _⟹_ ε

    field
        -- || Laws
        -- First triangle identity: εF ∘ Fη = ιd
        tri1 : ∀ {A : ℂ.obj} -> ε.at (F.omap A) 𝔻.∘ F.fmap (η.at A) 𝔻.≈ 𝔻.id
        -- Second triangle inequality: Gε ∘ ηG = ιd
        tri2 : ∀ {B : 𝔻.obj} -> G.fmap (ε.at B) ℂ.∘ η.at (G.omap B) ℂ.≈ ℂ.id

-- || An adjunction induces a monad and a comonad
instance
    AdjM : ∀ {n} {ℂ 𝔻 : Category n} (F : Functor ℂ 𝔻) (G : Functor 𝔻 ℂ)
        -> F ⊣ G -> Monad ℂ
    AdjM {n} {ℂ} {𝔻} F G adj = record
        { T = G ◯ F
        ; η = F⊣G.η
        ; μ = record
            { at = λ A → G.fmap (at F⊣G.ε (F.omap A))
            ; nat-cond = G.fmap-∘ [sym] ≈> G.fmap-cong (nat-cond F⊣G.ε) ≈> G.fmap-∘
            }
        ; η-unit1 = F⊣G.tri2
        ; η-unit2 = G.fmap-∘ [sym] ≈> G.fmap-cong (F⊣G.tri1) ≈> G.fmap-id
        ; μ-assoc = G.fmap-∘ [sym] ≈> G.fmap-cong (nat-cond F⊣G.ε) ≈> G.fmap-∘
        }
        where
        private module F⊣G = _⊣_ adj
        open Category ℂ
        private module 𝔻 = Category 𝔻
        private module F = Functor F
        private module G = Functor G
        open _⟹_

instance
    AdjC : ∀ {n} {ℂ 𝔻 : Category n} (F : Functor ℂ 𝔻) (G : Functor 𝔻 ℂ)
        -> F ⊣ G -> Comonad 𝔻
    AdjC {n} {ℂ} {𝔻} F G adj = record
        { W = F ◯ G
        ; ε = F⊣G.ε
        ; δ = record
            { at = λ A → F.fmap (at F⊣G.η (G.omap A))
            ; nat-cond = F.fmap-∘ [sym] ≈> F.fmap-cong (nat-cond F⊣G.η) ≈> F.fmap-∘
            }
        ; ε-unit1 = F⊣G.tri1
        ; ε-unit2 = F.fmap-∘ [sym] ≈> F.fmap-cong (F⊣G.tri2) ≈> F.fmap-id
        ; δ-assoc = F.fmap-∘ [sym] ≈> F.fmap-cong ((nat-cond F⊣G.η) ℂ.[sym]) ≈> F.fmap-∘
        }
        where
        private module F⊣G = _⊣_ adj
        open Category 𝔻
        private module ℂ = Category ℂ
        private module F = Functor F
        private module G = Functor G
        open _⟹_
