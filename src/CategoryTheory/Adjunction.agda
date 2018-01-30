
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
            ; nat-cond = λ {A} {B} {f} ->
                begin
                    Functor.fmap (G ◯ F) f ∘ G.fmap (at F⊣G.ε (F.omap A))
                ≈⟨ G.fmap-∘ [sym] ⟩
                    G.fmap (F.fmap f 𝔻.∘ at F⊣G.ε (F.omap A))
                ≈⟨ G.fmap-cong (nat-cond F⊣G.ε) ⟩
                    G.fmap (at F⊣G.ε (F.omap B) 𝔻.∘ Functor.fmap (F ◯ G ◯ F) f)
                ≈⟨ G.fmap-∘ ⟩
                    G.fmap (at F⊣G.ε (F.omap B)) ∘ Functor.fmap ((G ◯ F) ²) f
                ∎
            }
            ; η-unit1 = λ {A} →
                begin
                    G.fmap (at F⊣G.ε (F.omap A)) ∘ at F⊣G.η (Functor.omap (G ◯ F) A)
                ≈⟨ F⊣G.tri2 ⟩
                    id
                ∎
            ; η-unit2 = λ {A} →
                begin
                    G.fmap (at F⊣G.ε (F.omap A)) ∘ Functor.fmap (G ◯ F) (at F⊣G.η A)
                ≈⟨ G.fmap-∘ [sym] ⟩
                    G.fmap (at F⊣G.ε (F.omap A) 𝔻.∘ F.fmap (at F⊣G.η A))
                ≈⟨ G.fmap-cong (F⊣G.tri1) ⟩
                    G.fmap 𝔻.id
                ≈⟨ G.fmap-id ⟩
                    id
                ∎
            ; μ-assoc = λ {A} →
                begin
                    G.fmap (at F⊣G.ε (F.omap A)) ∘
                    G.fmap (at F⊣G.ε (Functor.omap (F ◯ G ◯ F) A))
                ≈⟨ G.fmap-∘ [sym] ⟩
                    G.fmap (at F⊣G.ε (F.omap A) 𝔻.∘
                            at F⊣G.ε (Functor.omap (F ◯ G ◯ F) A))
                ≈⟨ G.fmap-cong (nat-cond F⊣G.ε) ⟩
                    G.fmap (at F⊣G.ε (F.omap A) 𝔻.∘
                            F.fmap (G.fmap (at F⊣G.ε (F.omap A))))
                ≈⟨ G.fmap-∘ ⟩
                    G.fmap (at F⊣G.ε (F.omap A)) ∘
                    Functor.fmap (G ◯ F) (G.fmap (at F⊣G.ε (F.omap A)))
                ∎
        }
        where
        private module F⊣G = _⊣_ adj
        open Category ℂ
        private module 𝔻 = Category 𝔻
        private module F = Functor F
        private module G = Functor G
        open _⟹_
