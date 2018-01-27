
{- Type class for natural transformations. -}
module CategoryTheory.NatTrans where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open CategoryTheory.Categories.Category using (obj)

infixr 25 _⟹_

-- Natural transformation between two functors
record _⟹_ {n} {ℂ 𝔻 : Category n} (F : Functor ℂ 𝔻) (G : Functor ℂ 𝔻) : Set (lsuc n) where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    private module F = Functor F
    private module G = Functor G
    field
        -- || Definitions
        -- One component of the natural transformations.
        at : ∀(A : obj ℂ) -> (F.omap A) 𝔻.~> (G.omap A)

        -- || Laws
        -- Naturality condition
        nat-cond : ∀{A B : obj ℂ} {f : A ℂ.~> B}
                -> (G.fmap f 𝔻.∘ at A) 𝔻.≈ (at B 𝔻.∘ F.fmap f)

-- Identity natural transformation
instance
    ιd : ∀ {n} {ℂ 𝔻 : Category n} -> (F : Functor ℂ 𝔻) -> F ⟹ F
    ιd {n} {ℂ} {𝔻} F = record
            { at = λ A -> F.fmap ℂ.id
            ; nat-cond =  λ {A} {B} {f} ->
                𝔻.begin
                    F.fmap f 𝔻.∘ F.fmap ℂ.id
                𝔻.≈⟨ 𝔻.≈-cong-right (F.fmap-id) ⟩
                    F.fmap f 𝔻.∘ 𝔻.id
                𝔻.≈⟨ 𝔻.id-right ⟩
                    F.fmap f
                𝔻.≈⟨  IsEquivalence.sym 𝔻.≈-equiv (𝔻.id-left)  ⟩
                    𝔻.id 𝔻.∘ F.fmap f
                𝔻.≈⟨ 𝔻.≈-cong-left (IsEquivalence.sym 𝔻.≈-equiv (F.fmap-id)) ⟩
                    F.fmap ℂ.id 𝔻.∘ F.fmap  f
                𝔻.∎
            }

        where
        open import Relation.Binary using (IsEquivalence)
        private module F = Functor F
        private module ℂ = Category ℂ
        private module 𝔻 = Category 𝔻

-- Vertical composition of natural transformations
instance
    _⊚_ : ∀ {n} {ℂ 𝔻 : Category n} -> {F G H : Functor ℂ 𝔻}
       -> G ⟹ H -> F ⟹ G -> F ⟹ H
    _⊚_ {n} {ℂ} {𝔻} {F} {G} {H} φ ψ = record
        { at = λ A -> (φ.at A) 𝔻.∘ (ψ.at A)
        ; nat-cond =  λ {A} {B} {f} ->
            𝔻.begin
                H.fmap f 𝔻.∘ (φ.at A 𝔻.∘ ψ.at A)
            𝔻.≈⟨ IsEquivalence.sym 𝔻.≈-equiv 𝔻.∘-assoc ⟩
                (H.fmap f 𝔻.∘ φ.at A) 𝔻.∘ ψ.at A
            𝔻.≈⟨  𝔻.≈-cong-left (φ.nat-cond) ⟩
                (φ.at B 𝔻.∘ G.fmap f) 𝔻.∘ ψ.at A
            𝔻.≈⟨ 𝔻.∘-assoc ⟩
                φ.at B 𝔻.∘ (G.fmap f 𝔻.∘ ψ.at A)
            𝔻.≈⟨ 𝔻.≈-cong-right (ψ.nat-cond) ⟩
                φ.at B 𝔻.∘ (ψ.at B 𝔻.∘ F.fmap f)
            𝔻.≈⟨ IsEquivalence.sym 𝔻.≈-equiv 𝔻.∘-assoc ⟩
                (φ.at B 𝔻.∘ ψ.at B) 𝔻.∘ F.fmap f
            𝔻.∎
        }
        where
        private module 𝔻 = Category 𝔻
        private module F = Functor F
        private module G = Functor G
        private module H = Functor H
        private module φ   = _⟹_ φ
        private module ψ = _⟹_ ψ
        open import Relation.Binary using (IsEquivalence)

-- Natural isomorphism between two functors
record _⟺_  {n} {ℂ 𝔻 : Category n} (F : Functor ℂ 𝔻) (G : Functor ℂ 𝔻) : Set (lsuc n) where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    private module F = Functor F
    private module G = Functor G
    field
        -- || Definitions
        -- NT from F to G
        to   : F ⟹ G
        -- NT from G to F
        from : G ⟹ F

    private module to   = _⟹_ to
    private module from = _⟹_ from

    field
        -- || Isomorphism laws
        iso1 : ∀{A : obj ℂ} -> (from.at A) 𝔻.∘ (to.at A)   𝔻.≈ 𝔻.id
        iso2 : ∀{A : obj ℂ} -> (to.at A)   𝔻.∘ (from.at A) 𝔻.≈ 𝔻.id
