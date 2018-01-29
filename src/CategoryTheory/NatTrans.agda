
{- Type class for natural transformations. -}
module CategoryTheory.NatTrans where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import Relation.Binary using (IsEquivalence)

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
        at : ∀(A : ℂ.obj) -> (F.omap A) 𝔻.~> (G.omap A)

        -- || Laws
        -- Naturality condition
        nat-cond : ∀{A B : ℂ.obj} {f : A ℂ.~> B}
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
                𝔻.≈⟨ 𝔻.id-comm ⟩
                    𝔻.id 𝔻.∘ F.fmap f
                𝔻.≈⟨ 𝔻.≈-cong-left (F.fmap-id 𝔻.[sym]) ⟩
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
            𝔻.≈⟨ 𝔻.∘-assoc 𝔻.[sym] ⟩
                (H.fmap f 𝔻.∘ φ.at A) 𝔻.∘ ψ.at A
            𝔻.≈⟨  𝔻.≈-cong-left (φ.nat-cond) 𝔻.≈> 𝔻.∘-assoc ⟩
                φ.at B 𝔻.∘ (G.fmap f 𝔻.∘ ψ.at A)
            𝔻.≈⟨ 𝔻.≈-cong-right (ψ.nat-cond) 𝔻.≈> (𝔻.∘-assoc 𝔻.[sym])⟩
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
        iso1 : ∀{A : ℂ.obj} -> (from.at A) 𝔻.∘ (to.at A)   𝔻.≈ 𝔻.id
        iso2 : ∀{A : ℂ.obj} -> (to.at A)   𝔻.∘ (from.at A) 𝔻.≈ 𝔻.id

-- Natural isomorphism is an equivalence
⟺-equiv : ∀ {n} {ℂ 𝔻 : Category n} -> IsEquivalence (_⟺_ {n} {ℂ} {𝔻})
⟺-equiv {n} {ℂ} {𝔻} = record
         { refl = λ {F} -> record
             { to = ιd F
             ; from = ιd F
             ; iso1 = λ {A} -> refl-iso-proof {A} {F}
             ; iso2 = λ {A} -> refl-iso-proof {A} {F} }
         ; sym = λ {F} {G} F⟺G -> record
             { to = _⟺_.from F⟺G
             ; from = _⟺_.to F⟺G
             ; iso1 = _⟺_.iso2 F⟺G
             ; iso2 = _⟺_.iso1 F⟺G }
         ; trans = λ {F} {G} {H} F⟺G G⟺H -> record
             { to = (_⟺_.to G⟺H) ⊚ (_⟺_.to F⟺G)
             ; from = (_⟺_.from F⟺G) ⊚ (_⟺_.from G⟺H)
             ; iso1 = λ {A} →
                𝔻.begin
                    at (from F⟺G ⊚ from G⟺H) A 𝔻.∘ at (to G⟺H ⊚ to F⟺G) A
                𝔻.≈⟨ 𝔻.∘-assoc 𝔻.[sym] 𝔻.≈> 𝔻.≈-cong-left (𝔻.∘-assoc) ⟩
                    (at (from F⟺G) A 𝔻.∘ (at (from G⟺H) A 𝔻.∘ at (to G⟺H) A)) 𝔻.∘ at (to F⟺G) A
                𝔻.≈⟨ 𝔻.≈-cong-left (𝔻.≈-cong-right (iso1 G⟺H)) ⟩
                    (at (from F⟺G) A 𝔻.∘ 𝔻.id) 𝔻.∘ at (to F⟺G) A
                𝔻.≈⟨ 𝔻.≈-cong-left (𝔻.id-right) ⟩
                    at (from F⟺G) A 𝔻.∘ at (to F⟺G) A
                𝔻.≈⟨ iso1 F⟺G ⟩
                    𝔻.id
                𝔻.∎
             ; iso2 = λ {A} →
                𝔻.begin
                    at (to G⟺H ⊚ to F⟺G) A 𝔻.∘ at (from F⟺G ⊚ from G⟺H) A
                𝔻.≈⟨ (𝔻.∘-assoc 𝔻.[sym]) 𝔻.≈> 𝔻.≈-cong-left (𝔻.∘-assoc) ⟩
                    (at (to G⟺H) A 𝔻.∘ (at (to F⟺G) A 𝔻.∘ at (from F⟺G) A)) 𝔻.∘ at (from G⟺H) A
                𝔻.≈⟨ 𝔻.≈-cong-left (𝔻.≈-cong-right (iso2 F⟺G)) ⟩
                    (at (to G⟺H) A 𝔻.∘ 𝔻.id) 𝔻.∘ at (from G⟺H) A
                𝔻.≈⟨ 𝔻.≈-cong-left (𝔻.id-right) ⟩
                    at (to G⟺H) A 𝔻.∘ at (from G⟺H) A
                𝔻.≈⟨ iso2 G⟺H ⟩
                    𝔻.id
                𝔻.∎
             }
         }
    where
    private module ℂ = Category ℂ
    private module 𝔻 = Category 𝔻
    open _⟹_
    open _⟺_
    refl-iso-proof : {A : ℂ.obj} {F : Functor ℂ 𝔻}
             -> _⟹_.at (ιd F) A 𝔻.∘ _⟹_.at (ιd F) A 𝔻.≈ 𝔻.id
    refl-iso-proof {A} {F} =
        𝔻.begin
            _⟹_.at (ιd F) A 𝔻.∘ _⟹_.at (ιd F) A
        𝔻.≈⟨ 𝔻.≈-cong-left (Functor.fmap-id F) ⟩
            𝔻.id 𝔻.∘ _⟹_.at (ιd F) A
        𝔻.≈⟨ 𝔻.≈-cong-right (Functor.fmap-id F) ⟩
            𝔻.id 𝔻.∘ 𝔻.id
        𝔻.≈⟨ 𝔻.id-left ⟩
            𝔻.id
        𝔻.∎
