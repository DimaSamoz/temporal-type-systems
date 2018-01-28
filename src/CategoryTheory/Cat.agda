
{- Category of categories -}
module CategoryTheory.Cat where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open CategoryTheory.Categories.Category using (obj)

-- Category of categories
instance
    ℂat : ∀{n} -> Category (lsuc n)
    ℂat {n} = record
            { obj = Category n
            ; _~>_ = Functor
            ; id = I
            ; _∘_ = _◯_
            ; _≈_ = _⟺_
            ; id-left = id-left-ℂat
            ; id-right = id-right-ℂat
            ; ∘-assoc = λ {𝔸} {𝔹} {ℂ} {𝔻} {H} {G} {F} ->
                            ∘-assoc-ℂat {𝔸} {𝔹} {ℂ} {𝔻} {F} {G} {H}
            ; ≈-equiv = ⟺-equiv
            ; ≈-cong = ≈-cong-ℂat
            }
        where
            id-left-ℂat : {ℂ 𝔻 : Category n} {F : Functor ℂ 𝔻} -> (I ◯ F) ⟺ F
            id-left-ℂat {ℂ} {𝔻} {F} = record
                { to = record
                    { at = λ A -> F.fmap ℂ.id
                    ; nat-cond =  λ {A} {B} {f} ->
                        𝔻.begin
                            F.fmap f 𝔻.∘ F.fmap ℂ.id
                        𝔻.≈⟨ 𝔻.≈-cong-right (F.fmap-id) ⟩
                            F.fmap f 𝔻.∘ 𝔻.id
                        𝔻.≈⟨ 𝔻.id-right ⟩
                            F.fmap f
                        𝔻.≈⟨  IsEquivalence.sym 𝔻.≈-equiv (𝔻.id-left)  ⟩
                            𝔻.id 𝔻.∘ Functor.fmap (I ◯ F) f
                        𝔻.≈⟨ 𝔻.≈-cong-left (IsEquivalence.sym 𝔻.≈-equiv (F.fmap-id)) ⟩
                            F.fmap ℂ.id 𝔻.∘ Functor.fmap (I ◯ F) f
                        𝔻.∎
                    }
                ; from = record {
                    at = λ A -> F.fmap ℂ.id
                    ; nat-cond =  λ {A} {B} {f} ->
                        𝔻.begin
                            Functor.fmap (I ◯ F) f 𝔻.∘ F.fmap ℂ.id
                        𝔻.≈⟨ 𝔻.≈-cong-right (F.fmap-id) ⟩
                            Functor.fmap (I ◯ F) f 𝔻.∘ 𝔻.id
                        𝔻.≈⟨ 𝔻.id-right ⟩
                            Functor.fmap (I ◯ F) f
                        𝔻.≈⟨ IsEquivalence.sym 𝔻.≈-equiv (𝔻.id-left) ⟩
                            𝔻.id 𝔻.∘ F.fmap f
                        𝔻.≈⟨ 𝔻.≈-cong-left (IsEquivalence.sym 𝔻.≈-equiv (F.fmap-id)) ⟩
                            F.fmap ℂ.id 𝔻.∘ F.fmap f
                        𝔻.∎
                    }
                ; iso1 = iso-proof
                ; iso2 = iso-proof }
                where
                open import Relation.Binary using (IsEquivalence)
                private module F = Functor F
                private module ℂ = Category ℂ
                private module 𝔻 = Category 𝔻

                iso-proof : ∀{A : obj ℂ} -> F.fmap (ℂ.id {A}) 𝔻.∘ F.fmap ℂ.id 𝔻.≈ 𝔻.id
                iso-proof =
                    𝔻.begin
                        F.fmap ℂ.id 𝔻.∘ F.fmap ℂ.id
                    𝔻.≈⟨ 𝔻.≈-cong-right (Functor.fmap-id F) ⟩
                        F.fmap ℂ.id 𝔻.∘ 𝔻.id
                    𝔻.≈⟨ 𝔻.≈-cong-left (Functor.fmap-id F) ⟩
                        𝔻.id 𝔻.∘ 𝔻.id
                    𝔻.≈⟨ 𝔻.id-left ⟩
                        𝔻.id
                    𝔻.∎

            id-right-ℂat : {ℂ 𝔻 : Category n} {F : Functor ℂ 𝔻} -> (F ◯ I) ⟺ F
            id-right-ℂat {ℂ} {𝔻} {F} = record
                { to = record
                    { at = λ A -> F.fmap ℂ.id
                    ; nat-cond =  λ {A} {B} {f} ->
                        𝔻.begin
                            F.fmap f 𝔻.∘ F.fmap ℂ.id
                        𝔻.≈⟨ 𝔻.≈-cong-right (F.fmap-id) ⟩
                            F.fmap f 𝔻.∘ 𝔻.id
                        𝔻.≈⟨ 𝔻.id-right ⟩
                            F.fmap f
                        𝔻.≈⟨ F.fmap-cong (IsEquivalence.refl ℂ.≈-equiv) ⟩
                            Functor.fmap (F ◯ I) f
                        𝔻.≈⟨ IsEquivalence.sym 𝔻.≈-equiv (𝔻.id-left) ⟩
                            𝔻.id 𝔻.∘ Functor.fmap (F ◯ I) f
                        𝔻.≈⟨ 𝔻.≈-cong-left (IsEquivalence.sym 𝔻.≈-equiv (F.fmap-id)) ⟩
                            F.fmap ℂ.id 𝔻.∘ Functor.fmap (F ◯ I) f
                        𝔻.∎
                    }
                ; from = record {
                    at = λ A -> F.fmap ℂ.id
                    ; nat-cond =  λ {A} {B} {f} ->
                        𝔻.begin
                            Functor.fmap (F ◯ I) f 𝔻.∘ F.fmap ℂ.id
                        𝔻.≈⟨ 𝔻.≈-cong-right (F.fmap-id) ⟩
                            Functor.fmap (F ◯ I) f 𝔻.∘ 𝔻.id
                        𝔻.≈⟨ 𝔻.id-right ⟩
                            Functor.fmap (F ◯ I) f
                        𝔻.≈⟨ IsEquivalence.sym 𝔻.≈-equiv (𝔻.id-left) ⟩
                            𝔻.id 𝔻.∘ F.fmap f
                        𝔻.≈⟨ 𝔻.≈-cong-left (IsEquivalence.sym 𝔻.≈-equiv (F.fmap-id)) ⟩
                            F.fmap ℂ.id 𝔻.∘ F.fmap f
                        𝔻.∎
                    }
                ; iso1 = iso-proof
                ; iso2 = iso-proof }
                where
                open import Relation.Binary using (IsEquivalence)
                private module F = Functor F
                private module ℂ = Category ℂ
                private module 𝔻 = Category 𝔻

                iso-proof : ∀{A : obj ℂ} -> F.fmap (ℂ.id {A}) 𝔻.∘ F.fmap ℂ.id 𝔻.≈ 𝔻.id
                iso-proof =
                    𝔻.begin
                        F.fmap ℂ.id 𝔻.∘ F.fmap ℂ.id
                    𝔻.≈⟨ 𝔻.≈-cong-right (Functor.fmap-id F) ⟩
                        F.fmap ℂ.id 𝔻.∘ 𝔻.id
                    𝔻.≈⟨ 𝔻.≈-cong-left (Functor.fmap-id F) ⟩
                        𝔻.id 𝔻.∘ 𝔻.id
                    𝔻.≈⟨ 𝔻.id-left ⟩
                        𝔻.id
                    𝔻.∎

            ∘-assoc-ℂat : {𝔸 𝔹 ℂ 𝔻 : Category n} {F : Functor 𝔸 𝔹}
                          {G : Functor 𝔹 ℂ} {H : Functor ℂ 𝔻}
                       -> (H ◯ G) ◯ F ⟺ H ◯ (G ◯ F)
            ∘-assoc-ℂat {𝔸} {𝔹} {ℂ} {𝔻} {F} {G} {H} = record
                { to = record
                    { at = λ A -> Functor.fmap (H ◯ (G ◯ F)) 𝔸.id
                    ; nat-cond = λ {A} {B} {f} ->
                        𝔻.begin
                            Functor.fmap (H ◯ (G ◯ F)) f 𝔻.∘ Functor.fmap (H ◯ (G ◯ F)) 𝔸.id
                        𝔻.≈⟨ 𝔻.≈-cong-right (Functor.fmap-id (H ◯ (G ◯ F))) ⟩
                            Functor.fmap (H ◯ (G ◯ F)) f 𝔻.∘ 𝔻.id
                        𝔻.≈⟨ 𝔻.id-right ⟩
                            Functor.fmap (H ◯ (G ◯ F)) f
                        𝔻.≈⟨ IsEquivalence.sym 𝔻.≈-equiv (𝔻.id-left) ⟩
                            𝔻.id 𝔻.∘ Functor.fmap (H ◯ G ◯ F) f
                        𝔻.≈⟨ 𝔻.≈-cong-left (IsEquivalence.sym 𝔻.≈-equiv (Functor.fmap-id ((H ◯ G) ◯ F))) ⟩
                            Functor.fmap (H ◯ G ◯ F) 𝔸.id 𝔻.∘ Functor.fmap (H ◯ G ◯ F) f
                        𝔻.∎
                    }
                ; from = record
                    { at = λ A -> Functor.fmap ((H ◯ G) ◯ F) 𝔸.id
                    ; nat-cond = λ {A} {B} {f} ->
                        𝔻.begin
                            Functor.fmap (H ◯ (G ◯ F)) f 𝔻.∘ Functor.fmap ((H ◯ G) ◯ F) 𝔸.id
                        𝔻.≈⟨ 𝔻.≈-cong-right (Functor.fmap-id ((H ◯ G) ◯ F)) ⟩
                            Functor.fmap (H ◯ (G ◯ F)) f 𝔻.∘ 𝔻.id
                        𝔻.≈⟨ 𝔻.id-right ⟩
                            Functor.fmap (H ◯ (G ◯ F)) f
                        𝔻.≈⟨ IsEquivalence.sym 𝔻.≈-equiv (𝔻.id-left) ⟩
                            𝔻.id 𝔻.∘ Functor.fmap (H ◯ G ◯ F) f
                        𝔻.≈⟨ 𝔻.≈-cong-left (IsEquivalence.sym 𝔻.≈-equiv (Functor.fmap-id ((H ◯ G) ◯ F))) ⟩
                            Functor.fmap (H ◯ G ◯ F) 𝔸.id 𝔻.∘ Functor.fmap (H ◯ G ◯ F) f
                        𝔻.∎
                    }
                ; iso1 = iso-proof

                ; iso2 = iso-proof
                }
                where
                open import Relation.Binary using (IsEquivalence)
                private module F = Functor F
                private module G = Functor G
                private module H = Functor H
                private module 𝔸 = Category 𝔸
                private module 𝔹 = Category 𝔹
                private module ℂ = Category ℂ
                private module 𝔻 = Category 𝔻

                iso-proof : ∀{A : obj 𝔸}
                         ->  Functor.fmap ((H ◯ G) ◯ F) (𝔸.id {A}) 𝔻.∘ Functor.fmap (H ◯ (G ◯ F)) 𝔸.id
                         𝔻.≈ 𝔻.id
                iso-proof =
                    𝔻.begin
                        Functor.fmap ((H ◯ G) ◯ F) 𝔸.id 𝔻.∘ Functor.fmap (H ◯ (G ◯ F)) 𝔸.id
                    𝔻.≈⟨ 𝔻.≈-cong-left (Functor.fmap-id ((H ◯ G) ◯ F)) ⟩
                        𝔻.id 𝔻.∘ Functor.fmap (H ◯ (G ◯ F)) 𝔸.id
                    𝔻.≈⟨ 𝔻.≈-cong-right (Functor.fmap-id (H ◯ (G ◯ F))) ⟩
                        𝔻.id 𝔻.∘ 𝔻.id
                    𝔻.≈⟨ 𝔻.id-left ⟩
                        𝔻.id
                    𝔻.∎

            ≈-cong-ℂat : {𝔸 𝔹 ℂ : Category n} {F F′ : Functor 𝔸 𝔹} {G G′ : Functor 𝔹 ℂ}
                      -> F ⟺ F′ -> G ⟺ G′ -> (G ◯ F) ⟺ (G′ ◯ F′)
            ≈-cong-ℂat {𝔸}{𝔹}{ℂ}{F}{F′}{G}{G′} F⟺F′ G⟺G′ = record
                { to = record
                    { at = λ A -> at G⟺G′.to (F′.omap A) ℂ.∘ G.fmap (at F⟺F′.to A)
                    ; nat-cond = λ {A} {B} {f} ->
                        ℂ.begin
                            Functor.fmap (G′ ◯ F′) f ℂ.∘ (at G⟺G′.to (F′.omap A) ℂ.∘ G.fmap (at F⟺F′.to A))
                        ℂ.≈⟨ IsEquivalence.sym ℂ.≈-equiv ℂ.∘-assoc ⟩
                            (Functor.fmap (G′ ◯ F′) f ℂ.∘ at G⟺G′.to (F′.omap A)) ℂ.∘ G.fmap (at F⟺F′.to A)
                        ℂ.≈⟨ ℂ.≈-cong-left (nat-cond (G⟺G′.to)) ⟩
                            (at G⟺G′.to (F′.omap B) ℂ.∘ Functor.fmap (G ◯ F′) f) ℂ.∘ G.fmap (at F⟺F′.to A)
                        ℂ.≈⟨ ℂ.∘-assoc ⟩
                            at G⟺G′.to (F′.omap B) ℂ.∘ (Functor.fmap (G ◯ F′) f ℂ.∘ G.fmap (at F⟺F′.to A))
                        ℂ.≈⟨ ℂ.≈-cong-right (IsEquivalence.sym ℂ.≈-equiv G.fmap-∘) ⟩
                            at G⟺G′.to (F′.omap B) ℂ.∘ G.fmap (F′.fmap f 𝔹.∘ at F⟺F′.to A)
                        ℂ.≈⟨ ℂ.≈-cong-right (G.fmap-cong (nat-cond (F⟺F′.to))) ⟩
                            at G⟺G′.to (F′.omap B) ℂ.∘ G.fmap (at F⟺F′.to B 𝔹.∘ F.fmap f)
                        ℂ.≈⟨ ℂ.≈-cong-right (G.fmap-∘) ⟩
                            at G⟺G′.to (F′.omap B) ℂ.∘ (G.fmap (at F⟺F′.to B) ℂ.∘ Functor.fmap (G ◯ F) f)
                        ℂ.≈⟨ IsEquivalence.sym ℂ.≈-equiv ℂ.∘-assoc ⟩
                            (at G⟺G′.to (F′.omap B) ℂ.∘ G.fmap (at F⟺F′.to B)) ℂ.∘ Functor.fmap (G ◯ F) f
                        ℂ.∎
                    }
                ; from = record
                    { at = λ A -> at G⟺G′.from (F.omap A) ℂ.∘ G′.fmap (at F⟺F′.from A)
                    ; nat-cond = λ {A} {B} {f} ->
                        ℂ.begin
                            Functor.fmap (G ◯ F) f ℂ.∘ (at G⟺G′.from (F.omap A) ℂ.∘ G′.fmap (at F⟺F′.from A))
                        ℂ.≈⟨ IsEquivalence.sym ℂ.≈-equiv ℂ.∘-assoc ⟩
                            (Functor.fmap (G ◯ F) f ℂ.∘ at G⟺G′.from (F.omap A)) ℂ.∘ G′.fmap (at F⟺F′.from A)
                        ℂ.≈⟨ ℂ.≈-cong-left (nat-cond (G⟺G′.from)) ⟩
                            (at G⟺G′.from (F.omap B) ℂ.∘ Functor.fmap (G′ ◯ F) f) ℂ.∘ G′.fmap (at F⟺F′.from A)
                        ℂ.≈⟨ ℂ.∘-assoc ⟩
                            at G⟺G′.from (F.omap B) ℂ.∘ (Functor.fmap (G′ ◯ F) f ℂ.∘ G′.fmap (at F⟺F′.from A))
                        ℂ.≈⟨ ℂ.≈-cong-right (IsEquivalence.sym ℂ.≈-equiv G′.fmap-∘) ⟩
                            at G⟺G′.from (F.omap B) ℂ.∘ G′.fmap (F.fmap f 𝔹.∘ at F⟺F′.from A)
                        ℂ.≈⟨ ℂ.≈-cong-right (G′.fmap-cong (nat-cond (F⟺F′.from))) ⟩
                            at G⟺G′.from (F.omap B) ℂ.∘ G′.fmap (at F⟺F′.from B 𝔹.∘ F′.fmap f)
                        ℂ.≈⟨ ℂ.≈-cong-right (G′.fmap-∘) ⟩
                            at G⟺G′.from (F.omap B) ℂ.∘ (G′.fmap (at F⟺F′.from B) ℂ.∘ Functor.fmap (G′ ◯ F′) f)
                        ℂ.≈⟨ IsEquivalence.sym ℂ.≈-equiv ℂ.∘-assoc ⟩
                            (at G⟺G′.from (F.omap B) ℂ.∘ G′.fmap (at F⟺F′.from B)) ℂ.∘ Functor.fmap (G′ ◯ F′) f
                        ℂ.∎
                    }
                ; iso1 = λ {A} ->
                    ℂ.begin
                        (at G⟺G′.from (F.omap A) ℂ.∘ G′.fmap (at F⟺F′.from A)) ℂ.∘
                        (at G⟺G′.to (F′.omap A) ℂ.∘ G.fmap (at F⟺F′.to A))
                    ℂ.≈⟨ ℂ.≈-cong-left (IsEquivalence.sym ℂ.≈-equiv (nat-cond G⟺G′.from)) ⟩
                        (G.fmap (at F⟺F′.from A) ℂ.∘ at G⟺G′.from ((F′.omap A))) ℂ.∘
                        (at G⟺G′.to (F′.omap A) ℂ.∘ G.fmap (at F⟺F′.to A))
                    ℂ.≈⟨ IsEquivalence.sym ℂ.≈-equiv (ℂ.∘-assoc) ⟩
                        ((G.fmap (at F⟺F′.from A) ℂ.∘ at G⟺G′.from ((F′.omap A))) ℂ.∘
                        at G⟺G′.to (F′.omap A)) ℂ.∘ G.fmap (at F⟺F′.to A)
                    ℂ.≈⟨ ℂ.≈-cong-left (ℂ.∘-assoc) ⟩
                        (G.fmap (at F⟺F′.from A) ℂ.∘
                            (at G⟺G′.from ((F′.omap A)) ℂ.∘ at G⟺G′.to (F′.omap A))) ℂ.∘
                        G.fmap (at F⟺F′.to A)
                    ℂ.≈⟨ ℂ.≈-cong-left (ℂ.≈-cong-right (G⟺G′.iso1)) ⟩
                        (G.fmap (at F⟺F′.from A) ℂ.∘
                            ℂ.id) ℂ.∘
                        G.fmap (at F⟺F′.to A)
                    ℂ.≈⟨ ℂ.≈-cong-left (ℂ.id-right) ⟩
                        G.fmap (at F⟺F′.from A) ℂ.∘
                        G.fmap (at F⟺F′.to A)
                    ℂ.≈⟨ IsEquivalence.sym ℂ.≈-equiv (G.fmap-∘) ⟩
                        G.fmap (at F⟺F′.from A 𝔹.∘ at F⟺F′.to A)
                    ℂ.≈⟨ G.fmap-cong (F⟺F′.iso1) ⟩
                        G.fmap 𝔹.id
                    ℂ.≈⟨ G.fmap-id ⟩
                        ℂ.id
                    ℂ.∎
                ; iso2 = λ {A} ->
                    ℂ.begin
                        (at G⟺G′.to (F′.omap A) ℂ.∘ G.fmap (at F⟺F′.to A)) ℂ.∘
                        (at G⟺G′.from (F.omap A) ℂ.∘ G′.fmap (at F⟺F′.from A))
                    ℂ.≈⟨ ℂ.≈-cong-left (IsEquivalence.sym ℂ.≈-equiv (nat-cond G⟺G′.to)) ⟩
                        (G′.fmap (at F⟺F′.to A) ℂ.∘ at G⟺G′.to ((F.omap A))) ℂ.∘
                        (at G⟺G′.from (F.omap A) ℂ.∘ G′.fmap (at F⟺F′.from A))
                    ℂ.≈⟨ IsEquivalence.sym ℂ.≈-equiv (ℂ.∘-assoc) ⟩
                        ((G′.fmap (at F⟺F′.to A) ℂ.∘ at G⟺G′.to ((F.omap A))) ℂ.∘
                        at G⟺G′.from (F.omap A)) ℂ.∘ G′.fmap (at F⟺F′.from A)
                    ℂ.≈⟨ ℂ.≈-cong-left (ℂ.∘-assoc) ⟩
                        (G′.fmap (at F⟺F′.to A) ℂ.∘
                            (at G⟺G′.to ((F.omap A)) ℂ.∘ at G⟺G′.from (F.omap A))) ℂ.∘
                        G′.fmap (at F⟺F′.from A)
                    ℂ.≈⟨ ℂ.≈-cong-left (ℂ.≈-cong-right (G⟺G′.iso2)) ⟩
                        (G′.fmap (at F⟺F′.to A) ℂ.∘
                            ℂ.id) ℂ.∘
                        G′.fmap (at F⟺F′.from A)
                    ℂ.≈⟨ ℂ.≈-cong-left (ℂ.id-right) ⟩
                        G′.fmap (at F⟺F′.to A) ℂ.∘
                        G′.fmap (at F⟺F′.from A)
                    ℂ.≈⟨ IsEquivalence.sym ℂ.≈-equiv (G′.fmap-∘) ⟩
                        G′.fmap (at F⟺F′.to A 𝔹.∘ at F⟺F′.from A)
                    ℂ.≈⟨ G′.fmap-cong (F⟺F′.iso2) ⟩
                        G′.fmap 𝔹.id
                    ℂ.≈⟨ G′.fmap-id ⟩
                        ℂ.id
                    ℂ.∎
                }
                where
                private module F = Functor F
                private module F′ = Functor F′
                private module G = Functor G
                private module G′ = Functor G′
                private module 𝔸 = Category 𝔸
                private module 𝔹 = Category 𝔹
                private module ℂ = Category ℂ
                open import Relation.Binary using (IsEquivalence)
                open _⟹_
                open _⟺_
                private module F⟺F′ = _⟺_ F⟺F′
                private module G⟺G′ = _⟺_ G⟺G′
