
{- Category of categories -}
module CategoryTheory.2Categories.Cat where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans

-- Category of categories
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
                    begin
                        F.fmap f ∘ F.fmap ℂ.id
                    ≈⟨ ≈-cong-right (F.fmap-id) ⟩
                        F.fmap f ∘ id
                    ≈⟨ id-comm ⟩
                        id ∘ Functor.fmap (I ◯ F) f
                    ≈⟨ ≈-cong-left (F.fmap-id [sym]) ⟩
                        F.fmap ℂ.id ∘ Functor.fmap (I ◯ F) f
                    ∎
                }
            ; from = record {
                at = λ A -> F.fmap ℂ.id
                ; nat-cond =  λ {A} {B} {f} ->
                    begin
                        Functor.fmap (I ◯ F) f ∘ F.fmap ℂ.id
                    ≈⟨ ≈-cong-right (F.fmap-id) ⟩
                        Functor.fmap (I ◯ F) f ∘ id
                    ≈⟨ id-comm ⟩
                        id ∘ F.fmap f
                    ≈⟨ ≈-cong-left (F.fmap-id [sym]) ⟩
                        F.fmap ℂ.id ∘ F.fmap f
                    ∎
                }
            ; iso1 = iso-proof
            ; iso2 = iso-proof }
            where
            open import Relation.Binary using (IsEquivalence)
            private module F = Functor F
            private module ℂ = Category ℂ
            open Category 𝔻

            iso-proof : ∀{A : ℂ.obj} -> F.fmap (ℂ.id {A}) ∘ F.fmap ℂ.id ≈ id
            iso-proof =
                begin
                    F.fmap ℂ.id ∘ F.fmap ℂ.id
                ≈⟨ ≈-cong F.fmap-id F.fmap-id ⟩
                    id ∘ id
                ≈⟨ id-left ⟩
                    id
                ∎

        id-right-ℂat : {ℂ 𝔻 : Category n} {F : Functor ℂ 𝔻} -> (F ◯ I) ⟺ F
        id-right-ℂat {ℂ} {𝔻} {F} = record
            { to = record
                { at = λ A -> F.fmap ℂ.id
                ; nat-cond =  λ {A} {B} {f} ->
                    begin
                        F.fmap f ∘ F.fmap ℂ.id
                    ≈⟨ ≈-cong-right (F.fmap-id) ⟩
                        F.fmap f ∘ id
                    ≈⟨ id-comm ⟩
                        id ∘ Functor.fmap (F ◯ I) f
                    ≈⟨ ≈-cong-left (F.fmap-id [sym]) ⟩
                        F.fmap ℂ.id ∘ Functor.fmap (F ◯ I) f
                    ∎
                }
            ; from = record {
                at = λ A -> F.fmap ℂ.id
                ; nat-cond =  λ {A} {B} {f} ->
                    begin
                        Functor.fmap (F ◯ I) f ∘ F.fmap ℂ.id
                    ≈⟨ ≈-cong-right (F.fmap-id) ⟩
                        Functor.fmap (F ◯ I) f ∘ id
                    ≈⟨ id-right ⟩
                        Functor.fmap (F ◯ I) f
                    ≈⟨ id-left [sym] ⟩
                        id ∘ F.fmap f
                    ≈⟨ ≈-cong-left (F.fmap-id [sym]) ⟩
                        F.fmap ℂ.id ∘ F.fmap f
                    ∎
                }
            ; iso1 = iso-proof
            ; iso2 = iso-proof }
            where
            open import Relation.Binary using (IsEquivalence)
            private module F = Functor F
            private module ℂ = Category ℂ
            open Category 𝔻

            iso-proof : ∀{A : ℂ.obj} -> F.fmap (ℂ.id {A}) ∘ F.fmap ℂ.id ≈ id
            iso-proof =
                begin
                    F.fmap ℂ.id ∘ F.fmap ℂ.id
                ≈⟨ ≈-cong F.fmap-id F.fmap-id ⟩
                    id ∘ id
                ≈⟨ id-left ⟩
                    id
                ∎

        ∘-assoc-ℂat : {𝔸 𝔹 ℂ 𝔻 : Category n} {F : Functor 𝔸 𝔹}
                      {G : Functor 𝔹 ℂ} {H : Functor ℂ 𝔻}
                   -> (H ◯ G) ◯ F ⟺ H ◯ (G ◯ F)
        ∘-assoc-ℂat {𝔸} {𝔹} {ℂ} {𝔻} {F} {G} {H} = record
            { to = record
                { at = λ A -> Functor.fmap (H ◯ (G ◯ F)) 𝔸.id
                ; nat-cond = λ {A} {B} {f} ->
                    begin
                        Functor.fmap (H ◯ (G ◯ F)) f ∘ Functor.fmap (H ◯ (G ◯ F)) 𝔸.id
                    ≈⟨ ≈-cong-right (Functor.fmap-id (H ◯ (G ◯ F))) ⟩
                        Functor.fmap (H ◯ (G ◯ F)) f ∘ id
                    ≈⟨ id-comm ⟩
                        id ∘ Functor.fmap (H ◯ G ◯ F) f
                    ≈⟨ ≈-cong-left (Functor.fmap-id ((H ◯ G) ◯ F) [sym]) ⟩
                        Functor.fmap (H ◯ G ◯ F) 𝔸.id ∘ Functor.fmap (H ◯ G ◯ F) f
                    ∎
                }
            ; from = record
                { at = λ A -> Functor.fmap ((H ◯ G) ◯ F) 𝔸.id
                ; nat-cond = λ {A} {B} {f} ->
                    begin
                        Functor.fmap (H ◯ (G ◯ F)) f ∘ Functor.fmap ((H ◯ G) ◯ F) 𝔸.id
                    ≈⟨ ≈-cong-right (Functor.fmap-id ((H ◯ G) ◯ F)) ⟩
                        Functor.fmap (H ◯ (G ◯ F)) f ∘ id
                    ≈⟨ id-comm ⟩
                        id ∘ Functor.fmap (H ◯ G ◯ F) f
                    ≈⟨ ≈-cong-left (Functor.fmap-id ((H ◯ G) ◯ F) [sym]) ⟩
                        Functor.fmap (H ◯ G ◯ F) 𝔸.id ∘ Functor.fmap (H ◯ G ◯ F) f
                    ∎
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
            open Category 𝔻

            iso-proof : ∀{A : 𝔸.obj}
                     ->  Functor.fmap ((H ◯ G) ◯ F) (𝔸.id {A}) ∘ Functor.fmap (H ◯ (G ◯ F)) 𝔸.id
                     ≈ id
            iso-proof =
                begin
                    Functor.fmap ((H ◯ G) ◯ F) 𝔸.id ∘ Functor.fmap (H ◯ (G ◯ F)) 𝔸.id
                ≈⟨ ≈-cong (Functor.fmap-id ((H ◯ G) ◯ F)) (Functor.fmap-id (H ◯ (G ◯ F))) ⟩
                    id ∘ id
                ≈⟨ id-left ⟩
                    id
                ∎

        ≈-cong-ℂat : {𝔸 𝔹 ℂ : Category n} {F F′ : Functor 𝔸 𝔹} {G G′ : Functor 𝔹 ℂ}
                  -> F ⟺ F′ -> G ⟺ G′ -> (G ◯ F) ⟺ (G′ ◯ F′)
        ≈-cong-ℂat {𝔸}{𝔹}{ℂ}{F}{F′}{G}{G′} F⟺F′ G⟺G′ = record
            { to = record
                { at = λ A -> at G⟺G′.to (F′.omap A) ∘ G.fmap (at F⟺F′.to A)
                ; nat-cond = λ {A} {B} {f} ->
                    begin
                        Functor.fmap (G′ ◯ F′) f ∘ (at G⟺G′.to (F′.omap A) ∘ G.fmap (at F⟺F′.to A))
                    ≈⟨ ∘-assoc [sym] ≈> ≈-cong-left (nat-cond (G⟺G′.to))⟩
                        (at G⟺G′.to (F′.omap B) ∘ Functor.fmap (G ◯ F′) f) ∘ G.fmap (at F⟺F′.to A)
                    ≈⟨ ∘-assoc ≈> ≈-cong-right (G.fmap-∘ [sym])⟩
                        at G⟺G′.to (F′.omap B) ∘ G.fmap (F′.fmap f 𝔹.∘ at F⟺F′.to A)
                    ≈⟨ ≈-cong-right (G.fmap-cong (nat-cond (F⟺F′.to))) ⟩
                        at G⟺G′.to (F′.omap B) ∘ G.fmap (at F⟺F′.to B 𝔹.∘ F.fmap f)
                    ≈⟨ ≈-cong-right (G.fmap-∘) ⟩
                        at G⟺G′.to (F′.omap B) ∘ (G.fmap (at F⟺F′.to B) ∘ Functor.fmap (G ◯ F) f)
                    ≈⟨ ∘-assoc [sym] ⟩
                        (at G⟺G′.to (F′.omap B) ∘ G.fmap (at F⟺F′.to B)) ∘ Functor.fmap (G ◯ F) f
                    ∎
                }
            ; from = record
                { at = λ A -> at G⟺G′.from (F.omap A) ∘ G′.fmap (at F⟺F′.from A)
                ; nat-cond = λ {A} {B} {f} ->
                    begin
                        Functor.fmap (G ◯ F) f ∘ (at G⟺G′.from (F.omap A) ∘ G′.fmap (at F⟺F′.from A))
                    ≈⟨ ∘-assoc [sym] ≈> ≈-cong-left (nat-cond (G⟺G′.from)) ⟩
                        (at G⟺G′.from (F.omap B) ∘ Functor.fmap (G′ ◯ F) f) ∘ G′.fmap (at F⟺F′.from A)
                    ≈⟨ ∘-assoc ≈> ≈-cong-right (G′.fmap-∘ [sym])⟩
                        at G⟺G′.from (F.omap B) ∘ G′.fmap (F.fmap f 𝔹.∘ at F⟺F′.from A)
                    ≈⟨ ≈-cong-right (G′.fmap-cong (nat-cond (F⟺F′.from))) ⟩
                        at G⟺G′.from (F.omap B) ∘ G′.fmap (at F⟺F′.from B 𝔹.∘ F′.fmap f)
                    ≈⟨ ≈-cong-right (G′.fmap-∘) ⟩
                        at G⟺G′.from (F.omap B) ∘ (G′.fmap (at F⟺F′.from B) ∘ Functor.fmap (G′ ◯ F′) f)
                    ≈⟨ ∘-assoc [sym] ⟩
                        (at G⟺G′.from (F.omap B) ∘ G′.fmap (at F⟺F′.from B)) ∘ Functor.fmap (G′ ◯ F′) f
                    ∎
                }
            ; iso1 = λ {A} ->
                begin
                    (at G⟺G′.from (F.omap A) ∘ G′.fmap (at F⟺F′.from A)) ∘
                    (at G⟺G′.to (F′.omap A) ∘ G.fmap (at F⟺F′.to A))
                ≈⟨ ≈-cong-left (nat-cond G⟺G′.from [sym]) ⟩
                    (G.fmap (at F⟺F′.from A) ∘ at G⟺G′.from ((F′.omap A))) ∘
                    (at G⟺G′.to (F′.omap A) ∘ G.fmap (at F⟺F′.to A))
                ≈⟨ ∘-assoc [sym] ≈> ≈-cong-left (∘-assoc) ⟩
                    (G.fmap (at F⟺F′.from A) ∘
                        (at G⟺G′.from ((F′.omap A)) ∘ at G⟺G′.to (F′.omap A))) ∘
                    G.fmap (at F⟺F′.to A)
                ≈⟨ ≈-cong-left (≈-cong-right (G⟺G′.iso1)) ⟩
                    (G.fmap (at F⟺F′.from A) ∘
                        id) ∘
                    G.fmap (at F⟺F′.to A)
                ≈⟨ ≈-cong-left (id-right) ⟩
                    G.fmap (at F⟺F′.from A) ∘
                    G.fmap (at F⟺F′.to A)
                ≈⟨ G.fmap-∘ [sym] ⟩
                    G.fmap (at F⟺F′.from A 𝔹.∘ at F⟺F′.to A)
                ≈⟨ G.fmap-cong (F⟺F′.iso1) ⟩
                    G.fmap 𝔹.id
                ≈⟨ G.fmap-id ⟩
                    id
                ∎
            ; iso2 = λ {A} ->
                begin
                    (at G⟺G′.to (F′.omap A) ∘ G.fmap (at F⟺F′.to A)) ∘
                    (at G⟺G′.from (F.omap A) ∘ G′.fmap (at F⟺F′.from A))
                ≈⟨ ≈-cong-left (nat-cond G⟺G′.to [sym]) ⟩
                    (G′.fmap (at F⟺F′.to A) ∘ at G⟺G′.to ((F.omap A))) ∘
                    (at G⟺G′.from (F.omap A) ∘ G′.fmap (at F⟺F′.from A))
                ≈⟨ ∘-assoc [sym] ≈> ≈-cong-left (∘-assoc) ⟩
                    (G′.fmap (at F⟺F′.to A) ∘
                        (at G⟺G′.to ((F.omap A)) ∘ at G⟺G′.from (F.omap A))) ∘
                    G′.fmap (at F⟺F′.from A)
                ≈⟨ ≈-cong-left (≈-cong-right (G⟺G′.iso2)) ⟩
                    (G′.fmap (at F⟺F′.to A) ∘
                        id) ∘
                    G′.fmap (at F⟺F′.from A)
                ≈⟨ ≈-cong-left (id-right) ⟩
                    G′.fmap (at F⟺F′.to A) ∘
                    G′.fmap (at F⟺F′.from A)
                ≈⟨ G′.fmap-∘ [sym] ⟩
                    G′.fmap (at F⟺F′.to A 𝔹.∘ at F⟺F′.from A)
                ≈⟨ G′.fmap-cong (F⟺F′.iso2) ⟩
                    G′.fmap 𝔹.id
                ≈⟨ G′.fmap-id ⟩
                    id
                ∎
            }
            where
            private module F = Functor F
            private module F′ = Functor F′
            private module G = Functor G
            private module G′ = Functor G′
            private module 𝔸 = Category 𝔸
            private module 𝔹 = Category 𝔹
            open Category ℂ
            open _⟹_
            open _⟺_
            private module F⟺F′ = _⟺_ F⟺F′
            private module G⟺G′ = _⟺_ G⟺G′
