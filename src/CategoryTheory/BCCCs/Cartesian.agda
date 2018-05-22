
-- Products and Cartesian categories
module CategoryTheory.BCCCs.Cartesian where

open import CategoryTheory.Categories

open import Relation.Binary using (IsEquivalence)

module _ {n} (ℂ : Category n) where

    open Category ℂ

    -- Terminal object in a category
    record TerminalObj : Set (lsuc n) where
        field
            -- | Data
            -- The terminal object
            ⊤ : obj
            -- Canonical morphism
            ! : {A : obj} -> (A ~> ⊤)

            -- | Laws
            -- Need to show that the canonical morphism ! is unique
            !-unique : {A : obj} -> (m : A ~> ⊤)
                  -> m ≈ !

    -- Product of two objects
    -- Based on github.com/copumpkin/categories
    record Product (A B : obj) : Set (lsuc n) where
        infix 10 ⟨_,_⟩
        field
            -- | Data
            -- Product of A and B
            A⊗B : obj
            -- First projection
            π₁ : A⊗B ~> A
            -- Second projection
            π₂ : A⊗B ~> B
            -- Canonical mediator
            ⟨_,_⟩ : ∀{P} -> (P ~> A) -> (P ~> B) -> (P ~> A⊗B)

            -- | Laws
            -- ⟨_,_⟩ expresses that given another candidate product C
            -- and candidate projections to A and B there is a morphism
            -- from P to A⊗B. We need to check that this mediator makes
            -- the product diagram commute and is unique.

            π₁-comm : ∀{P} -> {p₁ : P ~> A} {p₂ : P ~> B}
                   -> π₁ ∘ ⟨ p₁ , p₂ ⟩ ≈ p₁
            π₂-comm : ∀{P} -> {p₁ : P ~> A} {p₂ : P ~> B}
                   -> π₂ ∘ ⟨ p₁ , p₂ ⟩ ≈ p₂
            ⊗-unique  : ∀{P} -> {p₁ : P ~> A} {p₂ : P ~> B} {m : P ~> A⊗B}
                   -> π₁ ∘ m ≈ p₁ -> π₂ ∘ m ≈ p₂ -> ⟨ p₁ , p₂ ⟩ ≈ m

        -- η-expansion of function pairs (via morphisms)
        ⊗-η-exp : ∀{P} -> {m : P ~> A⊗B}
               -> ⟨ π₁ ∘ m , π₂ ∘ m ⟩ ≈ m
        ⊗-η-exp = ⊗-unique r≈ r≈

        -- Pairing of projection functions is the identity
        ⊗-η-id : ⟨ π₁ , π₂ ⟩ ≈ id
        ⊗-η-id = ⊗-unique id-right id-right

        -- Congruence over function pairing
        ⟨,⟩-cong : ∀{P} -> {p₁ q₁ : P ~> A} {p₂ q₂ : P ~> B}
               -> p₁ ≈ q₁ -> p₂ ≈ q₂
               -> ⟨ p₁ , p₂ ⟩ ≈ ⟨ q₁ , q₂ ⟩
        ⟨,⟩-cong pr1 pr2 = ⊗-unique (π₁-comm ≈> pr1 [sym]) (π₂-comm ≈> pr2 [sym])

        ⟨,⟩-distrib : ∀{P Q} -> {h : P ~> Q} {f : Q ~> A} {g : Q ~> B}
                  -> ⟨ f , g ⟩ ∘ h ≈ ⟨ f ∘ h , g ∘ h ⟩
        ⟨,⟩-distrib = ⊗-unique (∘-assoc [sym] ≈> ≈-cong-left π₁-comm)
                            (∘-assoc [sym] ≈> ≈-cong-left π₂-comm) [sym]

-- Type class for Cartesian categories
record Cartesian {n} (ℂ : Category n) : Set (lsuc n) where
    open Category ℂ
    field
        -- | Data
        -- Terminal object
        term : TerminalObj ℂ
        -- Binary products for all pairs of objects
        prod : ∀(A B : obj) -> Product ℂ A B

    open TerminalObj term public
    open module P {A} {B} = Product (prod A B) public

    -- Shorthand for sum object
    infixl 25 _⊗_
    _⊗_ : (A B : obj) -> obj
    A ⊗ B = A⊗B {A} {B}

    -- Parallel product of morphisms
    infixl 65 _*_
    _*_ : {A B P Q : obj} -> (A ~> P) -> (B ~> Q)
       -> (A ⊗ B ~> P ⊗ Q)
    _*_ {A} {B} {P} {Q} f g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩

    -- Parallel product with an idempotent morphism distributes over ∘
    *-idemp-dist-∘ : {A B C D : obj}{g : B ~> C}{f : A ~> B}{h : D ~> D}
            -> h ∘ h ≈ h
            -> g * h ∘ f * h ≈ (g ∘ f) * h
    *-idemp-dist-∘ {g = g}{f}{h} idemp = ⊗-unique u₁ u₂ [sym]
        where
        u₁ : π₁ ∘ (g * h ∘ f * h) ≈ (g ∘ f) ∘ π₁
        u₁ = ∘-assoc [sym] ≈> ≈-cong-left π₁-comm
          ≈> ∘-assoc ≈> ≈-cong-right π₁-comm ≈> ∘-assoc [sym]
        u₂ : π₂ ∘ (g * h ∘ f * h) ≈ h ∘ π₂
        u₂ = ∘-assoc [sym] ≈> ≈-cong-left π₂-comm
          ≈> ∘-assoc ≈> ≈-cong-right π₂-comm
          ≈> ∘-assoc [sym] ≈> ≈-cong-left idemp

    -- Parallel product with an idempotent morphism distributes over ∘
    *-id-dist-∘ : {A B C : obj}{g : B ~> C}{f : A ~> B}
            -> (_*_ {B = B} g id) ∘ f * id ≈ (g ∘ f) * id
    *-id-dist-∘ = *-idemp-dist-∘ id-right

    -- Commutativity of product
    comm : {A B : obj} -> A ⊗ B ~> B ⊗ A
    comm {A}{B} = ⟨ π₂ , π₁ ⟩

    -- Associativity of product
    assoc-left : {A B C : obj} -> A ⊗ (B ⊗ C) ~> (A ⊗ B) ⊗ C
    assoc-left = ⟨ ⟨ π₁ , (π₁ ∘ π₂) ⟩ , π₂ ∘ π₂ ⟩

    assoc-right : {A B C : obj} -> (A ⊗ B) ⊗ C ~> A ⊗ (B ⊗ C)
    assoc-right = ⟨ π₁ ∘ π₁ , ⟨ (π₂ ∘ π₁) , π₂ ⟩ ⟩

    -- Left and right unit for product
    unit-left : {A : obj} -> ⊤ ⊗ A ~> A
    unit-left = π₂

    unit-right : {A : obj} -> A ⊗ ⊤ ~> A
    unit-right = π₁

    -- The terminal object is the unit for product
    ⊤-left-cancel : ∀{A} -> ⊤ ⊗ A <~> A
    ⊤-left-cancel {A} = record
        { iso~> = π₂
        ; iso<~ = ⟨ ! , id ⟩
        ; iso-id₁ = iso-id₁-⊤
        ; iso-id₂ = π₂-comm
        }
        where
        iso-id₁-⊤ : ⟨ ! , id ⟩ ∘ π₂ ≈ id
        iso-id₁-⊤ =
            begin
                ⟨ ! , id ⟩ ∘ π₂
            ≈⟨ ⟨,⟩-distrib ⟩
                ⟨ ! ∘ π₂ , id ∘ π₂ ⟩
            ≈⟨ ⟨,⟩-cong r≈ id-left ⟩
                ⟨ ! ∘ π₂ , π₂ ⟩
            ≈⟨ ⟨,⟩-cong (!-unique (! ∘ π₂)) r≈ ⟩
                ⟨ ! , π₂ ⟩
            ≈⟨ ⟨,⟩-cong ((!-unique π₁) [sym]) r≈ ⟩
                ⟨ π₁ , π₂ ⟩
            ≈⟨ ⊗-η-id ⟩
                id
            ∎

    ⊤-right-cancel : ∀{A} -> A ⊗ ⊤ <~> A
    ⊤-right-cancel {A} = record
        { iso~> = π₁
        ; iso<~ = ⟨ id , ! ⟩
        ; iso-id₁ = iso-id₁-⊤
        ; iso-id₂ = π₁-comm
        }
        where
        iso-id₁-⊤ : ⟨ id , ! ⟩ ∘ π₁ ≈ id
        iso-id₁-⊤ =
            begin
                ⟨ id , ! ⟩ ∘ π₁
            ≈⟨ ⟨,⟩-distrib ⟩
                ⟨ id ∘ π₁ , ! ∘ π₁ ⟩
            ≈⟨ ⟨,⟩-cong id-left r≈ ⟩
                ⟨ π₁ , ! ∘ π₁ ⟩
            ≈⟨ ⟨,⟩-cong r≈ (!-unique (! ∘ π₁)) ⟩
                ⟨ π₁ , ! ⟩
            ≈⟨ ⟨,⟩-cong r≈ ((!-unique π₂) [sym]) ⟩
                ⟨ π₁ , π₂ ⟩
            ≈⟨ ⊗-η-id ⟩
                id
            ∎
