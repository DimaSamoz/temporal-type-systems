
-- Syntactic kits from Conor McBride's
-- "Type-Preserving Renaming and Substitution"
module Syntax.Substitution.Kits where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms

open import CategoryTheory.Categories

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

-- Type of entities that we can traverse
-- (instantiated by variables and types)
Schema : Set₁
Schema = Context -> Judgement -> Set

-- Explicit substitution from term in context Δ to term in context Γ
-- E.g. from Γ ⌊ A ⌋ Γ′ ⊢ N : B to Γ ⌊⌋ Γ′ ⊢ N[σ] : B
-- using substitution Γ ⌊⌋ Γ′ ⊢ σ : Γ ⌊ A ⌋ Γ′
data Subst (𝒮 : Schema) : Context -> Context -> Set where
    -- Empty substitution
    ●   : ∀ {Δ}     -> Subst 𝒮 ∙ Δ
    -- Extending the domain of a substitution
    _▸_ : ∀ {A Γ Δ} -> (σ : Subst 𝒮 Γ Δ) -> (T : 𝒮 Δ A) -> Subst 𝒮 (Γ , A) Δ

-- Syntactic kit grouping together common operations on traversable
-- syntactic entities such as variables and terms
record Kit (𝒮 : Schema) : Set where
    field
        -- Convert a variable to the entity
        𝓋 : ∀ {Γ A} -> A ∈ Γ -> 𝒮 Γ A
        -- Convert the entity to a term
        𝓉 : ∀ {Γ A} -> 𝒮 Γ A -> Γ ⊢ A
        -- Weaken the entity
        𝓌 : ∀ {B Γ A} -> 𝒮 Γ A -> 𝒮 (Γ , B) A
        -- Stabilise the context of the entity
        𝒶 : ∀ {Γ A} -> 𝒮 Γ (A always) -> 𝒮 (Γ ˢ) (A always)

-- Substitutable kit
record SubstKit (𝒮 : Schema) : Set where
    field
        -- Underlying traversable kit
        𝓀 : Kit 𝒮
        -- Apply substitution to a kit
        𝓈 : ∀ {Γ Δ A} -> Subst 𝒮 Γ Δ -> 𝒮 Γ A -> 𝒮 Δ A

open Kit

-- | Combinators
-- | All take a syntactic (substitutable) kit as an argument
-- | which provides the necessary operations

-- Weakening a substitution
-- Δ ⊢ σ : Γ to (Δ , A) ⊢ σ : Γ
_⁺_ : ∀ {A 𝒮 Γ Δ} -> Subst 𝒮 Γ Δ -> Kit 𝒮 -> Subst 𝒮 Γ (Δ , A)
●       ⁺ _ = ●
(σ ▸ T) ⁺ k = (σ ⁺ k) ▸ 𝓌 k T
infixl 40 _⁺_

-- Lifting a substitution
-- Δ ⊢ σ : Γ to (Δ , A) ⊢ σ : (Γ , A)
_↑_ : ∀ {A 𝒮 Γ Δ} -> Subst 𝒮 Γ Δ -> Kit 𝒮 -> Subst 𝒮 (Γ , A) (Δ , A)
σ ↑ k = (σ ⁺ k) ▸ 𝓋 k top
infixl 40 _↑_

-- Stabilising a substitution
-- Δ ⊢ σ : Γ to Δ ˢ ⊢ σ : Γ ˢ
_↓ˢ_ : ∀ {𝒮 Γ Δ} -> Subst 𝒮 Γ Δ -> Kit 𝒮 -> Subst 𝒮 (Γ ˢ) (Δ ˢ)
●                    ↓ˢ _ = ●
(_▸_ {A now} σ T)    ↓ˢ k = σ ↓ˢ k
(_▸_ {A always} σ T) ↓ˢ k = (σ ↓ˢ k) ▸ 𝒶 k T
infixl 40 _↓ˢ_

-- Identity substitution
idₛ : ∀ {Γ 𝒮} -> Kit 𝒮 -> Subst 𝒮 Γ Γ
idₛ {∙}     k = ●
idₛ {Γ , _} k = idₛ k ↑ k

-- Composition of substitutions
_∘[_]ₛ_ : ∀ {𝒮 Γ Δ Ξ} -> Subst 𝒮 Δ Ξ -> SubstKit 𝒮 -> Subst 𝒮 Γ Δ -> Subst 𝒮 Γ Ξ
σ₂ ∘[ k ]ₛ ●        = ●
σ₂ ∘[ k ]ₛ (σ₁ ▸ T) = (σ₂ ∘[ k ]ₛ σ₁) ▸ SubstKit.𝓈 k σ₂ T

-- Substitution from an order-preserving embedding
-- Γ ⊆ Δ to Δ ⊢ σ : Γ
_⊆ₛ_ : ∀ {𝒮 Γ Δ} -> Γ ⊆ Δ -> Kit 𝒮 -> Subst 𝒮 Γ Δ
refl ⊆ₛ k     = idₛ k
(keep s) ⊆ₛ k = (s ⊆ₛ k) ↑ k
(drop s) ⊆ₛ k = (s ⊆ₛ k) ⁺ k

-- Substitution from propositional equality of contexts
_≡ₛ_ : ∀ {𝒮 Γ Δ} -> Γ ≡ Δ -> Kit 𝒮 -> Subst 𝒮 Γ Δ
refl ≡ₛ k = idₛ k

-- Substitution from idempotence of stabilisation
_ˢˢₛ_ : ∀ {𝒮} -> (Γ : Context) -> Kit 𝒮 -> Subst 𝒮 (Γ ˢ) (Γ ˢ ˢ)
∙ ˢˢₛ k = ●
(Γ , A now) ˢˢₛ k = Γ ˢˢₛ k
(Γ , A always) ˢˢₛ k = (Γ ˢˢₛ k) ↑ k

-- | Standard substitutions
-- | Common transformations between contexts

module _ {𝒮 : Schema} (sk : SubstKit 𝒮) where
    open SubstKit sk
    open Kit 𝓀

    -- | Weakening

    -- Weakening the top of the context
    weak-topₛ : ∀{A Γ} -> Subst 𝒮 Γ (Γ , A)
    weak-topₛ = idₛ 𝓀 ⁺ 𝓀

    -- Weakening the middle of the context
    weak-midₛ : ∀{A} Γ Γ′ -> Subst 𝒮 (Γ ⌊⌋ Γ′) (Γ ⌊ A ⌋ Γ′)
    weak-midₛ Γ ∙ = weak-topₛ
    weak-midₛ Γ (Γ′ , B) = weak-midₛ Γ Γ′ ↑ 𝓀

    -- General weakening from an OPE
    weakₛ : ∀{Γ Δ} -> Γ ⊆ Δ -> Subst 𝒮 Γ Δ
    weakₛ = _⊆ₛ 𝓀

    -- | Exchange

    -- Exchange on top
    ex-topₛ : ∀{A B} Γ -> Subst 𝒮 (Γ , A , B) (Γ , B , A)
    ex-topₛ Γ = (idₛ 𝓀 ⁺ 𝓀 ↑ 𝓀) ▸ (𝓋 𝓀 (pop top))

    -- General exchange lemma
    exₛ : ∀{A B} Γ Γ′ Γ″ -> Subst 𝒮 (Γ ⌊ A ⌋ Γ′ ⌊ B ⌋ Γ″) (Γ ⌊ B ⌋ Γ′ ⌊ A ⌋ Γ″)
    exₛ Γ ∙ ∙ = ex-topₛ Γ
    exₛ {A} {B} Γ (Γ′ , C) ∙ =
        (exₛ Γ Γ′ [ A ] ∘[ sk ]ₛ ex-topₛ (Γ , C ⌊⌋ Γ′)) ∘[ sk ]ₛ exₛ Γ Γ′ [ B ]
    exₛ Γ ∙ (Γ″ , D) = exₛ Γ ∙ Γ″ ↑ 𝓀
    exₛ Γ (Γ′ , C) (Γ″ , D) = exₛ Γ (Γ′ , C) Γ″ ↑ 𝓀

    -- | Contraction

    -- Contraction on top
    contr-topₛ : ∀{A Γ} -> Subst 𝒮 (Γ , A , A) (Γ , A)
    contr-topₛ = (idₛ 𝓀) ▸ (𝓋 𝓀 top)

    -- General contraction lemma (left)
    contr-lₛ : ∀{A} Γ Γ′ Γ″ -> Subst 𝒮 (Γ ⌊ A ⌋ Γ′ ⌊ A ⌋ Γ″) (Γ ⌊ A ⌋ Γ′ ⌊⌋ Γ″)
    contr-lₛ Γ ∙ ∙ = contr-topₛ
    contr-lₛ Γ (Γ′ , B) ∙ = (idₛ 𝓀) ▸ (𝓌 𝓀 (𝓈 (contr-lₛ Γ Γ′ ∙) (𝓋 𝓀 top)))
    contr-lₛ Γ ∙ (Γ″ , C) = contr-lₛ Γ ∙ Γ″ ↑ 𝓀
    contr-lₛ Γ (Γ′ , B) (Γ″ , C) = contr-lₛ Γ (Γ′ , B) Γ″ ↑ 𝓀

    -- General contraction lemma (right)
    contr-rₛ : ∀{A} Γ Γ′ Γ″ -> Subst 𝒮 (Γ ⌊ A ⌋ Γ′ ⌊ A ⌋ Γ″) (Γ ⌊⌋ Γ′ ⌊ A ⌋ Γ″)
    contr-rₛ Γ ∙ ∙ = contr-topₛ
    contr-rₛ {A} Γ (Γ′ , B) ∙ =
        (ex-topₛ (Γ ⌊⌋ Γ′) ∘[ sk ]ₛ contr-rₛ Γ Γ′ [ B ]) ∘[ sk ]ₛ ex-topₛ (Γ , A ⌊⌋ Γ′)
    contr-rₛ Γ ∙ (Γ″ , C) = contr-rₛ Γ ∙ Γ″ ↑ 𝓀
    contr-rₛ Γ (Γ′ , B) (Γ″ , C) = contr-rₛ Γ (Γ′ , B) Γ″ ↑ 𝓀

    -- | Movement

    -- Moving a variable to the right in the context
    move-rₛ : ∀{A} Γ Γ′ Γ″ -> Subst 𝒮 (Γ ⌊ A ⌋ Γ′ ⌊⌋ Γ″) (Γ ⌊⌋ Γ′ ⌊ A ⌋ Γ″)
    move-rₛ {A} Γ Γ′ Γ″ = contr-rₛ Γ Γ′ Γ″ ∘[ sk ]ₛ weak-midₛ (Γ ⌊ A ⌋ Γ′) Γ″

    -- Moving a variable to the left in the context
    -- Bit verbose as we have to deal with associativity
    move-lₛ : ∀{A} Γ Γ′ Γ″ -> Subst 𝒮 (Γ ⌊⌋ Γ′ ⌊ A ⌋ Γ″) (Γ ⌊ A ⌋ Γ′ ⌊⌋ Γ″)
    move-lₛ {A} Γ Γ′ Γ″
        =        contr-lₛ Γ Γ′ Γ″
        ∘[ sk ]ₛ ((sym (⌊A⌋-assoc Γ Γ′ Γ″ A A) ≡ₛ 𝓀)
        ∘[ sk ]ₛ ((weak-midₛ {A} Γ (Γ′ ⌊ A ⌋ Γ″))
        ∘[ sk ]ₛ (⌊⌋-assoc Γ (Γ′ , A) Γ″ ≡ₛ 𝓀)))

    -- Moving a variable to the right in the stabilised context context
    moveˢ-rₛ : ∀{A} Γ Γ′ Γ″ -> Subst 𝒮 (Γ ˢ ⌊ A ⌋ (Γ′ ⌊⌋ Γ″) ˢ) ((Γ ⌊⌋ Γ′) ˢ ⌊ A ⌋ Γ″ ˢ)
    moveˢ-rₛ {A} Γ Γ′ Γ″
        rewrite ˢ-pres-⌊⌋ Γ Γ′
              | ˢ-pres-⌊⌋ Γ′ Γ″
              | sym (⌊⌋-assoc (Γ ˢ , A) (Γ′ ˢ) (Γ″ ˢ))
        = move-rₛ (Γ ˢ) (Γ′ ˢ) (Γ″ ˢ)

    -- | Substitution

    -- Substitution for the top of the context
    sub-topₛ : ∀{A Γ} -> 𝒮 Γ A -> Subst 𝒮 (Γ , A) Γ
    sub-topₛ T = (idₛ 𝓀) ▸ T

    -- Substitution for the top of a stabilised context
    sub-topˢₛ : ∀{Γ A} -> 𝒮 Γ A -> Subst 𝒮 (Γ ˢ , A) Γ
    sub-topˢₛ {Γ} T = (Γˢ⊆Γ Γ ⊆ₛ 𝓀) ▸ T

    -- Substitution for the middle of the context
    sub-midₛ : ∀{A} Γ Γ′ -> 𝒮 (Γ ⌊⌋ Γ′) A -> Subst 𝒮 (Γ ⌊ A ⌋ Γ′) (Γ ⌊⌋ Γ′)
    sub-midₛ Γ Γ′ T = sub-topₛ T ∘[ sk ]ₛ move-rₛ Γ Γ′ ∙
