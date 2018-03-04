
-- Typing contexts and environments
module Syntax.Context where

open import Syntax.Types

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

-- | Data types

-- A type judgement with temporal qualifiers:
-- a type is either inhabited now, or always
data Judgement : Set where
    _now    : Type -> Judgement
    _always : Type -> Judgement
infixl 60 _now
infixl 60 _always

-- Typing context as a list of types
data Context : Set where
    ∙ : Context
    _,_ : Context -> Judgement -> Context
infixl 50 _,_

-- Filter out the stable types from the context
_ˢ : Context -> Context
∙ ˢ = ∙
(Γ , A now) ˢ = Γ ˢ
(Γ , A always) ˢ = Γ ˢ , A always
infixl 60 _ˢ


-- | Context operations and predicates

-- Singleton context
[_] : Judgement -> Context
[ A ] = ∙ , A

-- Concatenation of contexts
_⌊⌋_ : Context -> Context -> Context
Γ ⌊⌋ ∙ = Γ
Γ ⌊⌋ (Γ′ , A) = (Γ ⌊⌋ Γ′) , A
infix 45 _⌊⌋_

-- Type in the middle of a context
_⌊_⌋_ : Context -> Judgement -> Context -> Context
Γ ⌊ A ⌋ Γ′ = Γ , A ⌊⌋ Γ′
infix 40 _⌊_⌋_

-- Predicate for context membership
data _∈_ : Judgement -> Context -> Set where
    top : ∀{Γ A} -> A ∈ Γ , A
    pop : ∀{Γ A B} -> A ∈ Γ -> A ∈ Γ , B
infix 35 _∈_

-- Predicate for context subset relation
data _⊆_ : Context -> Context -> Set where
    refl : ∀{Γ} -> Γ ⊆ Γ
    keep : ∀{Γ Γ′ A} -> Γ ⊆ Γ′ -> Γ , A ⊆ Γ′ , A
    drop : ∀{Γ Γ′ A} -> Γ ⊆ Γ′ -> Γ     ⊆ Γ′ , A
infix 30 _⊆_

-- Stabilised context is a subset of the full context
Γˢ⊆Γ : ∀{Γ} -> Γ ˢ ⊆ Γ
Γˢ⊆Γ {∙} = refl
Γˢ⊆Γ {Γ , A now} = drop Γˢ⊆Γ
Γˢ⊆Γ {Γ , A always} = keep Γˢ⊆Γ

-- Stable filtering preserves subcontext relation
ˢ-⊆-monotone : ∀{Γ Γ′} -> Γ ⊆ Γ′ -> Γ ˢ ⊆ Γ′ ˢ
ˢ-⊆-monotone refl = refl
ˢ-⊆-monotone (keep {Γ} {Γ′} {A now} s) = ˢ-⊆-monotone s
ˢ-⊆-monotone (keep {Γ} {Γ′} {A always} s) = keep (ˢ-⊆-monotone s)
ˢ-⊆-monotone (drop {Γ} {Γ′} {A now} s) = ˢ-⊆-monotone s
ˢ-⊆-monotone (drop {Γ} {Γ′} {A always} s) = drop (ˢ-⊆-monotone s)

-- Element of a subset is an element of a set.
∈-⊆-monotone : ∀{Γ Γ′ J} -> Γ ⊆ Γ′ -> J ∈ Γ -> J ∈ Γ′
∈-⊆-monotone refl e           = e
∈-⊆-monotone (keep p) top     = top
∈-⊆-monotone (keep p) (pop e) = pop (∈-⊆-monotone p e)
∈-⊆-monotone (drop p) e       = pop (∈-⊆-monotone p e)

-- Subset relation is reflexive
⊆-refl-eq : ∀{Γ Γ′} -> Γ ≡ Γ′ -> Γ ⊆ Γ′
⊆-refl-eq  refl = refl

-- Subset relation is transitive
⊆-trans : ∀{Γ Δ Ξ} -> Γ ⊆ Δ -> Δ ⊆ Ξ -> Γ ⊆ Ξ
⊆-trans refl c2 = c2
⊆-trans c1 refl = c1
⊆-trans c1 (drop c2) = drop (⊆-trans c1 c2)
⊆-trans (keep c1) (keep c2) = keep (⊆-trans c1 c2)
⊆-trans (drop c1) (keep c2) = drop (⊆-trans c1 c2)

-- Subset relation is a preorder
⊆-po : IsPreorder _≡_ _⊆_
⊆-po = record
    { isEquivalence = isEquivalence
    ; reflexive = ⊆-refl-eq
    ; trans = ⊆-trans
    }
