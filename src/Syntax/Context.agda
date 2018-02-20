
-- Typing contexts and environments
module Syntax.Context where

open import Syntax.Types

-- | Data types

-- Typing context as a list of types
data Context : Set where
    ∙ : Context
    _,_ : Context -> Type -> Context
infixl 50 _,_

-- Typing environment as a dual context
data Environment : Set where
    _⁏_ : Context -> Context -> Environment


-- | Context operations and predicates

-- Singleton context
[_] : Type -> Context
[ A ] = ∙ , A

-- Concatenation of contexts
_++_ : Context -> Context -> Context
Γ ++ ∙ = Γ
Γ ++ (Γ′ , A) = (Γ ++ Γ′) , A
infix 45 _++_

-- Predicate for context membership
data _∈_ : Type -> Context -> Set where
    top : ∀{Γ A} -> A ∈ Γ , A
    pop : ∀{Γ A B} -> A ∈ Γ -> A ∈ Γ , B
infix 40 _∈_

-- Predicate for context subset relation
data _⊆_ : Context -> Context -> Set where
    empt : ∀{Γ} -> ∙ ⊆ Γ
    keep : ∀{Γ Γ′ A} -> Γ ⊆ Γ′ -> Γ , A ⊆ Γ′ , A
    drop : ∀{Γ Γ′ A} -> Γ ⊆ Γ′ -> Γ     ⊆ Γ′ , A
infix 30 _⊆_
