
{- Denotational semantics of the contexts in the category of temporal types. -}
module Semantics.Context where

open import CategoryTheory.Instances.Reactive
open import TemporalOps.Box
open import TemporalOps.Diamond
open import Syntax.Context
open import Semantics.Types

open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

-- | Denotation of judgements and contexts

-- Denotation of judgements
⟦_⟧ⱼ : Judgement -> τ
⟦ A now ⟧ⱼ = ⟦ A ⟧ₜ
⟦ A always ⟧ⱼ = □ ⟦ A ⟧ₜ
infix 50 ⟦_⟧ⱼ

-- Denotation of contexts as a finite product of temporal types.
⟦_⟧ₓ : Context -> τ
⟦ ∙ ⟧ₓ = ⊤
⟦ Γ , A ⟧ₓ = ⟦ Γ ⟧ₓ ⊗ ⟦ A ⟧ⱼ
infix 50 ⟦_⟧ₓ

-- Transform the denotation of a context to the denotation of a stabilised context
⟦_⟧ˢₓ : ∀ Γ -> ⟦ Γ ⟧ₓ ⇴ (□ ⟦ Γ ˢ ⟧ₓ)
⟦ ∙            ⟧ˢₓ n ⟦Γ⟧ = λ k -> top.tt
⟦ Γ , A now    ⟧ˢₓ n (⟦Γ⟧ ,, ⟦A⟧) = ⟦ Γ ⟧ˢₓ n ⟦Γ⟧
⟦ Γ , A always ⟧ˢₓ n (⟦Γ⟧ ,, ⟦A⟧) = λ k → (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k) ,, ⟦A⟧

-- Denotation of order-preserving embeddings (subcontext relation)
⟦_⟧⊆ : ∀{Γ Δ} -> Γ ⊆ Δ -> ⟦ Δ ⟧ₓ ⇴ ⟦ Γ ⟧ₓ
⟦ refl ⟧⊆ n ⟦Δ⟧ = ⟦Δ⟧
⟦ keep s ⟧⊆ n (⟦Δ⟧ ,, ⟦A⟧) = ⟦ s ⟧⊆ n ⟦Δ⟧ ,, ⟦A⟧
⟦ drop s ⟧⊆ n (⟦Δ⟧ ,, ⟦A⟧) = ⟦ s ⟧⊆ n ⟦Δ⟧
