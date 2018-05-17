
{- Denotational semantics of the contexts in the category of temporal types. -}
module Semantics.Context where

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import CategoryTheory.Comonad
open import CategoryTheory.NatTrans
open import TemporalOps.Box
open import TemporalOps.Diamond
open import Syntax.Context
open import Semantics.Types

open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

open Comonad W-□
private module F-□ = Functor F-□

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

-- Denotation of context to denotation of stabilised context
-- Standard morphism arising from Γ ˢ ⊆ Γ
⟦_⟧ˢₓ : ∀ Γ -> ⟦ Γ ⟧ₓ ⇴ ⟦ Γ ˢ ⟧ₓ
⟦ ∙            ⟧ˢₓ = !
⟦ Γ , A now    ⟧ˢₓ = ⟦ Γ ⟧ˢₓ ∘ π₁
⟦ Γ , A always ⟧ˢₓ = ⟦ Γ ⟧ˢₓ * id

-- Denotation of context to stable denotation of stabilised context
-- Uses the Cartesian functor property of the □ comonad
⟦_⟧ˢₓ-□ : ∀ Γ -> ⟦ Γ ⟧ₓ ⇴ □ ⟦ Γ ˢ ⟧ₓ
⟦ ∙            ⟧ˢₓ-□ = u
⟦ Γ , A now    ⟧ˢₓ-□ = ⟦ Γ ⟧ˢₓ-□ ∘ π₁
⟦ Γ , A always ⟧ˢₓ-□ = m (⟦ Γ ˢ ⟧ₓ) (□ ⟦ A ⟧ₜ) ∘ (⟦ Γ ⟧ˢₓ-□ * δ.at ⟦ A ⟧ₜ)

-- The normal stabilisation transformation factors through
-- the comonadic one via ε
⟦⟧ˢₓ-factor : ∀ Γ -> ⟦ Γ ⟧ˢₓ ≈ ε.at ⟦ Γ ˢ ⟧ₓ ∘ ⟦ Γ ⟧ˢₓ-□
⟦⟧ˢₓ-factor ∙ = refl
⟦⟧ˢₓ-factor (Γ , A now) {n} {x ,, y} = ⟦⟧ˢₓ-factor Γ
⟦⟧ˢₓ-factor (Γ , A always) {n} {x ,, y} rewrite ⟦⟧ˢₓ-factor Γ {n} {x} = refl

⟦⟧ˢₓ-□-twice : ∀ Δ -> F-□.fmap ⟦ Δ ˢ ⟧ˢₓ-□ ∘ ⟦ Δ ⟧ˢₓ-□ ≈ δ.at ⟦ Δ ˢ ˢ ⟧ₓ ∘ ⟦ Δ ˢ ⟧ˢₓ-□ ∘ ⟦ Δ ⟧ˢₓ
⟦⟧ˢₓ-□-twice ∙ = refl
⟦⟧ˢₓ-□-twice (Δ , A now) = ⟦⟧ˢₓ-□-twice Δ
⟦⟧ˢₓ-□-twice (Δ , A always) {n} {⟦Δ⟧ ,, □⟦A⟧} = ext λ k → ext λ l → cong (_,, □⟦A⟧) (lemma k l)
    where lemma : ∀ k l -> ⟦ Δ ˢ ⟧ˢₓ-□ k (⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ k) l
                         ≡ ⟦ Δ ˢ ⟧ˢₓ-□ n (⟦ Δ ⟧ˢₓ n ⟦Δ⟧) l
          lemma k l = □-≡ k l (□-≡ n k (⟦⟧ˢₓ-□-twice Δ {n} {⟦Δ⟧}) k) l
