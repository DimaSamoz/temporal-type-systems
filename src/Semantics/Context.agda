
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
⟦_ˢ⟧ : ∀ Γ -> ⟦ Γ ⟧ₓ ⇴ ⟦ Γ ˢ ⟧ₓ
⟦ ∙            ˢ⟧ = !
⟦ Γ , A now    ˢ⟧ = ⟦ Γ ˢ⟧ ∘ π₁
⟦ Γ , A always ˢ⟧ = ⟦ Γ ˢ⟧ * id

-- Denotation of context to stable denotation of stabilised context
-- Uses the Cartesian functor property of the □ comonad
⟦_ˢ⟧□ : ∀ Γ -> ⟦ Γ ⟧ₓ ⇴ □ ⟦ Γ ˢ ⟧ₓ
⟦ ∙            ˢ⟧□ = u
⟦ Γ , A now    ˢ⟧□ = ⟦ Γ ˢ⟧□ ∘ π₁
⟦ Γ , A always ˢ⟧□ = m (⟦ Γ ˢ ⟧ₓ) (□ ⟦ A ⟧ₜ) ∘ (⟦ Γ ˢ⟧□ * δ.at ⟦ A ⟧ₜ)

-- The normal stabilisation transformation factors through
-- the comonadic one via ε
⟦ˢ⟧-factor : ∀ Γ -> ⟦ Γ ˢ⟧ ≈ ε.at ⟦ Γ ˢ ⟧ₓ ∘ ⟦ Γ ˢ⟧□
⟦ˢ⟧-factor ∙ = refl
⟦ˢ⟧-factor (Γ , A now) {n} {x ,, y} = ⟦ˢ⟧-factor Γ
⟦ˢ⟧-factor (Γ , A always) {n} {x ,, y} rewrite ⟦ˢ⟧-factor Γ {n} {x} = refl

-- Applying ⟦ˢ⟧□ twice can be replaced with one ⟦ˢ⟧□ and duplication
⟦ˢ⟧□-twice : ∀ Δ -> F-□.fmap ⟦ Δ ˢ ˢ⟧□ ∘ ⟦ Δ ˢ⟧□ ≈ δ.at ⟦ Δ ˢ ˢ ⟧ₓ ∘ ⟦ Δ ˢ ˢ⟧□ ∘ ⟦ Δ ˢ⟧
⟦ˢ⟧□-twice ∙ = refl
⟦ˢ⟧□-twice (Δ , A now) = ⟦ˢ⟧□-twice Δ
⟦ˢ⟧□-twice (Δ , A always) {n} {⟦Δ⟧ ,, □⟦A⟧} = ext λ k → ext λ l → cong (_,, □⟦A⟧) (lemma k l)
    where lemma : ∀ k l -> ⟦ Δ ˢ ˢ⟧□ k (⟦ Δ ˢ⟧□ n ⟦Δ⟧ k) l
                         ≡ ⟦ Δ ˢ ˢ⟧□ n (⟦ Δ ˢ⟧ n ⟦Δ⟧) l
          lemma k l = □-≡ k l (□-≡ n k (⟦ˢ⟧□-twice Δ {n} {⟦Δ⟧}) k) l

-- Applying ⟦ˢ⟧□ and ⟦ˢ⟧ can be commuted
⟦ˢ⟧-comm : ∀ Δ -> ⟦ Δ ˢ ˢ⟧□ ∘ ⟦ Δ ˢ⟧ ≈ F-□.fmap ⟦ Δ ˢ ˢ⟧ ∘ ⟦ Δ ˢ⟧□
⟦ˢ⟧-comm Δ {n} {⟦Δ⟧} = ext (lemma Δ ⟦Δ⟧)
    where
    lemma : ∀ Δ ⟦Δ⟧ l -> (⟦ Δ ˢ ˢ⟧□ ∘ ⟦ Δ ˢ⟧) n ⟦Δ⟧ l ≡ (F-□.fmap ⟦ Δ ˢ ˢ⟧ ∘ ⟦ Δ ˢ⟧□) n ⟦Δ⟧ l
    lemma ∙ ⟦Δ⟧ l = refl
    lemma (Δ , A now) (⟦Δ⟧ ,, ⟦A⟧) l = lemma Δ ⟦Δ⟧ l
    lemma (Δ , A always) (⟦Δ⟧ ,, □⟦A⟧) l = cong (_,, □⟦A⟧) (lemma Δ ⟦Δ⟧ l)
