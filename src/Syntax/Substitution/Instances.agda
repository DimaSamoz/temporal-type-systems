
-- Kit instances and generic term traversals
module Syntax.Substitution.Instances where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms
open import Syntax.Substitution.Kits

open import Data.Sum
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; cong ; subst)
open import Function using (id ; flip ; _∘_)
open ≡.≡-Reasoning

-- | Variable and term schemas
Var : Schema
Var = flip _∈_

Term : Schema
Term = _⊢_

-- | Variable kit

-- Variable kit
𝒱ar : Kit Var
𝒱ar = record
    { 𝓋 = id
    ; 𝓉 = var
    ; 𝓌 = pop
    ; 𝒶 = 𝒶-var
    }
    where
    𝒶-var : ∀{A Γ} → Var Γ (A always) → Var (Γ ˢ) (A always)
    𝒶-var top = top
    𝒶-var (pop {B = B now} v) = 𝒶-var v
    𝒶-var (pop {B = B always} v) = pop (𝒶-var v)

-- Generic substitution in a variable to any schema
subst-var : ∀ {𝒮 Γ Δ A} -> Subst 𝒮 Γ Δ → Var Γ A → 𝒮 Δ A
subst-var ● ()
subst-var (σ ▸ T) top = T
subst-var (σ ▸ T) (pop v) = subst-var σ v

-- Substitutable variable kit
𝒱arₛ : SubstKit Var
𝒱arₛ = record { 𝓀 = 𝒱ar ; 𝓈 = subst-var }

-- | Term traversal

module K {𝒮 : Schema} (k : Kit 𝒮) where
    open Kit k

    -- | Type-preserving term traversal
    -- | Traverses the syntax tree of the term, applying
    -- | the given substitution to the variables.
    mutual
        traverse : ∀{Γ Δ A} -> Subst 𝒮 Γ Δ -> Γ ⊢ A -> Δ ⊢ A
        traverse σ (var x)     = 𝓉 (subst-var σ x)
        traverse σ (lam M)     = lam (traverse (σ ↑ k) M)
        traverse σ (M $ N)     = traverse σ M $ traverse σ N
        traverse σ unit        = unit
        traverse σ [ M ,, N ]  = [ traverse σ M ,, traverse σ N ]
        traverse σ (fst M)     = fst (traverse σ M)
        traverse σ (snd M)     = snd (traverse σ M)
        traverse σ (inl M)     = inl (traverse σ M)
        traverse σ (inr M)     = inr (traverse σ M)
        traverse σ (case M inl↦ N₁ ||inr↦ N₂)
                               = case traverse σ M
                                   inl↦ traverse (σ ↑ k) N₁
                                 ||inr↦ traverse (σ ↑ k) N₂
        traverse σ (sample M) = sample (traverse σ M)
        traverse σ (stable M)  = stable (traverse (σ ↓ˢ k) M)
        traverse σ (sig M)     = sig (traverse σ M)
        traverse σ (letSig S In M) = letSig traverse σ S
                                         In traverse (σ ↑ k) M
        traverse σ (event E)   = event (traverse′ σ E)

        traverse′ : ∀{Γ Δ A} -> Subst 𝒮 Γ Δ -> Γ ⊨ A -> Δ ⊨ A
        traverse′ σ (pure M) = pure (traverse σ M)
        traverse′ σ (letSig S InC C) = letSig traverse σ S
                                         InC traverse′ (σ ↑ k) C
        traverse′ σ (letEvt E In C)  = letEvt traverse σ E
                                         In traverse′ (σ ↓ˢ k ↑ k) C
        traverse′ σ (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃) =
            select traverse σ E₁ ↦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁
                || traverse σ E₂ ↦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂
                ||both↦            traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃
open K


-- Renaming is a term traversal with variable substitutions
rename : ∀{A Γ Δ} -> Subst Var Γ Δ -> Γ ⊢ A -> Δ ⊢ A
rename = traverse 𝒱ar

-- Weakening is a renaming with a weakening substitution
weaken-top : ∀{B Γ A} -> Γ ⊢ A → Γ , B ⊢ A
weaken-top = rename (weak-topₛ 𝒱arₛ)

-- Weakening is a renaming with a weakening substitution
weaken′-top : ∀{B Γ A} -> Γ ⊨ A → Γ , B ⊨ A
weaken′-top = traverse′ 𝒱ar (weak-topₛ 𝒱arₛ)


-- | Term kit

-- Term kit
𝒯erm : Kit Term
𝒯erm = record
    { 𝓋 = var
    ; 𝓉 = id
    ; 𝓌 = weaken-top
    ; 𝒶 = 𝒶-term
    }
    where
    𝒶-term : {Γ : Context} {A : Type} → Γ ⊢ A always → Γ ˢ ⊢ A always
    𝒶-term {∙} M = M
    𝒶-term {Γ , B now} (var (pop x)) = 𝒶-term (var x)
    𝒶-term {Γ , B always} (var top) = var top
    𝒶-term {Γ , B always} (var {A = A} (pop x)) = weaken-top (𝒶-term (var x))
    𝒶-term {Γ , B now} (stable M) = 𝒶-term {Γ} (stable M)
    𝒶-term {Γ , B always} (stable {A = A} M) =
        stable (subst (λ x → x , B always ⊢ A now) (sym (ˢ-idemp Γ)) M)

-- Substitution is a traversal with term substitutions
substitute : ∀{Γ Δ A} -> Subst Term Γ Δ -> Γ ⊢ A -> Δ ⊢ A
substitute = traverse 𝒯erm

-- Computational substitution is a traversal with term substitutions
substitute′ : ∀{Γ Δ A} -> Subst Term Γ Δ -> Γ ⊨ A -> Δ ⊨ A
substitute′ = traverse′ 𝒯erm

-- Substitutable term kit
𝒯ermₛ : SubstKit Term
𝒯ermₛ = record { 𝓀 = 𝒯erm ; 𝓈 = substitute }
