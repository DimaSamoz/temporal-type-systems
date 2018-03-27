
-- Generic term traversals
module Syntax.Traversal where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms
open import Syntax.Kit

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
    ; 𝓉 = 𝓉-var
    ; 𝓌 = pop
    ; 𝒶 = 𝒶-var
    }
    where
    𝓉-var : {Γ : Context} {A : Judgement} → Var Γ A → Γ ⊢ A
    𝓉-var {Γ} {A now} = var
    𝓉-var {Γ} {A always} = svar

    𝓌-var : {Γ Δ : Context} {A : Judgement} → Γ ⊆ Δ → Var Γ A → Var Δ A
    𝓌-var refl v = v
    𝓌-var (keep s) top = top
    𝓌-var (keep s) (pop v) = pop (𝓌-var s v)
    𝓌-var (drop s) v = pop (𝓌-var s v)

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
    open SubstKit 𝒱arₛ

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
        traverse σ (svar x)    = 𝓉 (subst-var σ x)
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


-- | Term kit

-- Term kit
𝒯erm : Kit _⊢_
𝒯erm = record
    { 𝓋 = Kit.𝓉 𝒱ar
    ; 𝓉 = id
    ; 𝓌 = weaken-top
    ; 𝒶 = 𝒶-term
    }
    where
    𝒶-term : {Γ : Context} {A : Type} → Γ ⊢ A always → Γ ˢ ⊢ A always
    𝒶-term {∙} M = M
    𝒶-term {Γ , B now} (svar (pop x)) = 𝒶-term (svar x)
    𝒶-term {Γ , B now} (stable M) = 𝒶-term {Γ} (stable M)
    𝒶-term {Γ , B always} (svar {A = .B} top) = svar top
    𝒶-term {Γ , B always} (svar {A = A} (pop x)) = weaken-top (𝒶-term (svar x))
    -- 𝒶-term {Γ , B always} (stable {A = A} M) = stable (ˢ-dup (Γ , B always) M)
    𝒶-term {Γ , B always} (stable {A = A} M) =
        stable (subst (λ x → x , B always ⊢ A now) (sym (ˢ-idemp Γ)) M)
        -- where
        -- M′ : Γ ˢ ˢ , B always ⊢ A now
        -- M′ rewrite (ˢ-idemp Γ) = M

-- Substitution is a traversal with term substitutions
substitute : ∀{Γ Δ A} -> Subst Term Γ Δ -> Γ ⊢ A -> Δ ⊢ A
substitute = traverse 𝒯erm

-- Computational substitution is a traversal with term substitutions
substitute′ : ∀{Γ Δ A} -> Subst Term Γ Δ -> Γ ⊨ A -> Δ ⊨ A
substitute′ = traverse′ 𝒯erm

-- Substitutable term kit
𝒯ermₛ : SubstKit Term
𝒯ermₛ = record { 𝓀 = 𝒯erm ; 𝓈 = substitute }

-- | Lemmas from substitutions
-- | Concrete instances of structural and substitution lemmas
-- | can be expressed as substituting traversals on terms

-- Weakening lemma
weakening : ∀{Γ Δ A} ->     Γ ⊆ Δ   ->   Γ ⊢ A
                           --------------------
                     ->           Δ ⊢ A
weakening s = substitute (weakₛ 𝒯ermₛ s)

-- Exchange lemma
exchange : ∀ Γ Γ′ Γ″ {A B C}
                     ->   Γ ⌊ A ⌋ Γ′ ⌊ B ⌋ Γ″ ⊢ C
                         ----------------------
                     ->   Γ ⌊ B ⌋ Γ′ ⌊ A ⌋ Γ″ ⊢ C
exchange Γ Γ′ Γ″ = substitute (exₛ 𝒯ermₛ Γ Γ′ Γ″)

-- Contraction lemma
contraction : ∀ Γ Γ′ Γ″ {A B}
                     ->   Γ ⌊ A ⌋ Γ′ ⌊ A ⌋ Γ″ ⊢ B
                         ----------------------
                     ->   Γ ⌊ A ⌋ Γ′ ⌊⌋ Γ″ ⊢ B
contraction Γ Γ′ Γ″ = substitute (contr-lₛ 𝒯ermₛ Γ Γ′ Γ″)

-- Substitution lemma
substitution : ∀ Γ Γ′ {A B}
                     ->  Γ ⌊⌋ Γ′ ⊢ A   ->   Γ ⌊ A ⌋ Γ′ ⊢ B
                        --------------------------------
                     ->           Γ ⌊⌋ Γ′ ⊢ B
substitution Γ Γ′ M = substitute (sub-midₛ 𝒯ermₛ Γ Γ′ M)

-- Substitution lemma for computational terms
substitution′ : ∀ Γ Γ′ {A B}
                     ->  Γ ⌊⌋ Γ′ ⊢ A   ->   Γ ⌊ A ⌋ Γ′ ⊨ B
                        --------------------------------
                     ->           Γ ⌊⌋ Γ′ ⊨ B
substitution′ Γ Γ′ M = substitute′ (sub-midₛ 𝒯ermₛ Γ Γ′ M)

-- Top substitution lemma
[_/] : ∀ {Γ A B}
                     ->  Γ ⊢ A   ->   Γ , A  ⊢ B
                        --------------------------
                     ->           Γ ⊢ B
[_/] M = substitute (sub-topₛ 𝒯ermₛ M)

-- Top substitution lemma for computational terms
[_/′] : ∀ {Γ A B}
                     ->  Γ ⊢ A   ->   Γ , A  ⊨ B
                        --------------------------
                     ->           Γ ⊨ B
[_/′] M = substitute′ (sub-topₛ 𝒯ermₛ M)
