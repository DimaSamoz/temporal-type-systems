
-- Generic term traversals
module Syntax.Substitution.Lemmas where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms
open import Syntax.Substitution.Kits
open import Syntax.Substitution.Instances

open import Data.Sum
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; cong ; subst)
open import Function using (id ; flip ; _∘_)
open ≡.≡-Reasoning


-- | Lemmas from substitutions
-- | Concrete instances of structural and substitution lemmas
-- | can be expressed as substituting traversals on terms

-- Weakening lemma
weakening : ∀{Γ Δ A} ->     Γ ⊆ Δ   ->   Γ ⊢ A
                           --------------------
                     ->           Δ ⊢ A
weakening s = substitute (weakₛ 𝒯ermₛ s)

-- Weakening lemma for computations
weakening′ : ∀{Γ Δ A} ->     Γ ⊆ Δ   ->   Γ ⊨ A
                           --------------------
                     ->           Δ ⊨ A
weakening′ s = substitute′ (weakₛ 𝒯ermₛ s)

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

-- Top substitution of computation into a computation
⟨_/⟩ : ∀ {Γ A B}      ->  Γ ⊨ A now  ->   Γ ˢ , A now ⊨ B now
                        ------------------------------------
                     ->              Γ ⊨ B now
⟨ pure M               /⟩ D = substitute′ (sub-topˢₛ 𝒯ermₛ M) D
⟨ letSig S InC C       /⟩ D = letSig S InC ⟨ C /⟩ (substitute′ ((idₛ 𝒯erm) ⁺ 𝒯erm ↑ 𝒯erm) D)
⟨ (letEvt_In_ {Γ} E C) /⟩ D = letEvt E In  ⟨ C /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
⟨ select_↦_||_↦_||both↦_ {Γ} E₁ C₁ E₂ C₂ C₃ /⟩ D
                           = select E₁ ↦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
                                 || E₂ ↦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
                                 ||both↦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
