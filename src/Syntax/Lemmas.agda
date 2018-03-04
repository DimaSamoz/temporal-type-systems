
-- Structural lemmas for the language syntax
module Syntax.Lemmas where

open import Syntax.Types
open import Syntax.Terms
open import Syntax.Context


-- | Structural lemmas

-- Weakening lemma
mutual
    weaken : ∀{Γ Γ′ M}   ->     Γ ⊆ Γ′   ->   Γ ⊢ M
                               --------------------
                        ->            Γ′ ⊢ M

    weaken s (var x) = var (∈-⊆-monotone s x)
    weaken s (lam M) = lam (weaken (keep s) M)
    weaken s (F $ M) = weaken s F $ weaken s M
    weaken s unit = unit
    weaken s [ M ,, N ] = [ weaken s M ,, weaken s N ]
    weaken s (fst M) = fst (weaken s M)
    weaken s (snd M) = snd (weaken s M)
    weaken s (inl M) = inl (weaken s M)
    weaken s (inr M) = inr (weaken s M)
    weaken s (case S inl↦ B₁ ||inr↦ B₂) = case weaken s S
                                                inl↦ weaken (keep s) B₁
                                              ||inr↦ weaken (keep s) B₂
    weaken s (svar x) = svar (∈-⊆-monotone s x)
    weaken s (stable M) = stable (weaken (ˢ-⊆-monotone s) M)
    weaken s (sig M) = sig (weaken s M)
    weaken s (letSig S In B) = letSig weaken s S In weaken (keep s) B
    weaken s (event E) = event (weaken-⊨ s E)

    weaken-⊨ : ∀{Γ Γ′ M} ->     Γ ⊆ Γ′   ->   Γ ⊨ M
                               --------------------
                        ->            Γ′ ⊨ M
    weaken-⊨ s (pure M) = pure (weaken s M)
    weaken-⊨ s (letSig S InC B) = letSig weaken s S InC weaken-⊨ (keep s) B
    weaken-⊨ s (letEvt E In B) = letEvt weaken s E In B
    weaken-⊨ s (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃) =
            select weaken s E₁ ↦ C₁
                || weaken s E₂ ↦ C₂
                ||both↦ C₃

mutual
