
-- Structural lemmas for the language syntax
module Syntax.Lemmas where

open import Syntax.Types
open import Syntax.Terms
open import Syntax.Context


-- | Structural lemmas

-- Element of a subset is an element of a set.
∈-⊆-monotone : ∀{Γ Γ′ J} -> Γ ⊆ Γ′ -> J ∈ Γ -> J ∈ Γ′
∈-⊆-monotone empt ()
∈-⊆-monotone (keep p) top     = top
∈-⊆-monotone (keep p) (pop e) = pop (∈-⊆-monotone p e)
∈-⊆-monotone (drop p) e       = pop (∈-⊆-monotone p e)


-- Weakening lemma for Γ
mutual
    weaken-Γ : ∀{Γ Γ′ Δ M} ->     Γ ⊆ Γ′   ->   Δ ⁏ Γ ⊢ M
                               -------------------------
                          ->            Δ ⁏ Γ′ ⊢ M
    weaken-Γ s (var x)    = var (∈-⊆-monotone s x)
    weaken-Γ s (lam M)    = lam (weaken-Γ (keep s) M)
    weaken-Γ s (F $ A)    = weaken-Γ s F $ weaken-Γ s A
    weaken-Γ s unit       = unit
    weaken-Γ s [ M ,, N ] = [ (weaken-Γ s M) ,, (weaken-Γ s N) ]
    weaken-Γ s (fst M)    = fst (weaken-Γ s M)
    weaken-Γ s (snd M)    = snd (weaken-Γ s M)
    weaken-Γ s (inl M)    = inl (weaken-Γ s M)
    weaken-Γ s (inr M)    = inr (weaken-Γ s M)
    weaken-Γ s (case S inl↦ B₁ ||inr↦ B₂) = case weaken-Γ s S
                                                inl↦ weaken-Γ (keep s) B₁
                                              ||inr↦ weaken-Γ (keep s) B₂
    weaken-Γ s (svar x)        = svar x
    weaken-Γ s (sig S)         = sig S
    weaken-Γ s (letSig S In B) = letSig weaken-Γ s S In weaken-Γ s B
    weaken-Γ s (event E)       = event (weaken-Γ′ s E)

    weaken-Γ′ : ∀{Γ Γ′ Δ M} ->     Γ ⊆ Γ′   ->   Δ ⁏ Γ ⊨ M
                               -------------------------
                          ->            Δ ⁏ Γ′ ⊨ M
    weaken-Γ′ s (pure M)         = pure (weaken-Γ s M)
    weaken-Γ′ s (letSig S InC B) = letSig weaken-Γ s S InC weaken-Γ′ s B
    weaken-Γ′ s (letEvt E In B)  = letEvt weaken-Γ s E In B
    weaken-Γ′ s (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃) =
        select weaken-Γ s E₁ ↦ C₁
            || weaken-Γ s E₂ ↦ C₂
            ||both↦ C₃
