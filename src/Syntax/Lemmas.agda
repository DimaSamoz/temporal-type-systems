{-# OPTIONS --allow-unsolved-metas #-}
-- Structural lemmas for the language syntax
module Syntax.Lemmas where

open import Syntax.Types
open import Syntax.Terms
open import Syntax.Context

open import Relation.Binary.PropositionalEquality

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
    weaken-⊨ s (letEvt E In B) = letEvt weaken s E In weaken-⊨ (keep (ˢ-⊆-monotone s)) B
    weaken-⊨ s (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃) =
            select weaken s E₁ ↦ C₁
                || weaken s E₂ ↦ C₂
                ||both↦ C₃


∈-subst : ∀{Γ Γ′ A M}
                    ->  Γ ⌊⌋ Γ′ ⊢ M   ->   A ∈ Γ ⌊ M ⌋ Γ′
                       --------------------------------
                    ->           A ∈ Γ ⌊⌋ Γ′
∈-subst {Γ} {∙} {A} {.A} J top = {!  !}
∈-subst {Γ} {∙} {A} {M} J (pop e) = e
∈-subst {Γ} {Γ′ , B} {.B} {M} J top = top
∈-subst {Γ} {Γ′ , B} {A} {M} J (pop e) = ({!   !}) -- pop (∈-subst {Γ} {{!   !}} J e)

-- mutual
--     exchange : ∀(Γ Γ′ : Context){M N P}
--                             ->   Γ , M , N ⌊⌋ Γ′ ⊢ P
--                                 --------------------
--                             ->   Γ , N , M ⌊⌋ Γ′ ⊢ P
--     exchange Γ ∙ (var top) = var (pop top)
--     exchange Γ ∙ (var (pop x)) = weaken (keep (drop refl)) (var x)
--     exchange Γ (Γ′ , .(_ now)) (var top) = var top
--     exchange Γ (Γ′ , y) (var (pop x)) = weaken (drop refl) (exchange Γ Γ′ (var x))
--     exchange Γ Γ′ (lam {A = A} M) = lam (exchange Γ (Γ′ , A now) M)
--     exchange Γ Γ′ (F $ A) = exchange Γ Γ′ F $ exchange Γ Γ′ A
--     exchange Γ Γ′ unit = unit
--     exchange Γ Γ′ [ M ,, N ] = [ exchange Γ Γ′ M ,, exchange Γ Γ′ N ]
--     exchange Γ Γ′ (fst M) = fst (exchange Γ Γ′ M)
--     exchange Γ Γ′ (snd M) = snd (exchange Γ Γ′ M)
--     exchange Γ Γ′ (inl M) = inl (exchange Γ Γ′ M)
--     exchange Γ Γ′ (inr M) = inr (exchange Γ Γ′ M)
--     exchange Γ Γ′ (case_inl↦_||inr↦_ {A = A}{B} S B₁ B₂) =
--                                             case exchange Γ Γ′ S
--                                                   inl↦ exchange Γ (Γ′ , A now) B₁
--                                                 ||inr↦ exchange Γ (Γ′ , B now) B₂
--     exchange Γ ∙ (svar top) = svar (pop top)
--     exchange Γ ∙ (svar (pop x)) = weaken (keep (drop refl)) (svar x)
--     exchange Γ (Γ′ , .(_ always)) (svar top) = svar top
--     exchange Γ (Γ′ , y) (svar (pop x)) = weaken (drop refl) (exchange Γ Γ′ (svar x))
--     exchange Γ Γ′ {M now} {N now} (stable S) rewrite ˢ-preserves-⌊⌋ {Γ , M now , N now} {Γ′} = stable (exchange (Γ ˢ) {! Γ′ ˢ  !} S)
--     exchange Γ Γ′ {M now} {N always} (stable S) = stable {!   !}
--     exchange Γ Γ′ {M always} {N now} (stable S) = stable {!   !}
--     exchange Γ Γ′ {M always} {N always} (stable S) = stable {!   !}
--     exchange Γ Γ′ (sig S) = {!   !}
--     exchange Γ Γ′ (letSig S In B) = {!   !}
--     exchange Γ Γ′ (event E) = {!   !}
-- mutual
--     intchange : ∀{Γ Δ A B M} ->  Δ ⁏ Γ , A , B ⊢ M
--                                   --------------------
--                           ->        Δ ⁏ Γ , B , A ⊢ M
--     intchange (var top) = var (pop top)
--     intchange (var (pop x)) = var (∈-⊆-monotone (keep (drop ⊆-refl)) x)
--     intchange (lam M) = lam (weaken-Γ {!   !} (intchange M))
--     intchange (M $ M₁) = intchange M $ intchange M₁
--     intchange unit = unit
--     intchange [ M ,, M₁ ] = [ intchange M ,, intchange M₁ ]
--     intchange (fst M) = fst (intchange M)
--     intchange (snd M) = snd (intchange M)
--     intchange (inl M) = inl (intchange M)
--     intchange (inr M) = inr (intchange M)
--     intchange (case M inl↦ M₁ ||inr↦ M₂) = {!   !}
--     intchange (svar x) = svar x
--     intchange (sig M) = sig M
--     intchange (letSig M In M₁) = letSig intchange M In intchange M₁
--     intchange (event x) = {!   !}
