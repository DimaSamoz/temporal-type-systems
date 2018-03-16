{-# OPTIONS --allow-unsolved-metas #-}
-- Structural lemmas for the language syntax
module Syntax.Lemmas where

open import Syntax.Types
open import Syntax.Terms
open import Syntax.Context

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)
open import Data.Sum

-- | Structural lemmas

-- Weakening lemmas
mutual
    -- Weakening for pure terms
    weaken : ∀{Γ Γ′ A}   ->     Γ ⊆ Γ′   ->   Γ ⊢ A
                               --------------------
                        ->            Γ′ ⊢ A

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
    weaken s (present M) = present (weaken s M)
    weaken s (stable M) = stable (weaken (ˢ-⊆-monotone s) M)
    weaken s (sig M) = sig (weaken s M)
    weaken s (letSig S In B) = letSig weaken s S In weaken (keep s) B
    weaken s (event E) = event (weaken′ s E)

    -- Weakening for computational terms
    weaken′ : ∀{Γ Γ′ A} ->     Γ ⊆ Γ′   ->   Γ ⊨ A
                               --------------------
                       ->            Γ′ ⊨ A
    weaken′ s (pure M) = pure (weaken s M)
    weaken′ s (letSig S InC B) = letSig weaken s S InC weaken′ (keep s) B
    weaken′ s (letEvt E In B) = letEvt weaken s E In weaken′ (keep (ˢ-⊆-monotone s)) B
    weaken′ s (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃) =
            select weaken s E₁ ↦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₁
                || weaken s E₂ ↦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₂
                ||both↦ weaken′ ((keep (keep (ˢ-⊆-monotone s)))) C₃

-- Shorthand for weakening by a single variable
weaken-top :  ∀{Γ A B}   ->  Γ ⊢ A -> Γ , B ⊢ A
weaken-top = weaken (drop refl)

-- Exchange lemmas
mutual
    -- Exchange for pure terms
    exchange : ∀(Γ Γ′ : Context){A B C}
                            ->   Γ , A , B ⌊⌋ Γ′ ⊢ C
                                --------------------
                            ->   Γ , B , A ⌊⌋ Γ′ ⊢ C
    exchange Γ ∙ (var top) = var (pop top)
    exchange Γ ∙ (var (pop x)) = weaken (keep (drop refl)) (var x)
    exchange Γ (Γ′ , .(_ now)) (var top) = var top
    exchange Γ (Γ′ , y) (var (pop x)) = weaken-top (exchange Γ Γ′ (var x))
    exchange Γ Γ′ (lam {A = A} M) = lam (exchange Γ (Γ′ , A now) M)
    exchange Γ Γ′ (F $ A) = exchange Γ Γ′ F $ exchange Γ Γ′ A
    exchange Γ Γ′ unit = unit
    exchange Γ Γ′ [ M ,, N ] = [ exchange Γ Γ′ M ,, exchange Γ Γ′ N ]
    exchange Γ Γ′ (fst M) = fst (exchange Γ Γ′ M)
    exchange Γ Γ′ (snd M) = snd (exchange Γ Γ′ M)
    exchange Γ Γ′ (inl M) = inl (exchange Γ Γ′ M)
    exchange Γ Γ′ (inr M) = inr (exchange Γ Γ′ M)
    exchange Γ Γ′ (case_inl↦_||inr↦_ {A = A}{B} S B₁ B₂) =
                                            case exchange Γ Γ′ S
                                                  inl↦ exchange Γ (Γ′ , A now) B₁
                                                ||inr↦ exchange Γ (Γ′ , B now) B₂
    exchange Γ ∙ (svar top) = svar (pop top)
    exchange Γ ∙ (svar (pop x)) = weaken (keep (drop refl)) (svar x)
    exchange Γ (Γ′ , .(_ always)) (svar top) = svar top
    exchange Γ (Γ′ , y) (svar (pop x)) = weaken-top (exchange Γ Γ′ (svar x))
    exchange Γ Γ′ (stable S) = stable (ˢ-exchange Γ Γ′ S)
    exchange Γ Γ′ (sig S) = sig (exchange Γ Γ′ S)
    exchange Γ Γ′ (letSig_In_ {A = A} S B) = letSig exchange Γ Γ′ S In exchange Γ (Γ′ , A always) B
    exchange Γ Γ′ (event E) = event (exchange′ Γ Γ′ E)

    -- Exchange under stabilisation for pure terms
    ˢ-exchange : ∀(Γ Γ′ : Context) {A B C} -> (Γ , A , B ⌊⌋ Γ′) ˢ ⊢ C
                                          -> (Γ , B , A ⌊⌋ Γ′) ˢ ⊢ C
    ˢ-exchange Γ Γ′ {A now} {B now} M
        rewrite ˢ-pres-⌊⌋ (Γ , A now , B now) Γ′
              | ˢ-pres-⌊⌋ (Γ , B now , A now) Γ′ = M
    ˢ-exchange Γ Γ′ {A now} {B always} M
        rewrite ˢ-pres-⌊⌋ (Γ , A now , B always) Γ′
              | ˢ-pres-⌊⌋ (Γ , B always , A now) Γ′ = M
    ˢ-exchange Γ Γ′ {A always} {B now} M
        rewrite ˢ-pres-⌊⌋ (Γ , A always , B now) Γ′
              | ˢ-pres-⌊⌋ (Γ , B now , A always) Γ′ = M
    ˢ-exchange Γ Γ′ {A always} {B always} M
        rewrite ˢ-pres-⌊⌋ (Γ , A always , B always) Γ′
              | ˢ-pres-⌊⌋ (Γ , B always , A always) Γ′ = exchange (Γ ˢ) (Γ′ ˢ) M

    -- Exchange for computational terms
    exchange′ : ∀(Γ Γ′ : Context){A B C}
                            ->   Γ , A , B ⌊⌋ Γ′ ⊨ C
                                --------------------
                            ->   Γ , B , A ⌊⌋ Γ′ ⊨ C
    exchange′ Γ Γ′ (pure M) = pure (exchange Γ Γ′ M)
    exchange′ Γ Γ′ (letSig_InC_ {A = A} S C) = letSig exchange Γ Γ′ S InC exchange′ Γ (Γ′ , A now) C
    exchange′ Γ Γ′ (letEvt_In_ {A = A} E C) = letEvt exchange Γ Γ′ E In ˢ-exchange′ Γ Γ′ [ A now ] C
    exchange′ Γ Γ′ (select_↦_||_↦_||both↦_ {A = A} {B} E₁ C₁ E₂ C₂ C₃) =
        select (exchange Γ Γ′ E₁) ↦ ˢ-exchange′ Γ Γ′ (∙ , Event B now , A now) C₁
            || (exchange Γ Γ′ E₂) ↦ ˢ-exchange′ Γ Γ′ (∙ , Event A now , B now) C₂
            ||both↦ ˢ-exchange′ Γ Γ′ (∙ , A now , B now) C₃

    -- Exchange under stabilisation for computational terms
    ˢ-exchange′ : ∀(Γ Γ′ Δ : Context) {A B C} -> (Γ , A , B ⌊⌋ Γ′) ˢ ⌊⌋ Δ ⊨ C
                                            -> (Γ , B , A ⌊⌋ Γ′) ˢ ⌊⌋ Δ ⊨ C
    ˢ-exchange′ Γ Γ′ Δ {A now} {B now} M
        rewrite ˢ-pres-⌊⌋ (Γ , A now , B now) Γ′
              | ˢ-pres-⌊⌋ (Γ , B now , A now) Γ′ = M
    ˢ-exchange′ Γ Γ′ Δ {A now} {B always} M
        rewrite ˢ-pres-⌊⌋ (Γ , A now , B always) Γ′
              | ˢ-pres-⌊⌋ (Γ , B always , A now) Γ′ = M
    ˢ-exchange′ Γ Γ′ Δ {A always} {B now} M
        rewrite ˢ-pres-⌊⌋ (Γ , A always , B now) Γ′
              | ˢ-pres-⌊⌋ (Γ , B now , A always) Γ′ = M
    ˢ-exchange′ Γ Γ′ Δ {A always} {B always} M
        rewrite ˢ-pres-⌊⌋ (Γ , A always , B always) Γ′
              | ˢ-pres-⌊⌋ (Γ , B always , A always) Γ′
              | ⌊⌋-assoc (Γ ˢ , B always , A always) (Γ′ ˢ) Δ
              | ⌊⌋-assoc (Γ ˢ , A always , B always) (Γ′ ˢ) Δ = exchange′ (Γ ˢ) (Γ′ ˢ ⌊⌋ Δ) M


-- | Other lemmas

-- Context of a stable type can be stabilised
ˢ-always : ∀{Γ A} -> Γ ⊢ A always -> Γ ˢ ⊢ A always
ˢ-always {∙} M = M
ˢ-always {Γ , B now} (svar (pop x)) = svar (ˢ-∈-always x)
ˢ-always {Γ , B now} (stable M) = ˢ-always {Γ} (stable M)
ˢ-always {Γ , B always} (svar {A = A} x) with var-disjoint Γ ∙ x
ˢ-always {Γ , B always} (svar {A = .B} x) | inj₁ refl = svar top
ˢ-always {Γ , B always} (svar {A = A} x) | inj₂ y = weaken-top (svar (ˢ-∈-always y))
ˢ-always {Γ , B always} (stable {A = A} M) = stable M′
    where
    M′ : Γ ˢ ˢ , B always ⊢ A now
    M′ rewrite (ˢ-idemp Γ) = M

-- Stabilisation filters out reactive types from the middle of a context
ˢ-filter : ∀{Γ Γ′ A} -> (Γ ⌊ A now ⌋ Γ′) ˢ ≡ (Γ ⌊⌋ Γ′) ˢ
ˢ-filter {Γ} {Γ′} {A} rewrite ˢ-pres-⌊⌋ (Γ , A now) Γ′ = sym (ˢ-pres-⌊⌋ Γ Γ′)
