
module Syntax.Substitution where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms
open import Syntax.Lemmas

mutual
    -- Substitution of normal terms.
    subst : ∀(Γ Γ′ : Context) {M N}
                        ->  Γ ⌊⌋ Γ′ ⊢ M   ->   Γ ⌊ M ⌋ Γ′ ⊢ N
                           --------------------------------
                        ->           Γ ⌊⌋ Γ′ ⊢ N
    subst Γ ∙ M (var top) = M
    subst Γ ∙ M (var (pop x)) = var x
    subst Γ (Γ′ , B now) M (var top) = var top
    subst Γ (Γ′ , B now) M (var (pop x)) = var (pop {!   !})
    subst Γ (Γ′ , B always) M (var (pop x)) = {!    !}
    subst Γ Γ′ M (lam {A = A} B) = lam (subst Γ (Γ′ , A now) (weaken (drop refl) M) B)
    subst Γ Γ′ M (F $ A) = subst Γ Γ′ M F $ subst Γ Γ′ M A
    subst Γ Γ′ M unit = unit
    subst Γ Γ′ M [ A ,, B ] = [ subst Γ Γ′ M A ,, subst Γ Γ′ M B ]
    subst Γ Γ′ M (fst A) = fst (subst Γ Γ′ M A)
    subst Γ Γ′ M (snd A) = snd (subst Γ Γ′ M A)
    subst Γ Γ′ M (inl A) = inl (subst Γ Γ′ M A)
    subst Γ Γ′ M (inr A) = inr (subst Γ Γ′ M A)
    subst Γ Γ′ M (case_inl↦_||inr↦_ {A = A} {B} S B₁ B₂) =
        case subst Γ Γ′ M S
           inl↦ subst Γ (Γ′ , A now) (weaken (drop refl) M) B₁
         ||inr↦ subst Γ (Γ′ , B now) (weaken (drop refl) M) B₂
    subst Γ ∙ M (svar top) = svar {!   !}
    subst Γ ∙ M (svar (pop x)) = {!   !}
    subst Γ (Γ′ , x₁) M (svar x) = {!   !}
    subst Γ Γ′ M (stable S) = stable {!   !}
    subst Γ Γ′ M (sig S) = sig (subst Γ Γ′ M S)
    subst Γ Γ′ M (letSig S In B) = {!   !}
    subst Γ Γ′ M (event x) = {!   !}
    -- [_/]_ {Γ} {∙} M (var top) = M
    -- [_/]_ {Γ} {∙} M (var (pop x)) = var x
    -- [_/]_ {Γ} {Γ′ , .(_ now)} M (var top) = var top
    -- [_/]_ {Γ} {Γ′ , A now} M (var {A = V} (pop x)) = {!   !}
    -- [_/]_ {Γ} {Γ′ , A always} M (var {A = V} (pop x)) = var {!   !}
    -- [_/]_ {Γ}{Γ′} M (lam {A = A} B) = lam ([_/]_ {Γ} {Γ′ , A now} (weaken (drop refl) M) B)
    -- [_/]_ {Γ}{Γ′} M (F $ A) = ([_/]_ {Γ} {Γ′} M F) $ [_/]_ {Γ} {Γ′} M A
    -- [ M /] unit = unit
    -- [ M /] [ A ,, B ] = [ [ M /] A ,, [ M /] B ]
    -- [ M /] fst A = {!   !}
    -- [ M /] snd A = {!   !}
    -- [ M /] inl A = {!   !}
    -- [ M /] inr A = {!   !}
    -- [ M /] (case S inl↦ B₁ ||inr↦ B₂) = {!   !}
    -- [ M /] svar x = {!   !}
    -- [ M /] stable S = {!   !}
    -- [ M /] sig S = {!   !}
    -- [ M /] (letSig S In B) = {!   !}
    -- [ M /] event x = {!   !}

    -- [ M /] var top          = M
    -- [ M /] var (pop x)      = var x
    -- [ M /] lam A            = lam {!  !}
    -- [ M /] (F $ A)          = ([ M /] F) $ ([ M /] A)
    -- [ M /] unit             = unit
    -- [ M /] [ A ,, B ]        = [ [ M /] A ,, [ M /] B ]
    -- [ M /] fst A            = fst ([ M /] A)
    -- [ M /] snd A            = snd ([ M /] A)
    -- [ M /] inl A            = inl ([ M /] A)
    -- [ M /] inr A            = inr ([ M /] A)
    -- [ M /] (case S inl↦ B₁
    --              ||inr↦ B₂) = case [ M /] S inl↦ {!   !}
    --                                       ||inr↦ {!   !}
    -- [ M /] svar x           = svar x
    -- [ M /] sig A            = sig A
    -- [ M /] (letSig S In B)  = letSig [ M /] S In {!   !}
    -- [ M /] event A          = {!  !}
    --
    --
    -- -- Substitution for stable variables
    -- ⟦_/⟧_ : ∀{Γ Δ F G}  ->  Δ ⁏ ∙ ⊢ F   ->   Δ , F ⁏ Γ ⊢ G
    --                        --------------------------------
    --                     ->           Δ ⁏ Γ ⊢ G
    -- ⟦ M /⟧ var x           = var x
    -- ⟦ M /⟧ lam A           = lam (⟦ M /⟧ A)
    -- ⟦ M /⟧ (F $ A)         = (⟦ M /⟧ F) $ (⟦ M /⟧ A)
    -- ⟦ M /⟧ unit            = unit
    -- ⟦ M /⟧ [ A ,, B ]       = [ ⟦ M /⟧ A ,, ⟦ M /⟧ B ]
    -- ⟦ M /⟧ fst A           = fst (⟦ M /⟧ A)
    -- ⟦ M /⟧ snd A           = snd (⟦ M /⟧ A)
    -- ⟦ M /⟧ inl A           = inl (⟦ M /⟧ A)
    -- ⟦ M /⟧ inr A           = inr (⟦ M /⟧ A)
    -- ⟦ M /⟧ (case S inl↦ B₁
    --             ||inr↦ B₂) = case ⟦ M /⟧ S inl↦ ⟦ M /⟧ B₁
    --                                     ||inr↦ (⟦ M /⟧ B₂)
    -- ⟦ M /⟧ svar top        = {!   !}
    -- ⟦ M /⟧ svar (pop x)    = svar x
    -- ⟦ M /⟧ sig A           = sig (⟦ M /⟧ A)
    -- ⟦ M /⟧ (letSig S In B) = letSig ⟦ M /⟧ S In {!   !}
    -- ⟦ M /⟧ event A         = {!   !}
    --
    --
    -- -- Substitution for of computational terms
    -- ⟪_/⟫_ : ∀{Γ Δ F G}  ->  Δ ⁏ Γ ⊨ F   ->   Δ ⁏ [ F ] ⊨ G
    --                        --------------------------------
    --                     ->           Δ ⁏ Γ ⊨ G
    -- ⟪ pure M /⟫         A   = {!  !}
    -- ⟪ letSig S InC B /⟫ A   = letSig S InC (⟪ B /⟫ {! A  !})
    -- ⟪ letEvt E In B /⟫  A   = letEvt E In (⟪ B /⟫ A)
    -- ⟪ select E₁ ↦ B₁ || E₂ ↦ B₂ ||both↦ B₃ /⟫ A =
    --     select E₁ ↦ ⟪ B₁ /⟫ A || E₂ ↦ ⟪ B₂ /⟫ A ||both↦ (⟪ B₃ /⟫ A)
