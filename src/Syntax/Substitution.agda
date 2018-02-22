
module Syntax.Substitution where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms

mutual
    -- Normal substitution for object variables.
    [_/]_ : ∀{Γ Δ F G}  ->  Δ ⁏ Γ ⊢ F   ->   Δ ⁏ Γ , F ⊢ G
                           --------------------------------
                        ->           Δ ⁏ Γ ⊢ G
    [ M /] var top          = M
    [ M /] var (pop x)      = var x
    [ M /] lam A            = lam {!    !}
    [ M /] (F $ A)          = ([ M /] F) $ ([ M /] A)
    [ M /] unit             = unit
    [ M /] [ A , B ]        = [ [ M /] A , [ M /] B ]
    [ M /] fst A            = fst ([ M /] A)
    [ M /] snd A            = snd ([ M /] A)
    [ M /] inl A            = inl ([ M /] A)
    [ M /] inr A            = inr ([ M /] A)
    [ M /] (case S inl↦ B₁
                 ||inr↦ B₂) = case [ M /] S inl↦ {!   !}
                                          ||inr↦ {!   !}
    [ M /] svar x           = svar x
    [ M /] sig A            = sig A
    [ M /] (letSig S In B)  = letSig [ M /] S In {!   !}
    [ M /] event A          = {!  !}


    -- Substitution for stable variables
    ⟦_/⟧_ : ∀{Γ Δ F G}  ->  Δ ⁏ ∙ ⊢ F   ->   Δ , F ⁏ Γ ⊢ G
                           --------------------------------
                        ->           Δ ⁏ Γ ⊢ G
    ⟦ M /⟧ var x           = var x
    ⟦ M /⟧ lam A           = lam (⟦ M /⟧ A)
    ⟦ M /⟧ (F $ A)         = (⟦ M /⟧ F) $ (⟦ M /⟧ A)
    ⟦ M /⟧ unit            = unit
    ⟦ M /⟧ [ A , B ]       = [ ⟦ M /⟧ A , ⟦ M /⟧ B ]
    ⟦ M /⟧ fst A           = fst (⟦ M /⟧ A)
    ⟦ M /⟧ snd A           = snd (⟦ M /⟧ A)
    ⟦ M /⟧ inl A           = inl (⟦ M /⟧ A)
    ⟦ M /⟧ inr A           = inr (⟦ M /⟧ A)
    ⟦ M /⟧ (case S inl↦ B₁
                ||inr↦ B₂) = case ⟦ M /⟧ S inl↦ ⟦ M /⟧ B₁
                                        ||inr↦ (⟦ M /⟧ B₂)
    ⟦ M /⟧ svar top        = {!   !}
    ⟦ M /⟧ svar (pop x)    = svar x
    ⟦ M /⟧ sig A           = sig (⟦ M /⟧ A)
    ⟦ M /⟧ (letSig S In B) = letSig ⟦ M /⟧ S In {!   !}
    ⟦ M /⟧ event A         = {!   !}


    -- Substitution for of computational terms
    ⟪_/⟫_ : ∀{Γ Δ F G}  ->  Δ ⁏ Γ ⊨ F   ->   Δ ⁏ [ F ] ⊨ G
                           --------------------------------
                        ->           Δ ⁏ Γ ⊨ G
    ⟪ pure M /⟫         A   = {!  !}
    ⟪ letSig S InC B /⟫ A   = letSig S InC (⟪ B /⟫ {! A  !})
    ⟪ letEvt E In B /⟫  A   = letEvt E In (⟪ B /⟫ A)
    ⟪ select E₁ ↦ B₁ || E₂ ↦ B₂ ||both↦ B₃ /⟫ A =
        select E₁ ↦ ⟪ B₁ /⟫ A || E₂ ↦ ⟪ B₂ /⟫ A ||both↦ (⟪ B₃ /⟫ A)
