
module Syntax.Substitution where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms
open import Syntax.Lemmas

open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

mutual
    -- Substitution of normal terms.
    subst : ∀(Γ Γ′ : Context) {A B}
                        ->  Γ ⌊⌋ Γ′ ⊢ A   ->   Γ ⌊ A ⌋ Γ′ ⊢ B
                           --------------------------------
                        ->           Γ ⌊⌋ Γ′ ⊢ B
    subst Γ Γ′ M (var x) with var-disjoint Γ Γ′ x
    subst Γ Γ′ M (var x) | inj₁ refl = M
    subst Γ Γ′ M (var x) | inj₂ y = var y
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
    subst Γ Γ′ M (svar x) with var-disjoint Γ Γ′ x
    subst Γ Γ′ M (svar x) | inj₁ refl = M
    subst Γ Γ′ M (svar x) | inj₂ y = svar y
    subst Γ Γ′ M (present A) = present (subst Γ Γ′ M A)
    subst Γ Γ′ {C now} M (stable S) rewrite ˢ-preserves-⌊⌋ {Γ , C now} {Γ′}
                                         | sym (ˢ-preserves-⌊⌋ {Γ} {Γ′})
                                         = stable S
    subst Γ Γ′ {C always} M (stable {A = A} S) rewrite ˢ-preserves-⌊⌋ {Γ , C always} {Γ′}
            = stable S′
        where
        S′ : (Γ ⌊⌋ Γ′) ˢ ⊢ A now
        S′ rewrite ˢ-preserves-⌊⌋ {Γ} {Γ′} = subst (Γ ˢ) (Γ′ ˢ) M′ S
            where
            M′ : Γ ˢ ⌊⌋ Γ′ ˢ ⊢ C always
            M′ rewrite sym (ˢ-preserves-⌊⌋ {Γ} {Γ′}) = ˢ-always M
    subst Γ Γ′ M (sig S) = sig (subst Γ Γ′ M S)
    subst Γ Γ′ M (letSig_In_ {A = A} S B) = letSig (subst Γ Γ′ M S)
                                               In (subst Γ (Γ′ , A always) (weaken (drop refl) M) B)
    subst Γ Γ′ M (event E) = event (subst′ Γ Γ′ M E)

    subst′ : ∀(Γ Γ′ : Context) {A B}
                        ->  Γ ⌊⌋ Γ′ ⊢ A   ->   Γ ⌊ A ⌋ Γ′ ⊨ B
                           --------------------------------
                        ->           Γ ⌊⌋ Γ′ ⊨ B
    subst′ Γ Γ′ M (pure A) = pure (subst Γ Γ′ M A)
    subst′ Γ Γ′ M (letSig_InC_ {A = A} S C) =
        letSig subst Γ Γ′ M S
           InC subst′ Γ (Γ′ , A now) (weaken (drop refl) M) C
    subst′ Γ Γ′ {D now} M (letEvt E In C)
          rewrite ˢ-filter {Γ} {Γ′} {D}
        = letEvt subst Γ Γ′ M E In C
    subst′ Γ Γ′ {D always} M (letEvt_In_ {A = A} {B} E C)
          rewrite ˢ-preserves-⌊⌋ {Γ , D always} {Γ′}
        = letEvt subst Γ Γ′ M E In C′
        where
        C′ : (Γ ⌊⌋ Γ′) ˢ , A now ⊨ B now
        C′ rewrite ˢ-preserves-⌊⌋ {Γ} {Γ′}
            = subst′ (Γ ˢ) (Γ′ ˢ , A now) (weaken (drop refl) M′) C
            where
            M′ : Γ ˢ ⌊⌋ Γ′ ˢ ⊢ D always
            M′ rewrite sym (ˢ-preserves-⌊⌋ {Γ} {Γ′}) = ˢ-always M

    subst′ Γ Γ′ {D now} M (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃)
        rewrite ˢ-filter {Γ} {Γ′} {D}
        = select (subst Γ Γ′ M E₁) ↦ C₁ || (subst Γ Γ′ M E₂) ↦ C₂ ||both↦ C₃
    subst′ Γ Γ′ {D always} M (select_↦_||_↦_||both↦_ {A = A} {B} E₁ C₁ E₂ C₂ C₃) =
        select subst Γ Γ′ M E₁ ↦ ˢ-subst Γ Γ′ (∙ , Event B now , A now) M C₁
            || subst Γ Γ′ M E₂ ↦ ˢ-subst Γ Γ′ (∙ , Event A now , B now) M C₂
            ||both↦             ˢ-subst Γ Γ′ (∙ , A now , B now) M C₃
            where
            ˢ-subst : ∀(Γ Γ′ Δ : Context) {A B} -> Γ ⌊⌋ Γ′ ⊢ A always
                   -> (Γ ⌊ A always ⌋ Γ′) ˢ ⌊⌋ Δ ⊨ B
                   -> (Γ ⌊⌋ Γ′) ˢ ⌊⌋ Δ ⊨ B
            ˢ-subst Γ Γ′ Δ {A} {B} M N
                rewrite ˢ-preserves-⌊⌋ {Γ , A always} {Γ′}
                      | ⌊⌋-assoc (Γ ˢ , A always) (Γ′ ˢ) Δ
                      | ˢ-preserves-⌊⌋ {Γ} {Γ′}
                      | ⌊⌋-assoc (Γ ˢ) (Γ′ ˢ) Δ
                = subst′ (Γ ˢ) (Γ′ ˢ ⌊⌋ Δ) M′ N
                where
                M′ : Γ ˢ ⌊⌋ (Γ′ ˢ ⌊⌋ Δ) ⊢ A always
                M′ rewrite sym (⌊⌋-assoc (Γ ˢ) (Γ′ ˢ) Δ)
                      | sym (ˢ-preserves-⌊⌋ {Γ} {Γ′})
                    = weaken (Γ⊆Γ⌊⌋Δ ((Γ ⌊⌋ Γ′) ˢ) Δ) (ˢ-always M)


    subst″ : ∀(Γ Γ′ : Context) {A B}
                        ->  Γ ⌊⌋ Γ′ ⊨ A now  ->   Γ ˢ ⌊ A now ⌋ Γ′ ˢ ⊨ B now
                           --------------------------------
                        ->           Γ ⌊⌋ Γ′ ⊨ B now
    subst″ Γ Γ′ (pure {A = A} M) C = subst′ Γ Γ′ M (weaken-⊨ (sub Γ Γ′) C)
        where
        sub : ∀ (Γ Γ′ : Context) -> Γ ˢ ⌊ A now ⌋ Γ′ ˢ ⊆ Γ ⌊ A now ⌋ Γ′
        sub Γ ∙ = keep Γˢ⊆Γ
        sub Γ (Γ′ , B now) = drop (sub Γ Γ′)
        sub Γ (Γ′ , B always) = keep (sub Γ Γ′)
    subst″ Γ Γ′ (letSig_InC_ {A = A} S M) C = letSig S InC subst″ Γ (Γ′ , A now) M C
    subst″ Γ Γ′ {D}{F} (letEvt_In_ {A = A} E M) C
        = letEvt E In C′
        where
        C-idemp : Γ ˢ ˢ ⌊ D now ⌋ Γ′ ˢ ˢ ⊨ F now
        C-idemp rewrite ˢ-idemp Γ | ˢ-idemp Γ′ = C
        C′ : (Γ ⌊⌋ Γ′) ˢ , A now ⊨ F now
        C′ rewrite ˢ-preserves-⌊⌋ {Γ} {Γ′} = subst″ (Γ ˢ) (Γ′ ˢ , A now) M C-idemp
    subst″ Γ Γ′ {D}{F} (select_↦_||_↦_||both↦_ {A = A} {B} E₁ M₁ E₂ M₂ M₃) C
        = select E₁ ↦ C′ (Event B) A M₁
              || E₂ ↦ C′ (Event A) B M₂
              ||both↦ C′ A B M₃
        where
        C-idemp : Γ ˢ ˢ ⌊ D now ⌋ Γ′ ˢ ˢ ⊨ F now
        C-idemp rewrite ˢ-idemp Γ | ˢ-idemp Γ′ = C
        C′ : ∀ (A B : Type) -> (Γ ⌊⌋ Γ′) ˢ , A now , B now ⊨ D now
                           -> (Γ ⌊⌋ Γ′) ˢ , A now , B now ⊨ F now
        C′ A B M rewrite ˢ-preserves-⌊⌋ {Γ} {Γ′} =
            subst″ (Γ ˢ) (Γ′ ˢ , A now , B now) M C-idemp


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
