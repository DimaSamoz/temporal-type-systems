
module Syntax.Substitution where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms
open import Syntax.Lemmas

open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

mutual
    -- Substitution of pure terms into pure terms.
    substₚ : ∀(Γ Γ′ : Context) {A B}
                        ->  Γ ⌊⌋ Γ′ ⊢ A   ->   Γ ⌊ A ⌋ Γ′ ⊢ B
                           --------------------------------
                        ->           Γ ⌊⌋ Γ′ ⊢ B
    substₚ Γ Γ′ M (var x) with var-disjoint Γ Γ′ x
    substₚ Γ Γ′ M (var x) | inj₁ refl = M
    substₚ Γ Γ′ M (var x) | inj₂ y = var y
    substₚ Γ Γ′ M (lam {A = A} B) = lam (substₚ Γ (Γ′ , A now) (weaken (drop refl) M) B)
    substₚ Γ Γ′ M (F $ A) = substₚ Γ Γ′ M F $ substₚ Γ Γ′ M A
    substₚ Γ Γ′ M unit = unit
    substₚ Γ Γ′ M [ A ,, B ] = [ substₚ Γ Γ′ M A ,, substₚ Γ Γ′ M B ]
    substₚ Γ Γ′ M (fst A) = fst (substₚ Γ Γ′ M A)
    substₚ Γ Γ′ M (snd A) = snd (substₚ Γ Γ′ M A)
    substₚ Γ Γ′ M (inl A) = inl (substₚ Γ Γ′ M A)
    substₚ Γ Γ′ M (inr A) = inr (substₚ Γ Γ′ M A)
    substₚ Γ Γ′ M (case_inl↦_||inr↦_ {A = A} {B} S B₁ B₂) =
        case substₚ Γ Γ′ M S
           inl↦ substₚ Γ (Γ′ , A now) (weaken (drop refl) M) B₁
         ||inr↦ substₚ Γ (Γ′ , B now) (weaken (drop refl) M) B₂
    substₚ Γ Γ′ M (svar x) with var-disjoint Γ Γ′ x
    substₚ Γ Γ′ M (svar x) | inj₁ refl = M
    substₚ Γ Γ′ M (svar x) | inj₂ y = svar y
    substₚ Γ Γ′ M (present A) = present (substₚ Γ Γ′ M A)
    substₚ Γ Γ′ {C now} M (stable S) rewrite ˢ-preserves-⌊⌋ {Γ , C now} {Γ′}
                                         | sym (ˢ-preserves-⌊⌋ {Γ} {Γ′})
                                         = stable S
    substₚ Γ Γ′ {C always} M (stable {A = A} S)
        rewrite ˢ-preserves-⌊⌋ {Γ , C always} {Γ′}
            = stable S′
        where
        M′ : Γ ˢ ⌊⌋ Γ′ ˢ ⊢ C always
        M′ rewrite sym (ˢ-preserves-⌊⌋ {Γ} {Γ′}) = ˢ-always M
        S′ : (Γ ⌊⌋ Γ′) ˢ ⊢ A now
        S′ rewrite ˢ-preserves-⌊⌋ {Γ} {Γ′} = substₚ (Γ ˢ) (Γ′ ˢ) M′ S

    substₚ Γ Γ′ M (sig S) = sig (substₚ Γ Γ′ M S)
    substₚ Γ Γ′ M (letSig_In_ {A = A} S B) = letSig (substₚ Γ Γ′ M S)
                                               In (substₚ Γ (Γ′ , A always) (weaken (drop refl) M) B)
    substₚ Γ Γ′ M (event E) = event (substₚᶜ Γ Γ′ M E)

    -- Substitution of pure terms into computational terms
    substₚᶜ : ∀(Γ Γ′ : Context) {A B}
                        ->  Γ ⌊⌋ Γ′ ⊢ A   ->   Γ ⌊ A ⌋ Γ′ ⊨ B
                           --------------------------------
                        ->           Γ ⌊⌋ Γ′ ⊨ B
    substₚᶜ Γ Γ′ M (pure A) = pure (substₚ Γ Γ′ M A)
    substₚᶜ Γ Γ′ M (letSig_InC_ {A = A} S C) =
        letSig substₚ Γ Γ′ M S
           InC substₚᶜ Γ (Γ′ , A now) (weaken (drop refl) M) C
    substₚᶜ Γ Γ′ {D now} M (letEvt E In C)
        rewrite ˢ-filter {Γ} {Γ′} {D}
          = letEvt substₚ Γ Γ′ M E In C
    substₚᶜ Γ Γ′ {D always} M (letEvt_In_ {A = A} {B} E C)
        rewrite ˢ-preserves-⌊⌋ {Γ , D always} {Γ′}
            = letEvt substₚ Γ Γ′ M E In C′
        where
        M′ : Γ ˢ ⌊⌋ Γ′ ˢ ⊢ D always
        M′ rewrite sym (ˢ-preserves-⌊⌋ {Γ} {Γ′}) = ˢ-always M
        C′ : (Γ ⌊⌋ Γ′) ˢ , A now ⊨ B now
        C′ rewrite ˢ-preserves-⌊⌋ {Γ} {Γ′}
            = substₚᶜ (Γ ˢ) (Γ′ ˢ , A now) (weaken (drop refl) M′) C

    substₚᶜ Γ Γ′ {D now} M (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃)
        rewrite ˢ-filter {Γ} {Γ′} {D}
        = select (substₚ Γ Γ′ M E₁) ↦ C₁ || (substₚ Γ Γ′ M E₂) ↦ C₂ ||both↦ C₃
    substₚᶜ Γ Γ′ {D always} M (select_↦_||_↦_||both↦_ {A = A} {B} E₁ C₁ E₂ C₂ C₃) =
        select substₚ Γ Γ′ M E₁ ↦ ˢ-subst Γ Γ′ (∙ , Event B now , A now) M C₁
            || substₚ Γ Γ′ M E₂ ↦ ˢ-subst Γ Γ′ (∙ , Event A now , B now) M C₂
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
            = substₚᶜ (Γ ˢ) (Γ′ ˢ ⌊⌋ Δ) M′ N
            where
            M′ : Γ ˢ ⌊⌋ (Γ′ ˢ ⌊⌋ Δ) ⊢ A always
            M′ rewrite sym (⌊⌋-assoc (Γ ˢ) (Γ′ ˢ) Δ)
                  | sym (ˢ-preserves-⌊⌋ {Γ} {Γ′})
                = weaken (Γ⊆Γ⌊⌋Δ ((Γ ⌊⌋ Γ′) ˢ) Δ) (ˢ-always M)

    -- Substitution of computational terms into computational terms
    substᶜ : ∀(Γ Γ′ : Context) {A B}
                        ->  Γ ⌊⌋ Γ′ ⊨ A now  ->   Γ ˢ ⌊ A now ⌋ Γ′ ˢ ⊨ B now
                           ----------------------------------------------
                        ->                Γ ⌊⌋ Γ′ ⊨ B now
    substᶜ Γ Γ′ (pure {A = A} M) C = substₚᶜ Γ Γ′ M (weaken-⊨ (Γˢ⊆Γ-mid Γ Γ′) C)
    substᶜ Γ Γ′ (letSig_InC_ {A = A} S M) C = letSig S InC substᶜ Γ (Γ′ , A now) M C
    substᶜ Γ Γ′ {D}{F} (letEvt_In_ {A = A} E M) C
        = letEvt E In C′
        where
        C-idemp : Γ ˢ ˢ ⌊ D now ⌋ Γ′ ˢ ˢ ⊨ F now
        C-idemp rewrite ˢ-idemp Γ | ˢ-idemp Γ′ = C
        C′ : (Γ ⌊⌋ Γ′) ˢ , A now ⊨ F now
        C′ rewrite ˢ-preserves-⌊⌋ {Γ} {Γ′} = substᶜ (Γ ˢ) (Γ′ ˢ , A now) M C-idemp
    substᶜ Γ Γ′ {D}{F} (select_↦_||_↦_||both↦_ {A = A} {B} E₁ M₁ E₂ M₂ M₃) C
        = select E₁ ↦ C′ (Event B) A M₁
              || E₂ ↦ C′ (Event A) B M₂
              ||both↦ C′ A B M₃
        where
        C-idemp : Γ ˢ ˢ ⌊ D now ⌋ Γ′ ˢ ˢ ⊨ F now
        C-idemp rewrite ˢ-idemp Γ | ˢ-idemp Γ′ = C
        C′ : ∀ (A B : Type) -> (Γ ⌊⌋ Γ′) ˢ , A now , B now ⊨ D now
                           -> (Γ ⌊⌋ Γ′) ˢ , A now , B now ⊨ F now
        C′ A B M rewrite ˢ-preserves-⌊⌋ {Γ} {Γ′} =
            substᶜ (Γ ˢ) (Γ′ ˢ , A now , B now) M C-idemp
