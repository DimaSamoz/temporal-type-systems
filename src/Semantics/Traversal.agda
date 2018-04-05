
-- Semantics of syntactic traversal and substitution
module Semantics.Traversal where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Kit
open import Syntax.Traversal

open import Semantics.Types
open import Semantics.Context
open import Semantics.Select
open import Semantics.Terms
open import Semantics.Kit

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open Category ℝeactive hiding (begin_ ; _∎)
open import TemporalOps.Diamond using (◇-select ; _>>=_ ; ◇_ ; M-◇ ; >>=-assoc)

open import Data.Sum
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open ≡.≡-Reasoning


module _ {𝒮} {k : Kit 𝒮} (⟦k⟧ : ⟦Kit⟧ k) where
    open ⟦Kit⟧ ⟦k⟧
    open Kit k
    open ⟦K⟧ ⟦k⟧
    open K k

    -- Soundness of syntactic traversal:
    -- Denotation of a term M traversed with substitution σ is
    -- the same as the denotation of σ followed by the denotation of M
    mutual
        traverse-sound : ∀{Γ Δ A} (σ : Subst 𝒮 Γ Δ) (M : Γ ⊢ A)
                      -> (n : ℕ) -> (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
                      -> ⟦ traverse σ M ⟧ₘ n ⟦Δ⟧ ≡ ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)
        traverse-sound ● (var ()) n ⟦Δ⟧
        traverse-sound (σ ▸ T) (var top) n ⟦Δ⟧ = ⟦𝓉⟧ T n ⟦Δ⟧
        traverse-sound (σ ▸ T) (var (pop x)) n ⟦Δ⟧ = traverse-sound σ (var x) n ⟦Δ⟧
        traverse-sound σ (lam {A = A} M) n ⟦Δ⟧ = ext λ ⟦A⟧ →
            begin
                ⟦ traverse (σ ↑ k) M ⟧ₘ n (⟦Δ⟧ , ⟦A⟧)
            ≡⟨ traverse-sound (σ ↑ k) M n (⟦Δ⟧ , ⟦A⟧) ⟩
                ⟦ M ⟧ₘ n (⟦subst⟧ (_↑_ {A now} σ k) n (⟦Δ⟧ , ⟦A⟧))
            ≡⟨ cong (λ x → ⟦ M ⟧ₘ n x) (⟦↑⟧ (A now) σ n ⟦Δ⟧ ⟦A⟧) ⟩
                ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧ , ⟦A⟧)
            ∎
        traverse-sound σ (M $ N) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧
                                             | traverse-sound σ N n ⟦Δ⟧ = refl
        traverse-sound σ unit n ⟦Δ⟧ = refl
        traverse-sound σ [ M ,, N ] n ⟦Δ⟧
                                   rewrite traverse-sound σ M n ⟦Δ⟧
                                         | traverse-sound σ N n ⟦Δ⟧ = refl
        traverse-sound σ (fst M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (snd M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (inl M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (inr M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (case M inl↦ N₁ ||inr↦ N₂) n ⟦Δ⟧
            rewrite traverse-sound σ M n ⟦Δ⟧ with ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)
        traverse-sound σ (case_inl↦_||inr↦_ {A = A} M N₁ N₂) n ⟦Δ⟧ | inj₁ ⟦A⟧
            rewrite traverse-sound (σ ↑ k) N₁ n (⟦Δ⟧ , ⟦A⟧)
                  | ⟦↑⟧ (A now) σ n ⟦Δ⟧ ⟦A⟧ = refl
        traverse-sound σ (case_inl↦_||inr↦_ {B = B} M N₁ N₂) n ⟦Δ⟧ | inj₂ ⟦B⟧
            rewrite traverse-sound (σ ↑ k) N₂ n (⟦Δ⟧ , ⟦B⟧)
                  | ⟦↑⟧ (B now) σ n ⟦Δ⟧ ⟦B⟧ = refl
        traverse-sound ● (svar ()) n ⟦Δ⟧
        traverse-sound (σ ▸ T) (svar top) n ⟦Δ⟧ = ⟦𝓉⟧ T n ⟦Δ⟧
        traverse-sound (σ ▸ T) (svar (pop x)) n ⟦Δ⟧ = traverse-sound σ (svar x) n ⟦Δ⟧
        traverse-sound σ (sample M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound {Γ} {Δ} {A} σ (stable M) n ⟦Δ⟧ = ext λ l ->
            begin
                ⟦ traverse {Γ} {Δ} {A} σ (stable M) ⟧ₘ n ⟦Δ⟧ l
            ≡⟨ traverse-sound (σ ↓ˢ k) M l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ⟩
                ⟦ M ⟧ₘ l (⟦subst⟧ (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l))
            ≡⟨ cong (⟦ M ⟧ₘ l) (⟦subst⟧-⟦⟧ˢₓ σ n l ⟦Δ⟧) ⟩
                ⟦ M ⟧ₘ l (⟦ Γ ⟧ˢₓ n (⟦subst⟧ σ n ⟦Δ⟧) l)
            ≡⟨⟩
                ⟦ stable {Γ} M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) l
            ∎
        traverse-sound σ (sig M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (letSig_In_ {A = A} M N) n ⟦Δ⟧
            rewrite traverse-sound σ M n ⟦Δ⟧
                  | traverse-sound (σ ↑ k) N n (⟦Δ⟧ , ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))
                  | ⟦↑⟧ (A always) σ n ⟦Δ⟧ (⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)) = refl
        traverse-sound σ (event E) n ⟦Δ⟧ rewrite traverse-sound′ σ E n ⟦Δ⟧ = refl

        traverse-sound′ : ∀{Γ Δ A} -> (σ : Subst 𝒮 Γ Δ) -> (C : Γ ⊨ A)
                  -> (n : ℕ) -> (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
                  -> ⟦ traverse′ σ C ⟧ᵐ n ⟦Δ⟧ ≡ ⟦ C ⟧ᵐ n (⟦subst⟧ σ n ⟦Δ⟧)
        traverse-sound′ σ (pure M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound′ σ (letSig_InC_ {A = A} S C) n ⟦Δ⟧
            rewrite traverse-sound σ S n ⟦Δ⟧
                  | traverse-sound′ (σ ↑ k) C n (⟦Δ⟧ , ⟦ S ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))
                  | ⟦↑⟧ (A always) σ n ⟦Δ⟧ (⟦ S ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)) = refl
        traverse-sound′ {Γ} {Δ} σ (letEvt_In_ {A = A} E C) n ⟦Δ⟧ =
            begin
                ⟦ traverse′ σ (letEvt E In C) ⟧ᵐ n ⟦Δ⟧
            ≡⟨⟩
                ⟦ letEvt (traverse σ E) In (traverse′ (σ ↓ˢ k ↑ k) C) ⟧ᵐ n ⟦Δ⟧
            ≡⟨⟩
                ⟦ traverse σ E ⟧ₘ n ⟦Δ⟧ >>= (λ l ⟦A⟧ → ⟦ traverse′ (σ ↓ˢ k ↑ k) C ⟧ᵐ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧))
            ≡⟨ cong (λ x → x >>= _) (traverse-sound σ E n ⟦Δ⟧) ⟩
                ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) >>= (λ l ⟦A⟧ → ⟦ traverse′ (σ ↓ˢ k ↑ k) C ⟧ᵐ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧))
            ≡⟨ cong (λ x → ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) >>= x) (ext λ l → ext λ ⟦A⟧ →
                begin
                    ⟦ traverse′ (σ ↓ˢ k ↑ k) C ⟧ᵐ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧)
                ≡⟨ traverse-sound′ (σ ↓ˢ k ↑ k) C l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧) ⟩
                    ⟦ C ⟧ᵐ l (⟦subst⟧ (_↑_ {A now} (σ ↓ˢ k) k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧))
                ≡⟨ cong (⟦ C ⟧ᵐ l) (⟦↑⟧ (A now) (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ⟦A⟧) ⟩
                    ⟦ C ⟧ᵐ l (⟦subst⟧ (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) , ⟦A⟧)
                ≡⟨ cong (λ x → ⟦ C ⟧ᵐ l (x , ⟦A⟧)) (⟦subst⟧-⟦⟧ˢₓ σ n l ⟦Δ⟧) ⟩
                    ⟦ C ⟧ᵐ l (⟦ Γ ⟧ˢₓ n (⟦subst⟧ σ n ⟦Δ⟧) l , ⟦A⟧)
                ∎)
             ⟩
                ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) >>= (λ l ⟦A⟧ → ⟦ C ⟧ᵐ l (⟦ Γ ⟧ˢₓ n (⟦subst⟧ σ n ⟦Δ⟧) l , ⟦A⟧))
            ≡⟨⟩
                ⟦ letEvt E In C ⟧ᵐ n (⟦subst⟧ σ n ⟦Δ⟧)
            ∎
        traverse-sound′ {_} {Δ} σ (select_↦_||_↦_||both↦_ {Γ} {A} {B} {C} E₁ C₁ E₂ C₂ C₃) n ⟦Δ⟧ =
            begin
                ⟦ traverse′ σ (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃) ⟧ᵐ n ⟦Δ⟧
            ≡⟨⟩
                ⟦ select traverse σ E₁ ↦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁
                      || traverse σ E₂ ↦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂
                      ||both↦            traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ n ⟦Δ⟧
            ≡⟨⟩
                (◇-select n (⟦ traverse σ E₁ ⟧ₘ n ⟦Δ⟧ , ⟦ traverse σ E₂ ⟧ₘ n ⟦Δ⟧)
                >>= ⟦select⟧ Δ A B C n ⟦Δ⟧
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ)
            ≡⟨ cong (λ x → ◇-select n (⟦ traverse σ E₁ ⟧ₘ n ⟦Δ⟧ , ⟦ traverse σ E₂ ⟧ₘ n ⟦Δ⟧) >>= x)
                (ext λ l → ext λ c →
                begin
                    ⟦select⟧ Δ A B C n ⟦Δ⟧
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ l c
                ≡⟨ ind-hyp l c ⟩
                    ⟦select⟧ Δ A B C n ⟦Δ⟧
                        (⟦ C₁ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {A now} (_↑_ {Event B now} (σ ↓ˢ k) k) k)))
                        (⟦ C₂ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {Event A now} (σ ↓ˢ k) k) k)))
                        (⟦ C₃ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {A now}       (σ ↓ˢ k) k) k))) l c
                ≡⟨ ⟦subst⟧-⟦select⟧ A B σ n l c ⟦Δ⟧ ⟩
                    ⟦select⟧ Γ A B C n (⟦subst⟧ σ n ⟦Δ⟧) ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ l c
                ∎)
             ⟩
                ◇-select n ( ⟦ traverse σ E₁ ⟧ₘ n ⟦Δ⟧ , ⟦ traverse σ E₂ ⟧ₘ n ⟦Δ⟧)
                >>= ⟦select⟧ Γ A B C n (⟦subst⟧ σ n ⟦Δ⟧) ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ
            ≡⟨ cong₂ (λ y z → ◇-select n (y , z) >>= _) (traverse-sound σ E₁ n ⟦Δ⟧)
                                                        (traverse-sound σ E₂ n ⟦Δ⟧) ⟩
                ◇-select n (⟦ E₁ ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) , ⟦ E₂ ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))
                >>= ⟦select⟧ Γ A B C n (⟦subst⟧ σ n ⟦Δ⟧) ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ
            ≡⟨⟩
                ⟦ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ ⟧ᵐ n (⟦subst⟧ σ n ⟦Δ⟧)
            ∎
            where
            ind-hyp : ∀ l c
                -> ⟦select⟧ Δ A B C n ⟦Δ⟧
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ l c
                 ≡ ⟦select⟧ Δ A B C n ⟦Δ⟧
                        (⟦ C₁ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {A now} (_↑_ {Event B now} (σ ↓ˢ k) k) k)))
                        (⟦ C₂ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {Event A now} (σ ↓ˢ k) k) k)))
                        (⟦ C₃ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {A now}       (σ ↓ˢ k) k) k))) l c
            ind-hyp l c rewrite ext (λ n -> (ext λ ⟦Δ⟧ -> (traverse-sound′ (σ ↓ˢ k ↑ k ↑ k) C₁ n ⟦Δ⟧)))
                              | ext (λ n -> (ext λ ⟦Δ⟧ -> (traverse-sound′ (σ ↓ˢ k ↑ k ↑ k) C₂ n ⟦Δ⟧)))
                              | ext (λ n -> (ext λ ⟦Δ⟧ -> (traverse-sound′ (σ ↓ˢ k ↑ k ↑ k) C₃ n ⟦Δ⟧))) = refl

-- Denotation of variable kits
⟦𝒱ar⟧ : ⟦Kit⟧ 𝒱ar
⟦𝒱ar⟧ = record
    { ⟦_⟧ = ⟦_⟧-var
    ; ⟦𝓋⟧ = λ A Δ n ⟦Δ⟧ ⟦A⟧ → refl
    ; ⟦𝓉⟧ = ⟦𝓉⟧-var
    ; ⟦𝓌⟧ = λ B T n ⟦Δ⟧ ⟦B⟧ → refl
    ; ⟦𝒶⟧ = ⟦𝒶⟧-var
    }
    where
    open Kit 𝒱ar
    ⟦_⟧-var : ∀{A Γ} → Var Γ A → ⟦ Γ ⟧ₓ ⇴ ⟦ A ⟧ⱼ
    ⟦ top ⟧-var n (_ , ⟦A⟧) = ⟦A⟧
    ⟦ pop v ⟧-var n (⟦Γ⟧ , _) = ⟦ v ⟧-var n ⟦Γ⟧

    ⟦𝓉⟧-var : ∀{A Γ} → (x : Var Γ A)
          -> (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
          -> ⟦ 𝓉 x ⟧ₘ n ⟦Γ⟧ ≡ ⟦ x ⟧-var n ⟦Γ⟧
    ⟦𝓉⟧-var {A now} top n (⟦Γ⟧ , ⟦A⟧) = refl
    ⟦𝓉⟧-var {A always} top n (⟦Γ⟧ , ⟦A⟧) = refl
    ⟦𝓉⟧-var {A now} (pop x) n (⟦Γ⟧ , ⟦B⟧) = ⟦𝓉⟧-var x n ⟦Γ⟧
    ⟦𝓉⟧-var {A always} (pop x) n (⟦Γ⟧ , ⟦B⟧) = ⟦𝓉⟧-var x n ⟦Γ⟧

    ⟦𝒶⟧-var : ∀{A Γ} → (x : Var Γ (A always))
           -> (n l : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
           -> ⟦ 𝒶 x ⟧-var l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l) ≡ ⟦ x ⟧-var n ⟦Γ⟧
    ⟦𝒶⟧-var top n l ⟦Γ⟧ = refl
    ⟦𝒶⟧-var (pop {B = B now} x) n l (⟦Γ⟧ , ⟦B⟧) = ⟦𝒶⟧-var x n l ⟦Γ⟧
    ⟦𝒶⟧-var (pop {B = B always} x) n l (⟦Γ⟧ , ⟦B⟧) = ⟦𝒶⟧-var x n l ⟦Γ⟧

-- Denotation of term kits
⟦𝒯erm⟧ : ⟦Kit⟧ 𝒯erm
⟦𝒯erm⟧ = record
    { ⟦_⟧ = ⟦_⟧ₘ
    ; ⟦𝓋⟧ = λ A Δ n ⟦Δ⟧ ⟦A⟧ → ⟦𝓉⟧ {A} {Δ ,, A} top n (⟦Δ⟧ , ⟦A⟧)
    ; ⟦𝓉⟧ = λ T n ⟦Δ⟧ → refl
    ; ⟦𝓌⟧ = ⟦𝓌⟧-term
    ; ⟦𝒶⟧ = ⟦𝒶⟧-term
    }
    where
    open Kit 𝒯erm
    open ⟦Kit⟧ ⟦𝒱ar⟧
    open K
    open ⟦K⟧

    ⟦𝓌⟧-term : ∀ B {Δ A} → (M : Term Δ A)
           -> (n : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n) (⟦B⟧ : ⟦ B ⟧ⱼ n)
           -> ⟦ 𝓌 {B} M ⟧ₘ n (⟦Δ⟧ , ⟦B⟧) ≡ ⟦ M ⟧ₘ n ⟦Δ⟧
    ⟦𝓌⟧-term B {Δ} M n ⟦Δ⟧ ⟦B⟧ =
        begin
            ⟦ 𝓌 M ⟧ₘ n (⟦Δ⟧ , ⟦B⟧)
        ≡⟨⟩
            ⟦ traverse 𝒱ar (idₛ 𝒱ar ⁺ 𝒱ar) M ⟧ₘ n (⟦Δ⟧ , ⟦B⟧)
        ≡⟨ traverse-sound ⟦𝒱ar⟧ (idₛ 𝒱ar ⁺ 𝒱ar) M n (⟦Δ⟧ , ⟦B⟧) ⟩
            ⟦ M ⟧ₘ n (⟦subst⟧ ⟦𝒱ar⟧ {Δ} ((_⁺_ {B} (idₛ 𝒱ar) 𝒱ar)) n (⟦Δ⟧ , ⟦B⟧))
        ≡⟨ cong (⟦ M ⟧ₘ n) (
            begin
                ⟦subst⟧ ⟦𝒱ar⟧ (idₛ 𝒱ar ⁺ 𝒱ar) n (⟦Δ⟧ , ⟦B⟧)
            ≡⟨ ⟦⁺⟧ ⟦𝒱ar⟧ B (idₛ 𝒱ar) n ⟦Δ⟧ ⟦B⟧ ⟩
                ⟦subst⟧ ⟦𝒱ar⟧ (idₛ 𝒱ar) n ⟦Δ⟧
            ≡⟨ ⟦idₛ⟧ ⟦𝒱ar⟧ n ⟦Δ⟧ ⟩
                ⟦Δ⟧
            ∎)
         ⟩
            ⟦ M ⟧ₘ n ⟦Δ⟧
        ∎

    postulate
        duh : ∀ {A : Set}{x y : A} -> x ≡ y

    ⟦𝒶⟧-term : ∀{A Δ} → (M : Term Δ (A always))
           -> (n l : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
           -> ⟦ 𝒶 M ⟧ₘ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ≡ ⟦ M ⟧ₘ n ⟦Δ⟧
    ⟦𝒶⟧-term {A} {∙} (svar ()) n l ⊤.tt
    ⟦𝒶⟧-term {A} {∙} (stable M) n l ⊤.tt = refl
    ⟦𝒶⟧-term {A} {Δ ,, B now} (svar (pop x)) n l (⟦Δ⟧ , ⟦B⟧) = ⟦𝒶⟧-term (svar x) n l ⟦Δ⟧
    ⟦𝒶⟧-term {A} {Δ ,, B now} (stable M) n l (⟦Δ⟧ , ⟦B⟧) = ⟦𝒶⟧-term {A} {Δ} (stable M) n l ⟦Δ⟧
    ⟦𝒶⟧-term {Δ = Δ ,, B always} (svar {A = .B} top) n l (⟦Δ⟧ , ⟦B⟧) = refl
    ⟦𝒶⟧-term {Δ = Δ ,, B always} (svar {A = A} (pop x)) n l (⟦Δ⟧ , ⟦B⟧)
        rewrite ⟦𝓌⟧-term (B always) (𝒶 (svar x)) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ⟦B⟧
              | ⟦𝒶⟧-term (svar x) n l ⟦Δ⟧ = refl
    ⟦𝒶⟧-term {A} {Δ ,, B always} (stable M) n l (⟦Δ⟧ , ⟦B⟧) = ext λ m →
        begin
            ⟦ 𝒶 (stable {Δ ,, B always} M) ⟧ₘ l (⟦ Δ ,, B always ⟧ˢₓ n (⟦Δ⟧ , ⟦B⟧) l) m
        ≡⟨⟩
            ⟦ subst (λ x → x ,, B always ⊢ A now) (sym (ˢ-idemp Δ)) M ⟧ₘ m (⟦ Δ ˢ ⟧ˢₓ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) m , ⟦B⟧)
        ≡⟨ duh ⟩
            ⟦ M ⟧ₘ m (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ m , ⟦B⟧)
        ≡⟨⟩
            ⟦ stable {Δ ,, B always} M ⟧ₘ n (⟦Δ⟧ , ⟦B⟧) m
        ∎


-- | Soundness theorems
-- | Concrete soundness theorems for structural lemmas and substitution
-- | are instances of the general traversal soundness proof

open ⟦K⟧ ⟦𝒯erm⟧

-- Denotation of term substitutions
⟦_⟧ₛ : ∀{Γ Δ} -> Subst Term Γ Δ -> ⟦ Δ ⟧ₓ ⇴ ⟦ Γ ⟧ₓ
⟦ σ ⟧ₛ = ⟦subst⟧ σ

-- Denotation of OPEs
⟦_⟧⊆ : ∀{Γ Δ} -> Γ ⊆ Δ -> ⟦ Δ ⟧ₓ ⇴ ⟦ Γ ⟧ₓ
⟦ s ⟧⊆ = ⟦ s ⊆ₛ 𝒯erm ⟧ₛ

-- Denotation of context exchange
⟦exch⟧ : ∀ Γ Γ′ Γ″ {A B} -> ⟦ Γ ⌊ B ⌋ Γ′ ⌊ A ⌋ Γ″ ⟧ₓ ⇴ ⟦ Γ ⌊ A ⌋ Γ′ ⌊ B ⌋ Γ″ ⟧ₓ
⟦exch⟧ Γ Γ′ Γ″ = ⟦ exₛ 𝒯ermₛ Γ Γ′ Γ″ ⟧ₛ

-- Denotation of context contraction
⟦contr⟧ : ∀ Γ Γ′ Γ″ {A} -> ⟦ Γ ⌊ A ⌋ Γ′ ⌊⌋ Γ″ ⟧ₓ ⇴ ⟦ Γ ⌊ A ⌋ Γ′ ⌊ A ⌋ Γ″ ⟧ₓ
⟦contr⟧ Γ Γ′ Γ″ = ⟦ contr-lₛ 𝒯ermₛ Γ Γ′ Γ″ ⟧ₛ

-- Denotation of middle context substitution
⟦_⌊⌋ₛ_⊢ₛ_⟧ : ∀ Γ Γ′ {A} -> Γ ⌊⌋ Γ′ ⊢ A -> ⟦ Γ ⌊⌋ Γ′ ⟧ₓ ⇴ ⟦ Γ ⌊ A ⌋ Γ′ ⟧ₓ
⟦ Γ ⌊⌋ₛ Γ′ ⊢ₛ M ⟧ = ⟦ sub-midₛ 𝒯ermₛ Γ Γ′ M ⟧ₛ

-- Denotational soundness of top substitution
⟦sub-topₛ⟧ : ∀ {Γ A} -> (M : Γ ⊢ A) (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
        -> ⟨ id , ⟦ M ⟧ₘ ⟩ n ⟦Γ⟧ ≡ ⟦ sub-topₛ 𝒯ermₛ M ⟧ₛ n ⟦Γ⟧
⟦sub-topₛ⟧ M n ⟦Γ⟧ = cong (λ x → x , ⟦ M ⟧ₘ n ⟦Γ⟧) (sym (⟦idₛ⟧ n ⟦Γ⟧))

-- Substituting traversal is sound
substitute-sound : ∀{Γ Δ A} (σ : Subst Term Γ Δ) (M : Γ ⊢ A)
                -> ⟦ substitute σ M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ ⟦ σ ⟧ₛ
substitute-sound σ M {n} {⟦Δ⟧} = traverse-sound ⟦𝒯erm⟧ σ M n ⟦Δ⟧

substitute-sound′ : ∀{Γ Δ A} (σ : Subst Term Γ Δ) (M : Γ ⊨ A)
                -> ⟦ substitute′ σ M ⟧ᵐ ≈ ⟦ M ⟧ᵐ ∘ ⟦ σ ⟧ₛ
substitute-sound′ σ M {n} {⟦Δ⟧} = traverse-sound′ ⟦𝒯erm⟧ σ M n ⟦Δ⟧

-- Weakening lemma is sound
weakening-sound : ∀{Γ Δ A} (s : Γ ⊆ Δ) (M : Γ ⊢ A)
               -> ⟦ weakening s M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ ⟦ s ⟧⊆
weakening-sound s = substitute-sound (s ⊆ₛ 𝒯erm)

-- Exchange lemma is sound
exchange-sound : ∀{Γ Γ′ Γ″ A B C} (M : Γ ⌊ A ⌋ Γ′ ⌊ B ⌋ Γ″ ⊢ C)
              -> ⟦ exchange Γ Γ′ Γ″ M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ (⟦exch⟧ Γ Γ′ Γ″)
exchange-sound {Γ} {Γ′} {Γ″} = substitute-sound (exₛ 𝒯ermₛ Γ Γ′ Γ″)

-- Contraction lemma is sound
contraction-sound : ∀{Γ Γ′ Γ″ A B} (M : Γ ⌊ A ⌋ Γ′ ⌊ A ⌋ Γ″ ⊢ B)
                 -> ⟦ contraction Γ Γ′ Γ″ M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ (⟦contr⟧ Γ Γ′ Γ″)
contraction-sound {Γ} {Γ′} {Γ″} = substitute-sound (contr-lₛ 𝒯ermₛ Γ Γ′ Γ″)

-- Substitution lemma is sound
substitution-sound : ∀{Γ Γ′ A B} (M : Γ ⌊⌋ Γ′ ⊢ A) (N : Γ ⌊ A ⌋ Γ′ ⊢ B)
                 -> ⟦ substitution Γ Γ′ M N ⟧ₘ ≈ ⟦ N ⟧ₘ ∘ ⟦ Γ ⌊⌋ₛ Γ′ ⊢ₛ M ⟧
substitution-sound {Γ} {Γ′} M = substitute-sound (sub-midₛ 𝒯ermₛ Γ Γ′ M)

-- Substitution lemma is sound
substitution′-sound : ∀{Γ Γ′ A B} (M : Γ ⌊⌋ Γ′ ⊢ A) (N : Γ ⌊ A ⌋ Γ′ ⊨ B)
                 -> ⟦ substitution′ Γ Γ′ M N ⟧ᵐ ≈ ⟦ N ⟧ᵐ ∘ ⟦ Γ ⌊⌋ₛ Γ′ ⊢ₛ M ⟧
substitution′-sound {Γ} {Γ′} M N {n} {⟦Δ⟧} = traverse-sound′ ⟦𝒯erm⟧ (sub-midₛ 𝒯ermₛ Γ Γ′ M) N n ⟦Δ⟧

-- Top substitution is sound (full categorical proof)
subst-sound : ∀{Γ A B} (M : Γ ⊢ A) (N : Γ ,, A ⊢ B)
           -> ⟦ [ M /] N ⟧ₘ ≈ ⟦ N ⟧ₘ ∘ ⟨ id , ⟦ M ⟧ₘ ⟩
subst-sound M N {n} {a} rewrite ⟦sub-topₛ⟧ M n a =
    substitute-sound (sub-topₛ 𝒯ermₛ M) N

-- Top substitution is sound (full categorical proof)
subst-sound′ : ∀{Γ A B} (M : Γ ⊢ A) (N : Γ ,, A ⊨ B)
           -> ⟦ [ M /′] N ⟧ᵐ ≈ ⟦ N ⟧ᵐ ∘ ⟨ id , ⟦ M ⟧ₘ ⟩
subst-sound′ M N {n} {a} rewrite ⟦sub-topₛ⟧ M n a =
    traverse-sound′ ⟦𝒯erm⟧ (sub-topₛ 𝒯ermₛ M) N n a

open K 𝒯erm
open Monad M-◇

-- Lemma used in the soundness proof of computational substitution
subst″-sound-lemma : ∀ Γ {A B} (n k l : ℕ)
                    -> (D : Γ ˢ ,, A now ⊨ B now)
                    -> (⟦Γ⟧ : ⟦ Γ ⟧ₓ n) (⟦A⟧ : ⟦ A ⟧ₜ l)
                  -> ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ l (⟦ Γ ˢ ⟧ˢₓ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k) l , ⟦A⟧)
                   ≡ ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧)
subst″-sound-lemma Γ {A} n k l D ⟦Γ⟧ ⟦A⟧ =
    begin
        ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ l (⟦ Γ ˢ ⟧ˢₓ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k) l , ⟦A⟧)
    ≡⟨ substitute-sound′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D {l} {⟦ Γ ˢ ⟧ˢₓ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k) l , ⟦A⟧} ⟩
        ⟦ D ⟧ᵐ l (⟦ _↑_ {A now} (Γ ˢˢₛ 𝒯erm) 𝒯erm ⟧ₛ l (⟦ Γ ˢ ⟧ˢₓ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k) l , ⟦A⟧))
    ≡⟨ cong (⟦ D ⟧ᵐ l) (⟦↑⟧ (A now) (Γ ˢˢₛ 𝒯erm) l (⟦ Γ ˢ ⟧ˢₓ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k) l) ⟦A⟧) ⟩
        ⟦ D ⟧ᵐ l (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ l (⟦ Γ ˢ ⟧ˢₓ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k) l) , ⟦A⟧)
    ≡⟨ cong (λ x → ⟦ D ⟧ᵐ l (x , ⟦A⟧)) (⟦ˢˢ⟧ Γ k l n ⟦Γ⟧) ⟩
        ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧)
    ∎

-- Substitution of a computation into a computation is sound
subst-sound″ : ∀{Γ A B} (C : Γ ⊨ A now) (D : Γ ˢ ,, A now ⊨ B now)
            -> (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
            -> ⟦ ⟨ C /⟩ D ⟧ᵐ n ⟦Γ⟧
             ≡ (⟦ C ⟧ᵐ n ⟦Γ⟧ >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l ((⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l) , ⟦A⟧))
subst-sound″ {Γ} (pure {A = A} M) D n ⟦Γ⟧ =
    begin
        ⟦ ⟨ pure M /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ⟦ traverse′ (sub-topˢₛ 𝒯ermₛ M) D ⟧ᵐ n ⟦Γ⟧
    ≡⟨ traverse-sound′ ⟦𝒯erm⟧ (sub-topˢₛ 𝒯ermₛ M) D n ⟦Γ⟧ ⟩
        ⟦ D ⟧ᵐ n (⟦subst⟧ (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) n ⟦Γ⟧ , ⟦ M ⟧ₘ n ⟦Γ⟧)
    ≡⟨ cong (λ x -> ⟦ D ⟧ᵐ n (x , ⟦ M ⟧ₘ n ⟦Γ⟧))
        (begin
            ⟦ Γˢ⊆Γ Γ ⟧⊆ n ⟦Γ⟧
        ≡⟨ lemma Γ n ⟦Γ⟧ ⟩
            ⟦ Γ ⟧ˢₓ n ⟦Γ⟧ n
        ∎)
     ⟩
        ⟦ D ⟧ᵐ n (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ n , ⟦ M ⟧ₘ n ⟦Γ⟧)
    ≡⟨ η-unit1 ⟩
        (η.at ⟦ A ⟧ⱼ n (⟦ M ⟧ₘ n ⟦Γ⟧) >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧)))
    ≡⟨⟩
        (⟦ pure M ⟧ᵐ n ⟦Γ⟧ >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧)))
    ∎
    where
    private module η = _⟹_ (Monad.η M-◇)
    lemma : ∀ Γ n ⟦Γ⟧ -> ⟦ Γˢ⊆Γ Γ ⟧⊆ n ⟦Γ⟧ ≡ ⟦ Γ ⟧ˢₓ n ⟦Γ⟧ n
    lemma ∙ n ⟦Γ⟧ = refl
    lemma (Γ ,, B now) n (⟦Γ⟧ , ⟦B⟧)
            rewrite ⟦⁺⟧ (B now) (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) n ⟦Γ⟧ ⟦B⟧
                  | lemma Γ n ⟦Γ⟧ = refl
    lemma (Γ ,, B always) n (⟦Γ⟧ , ⟦B⟧)
            rewrite ⟦↑⟧ (B always) (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) n ⟦Γ⟧ ⟦B⟧
                  | lemma Γ n ⟦Γ⟧ = refl

subst-sound″ {Γ} {A} (letSig_InC_ {A = B} S C) D n ⟦Γ⟧ =
    begin
        ⟦ ⟨ letSig S InC C /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ⟦ ⟨ C /⟩ (substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D) ⟧ᵐ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧)
    ≡⟨ subst-sound″ C (substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D) n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧) ⟩
        ⟦ C ⟧ᵐ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧)
        >>= (λ l ⟦A⟧ → ⟦ substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D ⟧ᵐ l ((⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧))
    ≡⟨ cong (λ x → (⟦ C ⟧ᵐ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧) >>= x))
        (ext λ l → ext λ ⟦A⟧ →
            begin
                ⟦ substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D ⟧ᵐ l ((⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧)
            ≡⟨ substitute-sound′ (_↑_ {A now} (_⁺_ {B always} (idₛ 𝒯erm) 𝒯erm) 𝒯erm) D {l} {((⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧)} ⟩
                ⟦ D ⟧ᵐ l (⟦ (_↑_ {A now} {Γ = Γ ˢ} (_⁺_ {B always} (idₛ 𝒯erm) 𝒯erm) 𝒯erm) ⟧ₛ l ((⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧))
            ≡⟨ cong (⟦ D ⟧ᵐ l) (⟦↑⟧ (A now) (_⁺_ {B always} (idₛ 𝒯erm) 𝒯erm) l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) ⟦A⟧) ⟩
                ⟦ D ⟧ᵐ l (⟦ _⁺_ {B always} {Γ = Γ ˢ} (idₛ 𝒯erm) 𝒯erm ⟧ₛ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧)
            ≡⟨ cong (λ x → ⟦ D ⟧ᵐ l (x , ⟦A⟧)) (⟦⁺⟧ (B always) (idₛ 𝒯erm) l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l) (⟦ S ⟧ₘ n ⟦Γ⟧)) ⟩
                ⟦ D ⟧ᵐ l (⟦ idₛ {Γ ˢ} 𝒯erm ⟧ₛ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l) , ⟦A⟧)
            ≡⟨ cong (λ x → ⟦ D ⟧ᵐ l (x , ⟦A⟧)) (⟦idₛ⟧ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l)) ⟩
                ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧)
            ∎
        )
     ⟩
        ⟦ letSig S InC C ⟧ᵐ n ⟦Γ⟧
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧))
    ∎
subst-sound″ {Γ} {A} {B} (letEvt E In C) D n ⟦Γ⟧ =
    begin
        ⟦ ⟨ letEvt E In C /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ⟦ E ⟧ₘ n ⟦Γ⟧
            >>= (λ k ⟦A⟧ → ⟦ ⟨ C /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k , ⟦A⟧))
    ≡⟨ cong (λ x → ⟦ E ⟧ₘ n ⟦Γ⟧ >>= x)
        (ext λ k → ext λ ⟦A⟧ → (begin
            ⟦ ⟨ C /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k , ⟦A⟧)
        ≡⟨ subst-sound″ C (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k , ⟦A⟧) ⟩
            ⟦ C ⟧ᵐ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k , ⟦A⟧)
            >>= (λ l ⟦A⟧₁ → ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ l (⟦ Γ ˢ ⟧ˢₓ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k) l , ⟦A⟧₁))
        ≡⟨ cong (λ x → ⟦ C ⟧ᵐ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k , ⟦A⟧) >>= x)
                (ext λ l → ext λ ⟦A⟧₁ → subst″-sound-lemma Γ n k l D ⟦Γ⟧ ⟦A⟧₁) ⟩
            ⟦ C ⟧ᵐ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k , ⟦A⟧)
            >>= (λ l ⟦A⟧₁ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧₁))
        ∎)) ⟩
        ⟦ E ⟧ₘ n ⟦Γ⟧
            >>= (λ k ⟦A⟧ → ⟦ C ⟧ᵐ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k , ⟦A⟧)
                >>=  λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨ sym (>>=-assoc (⟦ E ⟧ₘ n ⟦Γ⟧) _ _) ⟩
        (⟦ E ⟧ₘ n ⟦Γ⟧
            >>= λ k ⟦A⟧ → ⟦ C ⟧ᵐ k (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ k , ⟦A⟧))
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨⟩
        (⟦ letEvt E In C ⟧ᵐ n ⟦Γ⟧
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧)))
    ∎
subst-sound″ {B = E} (select_↦_||_↦_||both↦_ {Γ}{A}{B}{C} E₁ C₁ E₂ C₂ C₃) D n ⟦Γ⟧ =
    begin
        ⟦ ⟨ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ⟦ select E₁ ↦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
              || E₂ ↦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
              ||both↦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧)
        >>= ⟦select⟧ Γ A B E n ⟦Γ⟧
                ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ

    ≡⟨ cong (λ x -> ◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧) >>= x) (ext λ m → ext λ c →
        (begin
            ⟦select⟧ Γ A B E n ⟦Γ⟧
                ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ m c
        ≡⟨ lemma m c ⟩
            (⟦select⟧ Γ A B C n ⟦Γ⟧ ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ m c
                >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧))
        ∎))
     ⟩
        ◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧)
            >>= (λ m c → ⟦select⟧ Γ A B C n ⟦Γ⟧ ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ m c
                >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨ sym (>>=-assoc (◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧)) _ _) ⟩
        (◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧)
            >>= ⟦select⟧ Γ A B C n ⟦Γ⟧ ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ)
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨⟩
        ⟦ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ ⟧ᵐ n ⟦Γ⟧
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧))
    ∎
    where
    lemma : ∀ m c
           -> ⟦select⟧ Γ A B E n ⟦Γ⟧
               ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
               ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
               ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ m c
            ≡ (⟦select⟧ Γ A B C n ⟦Γ⟧ ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ m c
                >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l , ⟦A⟧))
    lemma m (inj₁ (inj₁ (⟦A⟧ , ⟦◇B⟧)))
        rewrite subst-sound″ C₁ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) m ((⟦ Γ ⟧ˢₓ n ⟦Γ⟧ m , ⟦◇B⟧) , ⟦A⟧)
              | (ext λ l → ext λ ⟦C⟧ → subst″-sound-lemma Γ n m l D ⟦Γ⟧ ⟦C⟧)
        = refl

    lemma m (inj₁ (inj₂ (⟦◇A⟧ , ⟦B⟧)))
        rewrite subst-sound″ C₂ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) m ((⟦ Γ ⟧ˢₓ n ⟦Γ⟧ m , ⟦◇A⟧) , ⟦B⟧)
              | (ext λ l → ext λ ⟦C⟧ → subst″-sound-lemma Γ n m l D ⟦Γ⟧ ⟦C⟧)
        = refl
    lemma m (inj₂ (⟦A⟧ , ⟦B⟧))
        rewrite subst-sound″ C₃ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) m ((⟦ Γ ⟧ˢₓ n ⟦Γ⟧ m , ⟦A⟧) , ⟦B⟧)
              | (ext λ l → ext λ ⟦C⟧ → subst″-sound-lemma Γ n m l D ⟦Γ⟧ ⟦C⟧)
        = refl
