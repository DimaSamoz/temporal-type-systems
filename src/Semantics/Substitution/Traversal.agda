
-- Semantics of syntactic traversal and substitution
module Semantics.Substitution.Traversal where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Substitution.Kits
open import Syntax.Substitution.Instances

open import Semantics.Types
open import Semantics.Context
open import Semantics.Terms
open import Semantics.Substitution.Kits

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Comonad
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open import TemporalOps.Diamond
open import TemporalOps.Box
open import TemporalOps.OtherOps
open import TemporalOps.Linear
open import TemporalOps.StrongMonad

open import Data.Sum
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open ≡.≡-Reasoning
private module F-□ = Functor F-□
private module F-◇ = Functor F-◇
open Comonad W-□
open Monad M-◇
open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional


module _ {𝒮} {k : Kit 𝒮} (⟦k⟧ : ⟦Kit⟧ k) where
    open ⟦Kit⟧ ⟦k⟧
    open Kit k
    open ⟦K⟧ ⟦k⟧
    open K k

    -- Soundness of syntactic traversal:
    -- Denotation of a term M traversed with substitution σ is
    -- the same as the denotation of σ followed by the denotation of M
    traverse-sound : ∀{Γ Δ A} (σ : Subst 𝒮 Γ Δ) (M : Γ ⊢ A)
                  -> ⟦ traverse σ M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ ⟦subst⟧ σ
    traverse′-sound : ∀{Γ Δ A} (σ : Subst 𝒮 Γ Δ) (C : Γ ⊨ A)
                  -> ⟦ traverse′ σ C ⟧ᵐ ≈ ⟦ C ⟧ᵐ ∘ ⟦subst⟧ σ

    traverse-sound ● (var ())
    traverse-sound (σ ▸ T) (var top) = ⟦𝓉⟧ T
    traverse-sound (σ ▸ T) (var (pop x)) = traverse-sound σ (var x)
    traverse-sound σ (lam {Γ} {A} M) {n} {⟦Δ⟧} = ext lemma
        where
        lemma : ∀(⟦A⟧ : ⟦ A ⟧ₜ n) →
                Λ ⟦ traverse (σ ↑ k) M ⟧ₘ n ⟦Δ⟧ ⟦A⟧ ≡ (Λ ⟦ M ⟧ₘ ∘ ⟦subst⟧ σ) n ⟦Δ⟧ ⟦A⟧
        lemma ⟦A⟧ rewrite traverse-sound (σ ↑ k) M {n} {⟦Δ⟧ , ⟦A⟧}
                        | ⟦↑⟧ (A now) σ {n} {⟦Δ⟧ , ⟦A⟧} = refl
    traverse-sound σ (M $ N) {n} {⟦Δ⟧} rewrite traverse-sound σ M {n} {⟦Δ⟧}
                                             | traverse-sound σ N {n} {⟦Δ⟧} = refl
    traverse-sound σ unit = refl
    traverse-sound σ [ M ,, N ] {n} {⟦Δ⟧} rewrite traverse-sound σ M {n} {⟦Δ⟧}
                                                | traverse-sound σ N {n} {⟦Δ⟧} = refl
    traverse-sound σ (fst M) {n} {⟦Δ⟧} rewrite traverse-sound σ M {n} {⟦Δ⟧} = refl
    traverse-sound σ (snd M) {n} {⟦Δ⟧} rewrite traverse-sound σ M {n} {⟦Δ⟧} = refl
    traverse-sound σ (inl M) {n} {⟦Δ⟧} rewrite traverse-sound σ M {n} {⟦Δ⟧} = refl
    traverse-sound σ (inr M) {n} {⟦Δ⟧} rewrite traverse-sound σ M {n} {⟦Δ⟧} = refl
    traverse-sound σ (case M inl↦ N₁ ||inr↦ N₂) {n} {⟦Δ⟧}
        rewrite traverse-sound σ M {n} {⟦Δ⟧} with ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)
    traverse-sound σ (case_inl↦_||inr↦_ {A = A} M N₁ N₂) {n} {⟦Δ⟧} | inj₁ ⟦A⟧
        rewrite traverse-sound (σ ↑ k) N₁ {n} {⟦Δ⟧ , ⟦A⟧}
              | ⟦↑⟧ (A now) σ {n} {⟦Δ⟧ , ⟦A⟧} = refl
    traverse-sound σ (case_inl↦_||inr↦_ {B = B} M N₁ N₂) {n} {⟦Δ⟧} | inj₂ ⟦B⟧
        rewrite traverse-sound (σ ↑ k) N₂ {n} {⟦Δ⟧ , ⟦B⟧}
              | ⟦↑⟧ (B now) σ {n} {⟦Δ⟧ , ⟦B⟧} = refl
    traverse-sound σ (sample M) {n} {⟦Δ⟧} rewrite traverse-sound σ M {n} {⟦Δ⟧} = refl
    traverse-sound {Γ} {Δ} {A} σ (stable M) {n} {⟦Δ⟧} = ext lemma
        where
        lemma : ∀ l -> ⟦ traverse {Γ} σ (stable M) ⟧ₘ n ⟦Δ⟧ l
                     ≡ (⟦ stable {Γ} M ⟧ₘ ∘ ⟦subst⟧ σ) n ⟦Δ⟧ l
        lemma l rewrite traverse-sound (σ ↓ˢ k) M {l} {⟦ Δ ˢ⟧□ n ⟦Δ⟧ l}
                      | □-≡ n l (⟦↓ˢ⟧ σ {n} {⟦Δ⟧}) l = refl
    traverse-sound σ (sig M) {n} {⟦Δ⟧} rewrite traverse-sound σ M {n} {⟦Δ⟧} = refl
    traverse-sound σ (letSig_In_ {A = A} M N) {n} {⟦Δ⟧}
        rewrite traverse-sound σ M {n} {⟦Δ⟧}
              | traverse-sound (σ ↑ k) N {n} {⟦Δ⟧ , ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)}
              | ⟦↑⟧ (A always) σ {n} {⟦Δ⟧ , (⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))} = refl
    traverse-sound σ (event E) = traverse′-sound σ E

    traverse′-sound σ (pure M) {n} {⟦Δ⟧} rewrite traverse-sound σ M {n} {⟦Δ⟧} = refl
    traverse′-sound σ (letSig_InC_ {A = A} S C) {n} {⟦Δ⟧}
                rewrite traverse-sound σ S {n} {⟦Δ⟧}
                      | traverse′-sound (σ ↑ k) C {n} {⟦Δ⟧ , ⟦ S ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)}
                      | ⟦↑⟧ (A always) σ {n} {⟦Δ⟧ , (⟦ S ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))} = refl

    traverse′-sound {Γ} {Δ} σ (letEvt_In_ {A = A} {B} E C) {n} {⟦Δ⟧}
        rewrite traverse-sound σ E {n} {⟦Δ⟧}
              | (ext λ m → ext λ b → traverse′-sound (σ ↓ˢ k ↑ k) C {m} {b}) =
        begin
            μ.at ⟦ B ⟧ₜ n (F-◇.fmap (⟦ C ⟧ᵐ ∘ ⟦subst⟧ (_↑_ {A = A now} (σ ↓ˢ k) k)) n
                         (F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                         (st ⟦ Δ ˢ ⟧ₓ ⟦ A ⟧ₜ n (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)))))
        ≡⟨ cong (μ.at ⟦ B ⟧ₜ n) (F-◇.fmap-∘ {g = ⟦ C ⟧ᵐ}
                    {f = ⟦subst⟧ (_↑_ {A = A now} (σ ↓ˢ k) k)} {n}
                    {F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n (st ⟦ Δ ˢ ⟧ₓ ⟦ A ⟧ₜ n
                        (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)))})
         ⟩
            μ.at ⟦ B ⟧ₜ n (F-◇.fmap ⟦ C ⟧ᵐ n
                (F-◇.fmap (⌞ ⟦subst⟧ (_↑_ {A = A now} (σ ↓ˢ k) k) ⌟) n
                (F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                (st ⟦ Δ ˢ ⟧ₓ ⟦ A ⟧ₜ n ( ⟦ Δ ˢ⟧□ n ⟦Δ⟧
                                   , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))))))
        ≡⟨ cong (λ x -> μ.at ⟦ B ⟧ₜ n (F-◇.fmap ⟦ C ⟧ᵐ n x)) (
            begin
                F-◇.fmap (⌞ ⟦subst⟧ (_↑_ {A = A now} (σ ↓ˢ k) k) ⌟) n
                (F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                (st ⟦ Δ ˢ ⟧ₓ ⟦ A ⟧ₜ n ( ⟦ Δ ˢ⟧□ n ⟦Δ⟧
                                   , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))))
            ≡⟨ cong! (ext λ m -> ext λ b → ⟦↑⟧ (A now) (σ ↓ˢ k) {m} {b}) ⟩
                F-◇.fmap (⟦subst⟧ (σ ↓ˢ k) * id) n
                (F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                    (st ⟦ Δ ˢ ⟧ₓ ⟦ A ⟧ₜ n ( ⟦ Δ ˢ⟧□ n ⟦Δ⟧
                                        , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))))
            ≡⟨ sym F-◇.fmap-∘ ⟩
                F-◇.fmap (⟦subst⟧ (σ ↓ˢ k) * id ∘ ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                    (st ⟦ Δ ˢ ⟧ₓ ⟦ A ⟧ₜ n ( ⟦ Δ ˢ⟧□ n ⟦Δ⟧
                                       , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)))
            ≡⟨⟩
                F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id ∘ F-□.fmap (⟦subst⟧ (σ ↓ˢ k)) * id) n
                        (st ⟦ Δ ˢ ⟧ₓ ⟦ A ⟧ₜ n ( ⟦ Δ ˢ⟧□ n ⟦Δ⟧
                                           , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)))
            ≡⟨ F-◇.fmap-∘ ⟩
                F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                    (F-◇.fmap (F-□.fmap (⟦subst⟧ (σ ↓ˢ k)) * id) n
                        (st ⟦ Δ ˢ ⟧ₓ ⟦ A ⟧ₜ n ( ⟦ Δ ˢ⟧□ n ⟦Δ⟧
                                           , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))))
            ≡⟨ cong (F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n)
                    (st-nat₁ (⟦subst⟧ (σ ↓ˢ k))) ⟩
                F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ n ( ⌞ F-□.fmap (⟦subst⟧ (σ ↓ˢ k)) n (⟦ Δ ˢ⟧□ n ⟦Δ⟧) ⌟
                                   , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)))
            ≡⟨ cong! (⟦↓ˢ⟧ σ) ⟩
                F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ n ( ⟦ Γ ˢ⟧□ n (⟦subst⟧ σ n ⟦Δ⟧)
                                   , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)))
            ∎
        ) ⟩
            μ.at ⟦ B ⟧ₜ n (F-◇.fmap ⟦ C ⟧ᵐ n
                (F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ n ( ⟦ Γ ˢ⟧□ n (⟦subst⟧ σ n ⟦Δ⟧)
                                   , ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)))))
        ≡⟨⟩
            ⟦ letEvt E In C ⟧ᵐ n (⟦subst⟧ σ n ⟦Δ⟧)
        ∎

    traverse′-sound {_} {Δ} σ (select_↦_||_↦_||both↦_ {Γ} {A} {B} {C} E₁ C₁ E₂ C₂ C₃) {n} {⟦Δ⟧}
        rewrite traverse-sound σ E₁ {n} {⟦Δ⟧}
              | traverse-sound σ E₂ {n} {⟦Δ⟧} =
        begin
            μ.at ⟦ C ⟧ₜ n
                (F-◇.fmap (⌞ handle ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁ ⟧ᵐ
                                    ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂ ⟧ᵐ
                                    ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ ⌟) n
                (F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                (st ⟦ Δ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟪ ⟦ E₁ ⟧ₘ ∘ ⟦subst⟧ σ , ⟦ E₂ ⟧ₘ ∘ ⟦subst⟧ σ ⟫ n ⟦Δ⟧))))
        ≡⟨ cong! (ext λ m → ext λ b → ind-hyp m b) ⟩
            μ.at ⟦ C ⟧ₜ n
                (F-◇.fmap (⌞ handle
                       (⟦ C₁ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {Event B now} (_↑_ {A now} (σ ↓ˢ k) k) k)))
                       (⟦ C₂ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {Event A now} (σ ↓ˢ k) k) k)))
                       (⟦ C₃ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {A now}       (σ ↓ˢ k) k) k))) ⌟) n
                (F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                (st ⟦ Δ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟪ ⟦ E₁ ⟧ₘ ∘ ⟦subst⟧ σ , ⟦ E₂ ⟧ₘ ∘ ⟦subst⟧ σ ⟫ n ⟦Δ⟧))))
        ≡⟨ cong! (ext λ m → ext λ b →
            ⟦subst⟧-handle {Δ}{Γ}{A}{B}{C} σ {⟦ C₁ ⟧ᵐ}{⟦ C₂ ⟧ᵐ}{⟦ C₃ ⟧ᵐ}{n = m} {b}) ⟩
            μ.at ⟦ C ⟧ₜ n
                (F-◇.fmap (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ ∘ ⟦subst⟧ (σ ↓ˢ k) * id) n
                (F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                (st ⟦ Δ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟪ ⟦ E₁ ⟧ₘ ∘ ⟦subst⟧ σ , ⟦ E₂ ⟧ₘ ∘ ⟦subst⟧ σ ⟫ n ⟦Δ⟧))))
        ≡⟨ cong (μ.at ⟦ C ⟧ₜ n) (F-◇.fmap-∘ {g = handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ}
                      {f = ⟦subst⟧ (σ ↓ˢ k) * id} {n}
                      {F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                      (st ⟦ Δ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                      (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟪ ⟦ E₁ ⟧ₘ ∘ ⟦subst⟧ σ , ⟦ E₂ ⟧ₘ ∘ ⟦subst⟧ σ ⟫ n ⟦Δ⟧))})
         ⟩
            μ.at ⟦ C ⟧ₜ n (F-◇.fmap (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ) n
              ⌞ (F-◇.fmap (⟦subst⟧ (σ ↓ˢ k) * id) n
                (F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                (st ⟦ Δ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟪ ⟦ E₁ ⟧ₘ ∘ ⟦subst⟧ σ , ⟦ E₂ ⟧ₘ ∘ ⟦subst⟧ σ ⟫ n ⟦Δ⟧)))) ⌟)
        ≡⟨ cong (λ x → μ.at ⟦ C ⟧ₜ n (F-◇.fmap (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ) n x)) (
            begin
                (F-◇.fmap (⟦subst⟧ (σ ↓ˢ k) * id) n
                (F-◇.fmap (ε.at ⟦ Δ ˢ ⟧ₓ * id) n
                (st ⟦ Δ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟪ ⟦ E₁ ⟧ₘ ∘ ⟦subst⟧ σ , ⟦ E₂ ⟧ₘ ∘ ⟦subst⟧ σ ⟫ n ⟦Δ⟧))))
            ≡⟨ sym F-◇.fmap-∘ ⟩
                F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id ∘ F-□.fmap (⟦subst⟧ (σ ↓ˢ k)) * id) n
                (st ⟦ Δ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟪ ⟦ E₁ ⟧ₘ ∘ ⟦subst⟧ σ , ⟦ E₂ ⟧ₘ ∘ ⟦subst⟧ σ ⟫ n ⟦Δ⟧))
            ≡⟨ F-◇.fmap-∘ ⟩
                F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                (F-◇.fmap (F-□.fmap (⟦subst⟧ (σ ↓ˢ k)) * id) n
                (st ⟦ Δ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⟦ Δ ˢ⟧□ n ⟦Δ⟧ , ⟪ ⟦ E₁ ⟧ₘ ∘ ⟦subst⟧ σ , ⟦ E₂ ⟧ₘ ∘ ⟦subst⟧ σ ⟫ n ⟦Δ⟧)))
            ≡⟨ cong (F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n)
                    (st-nat₁ (⟦subst⟧ (σ ↓ˢ k))) ⟩
                F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                (st ⟦ Γ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⌞ F-□.fmap (⟦subst⟧ (σ ↓ˢ k)) n (⟦ Δ ˢ⟧□ n ⟦Δ⟧) ⌟ , ⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫  n (⟦subst⟧ σ n ⟦Δ⟧)))
            ≡⟨ cong! (⟦↓ˢ⟧ σ) ⟩
                F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                (st ⟦ Γ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⟦ Γ ˢ⟧□  n (⟦subst⟧ σ n ⟦Δ⟧) , ⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫  n (⟦subst⟧ σ n ⟦Δ⟧)))
            ∎
        ) ⟩
            μ.at ⟦ C ⟧ₜ n (F-◇.fmap (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ) n
                (F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                (st ⟦ Γ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) n
                (⟦ Γ ˢ⟧□  n (⟦subst⟧ σ n ⟦Δ⟧) , ⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫  n (⟦subst⟧ σ n ⟦Δ⟧)))))
        ≡⟨⟩
            ⟦ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ ⟧ᵐ n (⟦subst⟧ σ n ⟦Δ⟧)
        ∎
        where
        ind-hyp : ∀ l c
            -> handle
                    ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁ ⟧ᵐ
                    ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂ ⟧ᵐ
                    ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ l c
             ≡ handle
                    (⟦ C₁ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {Event B now} (_↑_ {A now} (σ ↓ˢ k) k) k)))
                    (⟦ C₂ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {Event A now} (σ ↓ˢ k) k) k)))
                    (⟦ C₃ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {A now}       (σ ↓ˢ k) k) k))) l c
        ind-hyp l c rewrite ext (λ n -> (ext λ ⟦Δ⟧ -> (traverse′-sound (σ ↓ˢ k ↑ k ↑ k) C₁ {n} {⟦Δ⟧})))
                          | ext (λ n -> (ext λ ⟦Δ⟧ -> (traverse′-sound (σ ↓ˢ k ↑ k ↑ k) C₂ {n} {⟦Δ⟧})))
                          | ext (λ n -> (ext λ ⟦Δ⟧ -> (traverse′-sound (σ ↓ˢ k ↑ k ↑ k) C₃ {n} {⟦Δ⟧}))) = refl
