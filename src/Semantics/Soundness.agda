
-- Soundness of term equality
module Semantics.Soundness where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Equality
open import Syntax.Substitution

open import Semantics.Types
open import Semantics.Context
open import Semantics.Terms
open import Semantics.Substitution

open import CategoryTheory.Categories using (ext)
open import CategoryTheory.BCCCs.Cartesian using (Product)
open import CategoryTheory.BCCCs
open import CategoryTheory.Instances.Reactive renaming (top to Top)
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import TemporalOps.Diamond
open import TemporalOps.OtherOps

open import Data.Sum
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open ≡.≡-Reasoning
open Monad M-◇
open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional

open ⟦Kit⟧ ⟦𝒯erm⟧
open Kit 𝒯erm
open ⟦K⟧ ⟦𝒯erm⟧
open K 𝒯erm

mutual
    -- Soundness of term equality: equal terms have equal denotations
    sound : ∀{A Γ} {M₁ M₂ : Γ ⊢ A}
             -> Γ ⊢ M₁ ≡ M₂ ∷ A
             -> ⟦ M₁ ⟧ₘ ≈ ⟦ M₂ ⟧ₘ
    sound (refl M) = refl
    sound (Eq.sym eq) = ≡.sym (sound eq)
    sound (Eq.trans eq₁ eq₂) = ≡.trans (sound eq₁) (sound eq₂)

    sound (β-lam N M) {n} {⟦Γ⟧} rewrite subst-sound M N {n} {⟦Γ⟧} = refl
    sound (β-fst M N) = refl
    sound (β-snd M N) = refl
    sound (β-inl M N₁ N₂) {n} {⟦Γ⟧} rewrite subst-sound M N₁ {n} {⟦Γ⟧} = refl
    sound (β-inr M N₁ N₂) {n} {⟦Γ⟧} rewrite subst-sound M N₂ {n} {⟦Γ⟧} = refl
    sound (β-sig N M) {n} {⟦Γ⟧} rewrite subst-sound M N {n} {⟦Γ⟧} = refl

    sound (η-lam {A} M) {n} {⟦Γ⟧} = ext λ ⟦A⟧ →
                        cong (λ x → x ⟦A⟧) (≡.sym (⟦𝓌⟧ (A now) M {n} {⟦Γ⟧ , ⟦A⟧}))
    sound (η-pair M) = ≡.sym (⊗-η-exp {m = ⟦ M ⟧ₘ})
    sound (η-unit M) = refl
    sound (η-sum M) {n} {⟦Γ⟧} with ⟦ M ⟧ₘ n ⟦Γ⟧
    sound (η-sum M) {n} {a} | inj₁ _ = refl
    sound (η-sum M) {n} {a} | inj₂ _ = refl
    sound (η-sig M) = refl
    sound (η-evt M) {n} {a} = ≡.sym (>>=-unit-right (⟦ M ⟧ₘ n a))

    sound (cong-pair eq₁ eq₂) {n} {a} rewrite sound eq₁ {n} {a}
                                            | sound eq₂ {n} {a} = refl
    sound (cong-fst eq) {n} {a} rewrite sound eq {n} {a} = refl
    sound (cong-snd eq) {n} {a} rewrite sound eq {n} {a} = refl
    sound (cong-lam eq) {n} {a} = ext λ ⟦A⟧ → sound eq
    sound (cong-app eq₁ eq₂) {n} {a} rewrite sound eq₁ {n} {a}
                                           | sound eq₂ {n} {a} = refl
    sound (cong-inl eq) {n} {a} rewrite sound eq {n} {a} = refl
    sound (cong-inr eq) {n} {a} rewrite sound eq {n} {a} = refl
    sound (cong-case eq N₁ N₂) {n} {a} rewrite sound eq {n} {a} = refl
    sound (cong-sig eq) {n} {a} rewrite sound eq {n} {a} = refl
    sound (cong-letSig eq N) {n} {a} rewrite sound eq {n} {a} = refl
    sound (cong-sample eq) {n} {a} rewrite sound eq {n} {a} = refl
    sound (cong-stable eq) = ext λ k → sound eq
    sound (cong-event eq) {n} {a} rewrite sound′ eq {n} {a} = refl

    -- Soundness of computational term equality: equal terms have equal denotations
    sound′ : ∀{A Γ} {M₁ M₂ : Γ ⊨ A}
             -> Γ ⊨ M₁ ≡ M₂ ∷ A
             -> ⟦ M₁ ⟧ᵐ ≈ ⟦ M₂ ⟧ᵐ
    sound′ (refl M) = refl
    sound′ (Eq′.sym eq) = ≡.sym (sound′ eq)
    sound′ (Eq′.trans eq₁ eq₂) = ≡.trans (sound′ eq₁) (sound′ eq₂)
    sound′ (β-sig′ C M) {n} {⟦Γ⟧} rewrite subst′-sound M C {n} {⟦Γ⟧} = refl
    sound′ (β-evt′ C D) {n} {⟦Γ⟧} rewrite subst″-sound D C n ⟦Γ⟧ = refl
    sound′ {_}{Γ} (β-selectₚ {A}{B}{C} C₁ C₂ C₃ M₁ M₂) {n} {⟦Γ⟧} =
        begin
            ⟦ select event (pure M₁) ↦ C₁ || event (pure M₂) ↦ C₂ ||both↦ C₃ ⟧ᵐ n ⟦Γ⟧
        ≡⟨⟩
            ⟦ C₃ ⟧ᵐ n ((⌞ ⟦ Γ ˢ⟧□ n ⟦Γ⟧ n ⌟ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧) , ⟦ M₂ ⟧ₘ n ⟦Γ⟧)
        ≡⟨ cong! (⟦ˢ⟧-factor Γ {n} {⟦Γ⟧}) ⟩
            ⟦ C₃ ⟧ᵐ n ((⌞ ⟦ Γ ˢ⟧ n ⟦Γ⟧ ⌟ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧) , ⟦ M₂ ⟧ₘ n ⟦Γ⟧)
        ≡⟨ cong! (⟦subst⟧-Γˢ⊆Γ Γ {n} {⟦Γ⟧}) ⟩
            ⟦ C₃ ⟧ᵐ n (⌞ (⟦subst⟧ (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) n ⟦Γ⟧ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧) ⌟ , ⟦ M₂ ⟧ₘ n ⟦Γ⟧ )
        ≡⟨ cong! (⟦↑⟧ (A now) (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) {n} {⟦Γ⟧ , (⟦ M₁ ⟧ₘ n ⟦Γ⟧)}) ⟩
            ⟦ C₃ ⟧ᵐ n ⌞ ((⟦subst⟧ (_↑_ {A now} (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) 𝒯erm) n (⟦Γ⟧ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧)) , ⟦ M₂ ⟧ₘ n ⟦Γ⟧) ⌟
        ≡⟨ cong! (⟦↑⟧ (B now) (_↑_ {A now} (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) 𝒯erm) {n} {(⟦Γ⟧ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧) , (⟦ M₂ ⟧ₘ n ⟦Γ⟧)}) ⟩
            ⟦ C₃ ⟧ᵐ n (⟦subst⟧ (_↑_ {B now} (_↑_ {A now} (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) 𝒯erm) 𝒯erm) n ((⟦Γ⟧ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧) , ⌞ ⟦ M₂ ⟧ₘ n ⟦Γ⟧ ⌟))
        ≡⟨ cong! (⟦𝓌⟧ (A now) M₂ {n} {⟦Γ⟧ , (⟦ M₁ ⟧ₘ n ⟦Γ⟧)}) ⟩
            ⟦ C₃ ⟧ᵐ n (⟦subst⟧ (weakₛ 𝒯ermₛ s) n ((⟦Γ⟧ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧) , ⟦ 𝓌 M₂ ⟧ₘ n (⟦Γ⟧ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧)))
        ≡⟨ ≡.sym (traverse′-sound ⟦𝒯erm⟧ (weakₛ 𝒯ermₛ s) C₃ {n} {(⟦Γ⟧ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧) , ⟦ 𝓌 M₂ ⟧ₘ n (⟦Γ⟧ , (⟦ M₁ ⟧ₘ n ⟦Γ⟧))})  ⟩
            ⟦ traverse′ (weakₛ 𝒯ermₛ s) C₃ ⟧ᵐ n ((⟦Γ⟧ , ⟦ M₁ ⟧ₘ n ⟦Γ⟧) , ⟦ 𝓌 M₂ ⟧ₘ n (⟦Γ⟧ , (⟦ M₁ ⟧ₘ n ⟦Γ⟧)))
        ≡⟨ ≡.sym (subst′-sound (𝓌 M₂) (weakening′ s C₃) {n} {⟦Γ⟧ , (⟦ M₁ ⟧ₘ n ⟦Γ⟧)}) ⟩
            ⟦ [ 𝓌 M₂ /′] (weakening′ s C₃) ⟧ᵐ n (⟦Γ⟧ , (⟦ M₁ ⟧ₘ n ⟦Γ⟧))
        ≡⟨ ≡.sym (subst′-sound M₁ ([ 𝓌 M₂ /′] (weakening′ s C₃)) {n} {⟦Γ⟧} ) ⟩
            ⟦ [ M₁ /′] ([ 𝓌 M₂ /′] (weakening′ s C₃)) ⟧ᵐ n ⟦Γ⟧
        ∎
        where
        s : Γ ˢ ,, A now ,, B now ⊆ Γ ,, A now ,, B now
        s = keep (keep (Γˢ⊆Γ Γ))
    sound′ (η-sig′ M) = refl
    sound′ (cong-pure′ eq) {n} {⟦Γ⟧} rewrite sound eq {n} {⟦Γ⟧} = refl
    sound′ (cong-letSig′ eq B) {n} {⟦Γ⟧} rewrite sound eq {n} {⟦Γ⟧} = refl
    sound′ (cong-letEvt′ eq D) {n} {⟦Γ⟧} rewrite sound eq {n} {⟦Γ⟧} = refl
