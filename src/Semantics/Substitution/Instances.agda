
-- Instances of semantic kits
module Semantics.Substitution.Instances where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Substitution.Kits
open import Syntax.Substitution.Instances

open import Semantics.Types
open import Semantics.Context
open import Semantics.Select
open import Semantics.Terms
open import Semantics.Substitution.Kits
open import Semantics.Substitution.Traversal

open import CategoryTheory.Categories using (ext)
open import CategoryTheory.NatTrans
open import CategoryTheory.Functor
open import CategoryTheory.Monad
open import CategoryTheory.Comonad
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open import TemporalOps.Diamond
open import TemporalOps.Box

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
private module F-□ = Functor F-□
open Comonad W-□

-- Denotation of variable kits
⟦𝒱ar⟧ : ⟦Kit⟧ 𝒱ar
⟦𝒱ar⟧ = record
    { ⟦_⟧ = ⟦_⟧-var
    ; ⟦𝓋⟧ = λ A Δ → refl
    ; ⟦𝓉⟧ = ⟦𝓉⟧-var
    ; ⟦𝓌⟧ = λ B T → refl
    ; ⟦𝒶⟧ = ⟦𝒶⟧-var
    }
    where
    open Kit 𝒱ar
    ⟦_⟧-var : ∀{A Γ} → Var Γ A → ⟦ Γ ⟧ₓ ⇴ ⟦ A ⟧ⱼ
    ⟦ top ⟧-var n (_ , ⟦A⟧) = ⟦A⟧
    ⟦ pop v ⟧-var n (⟦Γ⟧ , _) = ⟦ v ⟧-var n ⟦Γ⟧

    ⟦𝓉⟧-var : ∀{A Γ} → (x : Var Γ A)
          -> ⟦ 𝓉 x ⟧ₘ ≈ ⟦ x ⟧-var
    ⟦𝓉⟧-var {A now} top = refl
    ⟦𝓉⟧-var {A always} top = refl
    ⟦𝓉⟧-var {A now} (pop x) = ⟦𝓉⟧-var x
    ⟦𝓉⟧-var {A always} (pop x) = ⟦𝓉⟧-var x

    ⟦𝒶⟧-var : ∀{A Δ} → (x : Var Δ (A always))
           -> F-□.fmap ⟦ 𝒶 x ⟧-var ∘ ⟦ Δ ⟧ˢₓ-□ ≈ δ.at ⟦ A ⟧ₜ ∘ ⟦ x ⟧-var
    ⟦𝒶⟧-var top = refl
    ⟦𝒶⟧-var (pop {B = B now} x) = ⟦𝒶⟧-var x
    ⟦𝒶⟧-var (pop {B = B always} x) = ⟦𝒶⟧-var x


-- Denotation of term kits
⟦𝒯erm⟧ : ⟦Kit⟧ 𝒯erm
⟦𝒯erm⟧ = record
    { ⟦_⟧ = ⟦_⟧ₘ
    ; ⟦𝓋⟧ = λ A Δ → ⟦𝓉⟧ {A} top
    ; ⟦𝓉⟧ = λ T → refl
    ; ⟦𝓌⟧ = ⟦𝓌⟧-term
    ; ⟦𝒶⟧ = ⟦𝒶⟧-term
    }
    where
    open Kit 𝒯erm
    open ⟦Kit⟧ ⟦𝒱ar⟧
    open K
    open ⟦K⟧ ⟦𝒱ar⟧

    ⟦𝓌⟧-term : ∀ B {Δ A} → (M : Term Δ A)
           -> ⟦ 𝓌 {B} M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ π₁
    ⟦𝓌⟧-term B {Δ} M {n} {⟦Δ⟧ , ⟦B⟧}
        rewrite traverse-sound ⟦𝒱ar⟧ (_⁺_ {B} (idₛ 𝒱ar) 𝒱ar) M {n} {⟦Δ⟧ , ⟦B⟧}
              | ⟦⁺⟧ B {Δ} (idₛ 𝒱ar) {n} {⟦Δ⟧ , ⟦B⟧}
              | ⟦idₛ⟧ {Δ} {n} {⟦Δ⟧} = refl

    ⟦𝒶⟧-term : ∀{A Δ} (M : Δ ⊢ A always)
           -> F-□.fmap ⟦ 𝒶 M ⟧ₘ ∘ ⟦ Δ ⟧ˢₓ-□ ≈ δ.at ⟦ A ⟧ₜ ∘ ⟦ M ⟧ₘ
    ⟦𝒶⟧-term {A} {∙} (svar ())
    ⟦𝒶⟧-term {A} {∙} (stable M) = refl
    ⟦𝒶⟧-term {A} {Δ ,, B now} (svar (pop x)) = ⟦𝒶⟧-term (svar x)
    ⟦𝒶⟧-term {A} {Δ ,, B now} (stable M) = ⟦𝒶⟧-term {A} {Δ} (stable M)
    ⟦𝒶⟧-term {.B} {Δ ,, B always} (svar top) = refl
    ⟦𝒶⟧-term {A} {Δ ,, B always} (svar (pop x)) {n} {⟦Δ⟧ , ⟦□B⟧} = ext lemma
        where
        lemma : ∀ l -> ⟦ traverse 𝒱ar (_⁺_ {B always} (idₛ 𝒱ar) 𝒱ar) (𝒶 (svar x)) ⟧ₘ l (⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l , ⟦□B⟧)
                     ≡ ⟦ svar x ⟧ₘ n ⟦Δ⟧
        lemma l rewrite traverse-sound ⟦𝒱ar⟧ (_⁺_ {B always} (idₛ 𝒱ar) 𝒱ar) (𝒶 (svar x)) {l} {⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l , ⟦□B⟧}
                      | ⟦⁺⟧ (B always) {Δ ˢ} (idₛ 𝒱ar) {l} {⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l , ⟦□B⟧}
                      | ⟦idₛ⟧ {Δ ˢ} {l} {⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l}
                      | □-≡ n l (⟦𝒶⟧-term (svar x) {n} {⟦Δ⟧}) l = refl
    ⟦𝒶⟧-term {A} {Δ ,, B always} (stable M) {n} {⟦Δ⟧ , ⟦□B⟧} = ext λ l → ext (lemma l)
        where
        postulate
            duh : ∀ {A : Set}{x y : A} -> x ≡ y
        lemma : ∀ l m -> ⟦ subst (λ x₁ → x₁ ,, B always ⊢ A now) (sym (ˢ-idemp Δ)) M ⟧ₘ m
                            (⟦ Δ ˢ ⟧ˢₓ-□ l (⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l) m , ⟦□B⟧)
                          ≡ ⟦ M ⟧ₘ m (⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ m , ⟦□B⟧)
        lemma l m
            rewrite □-≡ l m (□-≡ n l (⟦⟧ˢₓ-□-twice Δ {n} {⟦Δ⟧}) l) m
            = duh
