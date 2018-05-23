
{- Denotational semantics of the terms in the category of temporal types. -}
module Semantics.Terms where

open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Types

open import Semantics.Types
open import Semantics.Context

open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Linear
open import TemporalOps.Box
open import TemporalOps.Diamond
open import TemporalOps.OtherOps
open import TemporalOps.Linear
open import TemporalOps.StrongMonad

open import CategoryTheory.Functor
open import CategoryTheory.NatTrans renaming (_⟹_ to ⟹)
import CategoryTheory.Monad as M
import CategoryTheory.Comonad as W

open import Data.Product
open import Data.Sum hiding ([_,_])
import Data.Nat as N

open W.Comonad W-□
open M.Monad M-◇
private module F-◇ = Functor F-◇
private module F-□ = Functor F-□
-- open Linear ℝeactive-linear

mutual
    -- Denotation of pure terms as morphisms from contexts to types.
    ⟦_⟧ₘ : ∀{Γ A} -> Γ ⊢ A -> (⟦ Γ ⟧ₓ ⇴ ⟦ A ⟧ⱼ)
    ⟦ var top       ⟧ₘ = π₂
    ⟦ var (pop x)   ⟧ₘ = ⟦ var x ⟧ₘ ∘ π₁
    ⟦ lam M         ⟧ₘ = Λ ⟦ M ⟧ₘ
    ⟦ F $ M         ⟧ₘ = eval ∘ ⟨ ⟦ F ⟧ₘ , ⟦ M ⟧ₘ ⟩
    ⟦ unit          ⟧ₘ = !
    ⟦ [ M ,, N ]    ⟧ₘ = ⟨ ⟦ M ⟧ₘ , ⟦ N ⟧ₘ ⟩
    ⟦ fst M         ⟧ₘ = π₁ ∘ ⟦ M ⟧ₘ
    ⟦ snd M         ⟧ₘ = π₂ ∘ ⟦ M ⟧ₘ
    ⟦ inl M         ⟧ₘ = ι₁ ∘ ⟦ M ⟧ₘ
    ⟦ inr M         ⟧ₘ = ι₂ ∘ ⟦ M ⟧ₘ
    ⟦ case M inl↦ B₁ ||inr↦ B₂ ⟧ₘ = [ ⟦ B₁ ⟧ₘ ⁏ ⟦ B₂ ⟧ₘ ] ∘ dist ∘ ⟨ id , ⟦ M ⟧ₘ ⟩
    ⟦ sample {A} S  ⟧ₘ = ε.at ⟦ A ⟧ₜ ∘ ⟦ S ⟧ₘ
    ⟦ stable {Γ} S  ⟧ₘ = F-□.fmap ⟦ S ⟧ₘ ∘ ⟦ Γ ˢ⟧□
    ⟦ sig S         ⟧ₘ = ⟦ S ⟧ₘ
    ⟦ letSig S In B ⟧ₘ = ⟦ B ⟧ₘ ∘ ⟨ id , ⟦ S ⟧ₘ ⟩
    ⟦ event E       ⟧ₘ = ⟦ E ⟧ᵐ

    -- Denotation of computational terms as Kleisli morphisms from contexts to types.
    ⟦_⟧ᵐ : ∀{Γ A} -> Γ ⊨ A -> (⟦ Γ ⟧ₓ ⇴ ◇ ⟦ A ⟧ⱼ)
    ⟦ pure {A} M     ⟧ᵐ = η.at ⟦ A ⟧ⱼ ∘ ⟦ M ⟧ₘ
    ⟦ letSig S InC C ⟧ᵐ = ⟦ C ⟧ᵐ ∘ ⟨ id , ⟦ S ⟧ₘ ⟩
    ⟦ letEvt_In_ {Γ} {A} E C ⟧ᵐ =
        (⟦ C ⟧ᵐ ⋆) ∘ F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) ∘ st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ ∘ ⟨ ⟦ Γ ˢ⟧□ , ⟦ E ⟧ₘ ⟩
    ⟦ select_↦_||_↦_||both↦_ {Γ} {A} {B} {C} E₁ C₁ E₂ C₂ C₃ ⟧ᵐ =
          (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ ⋆)
        ∘ F-◇.fmap (ε.at ⟦ Γ ˢ ⟧ₓ * id) ∘ st ⟦ Γ ˢ ⟧ₓ (⟦ A ⟧ₜ ⊛ ⟦ B ⟧ₜ) ∘ ⟨ ⟦ Γ ˢ⟧□ , ⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫ ⟩
