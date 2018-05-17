{-# OPTIONS --allow-unsolved-metas #-}
{- Denotational semantics of the terms in the category of temporal types. -}
module Semantics.Terms where

open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Types

open import Semantics.Types
open import Semantics.Context
open import Semantics.Select

open import CategoryTheory.Instances.Reactive
open import TemporalOps.Box
open import TemporalOps.Diamond
open import TemporalOps.OtherOps
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
    ⟦ svar top      ⟧ₘ = π₂
    ⟦ svar (pop x)  ⟧ₘ = ⟦ svar x ⟧ₘ ∘ π₁
    ⟦ sample {A} S  ⟧ₘ = ε.at ⟦ A ⟧ₜ ∘ ⟦ S ⟧ₘ
    ⟦ stable {Γ} S  ⟧ₘ = F-□.fmap ⟦ S ⟧ₘ ∘ ⟦ Γ ⟧ˢₓ-□
    ⟦ sig S         ⟧ₘ = ⟦ S ⟧ₘ
    ⟦ letSig S In B ⟧ₘ = ⟦ B ⟧ₘ ∘ ⟨ id , ⟦ S ⟧ₘ ⟩
    ⟦ event E       ⟧ₘ = ⟦ E ⟧ᵐ

    -- Denotation of computational terms as Kleisli morphisms from contexts to types.
    ⟦_⟧ᵐ : ∀{Γ A} -> Γ ⊨ A -> (⟦ Γ ⟧ₓ ⇴ ◇ ⟦ A ⟧ⱼ)
    ⟦ pure {A} M     ⟧ᵐ = η.at ⟦ A ⟧ⱼ ∘ ⟦ M ⟧ₘ
    ⟦ letSig S InC C ⟧ᵐ = ⟦ C ⟧ᵐ ∘ ⟨ id , ⟦ S ⟧ₘ ⟩
    ⟦ letEvt_In_ {Γ} {A} E C ⟧ᵐ n env =
        ⟦ E ⟧ₘ n env >>= λ k ⟦A⟧ → ⟦ C ⟧ᵐ k (⟦ Γ ⟧ˢₓ-□ n env k , ⟦A⟧)
    ⟦ select_↦_||_↦_||both↦_ {Γ} {A} {B} {C} E₁ C₁ E₂ C₂ C₃ ⟧ᵐ n env =
        ◇-select n (⟦ E₁ ⟧ₘ n env , ⟦ E₂ ⟧ₘ n env)
        >>= ⟦select⟧ Γ A B C n env ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ
    -- ⟦ letEvt_In_ {Γ} E C ⟧ᵐ = (⟦ C ⟧ᵐ ⋆) ∘ ◇-sample ∘ ⟨ ⟦ Γ ⟧ˢₓ-□ , ⟦ E ⟧ₘ ⟩
    -- ⟦ select_↦_||_↦_||both↦_ {Γ} {A} {B} {C} E₁ C₁ E₂ C₂ C₃ ⟧ᵐ =
    --       (⟦select⟧ Γ A B C ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ ⋆)
    --     ∘ ◇-sample ∘ ⟨ ⟦ Γ ⟧ˢₓ-□ , ◇-select ∘ ⟨ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟩ ⟩
