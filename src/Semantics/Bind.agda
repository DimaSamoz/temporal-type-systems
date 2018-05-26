{-# OPTIONS --allow-unsolved-metas #-}
module Semantics.Bind where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Substitution.Kits
open import Syntax.Substitution.Instances
open import Syntax.Substitution.Lemmas

open import Semantics.Types
open import Semantics.Terms
open import Semantics.Context
open import Semantics.Substitution.Kits
open import Semantics.Substitution.Traversal
open import Semantics.Substitution.Instances

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Comonad
open import CategoryTheory.CartesianStrength
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open import TemporalOps.Diamond
open import TemporalOps.Delay
open import TemporalOps.Box
open import TemporalOps.OtherOps
open import TemporalOps.StrongMonad

open import Data.Sum
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open ≡.≡-Reasoning
open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional

open Comonad W-□
open Monad M-◇
private module F-◇ = Functor F-◇
private module F-□ = Functor F-□
open Functor F-□ renaming (fmap to □-f)
open Functor F-◇ renaming (fmap to ◇-f)
private module ▹ᵏ-C k = CartesianFunctor (F-cart-delay k)
private module ▹ᵏ-F k = Functor (F-delay k)
private module □-▹ᵏ k = _⟹_ (□-to-▹ᵏ k)


bind-to->>= : ∀ Γ {⟦A⟧ ⟦B⟧} -> (⟦E⟧ : ⟦ Γ ⟧ₓ ⇴ ◇ ⟦A⟧) (⟦C⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ⟦A⟧ ⇴ ◇ ⟦B⟧)
        -> (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
        -> bindEvent Γ ⟦E⟧ ⟦C⟧ n ⟦Γ⟧
        ≡ (⟦E⟧ n ⟦Γ⟧ >>= λ l ⟦A⟧ → ⟦C⟧ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
bind-to->>= Γ {⟦A⟧} {⟦B⟧} ⟦E⟧ ⟦C⟧ n ⟦Γ⟧ =
    begin
        bindEvent Γ ⟦E⟧ ⟦C⟧ n ⟦Γ⟧
    ≡⟨⟩
        μ.at ⟦B⟧ n (F-◇.fmap (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n (st ⟦ Γ ˢ ⟧ₓ ⟦A⟧ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧)))
    ≡⟨ cong (μ.at ⟦B⟧ n) (lemma (⟦E⟧ n ⟦Γ⟧)) ⟩
        μ.at ⟦B⟧ n (F-◇.fmap (⟦C⟧ ∘ ⟨ (λ l _ → ⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , id ⟩) n (⟦E⟧ n ⟦Γ⟧))
    ≡⟨⟩
        (⟦E⟧ n ⟦Γ⟧ >>= (λ l ⟦A⟧ → ⟦C⟧ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧)))
    ∎
    where
    lemma : ∀ ◇⟦A⟧
         -> F-◇.fmap (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n (st ⟦ Γ ˢ ⟧ₓ ⟦A⟧ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦A⟧))
          ≡ F-◇.fmap (⟦C⟧ ∘ ⟨ (λ l _ → ⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , id ⟩) n ◇⟦A⟧
    lemma (k , a) =
        begin
            F-◇.fmap (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n (st ⟦ Γ ˢ ⟧ₓ ⟦A⟧ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , (k , a)))
        ≡⟨⟩
            k , ▹ᵏ-F.fmap k (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                (▹ᵏ-C.m k (□ ⟦ Γ ˢ ⟧ₓ) ⟦A⟧ n (□-▹ᵏ.at k (□ ⟦ Γ ˢ ⟧ₓ) n (δ.at ⟦ Γ ˢ ⟧ₓ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧)) , a))
        ≡⟨ {!   !} ⟩
            k , ▹ᵏ-F.fmap k (⟦C⟧ ∘ ⟨ (λ l _ → ⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , id ⟩) n a
        ≡⟨⟩
            F-◇.fmap (⟦C⟧ ∘ ⟨ (λ l _ → ⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , id ⟩) n (k , a)
        ∎
        where


-- -- Helper function for interpreting bound events
-- bindEvent : ∀ Γ {⟦A⟧ ⟦B⟧} -> (⟦E⟧ : ⟦ Γ ⟧ₓ ⇴ ◇ ⟦A⟧) (⟦C⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ⟦A⟧ ⇴ ◇ ⟦B⟧)
--               -> (⟦ Γ ⟧ₓ ⇴ ◇ ⟦B⟧)
-- bindEvent Γ {⟦A⟧}{⟦B⟧} ⟦E⟧ ⟦C⟧ =
--     μ.at ⟦B⟧ ∘ F-◇.fmap (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) ∘ st ⟦ Γ ˢ ⟧ₓ ⟦A⟧ ∘ ⟨ ⟦ Γ ˢ⟧□ , ⟦E⟧ ⟩

-- private
--     open ⟦K⟧ ⟦𝒯erm⟧
--     ⟦_⟧ₛ : ∀{Γ Δ} -> Subst Term Γ Δ -> ⟦ Δ ⟧ₓ ⇴ ⟦ Γ ⟧ₓ
--     ⟦ σ ⟧ₛ = ⟦subst⟧ σ

--
-- assoc-lemma : ∀ Γ {A B G} (⟦C⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ⟦ G ⟧ₜ ⇴ ◇ ⟦ A ⟧ₜ)
--         (⟦D⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ⟦ A ⟧ₜ ⇴ ◇ ⟦ B ⟧ₜ)
--      -> μ.at (◇ ⟦ B ⟧ₜ)
--         ∘ (◇-f (◇-f (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id ∘ ε.at ⟦ Γ ˢ ˢ ⟧ₓ * id)
--                            ∘ st ⟦ Γ ˢ ˢ ⟧ₓ ⟦ A ⟧ₜ
--                            ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ , ⟦C⟧ ⟩ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id))
--         ∘ st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ ∘ (⟦ Γ ˢ⟧□ * id)
--      ≈ ◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) ∘ st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ
--      ∘ ⟨ π₁ ∘ ⟦ Γ ˢ⟧□ * id , μ.at ⟦ A ⟧ₜ ∘ ◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id)
--                          ∘ st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ ∘ ⟦ Γ ˢ⟧□ * id ⟩
-- assoc-lemma Γ {A} {B} {G} ⟦C⟧ ⟦D⟧ {n} {⟦Γ⟧ , ◇⟦G⟧} =
--     begin
--         μ.at (◇ ⟦ B ⟧ₜ) n
--             (◇-f (⌞ ◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ∘ □-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) * id) ⌟
--                  ∘ st ⟦ Γ ˢ ˢ ⟧ₓ ⟦ A ⟧ₜ
--                  ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ , ⟦C⟧ ⟩ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id)) n
--         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))
--     ≡⟨ cong! (ext λ m → ext λ b →
--             F-◇.fmap-∘ {g = ⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id} {□-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) * id} {m} {b}) ⟩
--         μ.at (◇ ⟦ B ⟧ₜ) n
--             (◇-f (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) ∘
--                  ⌞ ◇-f (□-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) * id)
--                  ∘ st ⟦ Γ ˢ ˢ ⟧ₓ ⟦ A ⟧ₜ ⌟
--                  ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ , ⟦C⟧ ⟩ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id)) n
--         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))
--     ≡⟨ cong! (ext λ m → ext λ b → st-nat₁ {D = ⟦ A ⟧ₜ} (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) {m} {b}) ⟩
--         μ.at (◇ ⟦ B ⟧ₜ) n
--             (◇-f (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) ∘
--                  st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ ∘ □-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id
--                  ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ , ⟦C⟧ ⟩ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id)) n
--         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))
--     ≡⟨⟩
--         -- μ.at (◇ ⟦ B ⟧ₜ) n
--         --     (◇-f (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) ∘
--         --          st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ ∘ □-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id
--         --          ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--         -- (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))
--     -- -- ≡⟨ cong! (ext λ m → ext λ b → st-nat₁ {D = ⟦ A ⟧ₜ} (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) {m} {b}) ⟩
--         μ.at (◇ ⟦ B ⟧ₜ) n
--             (◇-f (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id)
--                     ∘ st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ
--                     ∘ ⟨ □-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) ∘ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                       , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                 (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))
--     ≡⟨ cong (μ.at (◇ ⟦ B ⟧ₜ) n) (F-◇.fmap-∘ {g = ◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) ∘ st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ}
--                             {⟨ □-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) ∘ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                                       , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩}{n}{st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)}) ⟩
--         μ.at (◇ ⟦ B ⟧ₜ) n
--             (◇-f (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id)
--                     ∘ st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ) n
--             (◇-f (⟨ □-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) ∘ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                       , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                 (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))))
--     ≡⟨ cong (μ.at (◇ ⟦ B ⟧ₜ) n) (F-◇.fmap-∘ {g = ◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id)} {st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ} {n}
--                                     {◇-f (⟨ □-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) ∘ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                                           , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                                           (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))})  ⟩
--         μ.at (◇ ⟦ B ⟧ₜ) n
--             (◇-f (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id)) n
--             (◇-f (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ) n
--                 ⌞ (◇-f (⟨ □-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) ∘ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                       , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                       (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))) ⌟ ))
--     ≡⟨ cong! lemma2 ⟩
--         μ.at (◇ ⟦ B ⟧ₜ) n
--             (◇-f (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id)) n
--             (◇-f (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ) n
--                 (st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                 (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                 (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))))))
--     ≡⟨ sym (μ.nat-cond {f = ⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id} {n}
--                         {◇-f (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ) n (st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                             (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                                         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))))}) ⟩
--         ◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--             (μ.at (□ ⟦ Γ ˢ ⟧ₓ ⊗ ⟦ A ⟧ₜ) n
--             (◇-f (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ) n
--             (st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                 (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                             (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))))))
--     ≡⟨ cong (λ x → ◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n x)
--         (st-μ {⟦ Γ ˢ ⟧ₓ} {⟦ A ⟧ₜ} {n} {⟦ Γ ˢ⟧□ n ⟦Γ⟧ ,
--             (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                 (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))}) ⟩
--         ◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--             (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ ,
--                 μ.at ⟦ A ⟧ₜ n (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                     (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))))
--     ∎
--         where
--         lemma2 : ◇-f (⟨ □-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) ∘ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                       , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))
--               ≡ st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                     (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))))
--         lemma2 =
--             begin
--                 ◇-f (⟨ □-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) ∘ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                      , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))
--             ≡⟨⟩
--                 ◇-f (( □-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) * id)
--                     ∘ ⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                       , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))
--             ≡⟨ F-◇.fmap-∘ ⟩
--                 ◇-f (□-f (⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ) * id) n
--                     (◇-f (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                           , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                     (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))
--             ≡⟨ cong (◇-f (□-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id) n) (
--                 -- ≡⟨ F-◇.fmap-∘ ⟩
--                 --     ◇-f ((⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ) * id) n
--                 --     (◇-f (⟨ π₁ , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                 --     (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))
--                 begin
--                     ◇-f (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                           , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                     (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⌞ ⟦ Γ ˢ⟧□ n ⟦Γ⟧ ⌟ , ◇⟦G⟧))
--                 ≡⟨ cong! (⟦ˢˢ⟧ Γ {n} {⟦Γ⟧}) ⟩
--                     ◇-f (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                           , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                     ⌞ (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (□-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ n (⟦ Γ ˢ ˢ⟧□ n (⟦ Γ ˢ⟧ n ⟦Γ⟧)) , ◇⟦G⟧)) ⌟
--                     -- ⌞ ((st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ ∘ (□-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ ∘ ⟦ Γ ˢ ˢ⟧□ ∘ ⟦ Γ ˢ⟧) * id) n (⟦Γ⟧ , ◇⟦G⟧)) ⌟
--                 ≡⟨ cong! (st-nat₁ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ {n} {⟦ Γ ˢ ˢ⟧□ n (⟦ Γ ˢ⟧ n ⟦Γ⟧) , ◇⟦G⟧}) ⟩
--                     ◇-f (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                           , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                     (◇-f (□-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id) n (st ⟦ Γ ˢ ˢ ⟧ₓ ⟦ G ⟧ₜ n ((⟦ Γ ˢ ˢ⟧□ n (⟦ Γ ˢ⟧ n ⟦Γ⟧)) , ◇⟦G⟧)))
--                 ≡⟨ sym F-◇.fmap-∘ ⟩
--                     ◇-f (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                           , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩ ∘ (□-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id)) n
--                     (st ⟦ Γ ˢ ˢ ⟧ₓ ⟦ G ⟧ₜ n ((⟦ Γ ˢ ˢ⟧□ n (⟦ Γ ˢ⟧ n ⟦Γ⟧)) , ◇⟦G⟧))
--                 ≡⟨⟩
--                     ◇-f (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ □-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ ∘ π₁
--                         , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ∘ □-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id ⟩) n
--                     (st ⟦ Γ ˢ ˢ ⟧ₓ ⟦ G ⟧ₜ n ((⟦ Γ ˢ ˢ⟧□ n (⟦ Γ ˢ⟧ n ⟦Γ⟧)) , ◇⟦G⟧))
--                 ≡⟨ {!   !} ⟩
--                     ◇-f (□-f ⟦ Γ ˢ ˢ⟧ * id) n
--                         (st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                             ( ⟦ Γ ˢ⟧□ n ⟦Γ⟧
--                             , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                                 (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))))
--                 ≡⟨ st-nat₁ ⟦ Γ ˢ ˢ⟧ ⟩
--                     st ⟦ Γ ˢ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                         ( ( ⌞ □-f ⟦ Γ ˢ ˢ⟧ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧) ⌟
--                           , ◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n
--                                 (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))))
--                 ≡⟨ cong! (⟦ˢ⟧-comm Γ) ⟩
--                     st ⟦ Γ ˢ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                         ( (⟦ Γ ˢ ˢ⟧□ n (⌞ ⟦ Γ ˢ⟧ n ⟦Γ⟧ ⌟)
--                           , ◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n
--                                 (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))))
--                 ≡⟨ cong! (⟦ˢ⟧-factor Γ) ⟩
--                     st ⟦ Γ ˢ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                         (((⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ) * id
--                           ∘ ⟨ π₁ , ◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) ∘ st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ ⟩) n
--                            (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))
--                 ∎
--             ) ⟩
--                 ◇-f (□-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id) n
--                     (st ⟦ Γ ˢ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                         (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
--                          , ◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id)
--                            ∘ st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ ⟩ n
--                            (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))
--             ≡⟨ st-nat₁ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ ⟩
--                 st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                     ((□-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * (id {◇ ◇ ⟦ A ⟧ₜ})) n
--                         (⟦ Γ ˢ ˢ⟧□ n (ε.at ⟦ Γ ˢ ⟧ₓ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧))
--                         , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                             (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))))
--             ≡⟨⟩
--                 st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                     ( □-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ n (⟦ Γ ˢ ˢ⟧□ n (⌞ ε.at ⟦ Γ ˢ ⟧ₓ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧) ⌟))
--                     , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))))
--             ≡⟨ cong! (⟦ˢ⟧-factor Γ) ⟩
--                 st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                     ( ⌞ □-f ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ n (⟦ Γ ˢ ˢ⟧□ n (⟦ Γ ˢ⟧ n ⟦Γ⟧)) ⌟
--                     , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))))
--             ≡⟨ cong! (⟦ˢˢ⟧ Γ) ⟩
--                 st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
--                     ( ⟦ Γ ˢ⟧□ n ⟦Γ⟧
--                     , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))))
--             ∎
                -- where
                -- bar : ∀ ◇⟦G⟧ -> ◇-f (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
                --       , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
                --         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))
                --     ≡ ◇-f (□-f ⟦ Γ ˢ ˢ⟧ * id) n
                --         (st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
                --             ( ⟦ Γ ˢ⟧□ n ⟦Γ⟧
                --             , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                --                 (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧)))))
                -- bar (k , a) =
                --     begin
                --         ◇-f (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
                --               , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
                --                 (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , (k , a)))
                --     ≡⟨⟩
                --         ◇-f (⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
                --               , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
                --                 (k , ▹ᵏ-C.m k (□ ⟦ Γ ˢ ⟧ₓ) ⟦ G ⟧ₜ n
                --                     (□-▹ᵏ.at k (□ ⟦ Γ ˢ ⟧ₓ) n
                --                         (δ.at (⟦ Γ ˢ ⟧ₓ) k (⟦ Γ ˢ⟧□ n ⟦Γ⟧)) , a))
                --     ≡⟨⟩
                --         k , ▹ᵏ-F.fmap k ( ⟨ ⟦ Γ ˢ ˢ⟧□ ∘ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁
                --                         , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
                --                 (▹ᵏ-C.m k (□ ⟦ Γ ˢ ⟧ₓ) ⟦ G ⟧ₜ n
                --                     (□-▹ᵏ.at k (□ ⟦ Γ ˢ ⟧ₓ) n
                --                         (δ.at (⟦ Γ ˢ ⟧ₓ) k (⟦ Γ ˢ⟧□ n ⟦Γ⟧)) , a))
                --     ≡⟨ {!   !} ⟩
                --         ◇-f (□-f ⟦ Γ ˢ ˢ⟧ * id) n
                --             (st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n
                --                 ( ⟦ Γ ˢ⟧□ n ⟦Γ⟧
                --                 , (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                --                     (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , (k , a))))))
                --     ∎
    -- st-◇ A B n (□A , (k , a)) = k , ▹ᵏ-C.m k (□ A) B n (□-▹ᵏ.at k (□ A) n (δ.at A k □A) , a)

-- -- Associativity property of binding
-- bind-assoc : ∀ Γ {A B G} (⟦E⟧ : ⟦ Γ ⟧ₓ ⇴ ◇ ⟦ G ⟧ₜ)
--             (⟦C⟧ : ⟦ Γ ˢ ,, G now ⟧ₓ ⇴ ◇ ⟦ A ⟧ₜ) (⟦D⟧ : ⟦ Γ ˢ ,, A now ⟧ₓ ⇴ ◇ ⟦ B ⟧ₜ)
--           -> bindEvent Γ ⟦E⟧
--                 (bindEvent (Γ ˢ ,, G now) ⟦C⟧ (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id))
--            ≈ bindEvent Γ (bindEvent Γ ⟦E⟧ ⟦C⟧) ⟦D⟧
-- bind-assoc Γ {A}{B}{G} ⟦E⟧ ⟦C⟧ ⟦D⟧ {n} {⟦Γ⟧} =
--     begin
--         bindEvent Γ ⟦E⟧ (bindEvent (Γ ˢ ,, G now) ⟦C⟧ (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id)) n ⟦Γ⟧
--     ≡⟨⟩
--         μ.at ⟦ B ⟧ₜ n
--         (◇-f (bindEvent (Γ ˢ ,, G now) ⟦C⟧ (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id) ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id)) n
--             (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧)))
--     ≡⟨⟩
--         μ.at ⟦ B ⟧ₜ n
--         (◇-f (μ.at ⟦ B ⟧ₜ ∘ ◇-f (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id ∘ ε.at ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ * id)
--                          ∘ st ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ ⟦ A ⟧ₜ
--                          ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) , ⟦C⟧ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) ⟩ ) n
--             (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧)))
--     ≡⟨ cong (μ.at ⟦ B ⟧ₜ n) (F-◇.fmap-∘ {g = μ.at ⟦ B ⟧ₜ} {◇-f (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id ∘ ε.at ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ * id)
--                     ∘ st ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ ⟦ A ⟧ₜ ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) , ⟦C⟧ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) ⟩ }
--                     {n} {st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧)}) ⟩
--         μ.at ⟦ B ⟧ₜ n (◇-f (μ.at ⟦ B ⟧ₜ) n
--             (◇-f (◇-f (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id ∘ ε.at ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ * id)
--                          ∘ st ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ ⟦ A ⟧ₜ
--                          ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) , ⟦C⟧ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) ⟩ ) n
--             (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧))))
--     ≡⟨ sym (μ-assoc {n = n} {◇-f (◇-f (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id ∘ ε.at ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ * id)
--                  ∘ st ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ ⟦ A ⟧ₜ
--                  ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) , ⟦C⟧ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) ⟩ ) n
--                     (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧))}) ⟩
--         μ.at ⟦ B ⟧ₜ n (μ.at (◇ ⟦ B ⟧ₜ) n
--             (◇-f (◇-f (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id ∘ ε.at ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ * id)
--                          ∘ st ⟦ (Γ ˢ ,, G now) ˢ ⟧ₓ ⟦ A ⟧ₜ
--                          ∘ ⟨ ⟦ Γ ˢ ,, G now ˢ⟧□ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) , ⟦C⟧ ∘ (ε.at ⟦ Γ ˢ ⟧ₓ * id) ⟩ ) n
--             (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧))))
--     ≡⟨ cong (μ.at ⟦ B ⟧ₜ n) (assoc-lemma Γ {A}{B}{G} ⟦C⟧ ⟦D⟧ {n} {⟦Γ⟧ , (⟦E⟧ n ⟦Γ⟧)}) ⟩
--     -- ≡⟨ cong (μ.at ⟦ B ⟧ₜ n) (lemma Γ {A} {B} {G} ⟦C⟧ ⟦D⟧ {n} {(⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧)}) ⟩
--     --     μ.at ⟦ B ⟧ₜ n (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--     --         (μ.at (□ ⟦ Γ ˢ ⟧ₓ ⊗ ⟦ A ⟧ₜ) n
--     --         (◇-f (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ) n
--     --         (st ⟦ Γ ˢ ⟧ₓ (◇ ⟦ A ⟧ₜ) n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ ,
--     --             (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--     --                 (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧))))))))
--     -- ≡⟨ cong (λ x → μ.at ⟦ B ⟧ₜ n (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n x))
--     --     (st-μ {⟦ Γ ˢ ⟧ₓ} {⟦ A ⟧ₜ} {n} {⟦ Γ ˢ⟧□ n ⟦Γ⟧ ,
--     --         (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--     --             (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧)))}) ⟩
--     --     μ.at ⟦ B ⟧ₜ n (◇-f ⟦D⟧ n
--     --         (◇-f (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--     --         (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ ,
--     --             μ.at ⟦ A ⟧ₜ n (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--     --                 (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧)))))))
--     -- ≡⟨ cong (μ.at ⟦ B ⟧ₜ n) (sym (F-◇.fmap-∘ {g = ⟦D⟧}{ε.at ⟦ Γ ˢ ⟧ₓ * id}{n}
--     --                 {st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ ,
--     --                     μ.at ⟦ A ⟧ₜ n (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--     --                         (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧))))})) ⟩
--         μ.at ⟦ B ⟧ₜ n (◇-f (⟦D⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--             (st ⟦ Γ ˢ ⟧ₓ ⟦ A ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ ,
--                 μ.at ⟦ A ⟧ₜ n (◇-f (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                     (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧))))))
--     ≡⟨⟩
--         bindEvent Γ (bindEvent Γ ⟦E⟧ ⟦C⟧) ⟦D⟧ n ⟦Γ⟧
--     ∎
--                 ≡⟨ F-◇.fmap-∘ ⟩
--                     ◇-f (⟦ Γ ˢ ˢ⟧□ * id) n
--                     (◇-f (ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                     (◇-f (⟨ π₁ , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                     (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))))
--                     -- ((◇-f (⟨ ε.at ⟦ Γ ˢ ⟧ₓ ∘ π₁ , ⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id ⟩) n
--                 ≡⟨ cong (◇-f (⟦ Γ ˢ ˢ⟧□ * id) n) (sym F-◇.fmap-∘) ⟩
--                     ◇-f (⟦ Γ ˢ ˢ⟧□ * id) n
--                         ((◇-f (⟨ π₁ , ⟦C⟧ ⟩ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
--                             (st ⟦ Γ ˢ ⟧ₓ ⟦ G ⟧ₜ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦G⟧))))

-- bind-assoc : ∀ Γ A B G (⟦E⟧ : ⟦ Γ ⟧ₓ ⇴ ◇ ⟦ G ⟧ₜ)
--             (⟦C⟧ : ⟦ Γ ˢ ,, G now ⟧ₓ ⇴ ◇ ⟦ A ⟧ₜ) (⟦D⟧ : ⟦ Γ ˢ ,, A now ⟧ₓ ⇴ ◇ ⟦ B ⟧ₜ)
--           -> bindEvent Γ ⟦E⟧
--                 (bindEvent (Γ ˢ ,, G now) ⟦C⟧ (⟦D⟧ ∘ ⟦ Γ ˢˢₛ 𝒯erm ⟧ₛ * id))
--            ≈ bindEvent Γ (bindEvent Γ ⟦E⟧ ⟦C⟧) ⟦D⟧
-- bind-assoc Γ A B G ⟦E⟧ ⟦C⟧ ⟦D⟧ {n} {⟦Γ⟧} = {!   !}
