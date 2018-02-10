
{- Diamond operator. -}
module TemporalOps.Diamond where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import TemporalOps.Common
open import TemporalOps.Next
open import TemporalOps.Delay
open import TemporalOps.Diamond.Functor
open import TemporalOps.Diamond.Join

import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
    using (_≅_ ; ≅-to-≡ ; ≡-to-≅ ; cong₂) renaming (sym to ≅-sym)
open import Data.Nat.Properties
    using (+-identityʳ ; +-comm ; +-suc ; +-assoc)


M-◇ : Monad ℝeactive
M-◇ = record
    { T = F-◇
    ; η = η-◇
    ; μ = μ-◇
    ; η-unit1 = refl
    ; η-unit2 = {!   !}
    ; μ-assoc = {!   !} }
    where
    η-◇ : I ⟹ F-◇
    η-◇ = record
        { at = λ A n x -> 0 , x
        ; nat-cond = λ {A} {B} {f} {n} {a} → refl }

        where
            n + suc l , rew (delay-⊤ n l) top.tt
