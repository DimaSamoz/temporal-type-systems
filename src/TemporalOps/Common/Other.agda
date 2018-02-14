
{- Other common operations and lemmas. -}
module TemporalOps.Common.Other where

open import Relation.Binary.HeterogeneousEquality as ≅ hiding (inspect)
open import Relation.Binary.PropositionalEquality hiding (inspect)


-- Time indexing (for clarity, synonym of function appliation at any level)
_at_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f at n = f n
infixl 45 _at_

-- Inspect idiom
data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl
