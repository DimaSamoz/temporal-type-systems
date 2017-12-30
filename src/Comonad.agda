
-- Comonadic structure of the box operator
module Comonad where

open import Category
open import Functor
open import TemporalOps

-- Counit for □.
ε : {A : τ} -> □ A ⇴ A
ε n a = a n

-- Duplicate for □.
δ : {A : τ} -> □ A ⇴ □ □ A
δ n a = λ k → a

-- || Comonad laws

fmap-ε∘δ=id : ∀{A : τ} -> fmap-□ {□ A} ε ∘ δ ≡ id
fmap-ε∘δ=id = refl

ε∘delta=id : ∀{A : τ} -> ε {□ A} ∘ δ ≡ id
ε∘delta=id = refl

fmap-δ∘δ=δ∘δ : ∀{A : τ} -> fmap-□ {□ A} δ ∘ δ ≡ δ ∘ δ
fmap-δ∘δ=δ∘δ = refl

-- || K axiom: □ preserves exponentials
K-□ : ∀{A B : τ} -> □ (A ⇒ B) ⇴ (□ A ⇒ □ B)
K-□ n f = fmap-□ f n
