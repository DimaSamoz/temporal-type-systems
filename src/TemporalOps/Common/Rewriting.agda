
{- Lemmas and operations involving rewriting and heterogeneous equality. -}
module TemporalOps.Common.Rewriting where

open import Relation.Binary.HeterogeneousEquality as ≅
open import Relation.Binary.PropositionalEquality as ≡


-- | Rewriting and heterogeneous equality

-- Substitution with identity predicate – explicit rewriting
rew : ∀{ℓ}{x y : Set ℓ} -> x ≡ y -> x -> y
rew refl x = x

-- Rewriting preserves heterogeneous equality
rew-to-≅ : ∀{ℓ}{A B : Set ℓ}{v : A} -> (p : A ≡ B) -> v ≅ rew p v
rew-to-≅ {A = A} {.A} {v} refl = ≅.refl

-- Heterogenous equality with differently typed arguments
-- can be converted to homogeneous equality via rewriting of the types
≅-to-rew-≡ : ∀ {P Q : Set} {x : P} {y : Q}
            -> (p : x ≅ y) -> (e : P ≡ Q)
            -> rew e x ≡ y
≅-to-rew-≡ ≅.refl refl = refl

-- Rewriting by p is cancelled out by rewriting by (sym p)
rew-cancel : ∀ {P Q : Set}
            -> (v : P) -> (p : P ≡ Q)
            -> rew (≡.sym p) (rew p v) ≡ v
rew-cancel v refl = refl

-- | Other lemmas

-- Heterogeneous congruence of three arguments
≅-cong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ (x : A) → B x → Set c}
            {D : ∀ (x : A) -> (y : B x) -> C x y -> Set d} {x y z w u v}
       -> (f : (x : A) (y : B x) (z : C x y) → D x y z)
       -> x ≅ y -> z ≅ w -> u ≅ v -> f x z u ≅ f y w v
≅-cong₃ f ≅.refl ≅.refl ≅.refl = ≅.refl
