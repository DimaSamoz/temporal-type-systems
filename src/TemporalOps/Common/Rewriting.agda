
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

-- | Equality of equality proofs and functions
-- Two propositional equality proofs are propositionally (heterogeneously) equal
-- if given two heterogeneously equal values, rewriting each with
-- the respective proofs gives propositionally (heterogeneously) equal terms.

-- Propositional equality of equality proofs
Proof-≅ : ∀{p1 p2 q1 q2 : Set} -> p1 ≡ q1 -> p2 ≡ q2 -> Set
Proof-≅ {p1}{p2} pf1 pf2 =
        (v : p1) (v′ : p2) -> v ≅ v′ -> rew pf1 v ≅ rew pf2 v′

-- Propositional equality of equality proofs
Proof-≡ : ∀{p1 p2 q : Set} -> p1 ≡ q -> p2 ≡ q -> Set
Proof-≡ {p1}{p2} pf1 pf2 =
        (v : p1) (v′ : p2) -> v ≅ v′ -> rew pf1 v ≡ rew pf2 v′

-- Propositional equality of functions
Fun-≅ : ∀{a1 a2 b1 b2 : Set} -> (a1 -> b1) -> (a2 -> b2) -> Set
Fun-≅ {a1}{a2} f1 f2 =
        (v : a1) (v′ : a2) -> v ≅ v′ -> f1 v ≅ f2 v′


-- | Other lemmas

-- Heterogeneous congruence of three arguments
≅-cong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ (x : A) → B x → Set c}
            {D : ∀ (x : A) -> (y : B x) -> C x y -> Set d} {x y z w u v}
       -> (f : (x : A) (y : B x) (z : C x y) → D x y z)
       -> x ≅ y -> z ≅ w -> u ≅ v -> f x z u ≅ f y w v
≅-cong₃ f ≅.refl ≅.refl ≅.refl = ≅.refl
