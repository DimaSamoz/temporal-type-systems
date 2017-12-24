
{- Category of temporal types.
    Objects: types indexed by time (natural numbers)
    Arrows: functions indexed by time
-}
module Category where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
import Data.Unit using (⊤)
import Data.Empty using (⊥)
open import Data.Product
open import Data.Sum renaming (_⊎_ to _∨_)


infixr 30 _⇴_
infixl 55 _∘_


-- || Objects and arrows

-- Time-indexed types.
τ : Set₁
τ = ℕ -> Set

-- Arrows
_⇴_ : τ -> τ -> Set
a ⇴ b = ∀(n : ℕ) -> a n -> b n

-- || Identity and composition

-- Identity arrow
id : {A : τ} -> A ⇴ A
id n = λ a -> a

-- Composition of arrows
_∘_ : {A B C : τ} -> B ⇴ C -> A ⇴ B -> A ⇴ C
(g ∘ f) n = λ a -> g n (f n a)

-- || Category laws

-- Left identity
id-left : ∀{A B : τ} {f : A ⇴ B} -> id ∘ f ≡ f
id-left = refl

-- Right identity
id-right : ∀{A B : τ} {f : A ⇴ B} -> f ∘ id ≡ f
id-right = refl

-- Associativity
∘-assoc : {A B C D : τ} {f : A ⇴ B} {g : B ⇴ C} {h : C ⇴ D}
       -> (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc = refl

-- || Cartesian, cocartesian, exponential structure

-- Final object
⊤ : τ
⊤ n = Data.Unit.⊤

-- Products
_⊗_ : τ -> τ -> τ
(A ⊗ B) n = A n × B n

-- Initial object
⊥ : τ
⊥ n = Data.Empty.⊥

-- Products
_⊕_ : τ -> τ -> τ
(A ⊕ B) n = A n ∨ B n

-- Exponentials
_⇒_ : τ -> τ -> τ
(A ⇒ B) n = A n -> B n
