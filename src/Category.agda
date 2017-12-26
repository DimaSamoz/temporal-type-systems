
{- Category of temporal types.
    Objects: types indexed by time (natural numbers)
    Arrows: functions indexed by time
-}
module Category where

open import Data.Nat public
open import Relation.Binary.PropositionalEquality public
open import Data.Unit using () renaming (⊤ to top) public
open import Data.Empty using () renaming (⊥ to bot) public
open import Data.Product public
open import Data.Sum renaming (_⊎_ to _∨_)




-- || Objects and arrows

-- Time-indexed types.
τ : Set₁
τ = ℕ -> Set

-- Arrows
_⇴_ : τ -> τ -> Set
a ⇴ b = ∀(n : ℕ) -> a n -> b n
infixr 30 _⇴_

-- || Identity and composition

-- Identity arrow
id : {A : τ} -> A ⇴ A
id n = λ a -> a

-- Composition of arrows
_∘_ : {A B C : τ} -> B ⇴ C -> A ⇴ B -> A ⇴ C
(g ∘ f) n = λ a -> g n (f n a)
infixl 55 _∘_

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
⊤ n = top

-- Products
_⊗_ : τ -> τ -> τ
(A ⊗ B) n = A n × B n
infixl 70 _⊗_

-- Initial object
⊥ : τ
⊥ n = bot

-- Products
_⊕_ : τ -> τ -> τ
(A ⊕ B) n = A n ∨ B n
infixl 65 _⊕_

-- Exponentials
_⇒_ : τ -> τ -> τ
(A ⇒ B) n = A n -> B n
infixr 50 _⇒_
