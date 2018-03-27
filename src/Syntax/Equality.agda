
-- Equality of terms
module Syntax.Equality where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms
open import Syntax.Kit
open import Syntax.Traversal

open Kit 𝒯erm

-- Shorthands for de Bruijn indices
x₁ : ∀{Γ A} -> Γ , A now ⊢ A now
x₁ = var top

x₂ : ∀{Γ A B} -> Γ , A now , B ⊢ A now
x₂ = var (pop top)

x₃ : ∀{Γ A B C} -> Γ , A now , B , C ⊢ A now
x₃ = var (pop (pop top))

s₁ : ∀{Γ A} -> Γ , A always ⊢ A always
s₁ = svar top

s₂ : ∀{Γ A B} -> Γ , A always , B ⊢ A always
s₂ = svar (pop top)

s₃ : ∀{Γ A B C} -> Γ , A always , B , C ⊢ A always
s₃ = svar (pop (pop top))


-- β-η equality of terms
data Eq (Γ : Context) : (A : Judgement) -> Γ ⊢ A -> (Γ ⊢ A) -> Set
syntax Eq Γ A M N = Γ ⊢ M ≡ N ∷ A
data Eq Γ where
    -- | Equivalence relation
    -- Reflexivity
    refl  : ∀{A}            ->            (M : Γ ⊢ A)
                                        ---------------
                            ->           Γ ⊢ M ≡ M ∷ A

    -- Symmetry
    sym   : ∀{A}{M₁ M₂ : Γ ⊢ A}
                            ->   Γ ⊢ M₁ ≡ M₂ ∷ A
                                -----------------
                            ->   Γ ⊢ M₂ ≡ M₁ ∷ A

    -- Transitivity
    trans : ∀{A}{M₁ M₂ M₃ : Γ ⊢ A}
                            ->   Γ ⊢ M₁ ≡ M₂ ∷ A   ->   Γ ⊢ M₂ ≡ M₃ ∷ A
                                -----------------------------------------
                            ->               Γ ⊢ M₁ ≡ M₃ ∷ A

    -- | β-equality
    -- β-reduction for function application
    β-lam : ∀{A B}          ->  (N : Γ , A now ⊢ B now)   (M : Γ ⊢ A now)
                               -------------------------------------------
                            ->      Γ ⊢ lam N $ M ≡ [ M /] N ∷ B now


    -- β-reduction for first projection

    β-fst : ∀{A B}          ->        (M : Γ ⊢ A now)   (N : Γ ⊢ B now)
                                     -----------------------------------
                            ->          Γ ⊢ fst [ M ,, N ] ≡ M ∷ A now

    -- β-reduction for second projection
    β-snd : ∀{A B}          ->        (M : Γ ⊢ A now)   (N : Γ ⊢ B now)
                                     -----------------------------------
                            ->          Γ ⊢ snd [ M ,, N ] ≡ N ∷ B now

    -- | η-equality
    -- η-expansion for functions
    η-lam : ∀{A B}          ->              (M : Γ ⊢ A => B now)
                                   --------------------------------------
                            ->      Γ ⊢ M ≡ lam (𝓌 M $ x₁) ∷ A => B now

    -- η-expansion for pairs
    η-pair : ∀{A B}         ->               (M : Γ ⊢ A & B now)
                                   ----------------------------------------
                            ->      Γ ⊢ M ≡ [ fst M ,, snd M ] ∷ A & B now

    -- η-expansion for unit
    η-unit :                                 (M : Γ ⊢ Unit now)
                                          -------------------------
                            ->             Γ ⊢ M ≡ unit ∷ Unit now

    -- | Congruence rules
    -- Congruence in pairs
    cong-pair : ∀{A B}{M₁ M₂ : Γ ⊢ A now}{N₁ N₂ : Γ ⊢ B now}
                            ->   Γ ⊢ M₁ ≡ M₂ ∷ A now  ->   Γ ⊢ N₁ ≡ N₂ ∷ B now
                                ------------------------------------------------
                            ->    Γ ⊢ [ M₁ ,, N₁ ] ≡ [ M₂ ,, N₂ ] ∷ A & B now

    -- Congruence in first projection
    cong-fst : ∀{A B}{M₁ M₂ : Γ ⊢ A & B now}
                            ->             Γ ⊢ M₁ ≡ M₂ ∷ A & B now
                                        ------------------------------
                            ->           Γ ⊢ fst M₁ ≡ fst M₂ ∷ A now

    -- Congruence in second projection
    cong-snd : ∀{A B}{M₁ M₂ : Γ ⊢ A & B now}
                            ->             Γ ⊢ M₁ ≡ M₂ ∷ A & B now
                                        ------------------------------
                            ->           Γ ⊢ snd M₁ ≡ snd M₂ ∷ B now

    -- Congruence in lambda body
    cong-lam : ∀{A B}{M₁ M₂ : Γ , A now ⊢ B now}
                            ->            Γ , A now ⊢ M₁ ≡ M₂ ∷ B now
                                       ----------------------------------
                            ->          Γ ⊢ lam M₁ ≡ lam M₂ ∷ A => B now

    -- Congruence in application
    cong-app : ∀{A B}{N₁ N₂ : Γ ⊢ A => B now}{M₁ M₂ : Γ ⊢ A now}
                            ->   Γ ⊢ N₁ ≡ N₂ ∷ A => B now  ->  Γ ⊢ M₁ ≡ M₂ ∷ A now
                                ---------------------------------------------------
                            ->            Γ ⊢ N₁ $ M₁ ≡ N₂ $ M₂ ∷ B now
