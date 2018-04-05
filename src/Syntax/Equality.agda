
-- Equality of terms
module Syntax.Equality where

open import Syntax.Types
open import Syntax.Context
open import Syntax.Terms
open import Syntax.Substitution.Kits
open import Syntax.Substitution.Instances
open import Syntax.Substitution.Lemmas

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
data Eq (Γ : Context) : (A : Judgement) -> Γ ⊢ A -> Γ ⊢ A -> Set
data Eq′ (Γ : Context) : (A : Judgement) -> Γ ⊨ A -> Γ ⊨ A -> Set
syntax Eq Γ A M N = Γ ⊢ M ≡ N ∷ A
syntax Eq′ Γ A M N = Γ ⊨ M ≡ N ∷ A

data Eq Γ where
    -- | Equivalence relation
    -- Reflexivity
    refl  : ∀{A}            ->               (M : Γ ⊢ A)
                                           ---------------
                            ->              Γ ⊢ M ≡ M ∷ A

    -- Symmetry
    sym   : ∀{A}{M₁ M₂ : Γ ⊢ A}
                            ->              Γ ⊢ M₁ ≡ M₂ ∷ A
                                           -----------------
                            ->              Γ ⊢ M₂ ≡ M₁ ∷ A

    -- Transitivity
    trans : ∀{A}{M₁ M₂ M₃ : Γ ⊢ A}
                            ->   Γ ⊢ M₁ ≡ M₂ ∷ A   ->   Γ ⊢ M₂ ≡ M₃ ∷ A
                                -----------------------------------------
                            ->               Γ ⊢ M₁ ≡ M₃ ∷ A

    -- | β-equality
    -- β-reduction for function application
    β-lam : ∀{A B}          ->  (N : Γ , A now ⊢ B now)   (M : Γ ⊢ A now)
                               -------------------------------------------
                            ->      Γ ⊢ (lam N) $ M ≡ [ M /] N ∷ B now

    -- β-reduction for first projection

    β-fst : ∀{A B}          ->        (M : Γ ⊢ A now)   (N : Γ ⊢ B now)
                                     -----------------------------------
                            ->          Γ ⊢ fst [ M ,, N ] ≡ M ∷ A now

    -- β-reduction for second projection
    β-snd : ∀{A B}          ->        (M : Γ ⊢ A now)   (N : Γ ⊢ B now)
                                     -----------------------------------
                            ->          Γ ⊢ snd [ M ,, N ] ≡ N ∷ B now

    -- β-reduction for case split on first injection
    β-inl : ∀{A B C}        ->                    (M : Γ ⊢ A now)
                                 (N₁ : Γ , A now ⊢ C now) (N₂ : Γ , B now ⊢ C now)
                                ---------------------------------------------------
                            ->       Γ ⊢ case (inl M) inl↦ N₁
                                                    ||inr↦ N₂ ≡ [ M /] N₁ ∷ C now

    -- β-reduction for case split on first injection
    β-inr : ∀{A B C}        ->                    (M : Γ ⊢ B now)
                                 (N₁ : Γ , A now ⊢ C now) (N₂ : Γ , B now ⊢ C now)
                                ---------------------------------------------------
                            ->       Γ ⊢ case (inr M) inl↦ N₁
                                                    ||inr↦ N₂ ≡ [ M /] N₂ ∷ C now

    -- β-reduction for signal binding
    β-sig : ∀{A B}          ->  (N : Γ , A always ⊢ B now)   (M : Γ ⊢ A always)
                               --------------------------------------------------
                            ->     Γ ⊢ letSig (sig M) In N ≡ [ M /] N ∷ B now

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

    -- η-expansion for sums
    η-sum : ∀{A B}          ->                (M : Γ ⊢ A + B now)
                                    ------------------------------------------
                            ->        Γ ⊢ M ≡ case M inl↦ inl x₁
                                                   ||inr↦ inr x₁ ∷ A + B now

    -- η-expansion for signals
    η-sig : ∀{A}            ->                (M : Γ ⊢ Signal A now)
                                    -------------------------------------------
                            ->       Γ ⊢ M ≡ letSig M In (sig s₁) ∷ Signal A now

    -- η-expansion for events in computational terms
    η-evt : ∀{A}           ->                  (M : Γ ⊢ Event A now)
                                  ----------------------------------------------------
                            ->     Γ ⊢ M ≡ event (letEvt M In pure x₁) ∷ Event A now

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

    -- Congruence in case split
    cong-case : ∀{A B C}{M₁ M₂ : Γ ⊢ A + B now}
                            ->               Γ ⊢ M₁ ≡ M₂ ∷ A + B now
                            ->   (N₁ : Γ , A now ⊢ C now) (N₂ : Γ , B now ⊢ C now)
                                ---------------------------------------------------
                            ->          Γ ⊢ case M₁ inl↦ N₁ ||inr↦ N₂
                                          ≡ case M₂ inl↦ N₁ ||inr↦ N₂ ∷ C now

    -- Congruence in first injection
    cong-inl : ∀{A B}{M₁ M₂ : Γ ⊢ A now}
                            ->              Γ ⊢ M₁ ≡ M₂ ∷ A now
                                      ------------------------------------
                            ->         Γ ⊢ inl M₁ ≡ inl M₂ ∷ A + B now

    -- Congruence in second injection
    cong-inr : ∀{A B}{M₁ M₂ : Γ ⊢ B now}
                            ->              Γ ⊢ M₁ ≡ M₂ ∷ B now
                                      ------------------------------------
                            ->         Γ ⊢ inr M₁ ≡ inr M₂ ∷ A + B now

    -- Congruence in signal constructor
    cong-sig : ∀{A}{M₁ M₂ : Γ ⊢ A always}
                            ->              Γ ⊢ M₁ ≡ M₂ ∷ A always
                                      ------------------------------------
                            ->         Γ ⊢ sig M₁ ≡ sig M₂ ∷ Signal A now

    -- Congruence in signal binding
    cong-letSig : ∀{A B}{S₁ S₂ : Γ ⊢ Signal A now}
                            ->          Γ ⊢ S₁ ≡ S₂ ∷ Signal A now
                            ->          (N : Γ , A always ⊢ B now)
                                ---------------------------------------------
                            ->   Γ ⊢ letSig S₁ In N ≡ letSig S₂ In N ∷ B now

    -- Congruence in sampling
    cong-sample : ∀{A}{M₁ M₂ : Γ ⊢ A always}
                            ->              Γ ⊢ M₁ ≡ M₂ ∷ A always
                                      -------------------------------------
                            ->         Γ ⊢ sample M₁ ≡ sample M₂ ∷ A now

    -- Congruence in stabilisation
    cong-stable : ∀{A}{M₁ M₂ : Γ ˢ ⊢ A now}
                            ->                 Γ ˢ ⊢ M₁ ≡ M₂ ∷ A now
                                      -------------------------------------
                            ->         Γ ⊢ stable M₁ ≡ stable M₂ ∷ A always

data Eq′ (Γ : Context) where
    -- | Equivalence relation
    -- Reflexivity
    refl  : ∀{A}            ->                (M : Γ ⊨ A)
                                            ---------------
                            ->               Γ ⊨ M ≡ M ∷ A

    -- Symmetry
    sym   : ∀{A}{M₁ M₂ : Γ ⊨ A}
                            ->              Γ ⊨ M₁ ≡ M₂ ∷ A
                                           -----------------
                            ->              Γ ⊨ M₂ ≡ M₁ ∷ A

    -- Transitivity
    trans : ∀{A}{M₁ M₂ M₃ : Γ ⊨ A}
                            ->   Γ ⊨ M₁ ≡ M₂ ∷ A   ->   Γ ⊨ M₂ ≡ M₃ ∷ A
                                -----------------------------------------
                            ->               Γ ⊨ M₁ ≡ M₃ ∷ A

    -- | β-equality
    -- β-reduction for signal binding in computational terms
    β-sig′ : ∀{A B}         ->  (C : Γ , A always ⊨ B now)   (M : Γ ⊢ A always)
                               --------------------------------------------------
                            ->     Γ ⊨ letSig (sig M) InC C ≡ [ M /′] C ∷ B now

    -- β-reduction for event binding in computational terms
    β-evt′ : ∀{A B}         ->     (C : Γ ˢ , A now ⊨ B now)   (D : Γ ⊨ A now)
                                 ---------------------------------------------
                            ->    Γ ⊨ letEvt (event D) In C ≡ ⟨ D /⟩ C ∷ B now

    -- | η-equality
    -- η-expansion for signals in computational terms
    η-sig′ : ∀{A}           ->                  (M : Γ ⊢ Signal A now)
                               --------------------------------------------------------
                            ->  Γ ⊨ pure M ≡ letSig M InC (pure (sig s₁)) ∷ Signal A now

    -- | Congruence rules
    -- Congruence in pure computational term
    cong-pure′ : ∀{A}{M₁ M₂ : Γ ⊢ A}
                            ->                Γ ⊢ M₁ ≡ M₂ ∷ A
                                         ---------------------------
                            ->            Γ ⊨ pure M₁ ≡ pure M₂ ∷ A

    -- Congruence in signal binding
    cong-letSig′ : ∀{A B}{S₁ S₂ : Γ ⊢ Signal A now}
                            ->            Γ ⊢ S₁ ≡ S₂ ∷ Signal A now
                            ->            (N : Γ , A always ⊨ B now)
                                -----------------------------------------------
                            ->   Γ ⊨ letSig S₁ InC N ≡ letSig S₂ InC N ∷ B now

    -- Congruence in event binding
    cong-letEvt′ : ∀{A B}{E₁ E₂ : Γ ⊢ Event A now}
                            ->            Γ ⊢ E₁ ≡ E₂ ∷ Event A now
                            ->            (D : Γ ˢ , A now ⊨ B now)
                                -----------------------------------------------
                            ->   Γ ⊨ letEvt E₁ In D ≡ letEvt E₂ In D ∷ B now
