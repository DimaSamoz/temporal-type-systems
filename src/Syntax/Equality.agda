
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

x₄ : ∀{Γ A B C D} -> Γ , A now , B , C , D ⊢ A now
x₄ = var (pop (pop (pop top)))

s₁ : ∀{Γ A} -> Γ , A always ⊢ A always
s₁ = var top

s₂ : ∀{Γ A B} -> Γ , A always , B ⊢ A always
s₂ = var (pop top)

s₃ : ∀{Γ A B C} -> Γ , A always , B , C ⊢ A always
s₃ = var (pop (pop top))

s₄ : ∀{Γ A B C D} -> Γ , A always , B , C , D ⊢ A always
s₄ = var (pop (pop (pop top)))


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

    -- Congruence in events
    cong-event : ∀{A}{E₁ E₂ : Γ ⊨ A now}
                            ->                 Γ ⊨ E₁ ≡ E₂ ∷ A now
                                      -------------------------------------
                            ->         Γ ⊢ event E₁ ≡ event E₂ ∷ Event A now

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

    -- β-reduction for event binding in computational terms
    β-selectₚ : ∀{A B C}    ->      (C₁ : Γ ˢ , A now , Event B now ⊨ C now)
                                    (C₂ : Γ ˢ , Event A now , B now ⊨ C now)
                                       (C₃ : Γ ˢ , A now , B now ⊨ C now)
                                      (M₁ : Γ ⊢ A now)   (M₂ : Γ ⊢ B now)
                                 ---------------------------------------------
                            ->    Γ ⊨ select event (pure M₁) ↦ C₁
                                          || event (pure M₂) ↦ C₂
                                          ||both↦ C₃
                                    ≡ [ M₁ /′] ([ 𝓌 M₂ /′]
                                        (weakening′ (keep (keep (Γˢ⊆Γ Γ))) C₃)) ∷ C now

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

test : ∀{A} -> ∙ ⊢ (Signal A => A) now
test = lam (letSig x₁ In sample s₁)

tes : ∀{A} -> ∙ ⊢ (Signal A => Signal (Signal A)) now
tes = lam (letSig x₁ In sig (stable (sig s₁)))

te : ∀{A} -> ∙ ⊢ (A => Event A) now
te = lam (event (pure x₁))

t2 : ∀{A} -> ∙ ⊢ (Signal A) now -> ∙ ⊢ A always
t2 M = stable (letSig M In sample s₁)

t : ∀{A} -> ∙ ⊢ (Event (Event A) => Event A) now
t = lam (event (letEvt x₁ In (letEvt x₁ In pure x₁)))

t3 : ∀{A B} -> ∙ ⊢ (Event A => Signal (A => Event B) => Event B) now
t3 = lam (lam
        (letSig x₁ In (event
        (letEvt x₃ In
        (letEvt (sample s₂ $ x₁) In pure x₁)))))

-- t4 : ∀{A B C} -> ∙ ⊢ (Event A => Event B => Signal (A => Event C) => Signal (B => Event C) => Event C) now
-- t4 = lam (lam (lam (lam (
--         letSig x₂ In (
--         letSig x₂ In (event (
--             select (var (pop (pop (pop (pop (pop top)))))) ↦ letEvt sample s₄ $ x₁ In pure x₁
--                 || (var (pop (pop (pop (pop top))))) ↦ letEvt (sample s₃ $ x₁) In pure x₁
--                 ||both↦ {!   !})))))))

t5 : ∀{A B} -> ∙ , Signal A now , Event (A => B) now ⊨ B now
t5 = letSig (var (pop top)) InC (letEvt (var (pop top)) In pure (x₁ $ sample s₂))

t6 : ∀{A B} -> ∙ , Event (Signal A) now , Signal B now ⊢ Event (Signal (A & B)) now
t6 = event (letSig x₁ InC (letEvt x₃ In (pure (letSig x₁ In (sig (stable [ sample s₁ ,, sample s₂ ]))))))
-- t6 = event (letSig x₁ InC (letEvt x₃ In (letSig x₁ InC (pure [ sample s₁ ,, sample s₃ ]))))

too : ∀{A B} -> ∙ ⊢ Signal (A => B) => (Event A => Event B) now
too = lam (lam (letSig x₂ In event (letEvt x₂ In pure (sample s₂ $ x₁))))
