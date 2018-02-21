
{- Terms of the language.
   Based on Pfenning and Davies' "Judgmental reconstruction of modal logic."
-}
module Syntax.Terms where

open import Syntax.Types
open import Syntax.Context

mutual
    -- Pure terms of the language, expressed as typing judgements
    infix 10 _⊢_
    data _⊢_ : Environment -> Type -> Set where
        -- Variables
        Var : ∀{Γ Δ A}          ->                  A ∈ Γ
                                                 -----------
                                ->                Δ ⁏ Γ ⊢ A

        -- Lambda abstraction
        Lam : ∀{Γ Δ A B}        ->              Δ ⁏ Γ , A ⊢ B
                                               ----------------
                                ->              Δ ⁏ Γ ⊢ A => B

        -- Application
        _$_ : ∀{Γ Δ A B}        ->       Δ ⁏ Γ ⊢ A => B   ->   Δ ⁏ Γ ⊢ A
                                        -------------------------------
                                ->                Δ ⁏ Γ ⊢ B

        -- Stable variables
        SVar : ∀{Γ Δ A}         ->                   A ∈ Δ
                                                  -----------
                                ->                 Δ ⁏ Γ ⊢ A

        -- Signal constructor
        Sig : ∀{Γ Δ A}          ->                 Δ ⁏ ∙ ⊢ A
                                               ------------------
                                ->              Δ ⁏ Γ ⊢ Signal A

        -- Signal destructor
        LetSig_In_ : ∀{Γ Δ A B} ->   Δ ⁏ Γ ⊢ Signal A   ->   Δ , A ⁏ Γ ⊢ B
                                    ----------------------------------------
                                ->                 Δ ⁏ Γ ⊢ B
        -- Event constructor
        Event : ∀{Γ Δ A}        ->                 Δ ⁏ Γ ⊨ A
                                               ------------------
                                ->              Δ ⁏ Γ ⊢ Event A

    -- Computational terms of the language
    infix 10 _⊨_
    data _⊨_ : Environment -> Type -> Set where
        -- Pure term is a computational term
        Pure : ∀{Γ Δ A}          ->                 Δ ⁏ Γ ⊢ A
                                                  -------------
                                 ->                 Δ ⁏ Γ ⊨ A
        -- Computational signal destructor
        LetSig_InC_ : ∀{Γ Δ A B} ->   Δ ⁏ Γ ⊢ Signal A   ->   Δ , A ⁏ Γ ⊨ B
                                     ----------------------------------------
                                 ->                 Δ ⁏ Γ ⊨ B
        -- Event destructor
        LetEvt_In_ : ∀{Γ Δ A B}  ->   Δ ⁏ Γ ⊢ Event A   ->   Δ ⁏ [ A ] ⊢ B
                                     ----------------------------------------
                                 ->                 Δ ⁏ Γ ⊨ B
