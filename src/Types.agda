
{- Type system of the language. -}
module Types where

-- Abstract grammar of types for the language.
data Type : Set where
    -- Unit type
    Unit      : Type
    -- Product type
    _&_       : Type -> Type -> Type
    -- Function type
    _=>_      : Type -> Type -> Type
    -- Next step type
    Next      : Type -> Type
    -- Event type
    Event     : Type -> Type
    -- Behaviour type
    Behaviour : Type -> Type
