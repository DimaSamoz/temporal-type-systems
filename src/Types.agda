
{- Type system of the language. -}
module Types where

-- Abstract grammar of types for the language.
data Type : Set where
    -- Unit type
    Unit   : Type
    -- Product type
    _&_    : Type -> Type -> Type
    -- Sum type
    _+_    : Type -> Type -> Type
    -- Function type
    _=>_   : Type -> Type -> Type
    -- Event type
    Event  : Type -> Type
    -- Signal type
    Signal : Type -> Type
