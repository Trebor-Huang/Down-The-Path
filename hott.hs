{-# LANGUAGE DeriveFunctor #-}
module Main where

type Name = String

data Tree a = Nil | Leaf a | Branch [Tree a]
  deriving (Eq, Show, Functor)
data Index = Here | There Int Index deriving (Eq, Show)
(!) :: Tree a -> Index -> a
Leaf a ! Here = a
Branch ts ! There k i = (ts !! k) ! i
_ ! _ = error "Tree index out of bounds."

newtype Scope = Unbound { bound :: Term } deriving (Show, Eq)
type Type = Term
type Telescope = Tree Term  -- ^ Essentially substitutions.
type IdTelescope = Tree (Term, Term, Term) -- ^ Left, Right, Paths
type Context = Tree Term  -- ^ Context lists run backwards.
data Term
  = FV Name
  | BV Index
  | Lam { ty :: Type , body :: Scope }
  | App { fun :: Term , arg :: Term }
  | Pair { projl :: Term , tyf :: Scope , projr :: Term }
  | Fst { arg :: Term }
  | Snd { arg :: Term }
  | Id { tele :: IdTelescope , tyf :: Scope , ty :: Type ,
    lhs :: Term , rhs :: Term }
  | Ap { tele :: IdTelescope , tyf :: Scope , arg :: Term }
  | TrR { tele :: IdTelescope , tyf :: Scope , ty :: Type ,
    arg :: Term }
  | TrL { tele :: IdTelescope , tyf :: Scope , ty :: Type ,
    arg :: Term }
  | FillR { tele :: IdTelescope , tyf :: Scope , ty :: Type ,
    arg :: Term }
  | FillL { tele :: IdTelescope , tyf :: Scope , ty :: Type ,
    arg :: Term }
  | ContrR { tele :: IdTelescope , tyf :: Scope , ty :: Type ,
    lhs :: Term , rhs :: Term , path :: Term }
  | ContrL { tele :: IdTelescope , tyf :: Scope , ty :: Type ,
    lhs :: Term , rhs :: Term , path :: Term }
  | TruncR { tele :: IdTelescope , tyf :: Scope , ty :: Type ,
    lhs :: Term , rhs :: Term , path :: Term }
  | TruncL { tele :: IdTelescope , tyf :: Scope , ty :: Type ,
    lhs :: Term , rhs :: Term , path :: Term }
  deriving (Show, Eq)

main = return ()
