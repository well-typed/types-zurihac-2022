{-# OPTIONS_GHC -Wall #-}
module Ver1 where

-- Version 1: Simple language

import Control.Monad (guard)

data Expr =
    Z
  | S        Expr
  | F
  | T
  | Equal    Expr Expr
  | If       Expr Expr Expr
  deriving Show

data Ty =
    TNat
  | TBool
  deriving (Show, Eq)

check :: Expr -> Ty -> Maybe ()
check e t = do
  t' <- infer e
  guard (t == t')

infer :: Expr -> Maybe Ty
infer Z              =  pure TNat
infer (S e)          =  do
  check e TNat
  pure TNat
infer F              =  pure TBool
infer T              =  pure TBool
infer (Equal e1 e2)  =  do
  check e1 TNat
  check e2 TNat
  pure TBool
infer (If e1 e2 e3)  =  do
  check e1 TBool
  t <- infer e2
  check e3 t
  pure t

data NF =
    VNat VNat
  | VBool Bool
  deriving Show

data VNat = VZ | VS VNat
  deriving Show

data WHNF =
    WNat WNat
  | WBool Bool
  deriving Show

data WNat = WZ | WS Expr
  deriving Show

eval :: Expr -> Maybe WHNF
eval Z                       =  pure (WNat WZ)
eval (S e)                   =  pure (WNat (WS e))
eval F                       =  pure (WBool False)
eval T                       =  pure (WBool True)
eval (Equal e1 e2)           =  do
  WNat v1 <- eval e1
  WNat v2 <- eval e2
  case (v1, v2) of
    (WZ, WZ) -> pure (WBool True)
    (WS e1', WS e2') -> eval (Equal e1' e2')
    _ -> pure (WBool False)
eval (If e1 e2 e3)           =  do
  WBool b <- eval e1
  if b then eval e2 else eval e3

-- Exercise 1-1:
--
-- Add integer literals to the language and addition on integers
-- to the language. Provide type rules and evaluation rules.

-- Exercise 1-2:
--
-- Generalise the type of equality so that it does not just work
-- on natural numbers, but also on Booleans (and integers).

-- Exercise 1-3:
--
-- Define a function
--
--   evalCompletely :: Expr -> NF
--
-- that evaluates an expression to normal form by repeatedly
-- calling eval, and crashes if there is a run-time type error.
--
-- Why is it somewhat problematic to give this function the type
--
--   evalCompletely :: Expr -> Maybe NF
--
-- instead?

-- Exercise 1-4:
--
-- How do the evaluation rules have to be adapted if we want to
-- switch to eager / call-by-value evaluation? I.e., if evaluation
-- is supposed to go all the way to normal form in one go, and
-- functions such as equality are supposed to force both arguments
-- to normal form before proceeding?
