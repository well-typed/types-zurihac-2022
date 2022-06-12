{-# OPTIONS_GHC -Wall #-}
module Ver2 where

-- Version 2: Variables and let

import Control.Monad (guard)
import Data.Maybe (fromJust)
import Prelude hiding (lookup)

data Expr =
    Z
  | S        Expr
  | F
  | T
  | Equal    Expr Expr
  | If       Expr Expr Expr
  | Var      Int
  | Let      Expr Expr
  deriving Show

data Ty =
    TNat
  | TBool
  deriving (Show, Eq)

dB ::
  (Int -> Int -> Expr) ->
  Expr -> Expr
dB var = go 0
  where
    go i (Var j)             =  var i j
    go i (Let e1 e2)         =  Let (go i e1) (go (i + 1) e2)
    go _ Z                   =  Z
    go i (S e)               =  S (go i e)
    go _ F                   =  F
    go _ T                   =  T
    go i (Equal e1 e2)       =  Equal (go i e1) (go i e2)
    go i (If e1 e2 e3)       =  If (go i e1) (go i e2) (go i e3)

subst :: Expr -> Expr -> Expr
subst e1 e2 = dB var e2
  where
    var i j =
      case compare i j of
        EQ -> shift i e1
        LT -> Var (j - 1)
        GT -> Var j

shift :: Int -> Expr -> Expr
shift n e2 =
  dB var e2
  where
    var i j
      | j < i     = Var j
      | otherwise = Var (j + n)

data Env =
    Empty
  | Extend  Env Ty

lookup :: Env -> Int -> Maybe Ty
lookup Empty          _ = Nothing
lookup (Extend _ t)   0 = pure t
lookup (Extend env _) i = lookup env (i - 1)

check :: Env -> Expr -> Ty -> Maybe ()
check env e t = do
  t' <- infer env e
  guard (t == t')

infer :: Env -> Expr -> Maybe Ty
infer _   Z                   = pure TNat
infer env (S e)               = do
  check env e TNat
  pure TNat
infer _   F                   = pure TBool
infer _   T                   = pure TBool
infer env (Equal e1 e2)       = do
  check env e1 TNat
  check env e2 TNat
  pure TBool
infer env (If e1 e2 e3)       = do
  check env e1 TBool
  a <- infer env e2
  check env e3 a
  pure a
infer env (Var i)             =
  lookup env i
infer env (Let e1 e2)         = do
  t1 <- infer env e1
  infer (Extend env t1) e2

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
eval (Var _)                 =  Nothing
eval (Let e1 e2)             =  eval (subst e1 e2)

evalCompletely :: Expr -> NF
evalCompletely e =
  case fromJust (eval e) of
    WNat WZ     -> VNat VZ
    WNat (WS e') ->
      VNat (VS
        (case evalCompletely e' of
           VNat v -> v
           _ -> error "type error"
        ))
    WBool False -> VBool False
    WBool True -> VBool True

-- Exercise 2-1:
--
-- Express "let x = 1 in let y = S x in x == y" as a term
-- of type Expr.

-- Exercise 2-2:
--
-- Write a pretty-printer for expressions that tries to produce
-- a more readable name-based presentation from the internal
-- de Bruijn representation.
--
-- A possible type for this is
--
--   pretty :: [String] -> [String] -> Expr -> String
--
-- where the first [String] is a supply of names we can use
-- for variables, and the second [String] is an environment
-- containing the names associated with the bound variables
-- currently in scope.

-- Exercise 2-3:
--
-- Even better output can be obtained if we remember the names
-- of binders, i.e., if we still store the original name in
-- the constructor Let, and adapt the pretty-printer accordingly.
--
-- Note, however, that we cannot always use the original name,
-- because we might then shadow variables we still need to
-- refer to. So we have to carry around names already used
-- to check for this.
