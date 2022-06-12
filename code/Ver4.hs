{-# OPTIONS_GHC -Wall #-}
module Ver4 where

-- Version 4: Recursion and case analysis

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
  | Lam      Ty Expr
  | App      Expr Expr
  | Letrec   Ty Expr Expr
  | CaseNat  Expr Expr Expr
  deriving Show

data Ty =
    TNat
  | TBool
  | TFun    Ty Ty
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
    go i (App e1 e2)         =  App (go i e1) (go i e2)
    go i (Lam t e)           =  Lam t (go (i + 1) e)
    go i (Letrec t e1 e2)    =  Letrec t (go (i + 1) e1) (go (i + 1) e2)
    go i (CaseNat e1 e2 e3)  =  CaseNat (go i e1) (go i e2) (go (i + 1) e3)

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
infer env (App e1 e2)         = do
  TFun t1 t2 <- infer env e1
  check env e2 t1
  pure t2
infer env (Lam t1 e)          = do
  t2 <- infer (Extend env t1) e
  pure (TFun t1 t2)
infer env (Letrec t1 e1 e2)   = do
  check (Extend env t1) e1 t1
  t2 <- infer (Extend env t1) e2
  pure t2
infer env (CaseNat e1 e2 e3)  = do
  check env e1 TNat
  t <- infer env e2
  check (Extend env TNat) e3 t
  pure t

data NF =
    VNat  VNat
  | VBool Bool
  | VLam  Ty Expr
  deriving Show

data VNat = VZ | VS VNat
  deriving Show

data WHNF =
    WNat  WNat
  | WBool Bool
  | WLam  Ty Expr
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
eval (App e1 e2)             =  do
  WLam _ e1' <- eval e1
  eval (subst e2 e1')
eval (Lam t e)               =  pure (WLam t e)
eval (Letrec t e1 e2)        =  do
  eval (subst (Letrec t e1 e1) e2)
eval (CaseNat e1 e2 e3)      =  do
  WNat v1 <- eval e1
  case v1 of
    WZ -> eval e2
    WS e1' -> eval (subst e1' e3)

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
    WLam t e' -> VLam t e'

-- Examples

fix_ :: Ty -> Expr -> Expr
fix_ t e =
  Letrec t e (Var 0)

dbl_ :: Expr
dbl_ =
  fix_ (TNat `TFun` TNat)
    (Lam TNat
      (CaseNat (Var 0)
        Z
        (S (S (Var 2 `App` Var 0)))
      )
    )

-- Exercise 4-1:
--
-- Often, recursion is not introduced via letrec but via
-- a fixed point construct.
--
-- Above, we define fix in terms of letrec. Can you provide
-- type and evaluation rules for fix directly? Can you then
-- define letrec in terms of fix instead?

