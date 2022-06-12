{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
module Ver3 where

-- Version 3: Functions (Simply Typed Lambda Calculus)

import Control.Monad (guard)
import Data.Maybe (fromJust)
import Data.Kind
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

-- Exercise 3-1:
--
-- We can make the language much more interesting by adding an
-- induction principle for natural numbers, akin to the following
-- Haskell function:
--

recNat :: VNat -> r -> (r -> r) -> r
recNat VZ     z _ = z
recNat (VS n) z s = s (recNat n z s)

--
-- Try to add this to the language as a built-in construct,
-- provide type rules, evaluation rules and all changes to the
-- implementation.

-- Exercise 3-2:
--
-- Use the induction principle to define a function that doubles
-- a natural number.

-- Exercise 3-3:
--
-- (This requires some familiarity with type-level programming
-- techniques.)
--
-- We can use GADTs to express well-typed expressions by
-- more or less transcribing the type rules of System F, roughly
-- as follows:

data WTExpr :: Env -> Ty -> Type where
  Z'     :: WTExpr gamma TNat
  S'     :: WTExpr gamma TNat -> WTExpr gamma TNat
  F'     :: WTExpr gamma TBool
  T'     :: WTExpr gamma TBool
  Equal' :: WTExpr gamma TNat -> WTExpr gamma TNat -> WTExpr gamma TBool
  If'    :: WTExpr gamma TBool -> WTExpr gamma t -> WTExpr gamma t -> WTExpr gamma t
  Var'   :: Elem t gamma -> WTExpr gamma t
  Let'   :: WTExpr gamma t -> WTExpr (Extend gamma t) t' -> WTExpr gamma t'
  Lam'   :: STy t1 -> WTExpr (Extend gamma t1) t2 -> WTExpr gamma (TFun t1 t2)
  App'   :: WTExpr gamma (TFun t1 t2) -> WTExpr gamma t1 -> WTExpr gamma t2

data STy :: Ty -> Type where
  STNat  :: STy TNat
  STBool :: STy TBool
  STFun  :: STy t1 -> STy t2 -> STy (TFun t1 t2)

data Elem :: Ty -> Env -> Type where
  First  :: Elem t (Extend gamma t)
  Next   :: Elem t gamma -> Elem t (Extend gamma t')

-- We can make the type-checker much more trustworthy by letting
-- it produce a value of type WTExpr as an output!

