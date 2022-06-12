{-# OPTIONS_GHC -Wall #-}
module Ver5 where

-- Version 5: Polymorphism (System F)

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
  | TLam     Expr
  | TApp     Expr Ty
  | Nil      Ty
  | Cons     Expr Expr
  | CaseList Expr Expr Expr
  deriving Show

data Ty =
    TNat
  | TBool
  | TFun    Ty Ty
  | TForall Ty
  | TVar    Int
  | TList   Ty
  deriving (Show, Eq)

dB ::
  (Int -> Int -> Ty) ->
  (Int -> Int -> Expr) ->
  Expr -> Expr
dB tvar var = go 0
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
    go i (Lam t e)           =  Lam (goT i t) (go (i + 1) e)
    go i (Letrec t e1 e2)    =  Letrec (goT i t) (go (i + 1) e1) (go (i + 1) e2)
    go i (CaseNat e1 e2 e3)  =  CaseNat (go i e1) (go i e2) (go (i + 1) e3)
    go i (TLam e)            =  TLam (go (i + 1) e)
    go i (TApp e t)          =  TApp (go i e) (goT i t)
    go i (Nil t)             =  Nil (goT i t)
    go i (Cons e1 e2)        =  Cons (go i e1) (go i e2)
    go i (CaseList e1 e2 e3) =  CaseList (go i e1) (go i e2) (go (i + 2) e3)

    goT i t                  =  dbT' tvar i t

dBT :: (Int -> Int -> Ty) -> Ty -> Ty
dBT tvar = dbT' tvar 0

dbT' :: (Int -> Int -> Ty) -> Int -> Ty -> Ty
dbT' tvar i' = go i'
  where
    go _ TNat          = TNat
    go _ TBool         = TBool
    go i (TFun t1 t2)  = TFun (go i t1) (go i t2)
    go i (TForall t)   = TForall (go (i + 1) t)
    go i (TVar j)      = tvar i j
    go i (TList t)     = TList (go i t)

subst :: Expr -> Expr -> Expr
subst e1 e2 = dB tvar var e2
  where
    tvar i j =
      case compare i j of
        EQ -> error "should not happen"
        LT -> TVar (j - 1)
        GT -> TVar j
    var i j =
      case compare i j of
        EQ -> shift i e1
        LT -> Var (j - 1)
        GT -> Var j

shift :: Int -> Expr -> Expr
shift n e2 = dB tvar var e2
  where
    tvar i j
      | j < i     = TVar j
      | otherwise = TVar (j + n)
    var i j
      | j < i     = Var j
      | otherwise = Var (j + n)

tsubst :: Ty -> Expr -> Expr
tsubst t e = dB tvar var e
  where
    tvar i j =
      case compare i j of
        EQ -> shiftT i t
        LT -> TVar (j - 1)
        GT -> TVar j
    var i j =
      case compare i j of
        EQ -> error "should not happen"
        LT -> Var (j - 1)
        GT -> Var j

tsubstT :: Ty -> Ty -> Ty
tsubstT t1 t2 = dBT tvar t2
  where
    tvar i j =
      case compare i j of
        EQ -> shiftT i t1
        LT -> TVar (j - 1)
        GT -> TVar j

shiftT :: Int -> Ty -> Ty
shiftT n t2 = dBT tvar t2
  where
    tvar i j
      | j < i     = TVar j
      | otherwise = TVar (j + n)

data Env =
    Empty
  | TExtend Env
  | Extend  Env Ty

lookupT :: Env -> Int -> Maybe ()
lookupT (TExtend _)     0 = pure ()
lookupT (TExtend env)   i = lookupT env (i - 1)
lookupT (Extend _ _)    0 = Nothing
lookupT (Extend env _)  i = lookupT env (i - 1)
lookupT Empty           _ = Nothing

lookup :: Env -> Int -> Maybe Ty
lookup Empty          _ = Nothing
lookup (TExtend _)    0 = Nothing
lookup (TExtend env)  i = lookup env (i - 1)
lookup (Extend _ t)   0 = pure t
lookup (Extend env _) i = lookup env (i - 1)

checkT :: Env -> Ty -> Maybe ()
checkT _    TNat          = pure ()
checkT _    TBool         = pure ()
checkT env  (TFun t1 t2)  = do
  checkT env t1
  checkT env t2
checkT env  (TVar i)      =
  lookupT env i
checkT env  (TForall t)   =
  checkT (TExtend env) t
checkT env  (TList t)     =
  checkT env t

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
  shiftT (i + 1) <$> lookup env i
infer env (Let e1 e2)         = do
  t1 <- infer env e1
  infer (Extend env t1) e2
infer env (App e1 e2)         = do
  TFun t1 t2 <- infer env e1
  check env e2 t1
  pure t2
infer env (Lam t1 e)          = do
  checkT env t1
  t2 <- infer (Extend env t1) e
  pure (TFun t1 (shiftT (-1) t2))
infer env (Letrec t1 e1 e2)   = do
  checkT env t1
  check (Extend env t1) e1 (shiftT 1 t1)
  t2 <- infer (Extend env t1) e2
  pure (shiftT (-1) t2)
infer env (CaseNat e1 e2 e3)  = do
  check env e1 TNat
  t <- infer env e2
  check (Extend env TNat) e3 t
  pure t
infer env (TLam e)            = do
  t <- infer (TExtend env) e
  pure (TForall t)
infer env (TApp e t')         = do
  TForall t <- infer env e
  checkT env t'
  pure (tsubstT t' t)
infer env (Nil t)             = do
  checkT env t
  pure (TList t)
infer env (Cons e1 e2)        = do
  t <- infer env e1
  check env e2 (TList t)
  pure (TList t)
infer env (CaseList e1 e2 e3) = do
  TList t <- infer env e1
  t' <- infer env e2
  check (Extend (Extend env t) (TList (shiftT 1 t))) e3 (shiftT 2 t')
  pure t'

data NF =
    VNat  VNat
  | VBool Bool
  | VLam  Ty Expr
  | VTLam Expr
  | VList [NF]
  deriving Show

data VNat = VZ | VS VNat
  deriving Show

data WHNF =
    WNat  WNat
  | WBool Bool
  | WLam  Ty Expr
  | WTLam Expr
  | WList WList
  deriving Show

data WNat = WZ | WS Expr
  deriving Show

data WList = WNil Ty | WCons Expr Expr
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
eval (TLam e)                =  pure (WTLam e)
eval (TApp e t)              =  do
  WTLam e' <- eval e
  eval (tsubst t e')
eval (Nil t)                 =  pure (WList (WNil t))
eval (Cons e1 e2)            =  pure (WList (WCons e1 e2))
eval (CaseList e1 e2 e3)     =  do
  WList v1 <- eval e1
  case v1 of
    WNil _ -> eval e2
    WCons e1' e2' -> eval (subst e1' (subst e2' e3))

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
    WTLam e' -> VTLam e'
    WList (WNil _) ->
      VList []
    WList (WCons e1 e2) ->
      VList (evalCompletely e1 :
        case evalCompletely e2 of
          VList v -> v
          _ -> error "type error"
      )

-- Pretty-printing

prettyT :: [String] -> [String] -> Ty -> String
prettyT _        _   TNat         = "Nat"
prettyT _        _   TBool        = "Bool"
prettyT supply   env (TFun t1 t2) = "(" <> prettyT supply env t1 <> " -> " <> prettyT supply env t2 <> ")"
prettyT (x : xs) env (TForall t)  = "forall " <> x <> ". " <> prettyT xs (x : env) t
prettyT _        env (TVar i)     = env !! i
prettyT supply   env (TList t)    = "[" <> prettyT supply env t <> "]"
prettyT _        _   _            = error "insufficient supply"

pretty :: [String] -> [String] -> Expr -> String
pretty _            _   Z                   = "Z"
pretty supply       env (S e)               = "(S " <> pretty supply env e <> ")"
pretty _            _   F                   = "F"
pretty _            _   T                   = "T"
pretty supply       env (Equal e1 e2)       =
  "(" <> pretty supply env e1 <> " == " <> pretty supply env e2 <> ")"
pretty supply       env (If e1 e2 e3)       =
  "if " <> pretty supply env e1 <> " then " <> pretty supply env e2 <> " else " <> pretty supply env e3
pretty _            env (Var i)             = env !! i
pretty (x : xs)     env (Let e1 e2)         =
  "let " <> x <> " = " <> pretty xs env e1 <> " in " <> pretty xs (x : env) e2
pretty (x : xs)     env (Lam t e)           =
  "\\ (" <> x <> " : " <> prettyT xs env t <> ") -> " <> pretty xs (x : env) e
pretty supply       env (App e1 e2)         =
  "(" <> pretty supply env e1 <> " " <> pretty supply env e2 <> ")"
pretty (x : xs)     env (Letrec t e1 e2)    =
  "letrec " <> x <> " : " <> prettyT xs env t <> " = " <> pretty xs (x : env) e1
  <> " in " <> pretty xs (x : env) e2
pretty (x : xs)     env (CaseNat e1 e2 e3)  =
  "case " <> pretty xs env e1
  <> " of Z -> " <> pretty xs env e2 <> "; S " <> x <> " -> " <> pretty xs (x : env) e3
pretty (x : xs)     env (TLam e)            = "\\ @" <> x <> " -> " <> pretty xs (x : env) e
pretty supply       env (TApp e t)          =
  "(" <> pretty supply env e <> " @" <> prettyT supply env t <> ")"
pretty supply       env (Nil t)             = "(Nil @" <> prettyT supply env t <> ")"
pretty supply       env (Cons e1 e2)        =
  "(Cons " <> pretty supply env e1 <> " " <> pretty supply env e2 <> ")"
pretty (x : y : xs) env (CaseList e1 e2 e3) =
  "case " <> pretty xs env e1
  <> " of Nil -> " <> pretty xs env e2
  <> "; Cons " <> x <> " " <> y <> " -> " <> pretty xs (y : x : env) e3
pretty _        _   _                       = error "insufficient supply"

defaultSupply :: [String]
defaultSupply = map (:[]) ['a' .. 'z']

pretty' :: Expr -> String
pretty' = pretty defaultSupply []

-- Examples

fix_ :: Ty -> Expr -> Expr
fix_ t e =
  Letrec t e (Var 0)

map_ :: Expr
map_ =
  TLam $
  TLam $
  Lam (TFun (TVar 1) (TVar 0)) $ -- a -> b
  fix_ (TList (TVar 2) `TFun` TList (TVar 1)) $
  Lam (TList (TVar 3)) $ -- [a]
  CaseList
    (Var 0)
    (Nil (TVar 3))
    -- 0 : [a]
    -- 1 : a
    -- 2 : [a]
    -- 3 : [a] -> [b]
    -- 4 : (a -> b)
    -- 5 : @b
    -- 6 : @a
    (Cons (Var 4 `App` Var 1) (Var 3 `App` Var 0))

dbl_ :: Expr
dbl_ =
  Letrec (TNat `TFun` TNat)
    (Lam TNat
      (CaseNat (Var 0)
        Z
        (S (S (Var 2 `App` Var 0)))
      )
    )
    (Var 0)

list_ :: Expr
list_ =
  Cons Z (Cons (S Z) (Cons (S (S Z)) (Nil TNat)))

mapApp_ :: Expr
mapApp_ =
  map_ `TApp` TNat `TApp` TNat `App` dbl_ `App` list_

-- Most of these exercises are rather advanced.

-- Exercise 5-1:
--
-- A lot of types / constructs can actually be encoded in System F.
-- Read up on Church encodings, and try out encoding some datatype,
-- such as lists, rather than using our "built-in" version.

-- Exercise 5-2:
--
-- Define a parser for expressions to make it more convenient to
-- write larger programs.

-- Exercise 5-3:
--
-- Add another specific datatype of your choice.

-- Exercise 5-4:
--
-- Add a *general* way to define datatypes akin to Haskell,
-- deriving a case analysis from the datatype definition automatically.

-- Exercise 5-5:
--
-- Add patterns to make case analyis more convenient.

-- Exercise 5-6:
--
-- Extend the system to System F-omega by adding function kinds.
-- I.e., allow the list type constructor to be used partially applied.
-- Allow abstraction and applications over type variables of higher
-- kinds.
