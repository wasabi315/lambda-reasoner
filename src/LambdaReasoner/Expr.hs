{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}

module LambdaReasoner.Expr
  ( Expr (..),
    BetaRedex (..),
    betaRedexView,
    freeVars,
    isBetaNormal,
    rename,
    nonCaptureAvoidingSubst,
    willCaptureOccur,
    (-->),
    alphaEq,
    etaRed,
    alphaEtaEq,
    alphaBetaEtaEq,
    normalize,
    fresh,
  )
where

import Control.Applicative
import Data.Char
import Data.Function
import Data.List (elemIndex, find)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Ideas.Common.Library as Ideas hiding (from, to)
import Text.ParserCombinators.ReadP (ReadP)
import qualified Text.ParserCombinators.ReadP as ReadP
import Text.Read

--------------------------------------------------------------------------------

-- | Untyped lambda terms.
data Expr
  = Var String
  | App Expr Expr
  | Abs String Expr
  deriving (Eq)

--------------------------------------------------------------------------------
-- Parser

lexeme :: ReadP a -> ReadP a
lexeme p = p <* ReadP.skipSpaces

sym :: String -> ReadP String
sym = lexeme . ReadP.string

varP :: ReadP String
varP =
  lexeme $
    (:) <$> ReadP.satisfy isAlpha <*> ReadP.many (ReadP.satisfy isAlphaNum)

atomP :: ReadP Expr
atomP =
  asum
    [ Var <$> varP,
      ReadP.between (sym "(") (sym ")") exprP
    ]

exprP :: ReadP Expr
exprP =
  asum
    [ Abs <$> (sym "\\" *> varP) <*> (sym "." *> exprP),
      ReadP.chainl1 atomP (pure App)
    ]

instance Read Expr where
  readPrec = lift (ReadP.skipSpaces *> exprP)

--------------------------------------------------------------------------------
-- Pretty-printer

instance Show Expr where
  showsPrec _ (Var x) = showString x
  showsPrec p (App t u) =
    showParen (p > 10) $ showsPrec 10 t . showString " " . showsPrec 11 u
  showsPrec p (Abs x t) =
    showParen (p > 0) $
      showString "\\" . showString x . showString " . " . shows t

--------------------------------------------------------------------------------
-- IsTerm instance

varSymbol, appSymbol, absSymbol :: Symbol
varSymbol = newSymbol "var"
appSymbol = newSymbol "app"
absSymbol = newSymbol "abs"

instance IsTerm Expr where
  toTerm (Var x) = TCon varSymbol [TVar x]
  toTerm (App t u) = TCon appSymbol [toTerm t, toTerm u]
  toTerm (Abs x t) = TCon absSymbol [TVar x, toTerm t]

  termDecoder =
    asum
      [ tCon1 varSymbol Var tVar,
        tCon2 appSymbol App termDecoder termDecoder,
        tCon2 absSymbol Abs tVar termDecoder
      ]

instance Reference Expr

--------------------------------------------------------------------------------
-- Beta redex

data BetaRedex = BetaRedex String Expr Expr

instance Show BetaRedex where
  showsPrec p t = showsPrec p (build betaRedexView t)

instance Read BetaRedex where
  readPrec = do
    t <- readPrec
    case match betaRedexView t of
      Just b -> return b
      Nothing -> fail "not a beta redex"

betaRedexSymbol :: Symbol
betaRedexSymbol = newSymbol "betaRedex"

instance IsTerm BetaRedex where
  toTerm (BetaRedex x t u) = TCon betaRedexSymbol [TVar x, toTerm t, toTerm u]

  termDecoder = tCon3 betaRedexSymbol BetaRedex tVar termDecoder termDecoder

instance Reference BetaRedex

betaRedexView :: View Expr BetaRedex
betaRedexView = makeView m b
  where
    m (App (Abs x t) u) = Just $ BetaRedex x t u
    m _ = Nothing
    b (BetaRedex x t u) = App (Abs x t) u

--------------------------------------------------------------------------------
-- Operations and predicates on lambda terms

-- | Compute the set of free variables in a term.
freeVars :: Expr -> Set String
freeVars (Var x) = Set.singleton x
freeVars (App t u) = freeVars t <> freeVars u
freeVars (Abs x t) = Set.delete x (freeVars t)

-- | Check if a term is in β-normal form.
isBetaNormal :: Expr -> Bool
isBetaNormal (App (Abs _ _) _) = False
isBetaNormal (App t u) = isBetaNormal t && isBetaNormal u
isBetaNormal (Abs _ t) = isBetaNormal t
isBetaNormal (Var _) = True

-- | @'rename' from to t@ renames all occurrences of @from@ to @to@ in @t@.
rename :: String -> String -> Expr -> Expr
rename from to (Var x)
  | x == from = Var to
  | otherwise = Var x
rename from to (App t u) = App (rename from to t) (rename from to u)
rename from to (Abs x t)
  | x /= from = Abs x (rename from to t)
  | otherwise = Abs x t

-- | @'nonCaptureAvoidingSubst' x u t@ substitutes @x@ with @u@ in @t@,
-- __/without avoiding variable capture/__. Please check that
-- @'willCaptureOccur' x u t@ is 'False' before using this function.
nonCaptureAvoidingSubst :: String -> Expr -> Expr -> Expr
nonCaptureAvoidingSubst x u (Var y)
  | x == y = u
  | otherwise = Var y
nonCaptureAvoidingSubst x u (App t v) =
  App (nonCaptureAvoidingSubst x u t) (nonCaptureAvoidingSubst x u v)
nonCaptureAvoidingSubst x u (Abs y t)
  | x == y = Abs y t
  | otherwise = Abs y (nonCaptureAvoidingSubst x u t)

-- | Check if substituting @x@ with @u@ in @t@ would capture any free variables in @u@.
willCaptureOccur :: String -> Expr -> Expr -> Bool
willCaptureOccur x t = aux
  where
    fvs = freeVars t

    aux (Var _) = False
    aux (App u v) = aux u || aux v
    aux (Abs y u) = x /= y && (y `Set.member` fvs || aux u)

-- | @(x '-->' u) t@ substitutes @x@ with @u@ in @t@.
-- 'fail's if the substitution would capture any free variables in @u@.
(-->) :: (MonadFail m) => String -> Expr -> Expr -> m Expr
(x --> u) t
  | willCaptureOccur x u t = fail "variable capture"
  | otherwise = pure $ nonCaptureAvoidingSubst x u t

--------------------------------------------------------------------------------

infix 4 `alphaEq`

-- | Check if two terms are α-equivalent.
alphaEq :: Expr -> Expr -> Bool
alphaEq = go [] []
  where
    go e1 e2 (Var x) (Var y) =
      case (x `elemIndex` e1, y `elemIndex` e2) of
        (Just i, Just j) -> i == j
        (Nothing, Nothing) -> x == y
        _ -> False
    go e1 e2 (App t u) (App t' u') =
      go e1 e2 t t' && go e1 e2 u u'
    go e1 e2 (Abs x t) (Abs y t') =
      go (x : e1) (y : e2) t t'
    go _ _ _ _ = False

--------------------------------------------------------------------------------
-- Eta reduction

-- | η-reduce a term.
etaRed :: Expr -> Expr
etaRed (Var x) = Var x
etaRed (App t u) = App (etaRed t) (etaRed u)
etaRed (Abs x t) = case etaRed t of
  App u (Var x')
    | x == x' && x `Set.notMember` freeVars u -> u
  t' -> Abs x t'

infix 4 `alphaEtaEq`

-- | Check if two terms are αη-equivalent.
alphaEtaEq :: Expr -> Expr -> Bool
alphaEtaEq = alphaEq `on` etaRed

--------------------------------------------------------------------------------
-- Normalization with gas limit

data Val
  = VVar String
  | VApp Val Val
  | --                  vvvvvvvvv maybe non-terminating, hence Maybe
    VAbs String (Int -> Maybe Val -> Maybe Val)

eval :: Int -> [(String, Maybe Val)] -> Expr -> Maybe Val
eval 0 _ _ = Nothing
eval _ env (Var x) = fromMaybe (pure $ VVar x) $ lookup x env
eval gas env (App t u) = do
  t' <- eval gas env t
  case t' of
    VAbs _ f -> f (gas - 1) (eval gas env u)
    _ -> VApp t' <$> eval gas env u
eval _ env (Abs x t) = pure $ VAbs x \gas u -> eval gas ((x, u) : env) t

fresh :: Set String -> String -> String
fresh xs x =
  x : [x ++ show n | n <- [0 :: Int ..]]
    & find (`Set.notMember` xs)
    & fromJust

quote :: Int -> Set String -> Val -> Maybe Expr
quote _ _ (VVar x) = pure $ Var x
quote gas ns (VApp t u) = App <$> quote gas ns t <*> quote gas ns u
quote gas ns (VAbs (fresh ns -> x) t) = do
  t1 <- t gas (pure $ VVar x)
  t2 <- quote gas (Set.insert x ns) t1
  return $ Abs x t2

-- | Normalize a term, up to a given gas limit.
normalize :: Int -> Expr -> Maybe Expr
normalize gas t = eval gas [] t >>= quote gas (freeVars t)

-- | Check if two terms are αβη-equivalent, up to a given gas limit.
alphaBetaEtaEq :: Int -> Expr -> Expr -> Bool
alphaBetaEtaEq gas t u = case (normalize gas t, normalize gas u) of
  (Just t', Just u') -> t' `alphaEtaEq` u'
  _ -> False
