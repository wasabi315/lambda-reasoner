{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module LambdaReasoner.Expr where

import Control.Applicative
import Data.Char
import Data.Function
import Data.List (elemIndex, find)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Ideas.Common.Library as Ideas
import Text.ParserCombinators.ReadP (ReadP)
import qualified Text.ParserCombinators.ReadP as ReadP

--------------------------------------------------------------------------------

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
varP = lexeme $ (:) <$> ReadP.satisfy isAlpha <*> ReadP.many (ReadP.satisfy isAlphaNum)

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
  readsPrec _ = ReadP.readP_to_S (ReadP.skipSpaces *> exprP <* ReadP.eof)

--------------------------------------------------------------------------------
-- Pretty-printer

instance Show Expr where
  showsPrec _ (Var x) = showString x
  showsPrec p (App t u) =
    showParen (p > 10) $ showsPrec 10 t . showString " " . showsPrec 11 u
  showsPrec p (Abs x t) =
    showParen (p > 0) $ showString "\\" . showString x . showString " . " . shows t

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

--------------------------------------------------------------------------------

freeVars :: Expr -> Set String
freeVars (Var x) = Set.singleton x
freeVars (App t u) = freeVars t <> freeVars u
freeVars (Abs x t) = Set.delete x (freeVars t)

hasBetaRedex :: Expr -> Bool
hasBetaRedex (App (Abs _ _) _) = True
hasBetaRedex (App t u) = hasBetaRedex t || hasBetaRedex u
hasBetaRedex (Abs _ t) = hasBetaRedex t
hasBetaRedex _ = False

--------------------------------------------------------------------------------
-- Alpha equivalence

infix 4 `alphaEq`

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

etaRed :: Expr -> Expr
etaRed (Var x) = Var x
etaRed (App t u) = App (etaRed t) (etaRed u)
etaRed (Abs x t) = case etaRed t of
  u `App` Var x'
    | x == x' && x `Set.notMember` freeVars u -> u
  t' -> Abs x t'

infix 4 `alphaEtaEq`

alphaEtaEq :: Expr -> Expr -> Bool
alphaEtaEq = alphaEq `on` etaRed

--------------------------------------------------------------------------------
-- Normalization

data Val
  = VVar String
  | VApp Val (Maybe Val)
  | VAbs String (Int -> Maybe Val -> Maybe Val)

eval :: Int -> [(String, Maybe Val)] -> Expr -> Maybe Val
eval 0 _ _ = Nothing
eval _ env (Var x) = fromMaybe (pure $ VVar x) $ lookup x env
eval gas env (App t u) =
  eval gas env t >>= \case
    VAbs _ f -> f (gas - 1) (eval gas env u)
    t' -> pure $ VApp t' (eval gas env u)
eval _ env (Abs x t) = pure $ VAbs x \gas u -> eval gas ((x, u) : env) t

fresh :: Set String -> String -> String
fresh xs x =
  x : [x ++ show n | n <- [0 :: Int ..]]
    & find (`Set.notMember` xs)
    & fromJust

_GAS :: Int
_GAS = 1024

quote :: Set String -> Val -> Maybe Expr
quote _ (VVar x) = pure $ Var x
quote ns (VApp t u) = App <$> quote ns t <*> (u >>= quote ns)
quote ns (VAbs (fresh ns -> x) t) =
  t _GAS (pure $ VVar x) >>= fmap (Abs x) . quote (Set.insert x ns)

normalize :: Expr -> Maybe Expr
normalize t = eval _GAS [] t >>= quote (freeVars t)

alphaBetaEtaEq :: Expr -> Expr -> Bool
alphaBetaEtaEq t u = case (normalize t, normalize u) of
  (Just t', Just u') -> t' `alphaEtaEq` u'
  _ -> False
