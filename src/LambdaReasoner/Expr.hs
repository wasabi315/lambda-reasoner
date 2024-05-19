{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}

module LambdaReasoner.Expr
  ( Expr (..),
    Sub (..),
    BetaRedex (..),
    betaRedexView,
    freeVars,
    isBetaNormal,
    Rename,
    rename,
    Subst,
    subst',
    subst,
    nonCaptureAvoidingSubst,
    (-->),
    isSubstSafe,
    Ctx (..),
    alphaEq,
    etaRed,
    alphaEtaEq,
    alphaBetaEtaEq,
    normalize,
    fresh,
    needRenameCtxs,
  )
where

import Control.Applicative
import Data.Char
import Data.Foldable
import Data.Function
import Data.List (elemIndex)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Ideas.Common.Library as Ideas
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
    (:) <$> ReadP.satisfy isAlpha <*> ReadP.munch (isAlphaNum <||> (== '\''))

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

data Sub = Sub String Expr

instance Show Sub where
  showsPrec p (Sub x t) =
    showParen (p > 10) $
      showString x . showString " -> " . showsPrec 11 t

instance Read Sub where
  readPrec = lift do
    ReadP.skipSpaces
    Sub <$> varP <*> (sym "->" *> exprP)

subSymbol :: Symbol
subSymbol = newSymbol "sub"

instance IsTerm Sub where
  toTerm (Sub x t) = TCon subSymbol [toTerm x, toTerm t]
  termDecoder = tCon2 subSymbol Sub termDecoder termDecoder

instance Reference Sub

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

type Rename = Map String String

-- | @'rename' r t@ renames all variables in @t@ according to @r@.
rename :: Rename -> Expr -> Expr
rename r (Var x)
  | Just x' <- Map.lookup x r = Var x'
  | otherwise = Var x
rename r (App t u) = App (rename r t) (rename r u)
rename r (Abs x t) = Abs x (rename (Map.delete x r) t)

data Ctx
  = CtxAppL
  | CtxAppR
  | CtxAbs
  deriving (Eq, Ord, Show)

type Subst = Map String Expr

-- Simultanous substitution
subst' :: Subst -> Expr -> (Expr, Set [Ctx])
subst' = go []
  where
    go _ sub (Var x)
      | Just u <- Map.lookup x sub = (u, mempty)
      | otherwise = (Var x, mempty)
    go ctx sub (App u v) =
      let (u', varCaps1) = go (CtxAppL : ctx) sub u
          (v', varCaps2) = go (CtxAppR : ctx) sub v
       in (App u' v', varCaps1 <> varCaps2)
    go ctx sub (Abs x u) =
      let sub' = Map.restrictKeys (Map.delete x sub) (freeVars u)
          fvs = foldMap freeVars sub'
          (u', varCaps1) = go (CtxAbs : ctx) sub' u
          varCaps2 = if x `Set.member` fvs then Set.singleton ctx else mempty
       in (Abs x u', varCaps1 <> varCaps2)

-- | @'subst' sub t@ substitutes variables in @t@ according to @sub@.
-- Returns 'Nothing' if variable capture occurs.
subst :: Subst -> Expr -> Maybe Expr
subst sub t = case subst' sub t of
  (t', Set.null -> True) -> Just t'
  _ -> Nothing

-- | @(x '-->' u) t@ substitutes @x@ with @u@ in @t@.
-- Returns 'Nothing' if the substitution captures any free variables in @u@.
(-->) :: String -> Expr -> Expr -> Maybe Expr
(x --> u) t = case subst' (Map.singleton x u) t of
  (t', Set.null -> True) -> Just t'
  _ -> Nothing

-- | @'nonCaptureAvoidingSubst' sub t@ substitutes variables in @t@ according to @sub@
-- __/without avoiding variable capture/__.
-- The second component of the result indicates whether variable capture __/does not occur/__.
nonCaptureAvoidingSubst :: Subst -> Expr -> (Expr, Bool)
nonCaptureAvoidingSubst sub t = Set.null <$> subst' sub t

-- | @'isSubstSafe' x u t@ checks if the substitution @(x --> u)@ is safe in @t@.
isSubstSafe :: String -> Expr -> Expr -> Bool
isSubstSafe x u t = isJust $ (x --> u) t

needRenameCtxs :: Expr -> Set [Ctx]
needRenameCtxs = go []
  where
    go ctx (App t u)
      | Abs x t' <- t =
          let varCaps' =
                subst' (Map.singleton x u) t'
                  & snd
                  & Set.map (\varCap -> varCap ++ [CtxAbs, CtxAppL] ++ ctx)
           in varCaps' <> varCaps
      | otherwise = varCaps
      where
        varCaps = go (CtxAppL : ctx) t <> go (CtxAppR : ctx) u
    go ctx (Abs _ t) = go (CtxAbs : ctx) t
    go _ (Var _) = mempty

--------------------------------------------------------------------------------

-- | Generate a fresh variable name that is not in the given set.
-- If @x@ is not in the set, it is returned as is.
fresh :: Set String -> String -> String
fresh xs x =
  x : [x ++ show n | n <- [0 :: Int ..]]
    & find (`Set.notMember` xs)
    & fromJust

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
  | VAbs String (Int -> Maybe Val -> Maybe Val)

eval :: Int -> [(String, Maybe Val)] -> Expr -> Maybe Val
eval 0 _ _ = Nothing
eval _ env (Var x) = fromMaybe (pure $ VVar x) $ lookup x env
eval gas env (App t u) = do
  t' <- eval gas env t
  case t' of
    VAbs _ f -> f (gas - 1) (eval gas env u)
    _ -> VApp t' <$> eval gas env u
eval _ env (Abs x t) = pure $ VAbs x \gas u -> eval gas ((x, u) : env) t

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
