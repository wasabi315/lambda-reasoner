{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}

module LambdaReasoner.Expr
  ( Expr (..),
    Subst (..),
    freeVars,
    isBetaNormal,
    rename,
    ExprPath (..),
    subst,
    nonCaptureAvoidingSubst,
    (-->),
    needRenamePaths,
    alphaEq,
    rhoEq,
    etaRed,
    alphaEtaEq,
    alphaBetaEtaEq,
    normalize,
    fresh,
  )
where

import Control.Applicative
import Data.Char
import Data.Foldable
import Data.Function
import Data.List (elemIndex)
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
-- Single substitution

data Subst = Subst String Expr

instance Show Subst where
  showsPrec p (Subst x t) =
    showParen (p > 10) $
      showString x . showString " -> " . showsPrec 11 t

instance Read Subst where
  readPrec = lift do
    ReadP.skipSpaces
    Subst <$> varP <*> (sym "->" *> exprP)

subSymbol :: Symbol
subSymbol = newSymbol "sub"

instance IsTerm Subst where
  toTerm (Subst x t) = TCon subSymbol [toTerm x, toTerm t]
  termDecoder = tCon2 subSymbol Subst termDecoder termDecoder

instance Reference Subst

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
rename x x' (Var y)
  | x == y = Var x'
  | otherwise = Var y
rename x x' (App t u) = App (rename x x' t) (rename x x' u)
rename x x' (Abs y t)
  | x == y = Abs y t
  | otherwise = Abs y (rename x x' t)

data ExprPath
  = PHere
  | PAppL ExprPath
  | PAppR ExprPath
  | PAbs ExprPath
  deriving (Eq, Ord, Show)

instance Semigroup ExprPath where
  PHere <> p = p
  PAppL p <> q = PAppL (p <> q)
  PAppR p <> q = PAppR (p <> q)
  PAbs p <> q = PAbs (p <> q)

instance Monoid ExprPath where
  mempty = PHere

subst :: String -> Expr -> Expr -> (Expr, Set ExprPath)
subst = go id
  where
    go _ x t (Var y)
      | x == y = (t, mempty)
      | otherwise = (Var y, mempty)
    go path x t (App u v) =
      let (u', varCaps1) = go (path . PAppL) x t u
          (v', varCaps2) = go (path . PAppR) x t v
       in (App u' v', varCaps1 <> varCaps2)
    go path x t (Abs y u)
      | x == y = (Abs y u, mempty)
      | y `Set.notMember` freeVars t =
          let (u', varCaps) = go (path . PAbs) x t u
           in (Abs y u', varCaps)
      | otherwise =
          let (u', varCaps) = go (path . PAbs) x t u
           in (Abs y u', Set.insert (path PHere) varCaps)

-- | @(x '-->' u) t@ substitutes @x@ with @u@ in @t@.
-- Returns 'Nothing' if the substitution captures any free variables in @u@.
(-->) :: String -> Expr -> Expr -> Maybe Expr
(x --> u) t = case subst x u t of
  (t', Set.null -> True) -> Just t'
  _ -> Nothing

-- | @'nonCaptureAvoidingSubst' sub t@ substitutes variables in @t@ according to @sub@
-- __/without avoiding variable capture/__.
-- The second component of the result indicates whether variable capture __/does not occur/__.
nonCaptureAvoidingSubst :: String -> Expr -> Expr -> (Expr, Bool)
nonCaptureAvoidingSubst x u t = Set.null <$> subst x u t

-- | Compute the set of abstractions that need renaming in order to perform β-reduction on β-redices in a given term with α-conversion.
-- >>> needRenamePaths $ read "(\\x. \\y. x) x"
-- fromList []
-- >>> needRenamePaths $ read "(\\x. \\y. x) y"
-- fromList [PAppL (PAbs PHere)]
-- >>> needRenamePaths $ read "(\\x. \\y. \\z. x) (y z)"
-- fromList [PAppL (PAbs PHere),PAppL (PAbs (PAbs PHere))]
needRenamePaths :: Expr -> Set ExprPath
needRenamePaths = go id
  where
    go path (App t u)
      | Abs x t' <- t =
          let varCaps' =
                subst x u t'
                  & snd
                  & Set.map (path . PAppL . PAbs)
           in varCaps' <> varCaps
      | otherwise = varCaps
      where
        varCaps = go (path . PAppL) t <> go (path . PAppR) u
    go path (Abs _ t) = go (path . PAbs) t
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

infix 4 `rhoEq`

-- | An equivalence relation that is stricter than α-equivalence.
-- | I don't know how to call this relation, so I named it "ρ-equivalence" (ρ for "rename").
-- | Two terms are ρ-equivalent if they are α-equivalent and the set of abstractions that need renaming for capture avoidance is the same.
-- | This is useful for checking if α-conversion is "helpful" for β-reduction.
rhoEq :: Expr -> Expr -> Bool
rhoEq x y = x `alphaEq` y && needRenamePaths x == needRenamePaths y

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
