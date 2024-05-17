{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}

module LambdaReasoner.Views
  ( AbsChain (..),
    absChainView,
    AppChain (..),
    appChainView,
    BetaChain (..),
    betaChainView,
  )
where

import Control.Arrow
import Data.Foldable
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Ideas.Common.Library
import Ideas.Utils.Decoding
import LambdaReasoner.Expr
import Text.Read

--------------------------------------------------------------------------------

-- | Chain of abstractions, i.e. λ x₁. λ x₂. ... λ xₙ. t, where n ≥ 1.
data AbsChain = AbsChain (NonEmpty String) Expr

instance Show AbsChain where
  showsPrec p t = showsPrec p (build absChainView t)

instance Read AbsChain where
  readPrec = do
    t <- readPrec
    case match absChainView t of
      Just b -> return b
      Nothing -> fail "not an abstraction chain"

absChainSymbol :: Symbol
absChainSymbol = newSymbol "absChain"

instance IsTerm AbsChain where
  toTerm (AbsChain xs t) =
    TCon absChainSymbol [toTerm (NonEmpty.toList xs), toTerm t]

  termDecoder =
    tCon2
      absChainSymbol
      AbsChain
      do
        xs <- termDecoder
        case xs of
          [] -> errorStr "empty abstraction chain"
          x : xs' -> return $ x :| xs'
      termDecoder

instance Reference AbsChain

absChainView :: View Expr AbsChain
absChainView = makeView m b
  where
    m (Abs x t@(Abs _ _)) = do
      AbsChain xs u <- m t
      pure $ AbsChain (NonEmpty.cons x xs) u
    m (Abs x t) = pure $ AbsChain (x :| []) t
    m _ = Nothing
    b (AbsChain xs t) = foldr Abs t xs

--------------------------------------------------------------------------------

-- | Chain of applications, i.e. t u₁ u₂ ... uₙ, where n ≥ 1.
data AppChain = AppChain Expr (NonEmpty Expr)

instance Show AppChain where
  showsPrec p t = showsPrec p (build appChainView t)

instance Read AppChain where
  readPrec = do
    t <- readPrec
    case match appChainView t of
      Just b -> return b
      Nothing -> fail "not an application chain"

appChainSymbol :: Symbol
appChainSymbol = newSymbol "appChain"

instance IsTerm AppChain where
  toTerm (AppChain t us) =
    TCon appChainSymbol [toTerm t, toTerm (NonEmpty.toList us)]

  termDecoder =
    tCon2
      appChainSymbol
      AppChain
      termDecoder
      do
        us <- termDecoder
        case us of
          [] -> errorStr "empty application chain"
          u : us' -> return $ u :| us'

instance Reference AppChain

appChainView :: View Expr AppChain
appChainView = makeView m b
  where
    m (App t@(App _ _) u) = do
      AppChain t' us <- m t
      pure $ AppChain t' (us <> NonEmpty.singleton u)
    m (App t u) = pure $ AppChain t (u :| [])
    m _ = Nothing
    b (AppChain t us) = foldl' App t us

--------------------------------------------------------------------------------

-- | Chain of beta redices, i.e. (λ x₁. λ x₂. ... λ xₙ. t) u₁ u₂ ... uₙ where n ≥ 1.
data BetaChain = BetaChain (NonEmpty (String, Expr)) Expr

instance Show BetaChain where
  showsPrec p t = showsPrec p (build betaChainView t)

instance Read BetaChain where
  readPrec = do
    t <- readPrec
    case match betaChainView t of
      Just b -> return b
      Nothing -> fail "not a beta redices"

betaRedicesSymbol :: Symbol
betaRedicesSymbol = newSymbol "betaRedices"

instance IsTerm BetaChain where
  toTerm (BetaChain ss t) =
    TCon betaRedicesSymbol [toTerm (NonEmpty.toList ss), toTerm t]

  termDecoder =
    tCon2
      betaRedicesSymbol
      BetaChain
      do
        ss <- termDecoder
        case ss of
          [] -> errorStr "empty beta redices"
          s : ss' -> return $ s :| ss'
      termDecoder

instance Reference BetaChain

betaChainView :: View Expr BetaChain
betaChainView = matcherView m b
  where
    m = proc t -> do
      AppChain u us <- matcher appChainView -< t
      AbsChain xs v <- matcher absChainView -< u
      if length xs < length us
        then zeroArrow -< ()
        else
          let (NonEmpty.fromList -> xs1, xs2) = NonEmpty.splitAt (length us) xs
              v' = foldr Abs v xs2
           in returnA -< BetaChain (NonEmpty.zip xs1 us) v'

    b (BetaChain ss t) = do
      foldl' (\u (_, v) -> App u v) (foldr (Abs . fst) t ss) ss
