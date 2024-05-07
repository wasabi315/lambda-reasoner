{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}

module Main (main) where

import Control.Arrow
import Data.Function
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Ideas.Common.Library as Ideas
import Ideas.Main.Default
import Ideas.Utils.Prelude
import LambdaReasoner.Expr

buggySubst1 :: String -> Expr -> Expr -> Expr
buggySubst1 x u (Var y)
  | x == y = u
  | otherwise = Var y
buggySubst1 x u (App t v) = App (buggySubst1 x u t) (buggySubst1 x u v)
buggySubst1 x u (Abs y t) = Abs y (buggySubst1 x u t)

buggyBetaRed1 :: Rule Expr
buggyBetaRed1 = describe "β-reduction" $ buggyRule "eval.buggyRed1" f
  where
    f (App (Abs x t) u)
      | x `isBoundInside` t = Just $ buggySubst1 x u t
    f _ = Nothing

    isBoundInside _ (Var _) = False
    isBoundInside x (App t u) = isBoundInside x t || isBoundInside x u
    isBoundInside x (Abs y t) = x == y || isBoundInside x t

buggySubst2 :: String -> Expr -> Expr -> Expr
buggySubst2 x u (Var y)
  | x == y = u
  | otherwise = Var y
buggySubst2 x u (App t v) = App (buggySubst2 x u t) (buggySubst2 x u v)
buggySubst2 x u (Abs y t)
  | x == y = Abs y t
  | otherwise = Abs y (buggySubst2 x u t)

buggyBetaRed2 :: Rule Expr
buggyBetaRed2 = describe "β-reduction" $ buggyRule "eval.buggyRed2" f
  where
    f (App (Abs x t) u)
      | needAlphaConv (freeVars u) x t = Just $ buggySubst2 x u t
    f _ = Nothing

    needAlphaConv _ _ (Var _) = False
    needAlphaConv fv x (App t u) = needAlphaConv fv x t || needAlphaConv fv x u
    needAlphaConv fv x (Abs y t) = x /= y && (y `Set.member` fv || needAlphaConv fv x t)

rename :: String -> String -> Expr -> Expr
rename x y (Var z)
  | z == x = Var y
  | otherwise = Var z
rename x y (App t u) = App (rename x y t) (rename x y u)
rename x y (Abs z t)
  | z /= x = Abs z (rename x y t)
  | otherwise = Abs z t

subst :: (MonadFail m) => String -> Expr -> Expr -> m Expr
subst x u (Var y)
  | x == y = return u
  | otherwise = return $ Var y
subst x u (App t v) = App <$> subst x u t <*> subst x u v
subst x u (Abs y t)
  | x == y = return $ Abs y t
  | y `Set.notMember` freeVars u = Abs y <$> subst x u t
  | otherwise = fail "variable capture"

betaRed :: Rule Expr
betaRed = describe "β-reduction" $ makeRule "eval.beta" f
  where
    f (App (Abs x t) u) = subst x u t
    f _ = Nothing

fvarsRef :: Ref Term
fvarsRef = makeRef "fvars"

calcFreeVarsOfOperand :: Rule (Context Expr)
calcFreeVarsOfOperand =
  setMinor True
    . ruleTrans "calcfvars"
    . transLiftContext
    $ proc t -> do
      u <- transMaybe f -< t
      writeRef fvarsRef -< toTerm $ Set.mapMonotonic ShowString $ freeVars u
      returnA -< t
  where
    f (App (Abs _ _) u) = Just u
    f _ = Nothing

alphaConv :: Rule (Context Expr)
alphaConv =
  describe "α-conversion"
    . addRecognizerBool (withoutContext alphaEq)
    . ruleTrans "eval.alpha"
    . transLiftContext
    $ proc t -> do
      fvs <- readRefDefault (toTerm (Set.empty :: Set ShowString)) fvarsRef -< ()
      transMaybe f -< (fvs, t)
  where
    f (fvs, Abs x t)
      | x `Set.member` fvs' =
          let y = fresh (fvs' <> freeVars t) x
           in Just $ Abs y (rename x y t)
      | otherwise = Nothing
      where
        fvs' = Set.mapMonotonic fromShowString $ fromJust $ fromTerm fvs
    f _ = Nothing

alphaConvs :: Strategy (Context Expr)
alphaConvs = calcFreeVarsOfOperand .*. try (somewhere alphaConv)

alphaThenBeta :: LabeledStrategy (Context Expr)
alphaThenBeta =
  label "alpha-then-beta" $
    (alphaConvs .*. liftToContext (betaRed .|. buggyBetaRed1)) .|. liftToContext buggyBetaRed2

ruleEta :: Rule Expr
ruleEta = describe "η-reduction" $ makeRule "eval.eta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.notMember` freeVars t = Just t
    f _ = Nothing

buggyEta :: Rule Expr
buggyEta = describe "buggy η-reduction" $ buggyRule "eval.buggyEta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.member` freeVars t = Just t
    f _ = Nothing

fullBeta :: LabeledStrategy (Context Expr)
fullBeta =
  somewhere alphaThenBeta .|. somewhere (liftToContext (ruleEta .|. buggyEta))
    & repeatS
    & label "eval.fullbeta"
    & describe "Full β-reduction"

leftmostBeta :: LabeledStrategy (Context Expr)
leftmostBeta =
  alphaThenBeta
    & somewhere
    & repeatS
    & label "eval.leftmostbeta"
    & describe "Leftmost β-reduction"

--------------------------------------------------------------------------------

fullBetaEx :: Exercise Expr
fullBetaEx =
  emptyExercise
    { exerciseId = describe "Evaluate a lambda term" $ newId "eval.fullBeta",
      status = Experimental,
      strategy = fullBeta,
      navigation = termNavigator,
      equivalence = withoutContext alphaBetaEtaEq,
      similarity = withoutContext (==),
      prettyPrinter = show,
      parser = maybe (Left "") Right . readM,
      ready = predicate (not . hasBetaRedex),
      examples = examplesFor Easy [_S `App` _K `App` _K, _S `App` _K `App` _S, Abs "x" (Abs "y" (Var "x")) `App` Var "y", Abs "x" (Abs "x" $ Var "x") `App` Var "y"]
    }

_I :: Expr
_I = read "\\x . x"

_K :: Expr
_K = read "\\x . \\y . x"

_S :: Expr
_S = read "\\f . \\g . \\x . f x (g x)"

omega :: Expr
omega = read "(\\x . x x) (\\x . x x)"

------------------------------------------------------------------------------

dr :: DomainReasoner
dr =
  describe
    "Domain reasoner for tutorial"
    (newDomainReasoner "eval")
      { exercises = [Some fullBetaEx],
        services = myServices
      }

myServices :: [Service]
myServices = metaServiceList dr ++ serviceList

main :: IO ()
main = defaultMain dr
