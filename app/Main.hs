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
import Text.Read

--------------------------------------------------------------------------------

ruleBeta :: Rule Expr
ruleBeta = makeRule "eval.beta" f
  where
    f (App (Abs x t) u)
      | not (willCaptureOccur x u t) = Just $ nonCaptureAvoidingSubst x u t
    f _ = Nothing

fvarsRef :: Ref Term
fvarsRef = makeRef "fvars"

writeFVars :: Trans (Set String) ()
writeFVars =
  (toTerm . Set.mapMonotonic ShowString) ^>> writeRef fvarsRef >>^ const ()

readFVars :: Trans x (Set String)
readFVars =
  readRefMaybe fvarsRef
    >>^ maybe Set.empty (Set.mapMonotonic fromShowString . fromJust . fromTerm)

-- Administrative rule
ruleFVars :: Rule (Context Expr)
ruleFVars = setMinor True . ruleTrans "eval.fvars" $ transLiftContext g
  where
    f (App (Abs _ _) u) = Just u
    f _ = Nothing

    g = proc t -> do
      u <- transMaybe f -< t
      writeFVars -< freeVars u
      returnA -< t

ruleAlpha :: Rule (Context Expr)
ruleAlpha =
  addRecognizerBool (withoutContext alphaEq)
    . ruleTrans "eval.alpha"
    $ transLiftContext g
  where
    f (fvs, t@(Abs x u))
      | x `Set.member` fvs =
          let y = fresh (fvs <> freeVars t) x
           in Just $ Abs y (rename x y u)
    f _ = Nothing

    g = proc t -> do
      fvs <- readFVars -< ()
      transMaybe f -< (fvs, t)

-- First apply α-conversion in order to avoid variable capture, then β-reduction.
alphaThenBeta :: LabeledStrategy (Context Expr)
alphaThenBeta =
  label "alpha-then-beta" $
    ruleFVars .*. try (somewhere ruleAlpha) .*. liftToContext ruleBeta

ruleEta :: Rule Expr
ruleEta = makeRule "eval.eta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.notMember` freeVars t = Just t
    f _ = Nothing

evalStrategy :: LabeledStrategy (Context Expr)
evalStrategy =
  somewhere (alphaThenBeta .|. liftToContext ruleEta)
    & repeatS
    & label "eval"

--------------------------------------------------------------------------------
-- Buggy rules

buggySubst1 :: String -> Expr -> Expr -> Expr
buggySubst1 x u (Var y)
  | x == y = u
  | otherwise = Var y
buggySubst1 x u (App t v) = App (buggySubst1 x u t) (buggySubst1 x u v)
buggySubst1 x u (Abs y t) = Abs y (buggySubst1 x u t)

buggyBeta1 :: Rule Expr
buggyBeta1 = siblingOf ruleBeta $ buggyRule "eval.buggyBeta1" f
  where
    f (App (Abs x t) u)
      | x `isBoundInside` t = Just $ buggySubst1 x u t
    f _ = Nothing

    isBoundInside _ (Var _) = False
    isBoundInside x (App t u) = isBoundInside x t || isBoundInside x u
    isBoundInside x (Abs y t) = x == y || isBoundInside x t

buggyBeta2 :: Rule Expr
buggyBeta2 = siblingOf ruleBeta $ buggyRule "eval.buggyBeta2" f
  where
    f (App (Abs x t) u)
      | willCaptureOccur x u t = Just $ nonCaptureAvoidingSubst x u t
    f _ = Nothing

buggyAlpha :: Rule Expr
buggyAlpha = siblingOf ruleAlpha $ buggyRule "eval.buggyAlpha" f
  where
    f t@(Abs x u) = [Abs y (rename x y u) | y <- Set.toList (freeVars t)]
    f _ = []

buggyEta :: Rule Expr
buggyEta = siblingOf ruleEta $ buggyRule "eval.buggyEta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.member` freeVars t = Just t
    f _ = Nothing

buggyRules :: [Rule Expr]
buggyRules = [buggyBeta1, buggyBeta2, buggyAlpha, buggyEta]

--------------------------------------------------------------------------------

fullBetaEx :: Exercise Expr
fullBetaEx =
  emptyExercise
    { exerciseId = describe "Evaluate a lambda term" $ newId "eval.fullBeta",
      status = Experimental,
      strategy = evalStrategy,
      extraRules = map liftToContext buggyRules,
      navigation = termNavigator,
      equivalence = withoutContext alphaBetaEtaEq,
      similarity = withoutContext alphaEq,
      prettyPrinter = show,
      parser = readEither,
      ready = predicate isBetaNormal,
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
