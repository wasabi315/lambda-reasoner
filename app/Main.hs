{-# LANGUAGE BlockArguments #-}

module Main (main) where

import Data.Maybe
import Ideas.Common.Library
import Ideas.Main.Default
import LambdaReasoner.BuggyRules
import LambdaReasoner.Expr
import LambdaReasoner.Strategies
import Text.Read

--------------------------------------------------------------------------------

_GAS :: Int
_GAS = 1024

fullBetaEx, normalEx :: Exercise Expr
fullBetaEx =
  emptyExercise
    { exerciseId = describe "Evaluate a lambda term in the full beta reduction strategy" $ newId "eval.fullBeta",
      status = Experimental,
      strategy = fullBetaStrategy,
      extraRules = map liftToContext buggyRules,
      navigation = termNavigator,
      equivalence = withoutContext (alphaBetaEtaEq _GAS),
      similarity = withoutContext rhoEq,
      suitable = predicate (isJust . normalize _GAS),
      ready = predicate isBetaNormal,
      prettyPrinter = show,
      parser = readEither,
      examples =
        mconcat
          [ examplesFor
              Easy
              [ _I `App` _I,
                _K `App` Var "x" `App` Var "y",
                read "(\\x. \\y. x) y",
                read "(\\x. \\x. x) y"
              ],
            examplesFor
              Medium
              [ _S `App` _K `App` _K,
                _S `App` _K `App` _S,
                _K `App` _I `App` omega,
                read "(\\x. (\\y. \\z. x) (\\y. \\z. x)) (y z w)"
              ]
          ]
    }
normalEx =
  fullBetaEx
    { exerciseId = describe "Evaluate a lambda term in the normal evaluation order" $ newId "eval.normalBeta",
      strategy = normalBetaStrategy
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
      { exercises = [Some fullBetaEx, Some normalEx],
        services = myServices
      }

myServices :: [Service]
myServices = metaServiceList dr ++ serviceList

main :: IO ()
main = defaultMain dr
