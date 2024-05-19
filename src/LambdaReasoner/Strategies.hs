{-# LANGUAGE BlockArguments #-}

module LambdaReasoner.Strategies
  ( captureAvoidingBeta,
    fullBetaStrategy,
    leftmostBetaStrategy,
  )
where

import Data.Function
import Data.Maybe
import qualified Data.Set as Set
import Ideas.Common.Library as Ideas
import LambdaReasoner.Expr
import LambdaReasoner.Rules

--------------------------------------------------------------------------------

-- Apply α-conversion before β-reduction for capture avoidance
captureAvoidingBeta :: LabeledStrategy (Context Expr)
captureAvoidingBeta =
  label "capture-avoiding-beta" $
    repeatS
      ( ruleSaveSub
          .*. (ruleDown .*. ruleDownLast)
          .*. check containSubVar
          .*. Ideas.traverse [traversalFilter containSubVar] ruleAlpha
          .*. (ruleUp .*. ruleUp)
      )
      .*. liftToContext ruleBeta
  where
    containSubVar ctx
      | Just t <- currentInContext ctx,
        Sub x _ <- fromJust $ subRef ? ctx =
          x `Set.member` freeVars t
      | otherwise = True

fullBetaStrategy :: LabeledStrategy (Context Expr)
fullBetaStrategy =
  somewhere (captureAvoidingBeta .|. liftToContext ruleEta)
    & repeatS
    & label "eval.full-beta"

leftmostBetaStrategy :: LabeledStrategy (Context Expr)
leftmostBetaStrategy =
  leftmosttd captureAvoidingBeta .|. somewhere (liftToContext ruleEta)
    & repeatS
    & label "eval.leftmost-beta"
