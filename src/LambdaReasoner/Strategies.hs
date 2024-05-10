{-# LANGUAGE ViewPatterns #-}

module LambdaReasoner.Strategies
  ( fullBetaStrategy,
    leftmostBetaStrategy,
  )
where

import Data.Function
import Data.Maybe
import Ideas.Common.Library as Ideas
import LambdaReasoner.Expr
import LambdaReasoner.Rules

--------------------------------------------------------------------------------

-- Apply α-conversion before β-reduction for capture avoidance
captureAvoidingBeta :: LabeledStrategy (Context Expr)
captureAvoidingBeta =
  label "capture-avoiding-beta" $
    -- If the current term is a beta redex, say (\x. t) u, save it
    ruleSaveBetaRedex
      -- Go down to t
      .*. (ruleDown .*. ruleDownLast)
      -- Apply α-conversion to appropriate subterms referring to the saved beta redex
      .*. repeatS (Ideas.traverse [topdown, traversalFilter notShadowed] ruleAlpha)
      -- Why this doesn't work?
      -- .*. Ideas.traverse [full, topdown, traversalFilter notShadowed] (try ruleAlpha)
      -- Go back to the beta redex
      .*. (ruleUp .*. ruleUp)
      .*. liftToContext ruleBeta
      .*. ruleForgetBetaRedex
  where
    notShadowed ctx@(currentInContext -> Just (Abs y _)) =
      let BetaRedex x _ _ = fromJust $ betaRedexRef ? ctx
       in x /= y
    notShadowed _ = False

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
