{-# LANGUAGE BlockArguments #-}

module LambdaReasoner.Strategies
  ( captureAvoidingBeta,
    fullBetaStrategy,
    normalBetaStrategy,
  )
where

import Data.Function
import Data.Maybe
import Ideas.Common.Library as Ideas
import LambdaReasoner.Expr
import LambdaReasoner.Rules

--------------------------------------------------------------------------------

-- | Apply α-conversion before β-reduction for capture avoidance.
captureAvoidingBeta :: LabeledStrategy (Context Expr)
captureAvoidingBeta =
  label "capture-avoiding-beta" $
    repeatS
      ( -- If the current term is a β-redex, say (λx.t) u, save the substitution x ↦ u
        ruleSaveSubst
          -- Go down to the term t
          .*. (ruleDown .*. ruleDownLast)
          -- Apply α-conversions to appropriate subterms of t, respecting the saved substitution
          .*. Ideas.traverse [traversalFilter subVarNotShadowed] ruleAlpha
          -- Go back up to the redex
          .*. (ruleUp .*. ruleUp)
      )
      .*. liftToContext ruleBeta
  where
    -- Avoid traversing subterms where the variable x is shadowed
    subVarNotShadowed ctx
      | Just (Abs y _) <- currentInContext ctx,
        Subst x _ <- fromJust $ subRef ? ctx =
          x /= y
      | otherwise = True

fullBetaStrategy :: LabeledStrategy (Context Expr)
fullBetaStrategy =
  somewhere (captureAvoidingBeta .|. liftToContext ruleEta)
    & repeatS
    & label "eval.full-beta"

-- | Normal evaluation order: the leftmost outermost redex is reduced first.
-- The η-reduction rule can also be applied.
normalBetaStrategy :: LabeledStrategy (Context Expr)
normalBetaStrategy =
  leftmosttd captureAvoidingBeta .|. somewhere (liftToContext ruleEta)
    & repeatS
    & label "eval.normal-beta"
