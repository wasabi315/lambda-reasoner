module LambdaReasoner.Strategies
  ( fullBetaStrategy,
    leftmostBetaStrategy,
  )
where

import Data.Function
import Ideas.Common.Library as Ideas
import LambdaReasoner.Expr
import LambdaReasoner.Rules

--------------------------------------------------------------------------------

-- First apply α-conversion in order to avoid variable capture, then β-reduction.
alphaThenBeta :: LabeledStrategy (Context Expr)
alphaThenBeta =
  label "alpha-then-beta" $
    ruleFVars .*. try (somewhere ruleAlpha) .*. liftToContext ruleBeta

fullBetaStrategy :: LabeledStrategy (Context Expr)
fullBetaStrategy =
  somewhere (alphaThenBeta .|. liftToContext ruleEta)
    & repeatS
    & label "eval.fullBeta"

leftmostBetaStrategy :: LabeledStrategy (Context Expr)
leftmostBetaStrategy =
  leftmosttd (alphaThenBeta .|. liftToContext ruleEta)
    & repeatS
    & label "eval.leftmostBeta"
