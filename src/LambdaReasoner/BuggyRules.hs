module LambdaReasoner.BuggyRules
  ( buggyRules,
    buggyBeta1,
    buggyBeta2,
    buggyAlpha,
    buggyEta,
  )
where

import qualified Data.Set as Set
import Ideas.Common.Library
import LambdaReasoner.Expr
import LambdaReasoner.Rules

--------------------------------------------------------------------------------

-- A buggy version of the substitution function that does not take shadowing into account.
buggySubst1 :: String -> Expr -> Expr -> Expr
buggySubst1 x u (Var y)
  | x == y = u
  | otherwise = Var y
buggySubst1 x u (App t v) = App (buggySubst1 x u t) (buggySubst1 x u v)
buggySubst1 x u (Abs y t) = Abs y (buggySubst1 x u t)

-- | A buggy version of the β-reduction rule that does not check for shadowing.
-- e.g) (λx. λx. x) y ↝ λx. y
buggyBeta1 :: Rule Expr
buggyBeta1 = siblingOf ruleBeta $ buggyRule "eval.buggyBeta1" f
  where
    f (App (Abs x t) u)
      | x `isShadowedInside` t = Just $ buggySubst1 x u t
    f _ = Nothing

    isShadowedInside _ (Var _) = False
    isShadowedInside x (App t u) = isShadowedInside x t || isShadowedInside x u
    isShadowedInside x (Abs y t) = x == y || isShadowedInside x t

-- | A buggy version of the β-reduction rule that does not check variable capture.
-- e.g) (λx. λy. x) y ↝ λy. y
buggyBeta2 :: Rule Expr
buggyBeta2 = siblingOf ruleBeta $ buggyRule "eval.buggyBeta2" f
  where
    f (App (Abs x t) u)
      | (t', False) <- nonCaptureAvoidingSubst x u t = Just t'
    f _ = Nothing

-- | A buggy version of the α-conversion rule that captures a free variable.
-- e.g.) λx. y ↝ λy. y
buggyAlpha :: Rule Expr
buggyAlpha = siblingOf ruleAlpha $ buggyRule "eval.buggyAlpha" f
  where
    f t@(Abs x u) =
      [Abs y $ rename x y u | y <- Set.toList (freeVars t)]
    f _ = []

-- | A buggy version of the η-reduction rule that does not check for free variables.
-- e.g.) λx. f x x ↝ f x
buggyEta :: Rule Expr
buggyEta = siblingOf ruleEta $ buggyRule "eval.buggyEta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.member` freeVars t = Just t
    f _ = Nothing

buggyRules :: [Rule Expr]
buggyRules = [buggyBeta1, buggyBeta2, buggyAlpha, buggyEta]
