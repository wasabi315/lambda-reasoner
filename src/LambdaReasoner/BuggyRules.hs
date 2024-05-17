module LambdaReasoner.BuggyRules
  ( buggyRules,
    buggyBeta1,
    buggyBeta2,
    buggyAlpha,
    buggyEta,
  )
where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Ideas.Common.Library
import LambdaReasoner.Expr
import LambdaReasoner.Rules

--------------------------------------------------------------------------------

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
      | (t', False) <- nonCaptureAvoidingSubst (Map.singleton x u) t = Just t'
    f _ = Nothing

buggyAlpha :: Rule Expr
buggyAlpha = siblingOf ruleAlpha $ buggyRule "eval.buggyAlpha" f
  where
    f t@(Abs x u) =
      [Abs y (rename (Map.singleton x y) u) | y <- Set.toList (freeVars t)]
    f _ = []

buggyEta :: Rule Expr
buggyEta = siblingOf ruleEta $ buggyRule "eval.buggyEta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.member` freeVars t = Just t
    f _ = Nothing

buggyRules :: [Rule Expr]
buggyRules = [buggyBeta1, buggyBeta2, buggyAlpha, buggyEta]
