{-# LANGUAGE BlockArguments #-}

module LambdaReasoner.Rules
  ( ruleBeta,
    subRef,
    ruleSaveSub,
    ruleForgetSub,
    ruleAlpha,
    ruleEta,
  )
where

import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Ideas.Common.Library
import LambdaReasoner.Expr

--------------------------------------------------------------------------------

ruleBeta :: Rule Expr
ruleBeta = makeRule "eval.beta" f
  where
    f (App (Abs x t) u) = (x --> u) t
    f _ = Nothing

subRef :: Ref Sub
subRef = makeRef "sub"

ruleSaveSub :: Rule (Context Expr)
ruleSaveSub = minorRule "eval.save-sub" f
  where
    f ctx = do
      App (Abs x _) u <- currentInContext ctx
      pure $ insertRef subRef (Sub x u) ctx

ruleForgetSub :: Rule (Context Expr)
ruleForgetSub = minorRule "eval.forget-sub" (Just . deleteRef subRef)

ruleAlpha :: Rule (Context Expr)
ruleAlpha = makeRule "eval.alpha" f
  where
    f ctx = do
      t@(Abs x u) <- currentInContext ctx
      let fvs1 = foldMap (\(Sub _ v) -> freeVars v) $ subRef ? ctx
          fvs2 = freeVars t
          x' = fresh (fvs1 <> fvs2) x
      guard $ x /= x' -- skip if no renaming is needed
      pure $ replaceInContext (Abs x' $ rename (Map.singleton x x') u) ctx

ruleEta :: Rule Expr
ruleEta = makeRule "eval.eta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.notMember` freeVars t = Just t
    f _ = Nothing
