module LambdaReasoner.Rules
  ( ruleBeta,
    betaRedexRef,
    ruleSaveBetaRedex,
    ruleForgetBetaRedex,
    ruleAlpha,
    ruleEta,
  )
where

import Control.Monad
import qualified Data.Set as Set
import Ideas.Common.Library
import LambdaReasoner.Expr

--------------------------------------------------------------------------------

ruleBeta :: Rule Expr
ruleBeta = makeRule "eval.beta" f
  where
    f (App (Abs x t) u) = (x --> u) t
    f _ = Nothing

betaRedexRef :: Ref BetaRedex
betaRedexRef = makeRef "beta-redex"

ruleSaveBetaRedex :: Rule (Context Expr)
ruleSaveBetaRedex = minorRule "eval.save-beta-redex" f
  where
    f ctx = do
      App (Abs x t) u <- currentInContext ctx
      pure $ insertRef betaRedexRef (BetaRedex x t u) ctx

ruleForgetBetaRedex :: Rule (Context Expr)
ruleForgetBetaRedex = minorRule "eval.forget-beta-redex" f
  where
    f ctx = Just $ deleteRef betaRedexRef ctx

ruleAlpha :: Rule (Context Expr)
ruleAlpha =
  addRecognizerBool (withoutContext alphaEq) $ makeRule "eval.alpha" f
  where
    f ctx = do
      t@(Abs x u) <- currentInContext ctx
      let fvs = maybe Set.empty (\(BetaRedex _ _ v) -> freeVars v) $ betaRedexRef ? ctx
          y = fresh (fvs <> freeVars t) x
      guard $ x /= y
      pure $ replaceInContext (Abs y $ rename x y u) ctx

ruleEta :: Rule Expr
ruleEta = makeRule "eval.eta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.notMember` freeVars t = Just t
    f _ = Nothing
