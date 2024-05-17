module LambdaReasoner.Rules
  ( ruleBeta,
    betaRedexRef,
    ruleSaveBetaRedex,
    ruleForgetBetaRedex,
    betaChainRef,
    ruleSaveBetaChain,
    ruleForgetBetaChain,
    ruleAlpha,
    ruleEta,
  )
where

import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Ideas.Common.Library
import LambdaReasoner.Expr
import LambdaReasoner.Views

--------------------------------------------------------------------------------

ruleBeta :: Rule Expr
ruleBeta = makeRule "eval.beta" f
  where
    f (App (Abs x t) u) = subst (Map.singleton x u) t
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

betaChainRef :: Ref BetaChain
betaChainRef = makeRef "beta-chain"

ruleSaveBetaChain :: Rule (Context Expr)
ruleSaveBetaChain = minorRule "eval.save-beta-chain" f
  where
    f ctx = do
      bc <- match betaChainView =<< currentInContext ctx
      pure $ insertRef betaChainRef bc ctx

ruleForgetBetaChain :: Rule (Context Expr)
ruleForgetBetaChain = minorRule "eval.forget-beta-chain" f
  where
    f ctx = Just $ deleteRef betaChainRef ctx

ruleAlpha :: Rule (Context Expr)
ruleAlpha =
  addRecognizerBool (withoutContext alphaEq) $ makeRule "eval.alpha" f
  where
    f ctx = do
      t@(Abs x u) <- currentInContext ctx
      let fvs = maybe Set.empty (\(BetaRedex _ _ v) -> freeVars v) $ betaRedexRef ? ctx
          y = fresh (fvs <> freeVars t) x
      guard $ x /= y
      pure $ replaceInContext (Abs y $ rename (Map.singleton x y) u) ctx

ruleEta :: Rule Expr
ruleEta = makeRule "eval.eta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.notMember` freeVars t = Just t
    f _ = Nothing
