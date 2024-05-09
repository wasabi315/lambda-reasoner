module LambdaReasoner.Rules
  ( ruleBeta,
    ruleFVars,
    ruleAlpha,
    ruleEta,
  )
where

import Control.Monad
import Data.Maybe
import qualified Data.Set as Set
import Ideas.Common.Library
import LambdaReasoner.Expr

--------------------------------------------------------------------------------

ruleBeta :: Rule Expr
ruleBeta = makeRule "eval.beta" f
  where
    f (App (Abs x t) u) = (x --> u) t
    f _ = Nothing

fvarsRef :: Ref Term
fvarsRef = makeRef "fvars"

-- Administrative rule
ruleFVars :: Rule (Context Expr)
ruleFVars = minorRule "eval.fvars" f
  where
    f ctx = do
      App (Abs _ _) u <- currentInContext ctx
      pure $ insertRef fvarsRef (toTerm $ freeVars u) ctx

ruleAlpha :: Rule (Context Expr)
ruleAlpha =
  addRecognizerBool (withoutContext alphaEq) $ makeRule "eval.alpha" f
  where
    f ctx = do
      t@(Abs x u) <- currentInContext ctx
      let fvs = maybe Set.empty (fromJust . fromTerm) $ fvarsRef ? ctx
          y = fresh (fvs <> freeVars t) x
      guard $ x /= y
      pure $ replaceInContext (Abs y $ rename x y u) ctx

ruleEta :: Rule Expr
ruleEta = makeRule "eval.eta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.notMember` freeVars t = Just t
    f _ = Nothing
