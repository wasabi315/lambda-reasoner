{-# LANGUAGE Arrows #-}

module LambdaReasoner.Rules
  ( ruleBeta,
    ruleFVars,
    ruleAlpha,
    ruleEta,
  )
where

import Control.Arrow
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Ideas.Common.Library
import Ideas.Utils.Prelude
import LambdaReasoner.Expr

--------------------------------------------------------------------------------

ruleBeta :: Rule Expr
ruleBeta = makeRule "eval.beta" f
  where
    f (App (Abs x t) u)
      | not (willCaptureOccur x u t) = Just $ nonCaptureAvoidingSubst x u t
    f _ = Nothing

fvarsRef :: Ref Term
fvarsRef = makeRef "fvars"

writeFVars :: Trans (Set String) ()
writeFVars =
  (toTerm . Set.mapMonotonic ShowString) ^>> writeRef fvarsRef >>^ const ()

readFVars :: Trans x (Set String)
readFVars =
  readRefMaybe fvarsRef
    >>^ maybe Set.empty (Set.mapMonotonic fromShowString . fromJust . fromTerm)

-- Administrative rule
ruleFVars :: Rule (Context Expr)
ruleFVars = setMinor True . ruleTrans "eval.fvars" $ transLiftContext g
  where
    f (App (Abs _ _) u) = Just u
    f _ = Nothing

    g = proc t -> do
      u <- transMaybe f -< t
      writeFVars -< freeVars u
      returnA -< t

ruleAlpha :: Rule (Context Expr)
ruleAlpha =
  addRecognizerBool (withoutContext alphaEq)
    . ruleTrans "eval.alpha"
    $ transLiftContext g
  where
    f (fvs, t@(Abs x u))
      | x `Set.member` fvs =
          let y = fresh (fvs <> freeVars t) x
           in Just $ Abs y (rename x y u)
    f _ = Nothing

    g = proc t -> do
      fvs <- readFVars -< ()
      transMaybe f -< (fvs, t)

ruleEta :: Rule Expr
ruleEta = makeRule "eval.eta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.notMember` freeVars t = Just t
    f _ = Nothing
