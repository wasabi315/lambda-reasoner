{-# LANGUAGE BlockArguments #-}

module LambdaReasoner.Rules
  ( ruleBeta,
    subRef,
    ruleSaveSubst,
    ruleForgetSubst,
    ruleAlpha,
    ruleEta,
  )
where

import Control.Monad
import qualified Data.Set as Set
import Ideas.Common.Library
import LambdaReasoner.Expr

--------------------------------------------------------------------------------

-- | β-reduction: (λx.t) u ↝ t[x ↦ u].
-- Fails if variable capture occurs.
ruleBeta :: Rule Expr
ruleBeta =
  describe
    "β-reduction: (λx.t) u ↝ t[x ↦ u].\
    \Appropriate α-conversions should be applied before this rule."
    $ makeRule "eval.beta" f
  where
    f (App (Abs x t) u) = (x --> u) t
    f _ = Nothing

-- | Reference to the current substitution.
-- This is used to calculate a set of variables that should be avoided in α-conversion.
subRef :: Ref Subst
subRef = makeRef "subst"

-- | An administrative rule to save the current substitution.
ruleSaveSubst :: Rule (Context Expr)
ruleSaveSubst = minorRule "eval.save-subst" f
  where
    f ctx = do
      App (Abs x _) u <- currentInContext ctx
      pure $ insertRef subRef (Subst x u) ctx

-- | An administrative rule to forget the current substitution.
ruleForgetSubst :: Rule (Context Expr)
ruleForgetSubst = minorRule "eval.forget-subst" (Just . deleteRef subRef)

-- | α-conversion: λx.t ↝ λy.t[x ↦ y], where y is fresh.
-- If subRef is defined, say x ↦ u, then the free variables of u are also avoided.
ruleAlpha :: Rule (Context Expr)
ruleAlpha =
  describe "α-conversion: λx.t ↝ λy.t[x ↦ y], where y is fresh." $
    makeRule "eval.alpha" f
  where
    f ctx = do
      t@(Abs x u) <- currentInContext ctx
      let fvs1 = foldMap (\(Subst _ v) -> freeVars v) $ subRef ? ctx
          fvs2 = freeVars t
          y = fresh (fvs1 <> fvs2) x
      guard $ x /= y -- skip if no renaming is needed
      pure $ replaceInContext (Abs y $ rename x y u) ctx

-- | η-reduction: λx. t x ↝ t, if x ∉ FV(t).
ruleEta :: Rule Expr
ruleEta =
  describe "η-reduction: λx. t x ↝ t, if x ∉ FV(t)." $
    makeRule "eval.eta" f
  where
    f (Abs x (App t (Var y)))
      | x == y && x `Set.notMember` freeVars t = Just t
    f _ = Nothing
