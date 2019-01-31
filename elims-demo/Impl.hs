{-# language
  Strict, LambdaCase, ViewPatterns, TupleSections,
  UndecidableInstances, UnicodeSyntax, OverloadedStrings, CPP,
  MultiParamTypeClasses, AllowAmbiguousTypes, PatternSynonyms,
  TypeApplications, ScopedTypeVariables, FlexibleInstances,
  FunctionalDependencies, InstanceSigs #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module Impl (hiitToAgda, runHIITDefs) where

-- TODO:
--  - universes in target TT
--  - apd in output

import Control.Arrow
import Control.Monad hiding (ap)
import Control.Monad.Except hiding (ap)
import Data.Foldable
import Data.Function
import Data.IORef
import Data.Char
import Data.List
import Data.List.Split
import Data.Maybe
import Data.String
import Prelude hiding (ap)
import System.IO.Unsafe

import Text.Megaparsec.Pos
import Text.Megaparsec.Error

import Presyntax

-- Errors
--------------------------------------------------------------------------------

{-# noinline currPos #-}
currPos ∷ IORef SourcePos
currPos = unsafeDupablePerformIO (newIORef (initialPos ""))

reportError ∷ String → Elab a
reportError msg =
  let pos = unsafeDupablePerformIO (readIORef currPos)
  in Left (sourcePosPretty pos ++ ":\n\n" ++ msg ++ "\n")

updPos ∷ Posed a → Posed a
updPos (p, a) = seq (unsafeDupablePerformIO (writeIORef currPos p)) (p, a)

--------------------------------------------------------------------------------

type Bind a  = (Name, a)
type Bind2 a = (Name, Name, a)
type Sub a   = [Bind a]

data Tm
  = Var Name
  | App Tm Tm
  | Lam (Bind Tm)
  | Pi Tm (Bind Tm)
  | Id (Maybe Tm) Tm Tm  -- Id A t u
  | J Tm Tm Tm           -- J {a : U}{t : a}(P : (u : a)
                         --   → t ≡ u → U)(pr : P t refl){u : a}(eq : Id t u)
  | Refl (Maybe Tm)      -- refl {A}(x : A)
  | U

data Val
  = VVar Name
  | VApp Val ~Val
  | VLam (Bind (Val → Val))
  | VPi Val (Bind (Val → Val))
  | VU
  | VRefl (Maybe Val)
  | VId (Maybe Val) Val Val
  | VJ Val ~Val Val

data Code
  = CVar Name
  | CPiI Code (Bind Code)
  | CAppI Code (Bind Code) Code Code -- app A (x.B) t u
  | CPiNI Tm (Bind Code)
  | CAppNI Code Tm
  | CPiSNI Tm (Bind Code)
  | CAppSNI Tm (Bind Code) Code Tm
  | CId Code Code Code                        -- Id A t u
  | CJ Code Code (Bind2 Code) Code Code Code  -- J A t P pr u eq
  | CRefl Code Code
  | CU
  | CEl Code

data CVal
  = CVVar Name
  | CVPiI CVal (Bind (CVal → CVal))
  | CVAppI CVal (Bind (CVal → CVal)) CVal ~CVal
  | CVPiNI Val (Bind (Val → CVal))
  | CVAppNI CVal ~Val
  | CVPiSNI Val (Bind (Val → CVal))
  | CVAppSNI Val (Bind (Val → CVal)) CVal ~Val
  | CVId CVal CVal CVal                                       -- Id A t u
  | CVJ CVal CVal (Bind2 (CVal → CVal → CVal)) CVal CVal CVal  -- J A t P pr u eq
  | CVRefl CVal CVal
  | CVU
  | CVEl CVal

--------------------------------------------------------------------------------

instance IsString Tm    where fromString = Var
instance IsString Val   where fromString = VVar
instance IsString Code  where fromString = CVar
instance IsString CVal  where fromString = CVVar

pattern Lam' x t = Lam (x, t)
pattern Pi' x a b = Pi a (x, b)

infixl 8 ∙
(∙) = App
infixr 4 ==>
(==>) = Pi' "_"

type Elab = Either String
type Vals = Sub (Maybe (Either Val CVal))

lookup' :: Name → [(Name, c)] → c
lookup' x = maybe (error ("where's that: " ++ x)) id . lookup x

fresh ∷ Sub a → Name → Name
fresh vs x = go (0 ∷ Int) where
  go n =
    let x' = if n == 0 then x else x ++ show n
    in maybe x' (\_ → go (n + 1)) (lookup x' vs)

inventName ∷ Tm → Name
inventName = \case
  Var x   → map toLower (take 1 x)
  App t _ → inventName t
  Pi{}    → "f"
  Id{}    → "eq"
  U       → "A"
  _       → "_"

checkShadowing ∷ Sub a → Name → Elab ()
checkShadowing vs x =
  maybe (pure ()) (\_ → Left "no name shadowing allowed")
        (lookup x vs)

-- | If var is _, try to invent a sensible name from its (optional) type,
--   otherwise check shadowing
elabBinder ∷ Vals → Maybe Tm → Name → Elab Name
elabBinder vs hint "_" = pure $ maybe "_" (fresh vs . inventName) hint
elabBinder vs hint x   = x <$ checkShadowing vs x

-- Evaluate Tm
--------------------------------------------------------------------------------

evalBind ∷ Vals → Bind Tm → Bind (Val → Val)
evalBind vs (x, t) = (x, \u → eval ((x, Just (Left u)):vs) t)

vapp ∷ Val → Val → Val
vapp t ~u = case t of
  VLam (_, t) → t u
  t           → VApp t u

eval ∷ Vals → Tm → Val
eval vs = \case
  Var x     → maybe (VVar x) (either id (error "impossible")) $ lookup' x vs
  App t u   → vapp (eval vs t) (eval vs u)
  Lam t     → VLam (evalBind vs t)
  Pi a b    → VPi (eval vs a) (evalBind vs b)
  U         → VU
  J p pr eq → case eval vs eq of
                VRefl _ → eval vs pr
                eq      → VJ (eval vs p) (eval vs pr) eq
  Id a t u  → VId (eval vs <$> a) (eval vs t) (eval vs u)
  Refl t    → VRefl (eval vs <$> t)

quoteBind ∷ Vals → Bind (Val → Val) → Bind Tm
quoteBind vs (fresh vs → x, t) = (x, quote ((x, Nothing):vs) (t (VVar x)))

quote ∷ Vals → Val → Tm
quote vs = \case
  VVar x     → Var x
  VApp t u   → App (quote vs t) (quote vs u)
  VLam t     → Lam (quoteBind vs t)
  VPi a b    → Pi (quote vs a) (quoteBind vs b)
  VU         → U
  VRefl t    → Refl (quote vs <$> t)
  VId a t u  → Id (quote vs <$> a) (quote vs t) (quote vs u)
  VJ p pr eq → J (quote vs p) (quote vs pr) (quote vs eq)

convBind ∷ Vals → Bind (Val → Val) → Bind (Val → Val) → Bool
convBind vs (fresh vs → x, t) (_, t') = conv ((x, Nothing):vs) (t (VVar x)) (t' (VVar x))

conv ∷ Vals → Val → Val → Bool
conv vs t t' = case (t, t') of
  (VVar x     , VVar x'      ) → x == x'
  (VApp t u   , VApp t' u'   ) → conv vs t t' && conv vs u u'
  (VLam t     , VLam t'      ) → convBind vs t t'
  (VPi a b    , VPi a' b'    ) → conv vs a a' && convBind vs b b'
  (VU         , VU           ) → True
  (VId _ t u  , VId _ t' u'  ) → conv vs t t' && conv vs u u'
  (VRefl _    , VRefl _      ) → True
  (VJ p pr eq , VJ p' pr' eq') → conv vs p p' && conv vs pr pr' && conv vs eq eq'
  _                            → False

nf ∷ Vals → Tm → Tm
nf vs = quote vs . eval vs

-- Tm to Agda
--------------------------------------------------------------------------------

freeIn ∷ Name → Tm → Bool
freeIn x = \case
  Var x'          → x == x'
  App f a         → freeIn x f || freeIn x a
  Lam (x', t)     → if x == x' then False else freeIn x t
  Pi a (x', b)    → freeIn x a || if x == x' then False else freeIn x b
  Id a t u        → any (freeIn x) [t, u] || maybe False (freeIn x) a
  J p pr eq       → any (freeIn x) [p, pr, eq]
  Refl   t        → maybe False (freeIn x) t
  U               → False

pattern Tr ∷ Tm → Tm → Tm → Tm
pattern Tr p eq pr ←
  ((\case J (Lam' x (Lam' y p)) pr eq | not (freeIn y p) → Just (Lam' x p, eq, pr)
          _ -> Nothing) → Just (p, eq, pr))

-- pattern Ap ∷ Tm → Tm → Tm
-- pattern Ap f eq ←
--   ((\case Tr (Lam' y (Id _ (App f _) (App f' (Var y')))) eq (Refl _)
--              | y == y', show f == show f' → Just (f, eq)
--           _ → Nothing) → Just (f, eq))

pattern Apd ∷ Tm → Tm → Tm
pattern Apd f eq ←
  ((\case J (Lam' y (Lam' p (Id _ (Tr b (Var p') (App f t)) (App f' (Var y')))))
            (Refl _) eq | y == y', p == p', show f == show f',
                          all (not . freeIn y) [b, t, f],
                          all (not . freeIn p) [b, t, f]
                          → Just (f, eq)
          _ → Nothing) → Just (f, eq))

-- pattern Compose ∷ Tm → Tm → Tm
-- pattern Compose p q ←
--   ((\case Tr (Lam' x (Id _ t (Var x'))) q p | not (freeIn x t), x == x' → Just (p, q)
--           _ → Nothing) → Just (p, q))

-- pattern Sym ∷ Tm → Tm
-- pattern Sym p ←
--   ((\case Tr (Lam' x (Id _ (Var x') t)) p (Refl _) | not (freeIn x t), x == x' → Just p
--           _ → Nothing) → Just p)

tmToAgda ∷ Int → Tm → ShowS
tmToAgda prec = go (prec /= 0) where

  goLam ∷ Tm → ShowS
  goLam (Lam (x, t)) = (' ':)   . (x++) . goLam t
  goLam t         = (" → "++) . go False t

  goPi ∷ Bool → Tm → ShowS
  goPi p (Pi a (x, b))
    | freeIn x b = ('(':) . (x++) . (" : "++) . go False a . (')':) . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of Pi{} → True; _ → False) a .
       (" → "++) . go False b
  goPi p t = (if p then (" → "++) else id) . go False t

  go ∷ Bool → Tm → ShowS
  go p = \case
    Var x → (x++)
    App (App t u) u' →
      showParen p (go False t . (' ':) . go True u . (' ':) . go True u')
    App t u → showParen p (go True t . (' ':) . go True u)
    Lam (x, App t (Var x')) | x == x', not (freeIn x t) → go p t
    Lam (x, t)  → showParen p (("λ "++) . (x++) . goLam t)
    Pi a (x, b) → showParen p (goPi False (Pi a (x, b)))
    Refl _ → ("refl"++)
    -- Compose p' q → case (go True p' [], go True q []) of
      -- ("refl", qs) → showParen p (qs++)
      -- (ps, "refl") → showParen p (ps++)
      -- (ps, qs)     → showParen p ((ps++) . (" ◾ "++) . (qs++))
    -- Sym p' → go p ("sym" ∙ p')
    -- Ap f eq → go p ("ap" ∙ f ∙ eq)
    Apd f eq → go p ("apd" ∙ f ∙ eq)
    Tr p' eq pr → go p ("tr" ∙ p' ∙ eq ∙ pr)
    J p' pr eq →
      showParen p (("J "++) . go True p' . (' ':) . go True pr . (' ':) . go True eq)
    Id _ (Refl (Just t)) (Refl _) →
      showParen p (("refl {x = "++).go False t.("} ≡ refl"++))
    Id _ t u → showParen p (
      go (case t of Lam{} → True; Pi{} → True; Id{} → True; _ → False) t . (" ≡ "++) .
      go (case u of Lam{} → True; Pi{} → True; Id{} → True; _ → False) u)
    U → ('U':)

instance Show Tm where showsPrec = tmToAgda

-- Elaborate to Tm
--------------------------------------------------------------------------------

type Types = Sub (Either Val CVal)

check ∷ Types → Vals → Tmᴾ → Val → Elab Tm
check ts vs (updPos → (pos, t)) a = case (t, a) of
  (Lamᴾ x t, VPi a (_, b)) → do
    x ← elabBinder vs Nothing x
    t ← check ((x, Left a):ts) ((x, Nothing):vs) t (b (VVar x))
    pure $ Lam (x, t)
  (t, a) → do
    (t, a') ← infer ts vs (pos, t)
    unless (conv vs a a') $
      reportError ("type mismatch\n\nexpected:\n\n  "
                   ++ show (quote vs a)
                   ++ "\n\ngot: \n\n  " ++ show (quote vs a')
                   ++ "\n\nwhen checking:\n\n  "
                   ++ show t)
    pure t

infer ∷ Types → Vals → Tmᴾ → Elab (Tm, Val)
infer ts vs (updPos → (pos, t)) = case t of
  Varᴾ x → do
    when (x == "_") $ reportError ("can't use _ as identifier")
    case lookup x ts of
      Just (Left a)  → pure (Var x, a)
      Just (Right _) → reportError ("non-strictly positive variable occurrence: " ++ x)
      _              → reportError ("variable not in scope: " ++ x)
  Appᴾ t u → do
    (t, tty) ← infer ts vs t
    case tty of
      VPi a (_, b) → do
        u ← check ts vs u a
        pure (App t u, b (eval vs u))
      _ → reportError (
          "expected a function type for:\n\n  "
          ++ show t
          ++ "\n\ninferred type:\n\n  "
          ++ show (quote vs tty))
  Lamᴾ{} → reportError "can't infer type for lambda"
  Piᴾ x a b → do
    a ← check ts vs a VU
    let ~a' = eval vs a
    elabBinder vs (Just a) x
    b ← check ((x, Left a'):ts) ((x, Nothing):vs) b VU
    pure (Pi a (x, b), VU)
  Idᴾ t u → do
    (t, a) ← infer ts vs t
    u ← check ts vs u a
    pure (Id (Just (quote vs a)) t u, VU)
  Uᴾ → pure (U, VU)
  Jᴾ p pr eq → do
    (eq, eqty) ← infer ts vs eq
    case eqty of
      VId (Just a) t u → do
        let ux = fresh vs "u"
            px = fresh vs "p"
        p ← check ts vs p (VPi a (ux, \u → VPi (VId (Just a) t (VVar ux)) (px, \p → VU)))
        let ~p' = eval vs p
        pr ← check ts vs pr (vapp (vapp p' t) (VRefl (Just t)))
        pure (J p pr eq, vapp (vapp p' u) (eval vs eq))
      _ → reportError ("expected an identity type, inferred type:\n\n  "
                       ++ show (quote vs eqty) ++ "\n\nwhen type checking\n\n  "
                       ++ show eq)
  Reflᴾ t → do
    (t, a) ← infer ts vs t
    let ~t' = eval vs t
    pure (Refl (Just t), VId (Just a) t' t')

-- Evaluate Code
--------------------------------------------------------------------------------

evalBindᶜ ∷ Vals → Bind Code → Bind (CVal → CVal)
evalBindᶜ vs (x, t) = (x, \u → evalᶜ ((x, Just (Right u)):vs) t)

evalBindᵛᶜ ∷ Vals → Bind Code → Bind (Val → CVal)
evalBindᵛᶜ vs (x, t) = (x, \u → evalᶜ ((x, Just (Left u)):vs) t)

evalCJ ∷ Vals → Code → Code → Bind2 Code → Code → Code → Code → CVal
evalCJ vs a t (ux, eqx, p) pr u eq = case evalᶜ vs eq of
  CVRefl _ _ → evalᶜ vs pr
  eq         → CVJ (evalᶜ vs a) (evalᶜ vs t)
                 (ux, eqx, \u eq → evalᶜ ((eqx, Just (Right eq)):(ux, Just (Right u)):vs) p)
                 (evalᶜ vs pr) (evalᶜ vs u) eq

evalᶜ ∷ Vals → Code → CVal
evalᶜ vs = \case
  CVar x           → maybe (CVVar x) (either (error "impossible") id) $ lookup' x vs
  CPiI a b         → CVPiI (evalᶜ vs a) (evalBindᶜ vs b)
  CAppI a b t u    → CVAppI (evalᶜ vs a) (evalBindᶜ vs b) (evalᶜ vs t) (evalᶜ vs u)
  CPiNI a b        → CVPiNI (eval vs a) (evalBindᵛᶜ vs b)
  CAppNI t u       → CVAppNI (evalᶜ vs t) (eval vs u)
  CPiSNI a b       → CVPiSNI (eval vs a) (evalBindᵛᶜ vs b)
  CAppSNI a b t u  → CVAppSNI (eval vs a) (evalBindᵛᶜ vs b) (evalᶜ vs t) (eval vs u)
  CId a t u        → CVId (evalᶜ vs a) (evalᶜ vs t) (evalᶜ vs u)
  CJ a t p pr u eq → evalCJ vs a t p pr u eq
  CRefl a t        → CVRefl (evalᶜ vs a) (evalᶜ vs t)
  CU               → CVU
  CEl t            → CVEl (evalᶜ vs t)

convBindᶜ ∷ Vals → Bind (CVal → CVal) → Bind (CVal → CVal) → Bool
convBindᶜ vs (fresh vs → x, t) (_, t') = convᶜ ((x, Nothing):vs) (t (CVVar x)) (t' (CVVar x))

convBindᵛᶜ ∷ Vals → Bind (Val → CVal) → Bind (Val → CVal) → Bool
convBindᵛᶜ vs (fresh vs → x, t) (_, t') = convᶜ ((x, Nothing):vs) (t (VVar x)) (t' (VVar x))

convCVJ ∷ Vals → Bind2 (CVal -> CVal -> CVal) → CVal → CVal
               → Bind2 (CVal -> CVal -> CVal) → CVal → CVal
               → Bool
convCVJ vs (fresh vs → x, fresh ((x, Nothing):vs) → y, p) pr eq (_, _, p') pr' eq' =
  convᶜ ((y, Nothing):(x, Nothing):vs) (p (CVVar x) (CVVar y)) (p' (CVVar x) (CVVar y))
  && convᶜ vs pr pr' && convᶜ vs eq eq'

convᶜ ∷ Vals → CVal → CVal → Bool
convᶜ vs t t' = case (t, t') of
  (CVVar x           , CVVar x')             → x == x'
  (CVPiI a b         , CVPiI a' b')          → convᶜ vs a a' && convBindᶜ vs b b'
  (CVAppI _ _ t u    , CVAppI _ _ t' u')     → convᶜ vs t t' && convᶜ vs u u'
  (CVPiNI a b        , CVPiNI a' b')         → conv  vs a a' && convBindᵛᶜ vs b b'
  (CVAppNI t u       , CVAppNI t' u')        → convᶜ vs t t' && conv vs u u'
  (CVPiSNI a b       , CVPiSNI a' b')        → conv  vs a a' && convBindᵛᶜ vs b b'
  (CVAppSNI _ _ t u  , CVAppSNI _ _ t' u')   → convᶜ vs t t' && conv vs u u'
  (CVId _ t u        , CVId _ t' u')         → convᶜ vs t t' && convᶜ vs u u'
  (CVJ _ _ p pr _ eq , CVJ _ _ p' pr' _ eq') → convCVJ vs p pr eq p' pr' eq'
  (CVRefl _ t        , CVRefl _ t')          → convᶜ vs t t'
  (CVU               , CVU)                  → True
  (CVEl t            , CVEl t')              → convᶜ vs t t'
  _                                          → False

quoteBindᶜ ∷ Vals → Bind (CVal → CVal) → Bind Code
quoteBindᶜ vs (fresh vs → x, t) = (x, quoteᶜ ((x, Nothing):vs) (t (CVVar x)))

quoteBindᵛᶜ ∷ Vals → Bind (Val → CVal) → Bind Code
quoteBindᵛᶜ vs (fresh vs → x, t) = (x, quoteᶜ ((x, Nothing):vs) (t (VVar x)))

quoteCJV ∷ Vals → CVal → CVal
        → Bind2 (CVal → CVal → CVal) → CVal → CVal → CVal → Code
quoteCJV vs a t (fresh vs → x, fresh ((x, Nothing):vs) → y, p) pr u eq =
  CJ (quoteᶜ vs a) (quoteᶜ vs t)
     (x, y, quoteᶜ ((y, Nothing):(x,Nothing):vs) (p (CVVar x) (CVVar y)))
  (quoteᶜ vs pr) (quoteᶜ vs u) (quoteᶜ vs eq)

quoteᶜ ∷ Vals → CVal → Code
quoteᶜ vs = \case
  CVVar x           → CVar x
  CVPiI a b         → CPiI (quoteᶜ vs a) (quoteBindᶜ vs b)
  CVAppI a b t u    → CAppI (quoteᶜ vs a) (quoteBindᶜ vs b) (quoteᶜ vs t) (quoteᶜ vs u)
  CVPiNI a b        → CPiNI (quote vs a) (quoteBindᵛᶜ vs b)
  CVAppNI t u       → CAppNI (quoteᶜ vs t) (quote vs u)
  CVPiSNI a b       → CPiSNI (quote vs a) (quoteBindᵛᶜ vs b)
  CVAppSNI a b t u  → CAppSNI (quote vs a) (quoteBindᵛᶜ vs b) (quoteᶜ vs t) (quote vs u)
  CVId a t u        → CId (quoteᶜ vs a) (quoteᶜ vs t) (quoteᶜ vs u)
  CVJ a t p pr u eq → quoteCJV vs a t p pr u eq
  CVRefl a t        → CRefl (quoteᶜ vs a) (quoteᶜ vs t)
  CVU               → CU
  CVEl t            → CEl (quoteᶜ vs t)

renderCode ∷ Code → Tm
renderCode = go where
  go = \case
    CVar x           → Var x
    CPiI a b         → Pi (go a) (go <$> b)
    CAppI a b t u    → App (go t) (go u)
    CPiNI a b        → Pi a (go <$> b)
    CAppNI t u       → App (go t) u
    CPiSNI a b       → Pi a (go <$> b)
    CAppSNI a b t u  → App (go t) u
    CId a t u        → Id (Just (go a)) (go t) (go u)
    CJ a t (x, y, p) pr u eq → J (Lam' x $ Lam' y $ go p) (go pr) (go eq)
    CRefl a t        → Refl (Just (go t))
    CU               → U
    CEl t            → App "El" (go t)

instance Show Code where show = show . renderCode

nfᶜ ∷ Vals → Code → Code
nfᶜ vs = quoteᶜ vs . evalᶜ vs

-- Constructors / std translation
--------------------------------------------------------------------------------

c1 ∷ Bind Code → Tm
c1 (x, t) = Lam' x (c t)

c2 ∷ Bind2 Code → Tm
c2 (x, y, t) = Lam' x $ Lam' y (c t)

c ∷ Code → Tm
c = \case
  CVar x           → Var x
  CPiI a (x, b)    → Pi (c a) (x, c b)
  CAppI _ _ t u    → App (c t) (c u)
  CPiNI a (x, b)   → Pi a (x, c b)
  CAppNI t u       → App (c t) u
  CPiSNI a (x, b)  → Pi a (x, c b)
  CAppSNI _ _ t u  → App (c t) u
  CId a t u        → Id (Just (c a)) (c t) (c u)
  CRefl a t        → Refl (Just (c t))
  CU               → U
  CEl t            → c t
  CJ a t p pr u eq → J (c2 p) (c pr) (c eq)

-- Elaborate to Code
--------------------------------------------------------------------------------

checkᶜ ∷ Types → Vals → Tmᴾ → CVal → Elab Code
checkᶜ ts vs (updPos → (pos, t)) a = do
  (t, a') ← inferᶜ ts vs (pos, t)
  unless (convᶜ vs a a') $
    reportError ("type mismatch\n\nexpected type:\n\n  "
                   ++ show (quoteᶜ vs a)
                   ++ "\n\ninferred type:\n\n  " ++ show (quoteᶜ vs a')
                   ++ "\n\nwhen checking:\n\n  "
                   ++ show t)
  pure t

checkTypeᶜ ∷ Types → Vals → Tmᴾ → Elab Code
checkTypeᶜ ts vs (updPos → (pos, t)) = case t of
  Piᴾ x a b → do
    case check ts vs a VU of
      Left _ → do
        a ← checkᶜ ts vs a CVU
        let ~a' = evalᶜ vs a
        x ← elabBinder vs (Just (c a)) x
        b ← checkTypeᶜ ((x, Right (CVEl a')):ts) ((x, Nothing):vs) b
        pure (CPiI a (x, b))
      Right a → do
        let ~a' = eval vs a
        x ← elabBinder vs (Just a) x
        b ← checkTypeᶜ ((x, Left a'):ts) ((x, Nothing):vs) b
        pure (CPiNI a (x, b))
  Uᴾ → pure CU
  t  → CEl <$> checkᶜ ts vs (pos, t) CVU

inferᶜ ∷ Types → Vals → Tmᴾ → Elab (Code, CVal)
inferᶜ ts vs (updPos → (pos, t)) = case t of
  Varᴾ x → do
    when (x == "_") $ reportError "can't use _ as identifier"
    case lookup x ts of
      Just (Right a) → pure (CVar x, a)
      Just (Left a)  →
        reportError ("expected inductive type for variable "
                      ++ x ++ ", inferred type:\n\n  " ++ show (quote vs a))
      _ → reportError ("variable not in scope: " ++ x)
  Appᴾ t u → do
    (t, tty) ← inferᶜ ts vs t
    case tty of
      CVPiI a b → do
        u ← checkᶜ ts vs u (CVEl a)
        let ~u' = evalᶜ vs u
        pure (CAppI (quoteᶜ vs a) (quoteBindᶜ vs b) t u, snd b u')
      CVPiNI a b → do
        u ← check ts vs u a
        pure (CAppNI t u, snd b (eval vs u))
      CVEl (CVPiSNI a b) → do
        u ← check ts vs u a
        pure (CAppSNI (quote vs a) (quoteBindᵛᶜ vs b) t u, CVEl (snd b (eval vs u)))
      _ → reportError
          ("expected a function type for:\n\n  " ++
           show t ++ "\n\ninferrred type:\n\n  " ++ show (quoteᶜ vs tty))
  tp@Lamᴾ{} → reportError ("Can't infer type for lambda expression: " ++ show tp)
  Piᴾ x a b → do
    a ← check ts vs a VU
    x ← elabBinder vs (Just a) x
    b ← checkᶜ ((x, Left (eval vs a)):ts) ((x, Nothing):vs) b CVU
    pure (CPiSNI a (x, b), CVU)
  Idᴾ t u → do
    (t, a) ← inferᶜ ts vs t
    case a of
      CVEl a → do
        u ← checkᶜ ts vs u (CVEl a)
        pure (CId (quoteᶜ vs a) t u, CVU)
      _ → reportError
          ("expected a small type for\n\n"++ show t
            ++ "\n\ngot\n\n" ++ show (quoteᶜ vs a))
  Jᴾ (_, Lamᴾ ux (_, Lamᴾ eqx p)) pr eq → do
    checkShadowing vs ux
    checkShadowing ((ux, Nothing):vs) eqx
    (eq, eqty) ← inferᶜ ts vs eq
    case eqty of
      CVEl (CVId a t u) → do
        p ← checkᶜ ((eqx, Right (CVEl (CVId a t (CVVar ux)))):(ux, Right (CVEl a)):ts)
                   ((eqx, Nothing):(ux, Nothing):vs) p CVU
        pr ← checkᶜ ts vs pr
               (CVEl (evalᶜ ((eqx, Just (Right (CVRefl a t))):(ux, Just (Right t)):vs) p))
        pure (CJ (quoteᶜ vs a) (quoteᶜ vs t) (ux, eqx, p) pr (quoteᶜ vs u) eq,
              (CVEl (evalᶜ ((eqx, Just (Right (evalᶜ vs eq))):(ux, Just (Right u)):vs) p)))
      _ → reportError ("expected equality type for\n\n" ++ show eq
                       ++ "\n\ngot\n\n" ++ show (quoteᶜ vs eqty))
  Reflᴾ t → do
    (t, a) ← inferᶜ ts vs t
    case a of
      CVEl a → do
        let ~t' = evalᶜ vs t
        pure (CRefl (quoteᶜ vs a) t, CVEl (CVId a t' t'))
      _ → reportError
            ("expected a small type for\n\n"++ show t
             ++ "\n\ngot\n\n" ++ show (quoteᶜ vs a))
  Jᴾ{} → error "impossible"
  Uᴾ → reportError "Expected a term, got U"

--------------------------------------------------------------------------------

lamHOAS ∷ Name → (Tm → Tm) → Tm
lamHOAS x f = Lam (x, f (Var x))

piHOAS ∷ Name → Tm → (Tm → Tm) → Tm
piHOAS x a f = Pi a (x, f (Var x))

#define LAM_(x) lamHOAS "x'" $ \x →
#define LAM(x) lamHOAS "x" $ \x →
#define PI(x, a) piHOAS "x" a $ \x →
#define PI_(x, a) piHOAS "x'" a $ \x →

pattern Refl' = Refl Nothing
pattern Id' t u = Id Nothing t u

--------------------------------------------------------------------------------

tr ∷ Tm → Tm → Tm → Tm
tr p eq t = J (LAM_(u) LAM(_) p ∙ u) t eq

ap ∷ Tm → Tm → Tm → Tm → Tm
ap f t u p = tr (LAM_(u) Id' (f ∙ t) (f ∙ u)) p Refl'

apd ∷ Tm → Tm → Tm → Tm → Tm
apd b f t p = J (LAM_(u) LAM_(p) Id' (tr b p (f ∙ t)) (f ∙ u)) Refl' p

class M a b | a → b, b → a where m ∷ a → b

instance M Name Name where m = (++ "ᴹ")

m1 ∷ Bind Code → Tm
m1 (x, t) = Lam' x $ Lam' (m x) (m t)

m2 ∷ Bind2 Code → Tm
m2 (x, y, t) = Lam' x $ Lam' (m x) $ Lam' y $ Lam' (m y) (m t)

mj ∷ Tm → Tm → Tm → Tm → Tm → Tm →
     Tm → Tm → Tm → Tm → Tm → Tm → Tm
mj a aᴹ t tᴹ p pᴹ pr prᴹ u uᴹ eq eqᴹ =
  J (LAM_(uᴹ) LAM_(eqᴹ) pᴹ ∙ u ∙ uᴹ ∙ eq ∙ eqᴹ ∙ J p pr eq)
    (J (LAM_(u) LAM_(eq) pᴹ ∙ u ∙ tr aᴹ eq tᴹ ∙ eq ∙ Refl' ∙ J p pr eq)
       prᴹ eq)
    eqᴹ

instance M Code Tm where
  m = \case
    CVar x           → Var (m x)
    CPiI a (x, b)    → LAM_(f) Pi' x (c a) $ Pi' (m x) (m a ∙ Var x) $ m b ∙ (f ∙ Var x)
    CAppI _ _ t u    → m t ∙ c u ∙ m u
    CPiNI a (x, b)   → LAM_(f) Pi' x a $ m b ∙ (f ∙ Var x)
    CAppNI t u       → m t ∙ u
    CPiSNI a (x, b)  → LAM_(f) Pi' x a $ m b ∙ (f ∙ Var x)
    CAppSNI _ _ t u  → m t ∙ u
    CId a t u        → LAM_(eq) Id' (tr (m a) eq (m t)) (m u)
    CRefl _ t        → Refl'
    CU               → LAM_(a) (a ==> U)
    CEl t            → m t
    CJ a t p pr u eq → mj (c a) (m a) (c t) (m t) (c2 p) (m2 p)
                          (c pr) (m pr) (c u) (m u) (c eq) (m eq)

class E a b | a → b, b → a where e ∷ a → b

e1 ∷ Bind Code → Tm
e1 (x, t) = Lam' x $ Lam' (m x) $ Lam' (e x) (e t)

e2 ∷ Bind2 Code → Tm
e2 (x, y, t) = Lam' x $ Lam' (m x) $ Lam' (e x) $ Lam' y $ Lam' (m y) $ Lam' (e y) (e t)

instance E Name Name where e = (++"ᴱ")

eCAppI a aᴹ aᴱ b bᴹ bᴱ t tᴹ tᴱ u uᴹ uᴱ =
  J (LAM_(uᴹ) LAM_(uᴱ) bᴱ ∙ u ∙ uᴹ ∙ uᴱ ∙ (t ∙ u) ∙ (tᴹ ∙ u ∙ uᴹ)) (tᴱ ∙ u) uᴱ

eCAppSNI a b bᴹ bᴱ t tᴹ tᴱ u =
  ap (LAM_(f) f ∙ u) (LAM_(u) bᴱ ∙ u ∙ (t ∙ u)) tᴹ tᴱ

eCId a aᴹ aᴱ t tᴹ tᴱ u uᴹ uᴱ =
  (LAM_(e) tr
    (LAM_(xᴹ) Id' (tr aᴹ e xᴹ) uᴹ)
    tᴱ
    (tr (LAM_(yᴹ) Id' (tr aᴹ e (aᴱ ∙ t)) yᴹ) uᴱ (apd aᴹ aᴱ t e)))

eCRefl a aᴹ aᴱ t tᴹ tᴱ =
  (J (LAM_(xᴹ) LAM_(xᴱ)
      Id'
      (tr (LAM_(yᴹ) Id' yᴹ xᴹ) xᴱ
        (tr (LAM_(yᴹ) Id' (aᴱ ∙ t) yᴹ) xᴱ Refl'))
      Refl')
     Refl'
     tᴱ)

-- | Code generated with AgdaToHsUtils.hs
eCJ ∷ Tm → Tm → Tm → Tm → Tm → Tm
    → Tm → Tm → Tm → Tm → Tm → Tm
    → Tm → Tm → Tm → Tm → Tm → Tm
    → Tm
eCJ a aᴹ aᴱ t tᴹ tᴱ p pᴹ pᴱ pr prᴹ prᴱ u uᴹ uᴱ eq eqᴹ eqᴱ =
  J (Lam' "eqᴹ₁'" (Lam' "eqᴱ₁'" (Id' (pᴱ ∙ u ∙ uᴹ ∙ uᴱ ∙ eq ∙ "eqᴹ₁'"
  ∙ "eqᴱ₁'" ∙ (J p pr eq)) (J (Lam' "xᴹ'" (Lam' "zᴹ'" (pᴹ ∙ u ∙ "xᴹ'"
  ∙ eq ∙ "zᴹ'" ∙ (J p pr eq)))) (J (Lam' "x'" (Lam' "z'" (pᴹ ∙ "x'" ∙
  (J (Lam' "u₁'" (Lam' "p₁'" (aᴹ ∙ "u₁'"))) tᴹ "z'") ∙ "z'" ∙ Refl' ∙
  (J p pr "z'")))) prᴹ eq) "eqᴹ₁'")))) (J (Lam' "uᴹ₁'" (Lam' "uᴱ₁'"
  (Id' (pᴱ ∙ u ∙ "uᴹ₁'" ∙ "uᴱ₁'" ∙ eq ∙ (J (Lam' "u₁'" (Lam' "p₁'"
  (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴹ ∙ "u₂'"))) "u₁'" eq) "uᴹ₁'")))
  (J (Lam' "u₁'" (Lam' "p₁'" (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴹ ∙
  "u₂'"))) (aᴱ ∙ t) eq) "u₁'"))) (J (Lam' "y'" (Lam' "p₁'" (Id' (J
  (Lam' "u₁'" (Lam' "p₂'" (aᴹ ∙ "u₁'"))) (aᴱ ∙ t) "p₁'") (aᴱ ∙
  "y'")))) Refl' eq) "uᴱ₁'") tᴱ) ∙ Refl' ∙ (J p pr eq)) (J (Lam' "xᴹ'"
  (Lam' "zᴹ'" (pᴹ ∙ u ∙ "xᴹ'" ∙ eq ∙ "zᴹ'" ∙ (J p pr eq)))) (J (Lam'
  "x'" (Lam' "z'" (pᴹ ∙ "x'" ∙ (J (Lam' "u₁'" (Lam' "p₁'" (aᴹ ∙
  "u₁'"))) tᴹ "z'") ∙ "z'" ∙ Refl' ∙ (J p pr "z'")))) prᴹ eq) (J (Lam'
  "u₁'" (Lam' "p₁'" (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴹ ∙ "u₂'")))
  "u₁'" eq) "uᴹ₁'"))) (J (Lam' "u₁'" (Lam' "p₁'" (Id' (J (Lam' "u₂'"
  (Lam' "p₂'" (aᴹ ∙ "u₂'"))) (aᴱ ∙ t) eq) "u₁'"))) (J (Lam' "y'" (Lam'
  "p₁'" (Id' (J (Lam' "u₁'" (Lam' "p₂'" (aᴹ ∙ "u₁'"))) (aᴱ ∙ t) "p₁'")
  (aᴱ ∙ "y'")))) Refl' eq) "uᴱ₁'") tᴱ))))) (J (Lam' "u₁'" (Lam' "eq₁'"
  (Id' (pᴱ ∙ "u₁'" ∙ (aᴱ ∙ "u₁'") ∙ Refl' ∙ "eq₁'" ∙ (J (Lam' "u₂'"
  (Lam' "p₁'" (Id' (J (Lam' "u₃'" (Lam' "p₂'" (aᴹ ∙ "u₃'"))) "u₂'"
  "eq₁'") (aᴱ ∙ "u₁'")))) (J (Lam' "y'" (Lam' "p₁'" (Id' (J (Lam'
  "u₂'" (Lam' "p₂'" (aᴹ ∙ "u₂'"))) (aᴱ ∙ t) "p₁'") (aᴱ ∙ "y'"))))
  Refl' "eq₁'") tᴱ) ∙ Refl' ∙ (J p pr "eq₁'")) (J (Lam' "xᴹ'" (Lam'
  "zᴹ'" (pᴹ ∙ "u₁'" ∙ "xᴹ'" ∙ "eq₁'" ∙ "zᴹ'" ∙ (J p pr "eq₁'")))) (J
  (Lam' "x'" (Lam' "z'" (pᴹ ∙ "x'" ∙ (J (Lam' "u₂'" (Lam' "p₁'" (aᴹ ∙
  "u₂'"))) tᴹ "z'") ∙ "z'" ∙ Refl' ∙ (J p pr "z'")))) prᴹ "eq₁'") (J
  (Lam' "u₂'" (Lam' "p₁'" (Id' (J (Lam' "u₃'" (Lam' "p₂'" (aᴹ ∙
  "u₃'"))) "u₂'" "eq₁'") (aᴱ ∙ "u₁'")))) (J (Lam' "y'" (Lam' "p₁'"
  (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴹ ∙ "u₂'"))) (aᴱ ∙ t) "p₁'") (aᴱ ∙
  "y'")))) Refl' "eq₁'") tᴱ))))) (J (Lam' "tᴹ₁'" (Lam' "tᴱ₁'" (Pi'
  "pᴹ₁'" (Pi' "x'" a (Pi' "xᴹ'" (aᴹ ∙ "x'") (Pi' "z'" (Id' t "x'")
  ((Id' (J (Lam' "u₁'" (Lam' "p₁'" (aᴹ ∙ "u₁'"))) "tᴹ₁'" "z'") "xᴹ'")
  ==> (p ∙ "x'" ∙ "z'") ==> U)))) (Pi' "pᴱ₁'" (Pi' "x'" a (Pi' "xᴹ'"
  (aᴹ ∙ "x'") (Pi' "xᴱ'" (Id' (aᴱ ∙ "x'") "xᴹ'") (Pi' "z'" (Id' t
  "x'") (Pi' "zᴹ'" (Id' (J (Lam' "u₁'" (Lam' "p₁'" (aᴹ ∙ "u₁'")))
  "tᴹ₁'" "z'") "xᴹ'") ((Id' (J (Lam' "u₁'" (Lam' "p₁'" (Id' (J (Lam'
  "u₂'" (Lam' "p₂'" (aᴹ ∙ "u₂'"))) "u₁'" "z'") "xᴹ'"))) (J (Lam' "u₁'"
  (Lam' "p₁'" (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴹ ∙ "u₂'"))) (aᴱ ∙ t)
  "z'") "u₁'"))) (J (Lam' "y'" (Lam' "p₁'" (Id' (J (Lam' "u₁'" (Lam'
  "p₂'" (aᴹ ∙ "u₁'"))) (aᴱ ∙ t) "p₁'") (aᴱ ∙ "y'")))) Refl' "z'")
  "xᴱ'") "tᴱ₁'") "zᴹ'") ==> Pi' "x₁'" (p ∙ "x'" ∙ "z'") ("pᴹ₁'" ∙ "x'"
  ∙ "xᴹ'" ∙ "z'" ∙ "zᴹ'" ∙ "x₁'"))))))) (Pi' "prᴹ₁'" ("pᴹ₁'" ∙ t ∙
  "tᴹ₁'" ∙ Refl' ∙ Refl' ∙ pr) ((Id' ("pᴱ₁'" ∙ t ∙ "tᴹ₁'" ∙ "tᴱ₁'" ∙
  Refl' ∙ Refl' ∙ (J (Lam' "xᴹ'" (Lam' "xᴱ'" (Id' (J (Lam' "u₁'" (Lam'
  "p₁'" (Id' "u₁'" "xᴹ'"))) (J (Lam' "u₁'" (Lam' "p₁'" (Id' (aᴱ ∙ t)
  "u₁'"))) Refl' "xᴱ'") "xᴱ'") Refl'))) Refl' "tᴱ₁'") ∙ pr) "prᴹ₁'")
  ==> Id' ("pᴱ₁'" ∙ t ∙ (aᴱ ∙ t) ∙ Refl' ∙ Refl' ∙ (J (Lam' "u₁'"
  (Lam' "p₁'" (Id' "u₁'" (aᴱ ∙ t)))) Refl' "tᴱ₁'") ∙ Refl' ∙ pr) (J
  (Lam' "xᴹ'" (Lam' "zᴹ'" ("pᴹ₁'" ∙ t ∙ "xᴹ'" ∙ Refl' ∙ "zᴹ'" ∙ pr)))
  "prᴹ₁'" (J (Lam' "u₁'" (Lam' "p₁'" (Id' "u₁'" (aᴱ ∙ t)))) Refl'
  "tᴱ₁'")))))))) (Lam' "pᴹ₁'" (Lam' "pᴱ₁'" (Lam' "prᴹ₁'" (Lam' "prᴱ₁'"
  "prᴱ₁'")))) tᴱ ∙ pᴹ ∙ pᴱ ∙ prᴹ ∙ prᴱ) eq) uᴱ) eqᴱ

instance E Code Tm where
  e = \case
    CVar x → Var (e x)

    CPiI a (x, b) →
      LAM_(f) LAM_(fᴹ)
        Pi' x (c a)
          ((Lam' (m x) $ Lam' (e x) $ e b)
            ∙ (e a ∙ Var x)
            ∙ Refl'
            ∙ (f ∙ Var x)
            ∙ (fᴹ ∙ Var x ∙ (e a ∙ Var x)))

    CPiNI a (x, b)  → LAM_(f) LAM(fᴹ) Pi' x a (e b ∙ (f ∙ Var x) ∙ (fᴹ ∙ Var x))
    CPiSNI a (x, b) → LAM_(f) Lam' x (e b ∙ (f ∙ Var x))

    CAppI a b t u    → eCAppI (c a) (m a) (e a) (c1 b) (m1 b) (e1 b)
                              (c t) (m t) (e t) (c u) (m u) (e u)
    CAppNI t u       → e t ∙ u
    CAppSNI a b t u  → eCAppSNI a (c1 b) (m1 b) (e1 b) (c t) (m t) (e t) u

    CId a t u        → eCId (c a) (m a) (e a) (c t) (m t) (e t) (c u) (m u) (e u)
    CRefl a t        → eCRefl (c a) (m a) (e a) (c t) (m t) (e t)
    CU               → LAM_(a) LAM_(aᴹ) PI_(x, a) (aᴹ ∙ x)
    CEl a            → LAM_(t) LAM_(tᴹ) Id' (e a ∙ t) tᴹ
    CJ a t p pr u eq → eCJ (c a)  (m a)  (e a)
                           (c t)  (m t)  (e t)
                           (c2 p) (m2 p) (e2 p)
                           (c pr) (m pr) (e pr)
                           (c u)  (m u)  (e u)
                           (c eq) (m eq) (e eq)


--------------------------------------------------------------------------------

elabInp ∷ (Sub Tmᴾ, Sub Tmᴾ) → Elab (Sub Tm, Sub Code)
elabInp (nonind, ind) = do
  -- check nonind env
  (ts, vs, ns) ← foldrM
              (\(x, t) (ts, vs, ns) → do
                  x ← elabBinder vs Nothing x
                  t ← check ts vs t VU
                  pure ((x, Left (eval vs t)):ts, (x, Nothing):vs, (x, t):ns))
               ([], [], []) nonind
  -- check ind env
  (ts', vs', cs) ← foldrM
                 (\(x, t)(ts, vs, cs) → do
                     x ← elabBinder vs Nothing x
                     t ← evalᶜ vs <$> checkTypeᶜ ts vs t
                     pure ((x, Right t):ts, (x, Nothing):vs, (x, quoteᶜ vs t):cs))
                 (ts, vs, []) ind
  pure (ns, cs)

genElims ∷ (Sub Tmᴾ, Sub Tmᴾ) → Elab (Sub Tm, Sub Tm)
genElims (nonind, ind) = do
  (ns, cs) ← elabInp (nonind, ind)
  let cs' = foldr
              (\(x, t) acc → (e x, e t ∙ Var x ∙ Var (m x)):(m x, m t ∙ Var x):(x, c t):acc)
              [] cs
  pure (
    ns,
    fst $ foldr
      (\(x, t) (acc, vs) → ((x, nf vs t):acc, (x, Nothing):vs))
      ([], map (\(x, _) → (x, Nothing)) nonind) cs')

header ∷ String
header = unlines [
  "-- Agda header",
  "U = Set",
  "",
  "infix 4 _≡_",
  "data _≡_ {α} {A : Set α} (x : A) : A → Set α where",
  "  refl : x ≡ x",
  "",
  "J : ∀{α β}{A : Set α} {a₀ : A} (P : (a₁ : A) → a₀ ≡ a₁ → Set β) → P _ refl → ∀ {a₁}(p : a₀ ≡ a₁) → P a₁ p",
  "J P pr refl = pr",
  "",
  "tr : ∀{α β}{A : Set α}(B : A → Set β){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁) → B a₀ → B a₁",
  "tr B eq t = J (λ x _ → B x) t eq",
  "",
  "apd : ∀ {α β}{A : Set α}{B : A → Set β}(f : ∀ a → B a){x y : A}(p : x ≡ y) → tr B p (f x) ≡ f y",
  "apd {A = A} {B} f {t} {u} p = J (λ y p → tr B p (f t) ≡ f y) (refl {x = f t}) p"
  -- "",
  -- "infixr 5 _◾_",
  -- "_◾_ : ∀ {α}{A : Set α}{x y z : A} → x ≡ y → y ≡ z → x ≡ z",
  -- "_◾_ {x = x}{y}{z} p q = tr (λ z → x ≡ z) q p",
  -- "",
  -- "sym : ∀ {α}{A : Set α}{x y : A} → x ≡ y → y ≡ x",
  -- "sym {A = A} {x} {y} p = tr (λ z → z ≡ x) p refl"
  ]

toAgda ∷ (Sub Tmᴾ, Sub Tmᴾ) → IO ()
toAgda (reverse → nonind, reverse → ind) = do

  let renderCxt ts = unlines ["  " ++ x ++ " : " ++ show t | (x, t) ← ts]

  case genElims (nonind, ind) of
    Left e → do
      putStrLn e
    Right (ns, ts) → do
      case transpose (chunksOf 3 ts) of
        [es, ms, cs] → do
          putStrLn header
          putStrLn "postulate"
          when (not $ null ns) $ do
            putStrLn "  -- Assumed non-inductive context:"
            putStrLn $ renderCxt (reverse ns)
          putStrLn "  -- Constructors:"
          putStrLn $ renderCxt (reverse cs)
          putStrLn "  -- Induction methods:"
          putStrLn $ renderCxt (reverse ms)
          putStrLn "  -- Eliminators and β-rules:"
          putStrLn $ renderCxt (reverse es)
        _ → do
          putStrLn "Error in input:"
          putStrLn "No inductive constructors were given."

hiitToAgda ∷ String → IO ()
hiitToAgda inp = do
  case parseInput "" inp of
    Left e    → putStrLn $ errorBundlePretty e
    Right inp → toAgda inp

runHIITDefs ∷ String → IO ()
runHIITDefs path = do
  inp ← readFile path
  case parseInput path inp of
    Left e    → putStrLn $ errorBundlePretty e
    Right inp → toAgda inp
