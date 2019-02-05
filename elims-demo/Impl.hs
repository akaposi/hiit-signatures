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

data Sig
  = SVar Name
  | SPiI Sig (Bind Sig)
  | SAppI Sig (Bind Sig) Sig Sig -- app A (x.B) t u
  | SPiNI Tm (Bind Sig)
  | SAppNI Sig Tm
  | SPiSNI Tm (Bind Sig)
  | SAppSNI Tm (Bind Sig) Sig Tm
  | SId Sig Sig Sig                        -- Id A t u
  | SJ Sig Sig (Bind2 Sig) Sig Sig Sig  -- J A t P pr u eq
  | SRefl Sig Sig
  | SU
  | SEl Sig

data SVal
  = SVVar Name
  | SVPiI SVal (Bind (SVal → SVal))
  | SVAppI SVal (Bind (SVal → SVal)) SVal ~SVal
  | SVPiNI Val (Bind (Val → SVal))
  | SVAppNI SVal ~Val
  | SVPiSNI Val (Bind (Val → SVal))
  | SVAppSNI Val (Bind (Val → SVal)) SVal ~Val
  | SVId SVal SVal SVal                                       -- Id A t u
  | SVJ SVal SVal (Bind2 (SVal → SVal → SVal)) SVal SVal SVal  -- J A t P pr u eq
  | SVRefl SVal SVal
  | SVU
  | SVEl SVal

--------------------------------------------------------------------------------

instance IsString Tm    where fromString = Var
instance IsString Val   where fromString = VVar
instance IsString Sig  where fromString = SVar
instance IsString SVal  where fromString = SVVar

pattern Lam' x t = Lam (x, t)
pattern Pi' x a b = Pi a (x, b)

infixl 8 ∙
(∙) = App
infixr 4 ==>
(==>) = Pi' "_"

type Elab = Either String
type Vals = Sub (Maybe (Either Val SVal))

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

pattern Apd ∷ Tm → Tm → Tm
pattern Apd f eq ←
  ((\case J (Lam' y (Lam' p (Id _ (Tr b (Var p') (App f t)) (App f' (Var y')))))
            (Refl _) eq | y == y', p == p', show f == show f',
                          all (not . freeIn y) [b, t, f],
                          all (not . freeIn p) [b, t, f]
                          → Just (f, eq)
          _ → Nothing) → Just (f, eq))

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

type Types = Sub (Either Val SVal)

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

-- Evaluating signatures
--------------------------------------------------------------------------------

evalBindS ∷ Vals → Bind Sig → Bind (SVal → SVal)
evalBindS vs (x, t) = (x, \u → evalS ((x, Just (Right u)):vs) t)

evalBindᵛS ∷ Vals → Bind Sig → Bind (Val → SVal)
evalBindᵛS vs (x, t) = (x, \u → evalS ((x, Just (Left u)):vs) t)

evalSJ ∷ Vals → Sig → Sig → Bind2 Sig → Sig → Sig → Sig → SVal
evalSJ vs a t (ux, eqx, p) pr u eq = case evalS vs eq of
  SVRefl _ _ → evalS vs pr
  eq         → SVJ (evalS vs a) (evalS vs t)
                 (ux, eqx, \u eq → evalS ((eqx, Just (Right eq)):(ux, Just (Right u)):vs) p)
                 (evalS vs pr) (evalS vs u) eq

evalS ∷ Vals → Sig → SVal
evalS vs = \case
  SVar x           → maybe (SVVar x) (either (error "impossible") id) $ lookup' x vs
  SPiI a b         → SVPiI (evalS vs a) (evalBindS vs b)
  SAppI a b t u    → SVAppI (evalS vs a) (evalBindS vs b) (evalS vs t) (evalS vs u)
  SPiNI a b        → SVPiNI (eval vs a) (evalBindᵛS vs b)
  SAppNI t u       → SVAppNI (evalS vs t) (eval vs u)
  SPiSNI a b       → SVPiSNI (eval vs a) (evalBindᵛS vs b)
  SAppSNI a b t u  → SVAppSNI (eval vs a) (evalBindᵛS vs b) (evalS vs t) (eval vs u)
  SId a t u        → SVId (evalS vs a) (evalS vs t) (evalS vs u)
  SJ a t p pr u eq → evalSJ vs a t p pr u eq
  SRefl a t        → SVRefl (evalS vs a) (evalS vs t)
  SU               → SVU
  SEl t            → SVEl (evalS vs t)

convBindS ∷ Vals → Bind (SVal → SVal) → Bind (SVal → SVal) → Bool
convBindS vs (fresh vs → x, t) (_, t') = convS ((x, Nothing):vs) (t (SVVar x)) (t' (SVVar x))

convBindᵛS ∷ Vals → Bind (Val → SVal) → Bind (Val → SVal) → Bool
convBindᵛS vs (fresh vs → x, t) (_, t') = convS ((x, Nothing):vs) (t (VVar x)) (t' (VVar x))

convSVJ ∷ Vals → Bind2 (SVal -> SVal -> SVal) → SVal → SVal
               → Bind2 (SVal -> SVal -> SVal) → SVal → SVal
               → Bool
convSVJ vs (fresh vs → x, fresh ((x, Nothing):vs) → y, p) pr eq (_, _, p') pr' eq' =
  convS ((y, Nothing):(x, Nothing):vs) (p (SVVar x) (SVVar y)) (p' (SVVar x) (SVVar y))
  && convS vs pr pr' && convS vs eq eq'

convS ∷ Vals → SVal → SVal → Bool
convS vs t t' = case (t, t') of
  (SVVar x           , SVVar x')             → x == x'
  (SVPiI a b         , SVPiI a' b')          → convS vs a a' && convBindS vs b b'
  (SVAppI _ _ t u    , SVAppI _ _ t' u')     → convS vs t t' && convS vs u u'
  (SVPiNI a b        , SVPiNI a' b')         → conv  vs a a' && convBindᵛS vs b b'
  (SVAppNI t u       , SVAppNI t' u')        → convS vs t t' && conv vs u u'
  (SVPiSNI a b       , SVPiSNI a' b')        → conv  vs a a' && convBindᵛS vs b b'
  (SVAppSNI _ _ t u  , SVAppSNI _ _ t' u')   → convS vs t t' && conv vs u u'
  (SVId _ t u        , SVId _ t' u')         → convS vs t t' && convS vs u u'
  (SVJ _ _ p pr _ eq , SVJ _ _ p' pr' _ eq') → convSVJ vs p pr eq p' pr' eq'
  (SVRefl _ t        , SVRefl _ t')          → convS vs t t'
  (SVU               , SVU)                  → True
  (SVEl t            , SVEl t')              → convS vs t t'
  _                                          → False

quoteBindS ∷ Vals → Bind (SVal → SVal) → Bind Sig
quoteBindS vs (fresh vs → x, t) = (x, quoteS ((x, Nothing):vs) (t (SVVar x)))

quoteBindᵛS ∷ Vals → Bind (Val → SVal) → Bind Sig
quoteBindᵛS vs (fresh vs → x, t) = (x, quoteS ((x, Nothing):vs) (t (VVar x)))

quoteSJV ∷ Vals → SVal → SVal
        → Bind2 (SVal → SVal → SVal) → SVal → SVal → SVal → Sig
quoteSJV vs a t (fresh vs → x, fresh ((x, Nothing):vs) → y, p) pr u eq =
  SJ (quoteS vs a) (quoteS vs t)
     (x, y, quoteS ((y, Nothing):(x,Nothing):vs) (p (SVVar x) (SVVar y)))
  (quoteS vs pr) (quoteS vs u) (quoteS vs eq)

quoteS ∷ Vals → SVal → Sig
quoteS vs = \case
  SVVar x           → SVar x
  SVPiI a b         → SPiI (quoteS vs a) (quoteBindS vs b)
  SVAppI a b t u    → SAppI (quoteS vs a) (quoteBindS vs b) (quoteS vs t) (quoteS vs u)
  SVPiNI a b        → SPiNI (quote vs a) (quoteBindᵛS vs b)
  SVAppNI t u       → SAppNI (quoteS vs t) (quote vs u)
  SVPiSNI a b       → SPiSNI (quote vs a) (quoteBindᵛS vs b)
  SVAppSNI a b t u  → SAppSNI (quote vs a) (quoteBindᵛS vs b) (quoteS vs t) (quote vs u)
  SVId a t u        → SId (quoteS vs a) (quoteS vs t) (quoteS vs u)
  SVJ a t p pr u eq → quoteSJV vs a t p pr u eq
  SVRefl a t        → SRefl (quoteS vs a) (quoteS vs t)
  SVU               → SU
  SVEl t            → SEl (quoteS vs t)

renderSig ∷ Sig → Tm
renderSig = go where
  go = \case
    SVar x           → Var x
    SPiI a b         → Pi (go a) (go <$> b)
    SAppI a b t u    → App (go t) (go u)
    SPiNI a b        → Pi a (go <$> b)
    SAppNI t u       → App (go t) u
    SPiSNI a b       → Pi a (go <$> b)
    SAppSNI a b t u  → App (go t) u
    SId a t u        → Id (Just (go a)) (go t) (go u)
    SJ a t (x, y, p) pr u eq → J (Lam' x $ Lam' y $ go p) (go pr) (go eq)
    SRefl a t        → Refl (Just (go t))
    SU               → U
    SEl t            → App "El" (go t)

instance Show Sig where show = show . renderSig

nfS ∷ Vals → Sig → Sig
nfS vs = quoteS vs . evalS vs

-- Algebras
--------------------------------------------------------------------------------

a1 ∷ Bind Sig → Tm
a1 (x, t) = Lam' x (alg t)

a2 ∷ Bind2 Sig → Tm
a2 (x, y, t) = Lam' x $ Lam' y (alg t)

alg ∷ Sig → Tm
alg = \case
  SVar x           → Var x
  SPiI a (x, b)    → Pi (alg a) (x, alg b)
  SAppI _ _ t u    → App (alg t) (alg u)
  SPiNI a (x, b)   → Pi a (x, alg b)
  SAppNI t u       → App (alg t) u
  SPiSNI a (x, b)  → Pi a (x, alg b)
  SAppSNI _ _ t u  → App (alg t) u
  SId a t u        → Id (Just (alg a)) (alg t) (alg u)
  SRefl a t        → Refl (Just (alg t))
  SU               → U
  SEl t            → alg t
  SJ a t p pr u eq → J (a2 p) (alg pr) (alg eq)

-- Elaborate to Sig
--------------------------------------------------------------------------------

checkS ∷ Types → Vals → Tmᴾ → SVal → Elab Sig
checkS ts vs (updPos → (pos, t)) a = do
  (t, a') ← inferS ts vs (pos, t)
  unless (convS vs a a') $
    reportError ("type mismatch\n\nexpected type:\n\n  "
                   ++ show (quoteS vs a)
                   ++ "\n\ninferred type:\n\n  " ++ show (quoteS vs a')
                   ++ "\n\nwhen checking:\n\n  "
                   ++ show t)
  pure t

checkTypeS ∷ Types → Vals → Tmᴾ → Elab Sig
checkTypeS ts vs (updPos → (pos, t)) = case t of
  Piᴾ x a b → do
    case check ts vs a VU of
      Left _ → do
        a ← checkS ts vs a SVU
        let ~a' = evalS vs a
        x ← elabBinder vs (Just (alg a)) x
        b ← checkTypeS ((x, Right (SVEl a')):ts) ((x, Nothing):vs) b
        pure (SPiI a (x, b))
      Right a → do
        let ~a' = eval vs a
        x ← elabBinder vs (Just a) x
        b ← checkTypeS ((x, Left a'):ts) ((x, Nothing):vs) b
        pure (SPiNI a (x, b))
  Uᴾ → pure SU
  t  → SEl <$> checkS ts vs (pos, t) SVU

inferS ∷ Types → Vals → Tmᴾ → Elab (Sig, SVal)
inferS ts vs (updPos → (pos, t)) = case t of
  Varᴾ x → do
    when (x == "_") $ reportError "can't use _ as identifier"
    case lookup x ts of
      Just (Right a) → pure (SVar x, a)
      Just (Left a)  →
        reportError ("expected inductive type for variable "
                      ++ x ++ ", inferred type:\n\n  " ++ show (quote vs a))
      _ → reportError ("variable not in scope: " ++ x)
  Appᴾ t u → do
    (t, tty) ← inferS ts vs t
    case tty of
      SVPiI a b → do
        u ← checkS ts vs u (SVEl a)
        let ~u' = evalS vs u
        pure (SAppI (quoteS vs a) (quoteBindS vs b) t u, snd b u')
      SVPiNI a b → do
        u ← check ts vs u a
        pure (SAppNI t u, snd b (eval vs u))
      SVEl (SVPiSNI a b) → do
        u ← check ts vs u a
        pure (SAppSNI (quote vs a) (quoteBindᵛS vs b) t u, SVEl (snd b (eval vs u)))
      _ → reportError
          ("expected a function type for:\n\n  " ++
           show t ++ "\n\ninferrred type:\n\n  " ++ show (quoteS vs tty))
  tp@Lamᴾ{} → reportError ("Can't infer type for lambda expression: " ++ show tp)
  Piᴾ x a b → do
    a ← check ts vs a VU
    x ← elabBinder vs (Just a) x
    b ← checkS ((x, Left (eval vs a)):ts) ((x, Nothing):vs) b SVU
    pure (SPiSNI a (x, b), SVU)
  Idᴾ t u → do
    (t, a) ← inferS ts vs t
    case a of
      SVEl a → do
        u ← checkS ts vs u (SVEl a)
        pure (SId (quoteS vs a) t u, SVU)
      _ → reportError
          ("expected a small type for\n\n"++ show t
            ++ "\n\ngot\n\n" ++ show (quoteS vs a))
  Jᴾ (_, Lamᴾ ux (_, Lamᴾ eqx p)) pr eq → do
    checkShadowing vs ux
    checkShadowing ((ux, Nothing):vs) eqx
    (eq, eqty) ← inferS ts vs eq
    case eqty of
      SVEl (SVId a t u) → do
        p ← checkS ((eqx, Right (SVEl (SVId a t (SVVar ux)))):(ux, Right (SVEl a)):ts)
                   ((eqx, Nothing):(ux, Nothing):vs) p SVU
        pr ← checkS ts vs pr
               (SVEl (evalS ((eqx, Just (Right (SVRefl a t))):(ux, Just (Right t)):vs) p))
        pure (SJ (quoteS vs a) (quoteS vs t) (ux, eqx, p) pr (quoteS vs u) eq,
              (SVEl (evalS ((eqx, Just (Right (evalS vs eq))):(ux, Just (Right u)):vs) p)))
      _ → reportError ("expected equality type for\n\n" ++ show eq
                       ++ "\n\ngot\n\n" ++ show (quoteS vs eqty))
  Reflᴾ t → do
    (t, a) ← inferS ts vs t
    case a of
      SVEl a → do
        let ~t' = evalS vs t
        pure (SRefl (quoteS vs a) t, SVEl (SVId a t' t'))
      _ → reportError
            ("expected a small type for\n\n"++ show t
             ++ "\n\ngot\n\n" ++ show (quoteS vs a))
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

-- Displayed algebras
--------------------------------------------------------------------------------

class M a b | a → b, b → a where m ∷ a → b

instance M Name Name where m = (++ "ᴰ")

m1 ∷ Bind Sig → Tm
m1 (x, t) = Lam' x $ Lam' (m x) (m t)

m2 ∷ Bind2 Sig → Tm
m2 (x, y, t) = Lam' x $ Lam' (m x) $ Lam' y $ Lam' (m y) (m t)

mj ∷ Tm → Tm → Tm → Tm → Tm → Tm →
     Tm → Tm → Tm → Tm → Tm → Tm → Tm
mj a aᴹ t tᴹ p pᴹ pr prᴹ u uᴹ eq eqᴹ =
  J (LAM_(uᴹ) LAM_(eqᴹ) pᴹ ∙ u ∙ uᴹ ∙ eq ∙ eqᴹ ∙ J p pr eq)
    (J (LAM_(u) LAM_(eq) pᴹ ∙ u ∙ tr aᴹ eq tᴹ ∙ eq ∙ Refl' ∙ J p pr eq)
       prᴹ eq)
    eqᴹ

instance M Sig Tm where
  m = \case
    SVar x           → Var (m x)
    SPiI a (x, b)    → LAM_(f) Pi' x (alg a) $ Pi' (m x) (m a ∙ Var x) $ m b ∙ (f ∙ Var x)
    SAppI _ _ t u    → m t ∙ alg u ∙ m u
    SPiNI a (x, b)   → LAM_(f) Pi' x a $ m b ∙ (f ∙ Var x)
    SAppNI t u       → m t ∙ u
    SPiSNI a (x, b)  → LAM_(f) Pi' x a $ m b ∙ (f ∙ Var x)
    SAppSNI _ _ t u  → m t ∙ u
    SId a t u        → LAM_(eq) Id' (tr (m a) eq (m t)) (m u)
    SRefl _ t        → Refl'
    SU               → LAM_(a) (a ==> U)
    SEl t            → m t
    SJ a t p pr u eq → mj (alg a) (m a) (alg t) (m t) (a2 p) (m2 p)
                          (alg pr) (m pr) (alg u) (m u) (alg eq) (m eq)

class E a b | a → b, b → a where e ∷ a → b

e1 ∷ Bind Sig → Tm
e1 (x, t) = Lam' x $ Lam' (m x) $ Lam' (e x) (e t)

e2 ∷ Bind2 Sig → Tm

e2 (x, y, t) = Lam' x $ Lam' (m x) $ Lam' (e x) $ Lam' y $ Lam' (m y) $ Lam' (e y) (e t)

-- Displayed algebras sections
--------------------------------------------------------------------------------
instance E Name Name where e = (++"ˢ")

eSAppI a aᴹ aᴱ b bᴹ bᴱ t tᴹ tᴱ u uᴹ uᴱ =
  J (LAM_(uᴹ) LAM_(uᴱ) bᴱ ∙ u ∙ uᴹ ∙ uᴱ ∙ (t ∙ u) ∙ (tᴹ ∙ u ∙ uᴹ)) (tᴱ ∙ u) uᴱ

eSAppSNI a b bᴹ bᴱ t tᴹ tᴱ u =
  ap (LAM_(f) f ∙ u) (LAM_(u) bᴱ ∙ u ∙ (t ∙ u)) tᴹ tᴱ

eSId a aᴹ aᴱ t tᴹ tᴱ u uᴹ uᴱ =
  (LAM_(e) tr
    (LAM_(xᴹ) Id' (tr aᴹ e xᴹ) uᴹ)
    tᴱ
    (tr (LAM_(yᴹ) Id' (tr aᴹ e (aᴱ ∙ t)) yᴹ) uᴱ (apd aᴹ aᴱ t e)))

eSRefl a aᴹ aᴱ t tᴹ tᴱ =
  (J (LAM_(xᴹ) LAM_(xᴱ)
      Id'
      (tr (LAM_(yᴹ) Id' yᴹ xᴹ) xᴱ
        (tr (LAM_(yᴹ) Id' (aᴱ ∙ t) yᴹ) xᴱ Refl'))
      Refl')
     Refl'
     tᴱ)

-- | Sig generated with AgdaToHsUtils.hs
eSJ ∷ Tm → Tm → Tm → Tm → Tm → Tm
    → Tm → Tm → Tm → Tm → Tm → Tm
    → Tm → Tm → Tm → Tm → Tm → Tm
    → Tm
eSJ a aᴰ aˢ t tᴰ tˢ p pᴰ pˢ pr prᴰ prˢ u uᴰ uˢ eq eqᴰ eqˢ =
  J (Lam' "eqᴰ₁'" (Lam' "eqˢ₁'" (Id' (pˢ ∙ u ∙ uᴰ ∙ uˢ ∙ eq ∙ "eqᴰ₁'"
  ∙ "eqˢ₁'" ∙ (J p pr eq)) (J (Lam' "xᴰ'" (Lam' "zᴰ'" (pᴰ ∙ u ∙ "xᴰ'"
  ∙ eq ∙ "zᴰ'" ∙ (J p pr eq)))) (J (Lam' "x'" (Lam' "z'" (pᴰ ∙ "x'" ∙
  (J (Lam' "u₁'" (Lam' "p₁'" (aᴰ ∙ "u₁'"))) tᴰ "z'") ∙ "z'" ∙ Refl' ∙
  (J p pr "z'")))) prᴰ eq) "eqᴰ₁'")))) (J (Lam' "uᴰ₁'" (Lam' "uˢ₁'"
  (Id' (pˢ ∙ u ∙ "uᴰ₁'" ∙ "uˢ₁'" ∙ eq ∙ (J (Lam' "u₁'" (Lam' "p₁'"
  (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴰ ∙ "u₂'"))) "u₁'" eq) "uᴰ₁'")))
  (J (Lam' "u₁'" (Lam' "p₁'" (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴰ ∙
  "u₂'"))) (aˢ ∙ t) eq) "u₁'"))) (J (Lam' "y'" (Lam' "p₁'" (Id' (J
  (Lam' "u₁'" (Lam' "p₂'" (aᴰ ∙ "u₁'"))) (aˢ ∙ t) "p₁'") (aˢ ∙
  "y'")))) Refl' eq) "uˢ₁'") tˢ) ∙ Refl' ∙ (J p pr eq)) (J (Lam' "xᴰ'"
  (Lam' "zᴰ'" (pᴰ ∙ u ∙ "xᴰ'" ∙ eq ∙ "zᴰ'" ∙ (J p pr eq)))) (J (Lam'
  "x'" (Lam' "z'" (pᴰ ∙ "x'" ∙ (J (Lam' "u₁'" (Lam' "p₁'" (aᴰ ∙
  "u₁'"))) tᴰ "z'") ∙ "z'" ∙ Refl' ∙ (J p pr "z'")))) prᴰ eq) (J (Lam'
  "u₁'" (Lam' "p₁'" (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴰ ∙ "u₂'")))
  "u₁'" eq) "uᴰ₁'"))) (J (Lam' "u₁'" (Lam' "p₁'" (Id' (J (Lam' "u₂'"
  (Lam' "p₂'" (aᴰ ∙ "u₂'"))) (aˢ ∙ t) eq) "u₁'"))) (J (Lam' "y'" (Lam'
  "p₁'" (Id' (J (Lam' "u₁'" (Lam' "p₂'" (aᴰ ∙ "u₁'"))) (aˢ ∙ t) "p₁'")
  (aˢ ∙ "y'")))) Refl' eq) "uˢ₁'") tˢ))))) (J (Lam' "u₁'" (Lam' "eq₁'"
  (Id' (pˢ ∙ "u₁'" ∙ (aˢ ∙ "u₁'") ∙ Refl' ∙ "eq₁'" ∙ (J (Lam' "u₂'"
  (Lam' "p₁'" (Id' (J (Lam' "u₃'" (Lam' "p₂'" (aᴰ ∙ "u₃'"))) "u₂'"
  "eq₁'") (aˢ ∙ "u₁'")))) (J (Lam' "y'" (Lam' "p₁'" (Id' (J (Lam'
  "u₂'" (Lam' "p₂'" (aᴰ ∙ "u₂'"))) (aˢ ∙ t) "p₁'") (aˢ ∙ "y'"))))
  Refl' "eq₁'") tˢ) ∙ Refl' ∙ (J p pr "eq₁'")) (J (Lam' "xᴰ'" (Lam'
  "zᴰ'" (pᴰ ∙ "u₁'" ∙ "xᴰ'" ∙ "eq₁'" ∙ "zᴰ'" ∙ (J p pr "eq₁'")))) (J
  (Lam' "x'" (Lam' "z'" (pᴰ ∙ "x'" ∙ (J (Lam' "u₂'" (Lam' "p₁'" (aᴰ ∙
  "u₂'"))) tᴰ "z'") ∙ "z'" ∙ Refl' ∙ (J p pr "z'")))) prᴰ "eq₁'") (J
  (Lam' "u₂'" (Lam' "p₁'" (Id' (J (Lam' "u₃'" (Lam' "p₂'" (aᴰ ∙
  "u₃'"))) "u₂'" "eq₁'") (aˢ ∙ "u₁'")))) (J (Lam' "y'" (Lam' "p₁'"
  (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴰ ∙ "u₂'"))) (aˢ ∙ t) "p₁'") (aˢ ∙
  "y'")))) Refl' "eq₁'") tˢ))))) (J (Lam' "tᴰ₁'" (Lam' "tˢ₁'" (Pi'
  "pᴰ₁'" (Pi' "x'" a (Pi' "xᴰ'" (aᴰ ∙ "x'") (Pi' "z'" (Id' t "x'")
  ((Id' (J (Lam' "u₁'" (Lam' "p₁'" (aᴰ ∙ "u₁'"))) "tᴰ₁'" "z'") "xᴰ'")
  ==> (p ∙ "x'" ∙ "z'") ==> U)))) (Pi' "pˢ₁'" (Pi' "x'" a (Pi' "xᴰ'"
  (aᴰ ∙ "x'") (Pi' "xˢ'" (Id' (aˢ ∙ "x'") "xᴰ'") (Pi' "z'" (Id' t
  "x'") (Pi' "zᴰ'" (Id' (J (Lam' "u₁'" (Lam' "p₁'" (aᴰ ∙ "u₁'")))
  "tᴰ₁'" "z'") "xᴰ'") ((Id' (J (Lam' "u₁'" (Lam' "p₁'" (Id' (J (Lam'
  "u₂'" (Lam' "p₂'" (aᴰ ∙ "u₂'"))) "u₁'" "z'") "xᴰ'"))) (J (Lam' "u₁'"
  (Lam' "p₁'" (Id' (J (Lam' "u₂'" (Lam' "p₂'" (aᴰ ∙ "u₂'"))) (aˢ ∙ t)
  "z'") "u₁'"))) (J (Lam' "y'" (Lam' "p₁'" (Id' (J (Lam' "u₁'" (Lam'
  "p₂'" (aᴰ ∙ "u₁'"))) (aˢ ∙ t) "p₁'") (aˢ ∙ "y'")))) Refl' "z'")
  "xˢ'") "tˢ₁'") "zᴰ'") ==> Pi' "x₁'" (p ∙ "x'" ∙ "z'") ("pᴰ₁'" ∙ "x'"
  ∙ "xᴰ'" ∙ "z'" ∙ "zᴰ'" ∙ "x₁'"))))))) (Pi' "prᴰ₁'" ("pᴰ₁'" ∙ t ∙
  "tᴰ₁'" ∙ Refl' ∙ Refl' ∙ pr) ((Id' ("pˢ₁'" ∙ t ∙ "tᴰ₁'" ∙ "tˢ₁'" ∙
  Refl' ∙ Refl' ∙ (J (Lam' "xᴰ'" (Lam' "xˢ'" (Id' (J (Lam' "u₁'" (Lam'
  "p₁'" (Id' "u₁'" "xᴰ'"))) (J (Lam' "u₁'" (Lam' "p₁'" (Id' (aˢ ∙ t)
  "u₁'"))) Refl' "xˢ'") "xˢ'") Refl'))) Refl' "tˢ₁'") ∙ pr) "prᴰ₁'")
  ==> Id' ("pˢ₁'" ∙ t ∙ (aˢ ∙ t) ∙ Refl' ∙ Refl' ∙ (J (Lam' "u₁'"
  (Lam' "p₁'" (Id' "u₁'" (aˢ ∙ t)))) Refl' "tˢ₁'") ∙ Refl' ∙ pr) (J
  (Lam' "xᴰ'" (Lam' "zᴰ'" ("pᴰ₁'" ∙ t ∙ "xᴰ'" ∙ Refl' ∙ "zᴰ'" ∙ pr)))
  "prᴰ₁'" (J (Lam' "u₁'" (Lam' "p₁'" (Id' "u₁'" (aˢ ∙ t)))) Refl'
  "tˢ₁'")))))))) (Lam' "pᴰ₁'" (Lam' "pˢ₁'" (Lam' "prᴰ₁'" (Lam' "prˢ₁'"
  "prˢ₁'")))) tˢ ∙ pᴰ ∙ pˢ ∙ prᴰ ∙ prˢ) eq) uˢ) eqˢ

instance E Sig Tm where
  e = \case
    SVar x → Var (e x)

    SPiI a (x, b) →
      LAM_(f) LAM_(fᴹ)
        Pi' x (alg a)
          ((Lam' (m x) $ Lam' (e x) $ e b)
            ∙ (e a ∙ Var x)
            ∙ Refl'
            ∙ (f ∙ Var x)
            ∙ (fᴹ ∙ Var x ∙ (e a ∙ Var x)))

    SPiNI a (x, b)  → LAM_(f) LAM(fᴹ) Pi' x a (e b ∙ (f ∙ Var x) ∙ (fᴹ ∙ Var x))
    SPiSNI a (x, b) → LAM_(f) Lam' x (e b ∙ (f ∙ Var x))

    SAppI a b t u    → eSAppI (alg a) (m a) (e a) (a1 b) (m1 b) (e1 b)
                              (alg t) (m t) (e t) (alg u) (m u) (e u)
    SAppNI t u       → e t ∙ u
    SAppSNI a b t u  → eSAppSNI a (a1 b) (m1 b) (e1 b) (alg t) (m t) (e t) u

    SId a t u        → eSId (alg a) (m a) (e a) (alg t) (m t) (e t) (alg u) (m u) (e u)
    SRefl a t        → eSRefl (alg a) (m a) (e a) (alg t) (m t) (e t)
    SU               → LAM_(a) LAM_(aᴹ) PI_(x, a) (aᴹ ∙ x)
    SEl a            → LAM_(t) LAM_(tᴹ) Id' (e a ∙ t) tᴹ
    SJ a t p pr u eq → eSJ (alg a)  (m a)  (e a)
                           (alg t)  (m t)  (e t)
                           (a2 p) (m2 p) (e2 p)
                           (alg pr) (m pr) (e pr)
                           (alg u)  (m u)  (e u)
                           (alg eq) (m eq) (e eq)


--------------------------------------------------------------------------------

elabInp ∷ (Sub Tmᴾ, Sub Tmᴾ) → Elab (Sub Tm, Sub Sig)
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
                     t ← evalS vs <$> checkTypeS ts vs t
                     pure ((x, Right t):ts, (x, Nothing):vs, (x, quoteS vs t):cs))
                 (ts, vs, []) ind
  pure (ns, cs)

genElims ∷ (Sub Tmᴾ, Sub Tmᴾ) → Elab (Sub Tm, Sub Tm)
genElims (nonind, ind) = do
  (ns, cs) ← elabInp (nonind, ind)
  let cs' = foldr
              (\(x, t) acc → (e x, e t ∙ Var x ∙ Var (m x)):(m x, m t ∙ Var x):(x, alg t):acc)
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
            putStrLn "  -- External context:"
            putStrLn $ renderCxt (reverse ns)
          putStrLn "  -- Algebras"
          putStrLn $ renderCxt (reverse cs)
          putStrLn "  -- Displayed algebras"
          putStrLn $ renderCxt (reverse ms)
          putStrLn "  -- Displayed algebra sections"
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
