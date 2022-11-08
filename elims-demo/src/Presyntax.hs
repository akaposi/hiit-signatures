{-# language UnicodeSyntax, LambdaCase, TupleSections, ViewPatterns, Strict,
    PartialTypeSignatures #-}
{-# options_ghc -Wincomplete-patterns -Wno-partial-type-signatures #-}

module Presyntax (
    Name
  , Tmᴾ
  , Tmᴾ'(..)
  , parseTmᴾ
  , parseInput
  , Posed
  ) where

import Control.Monad
import Data.List
import Data.Void

import qualified Data.HashSet               as HS

import           Text.Megaparsec
import qualified Text.Megaparsec.Char  as C
import qualified Text.Megaparsec.Char.Lexer as L

--------------------------------------------------------------------------------

type Name = String
type Tmᴾ  = (SourcePos, Tmᴾ')

data Tmᴾ'
  = Varᴾ Name
  | Appᴾ Tmᴾ Tmᴾ
  | Lamᴾ Name Tmᴾ
  | Piᴾ Name Tmᴾ Tmᴾ
  | Reflᴾ Tmᴾ
  | Jᴾ Tmᴾ Tmᴾ Tmᴾ
  | Idᴾ Tmᴾ Tmᴾ
  | Uᴾ

-- Parser
--------------------------------------------------------------------------------

type Parser = Parsec Void String

sc ∷ Parser ()
sc = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme = L.lexeme sc
symbol = L.symbol sc
char c = lexeme (C.char c)

parens p   = lexeme (char '(' *> p <* char ')')
keywords   = HS.fromList ["assume", "constructors", "refl", "J", "Id", "U"]
keychars   = "ᴱᴹ'" ∷ String

pIdent = try $ lexeme $ do
  w ← some C.alphaNumChar
  when (HS.member w keywords) $
    fail ("can't use keyword for identifier: " ++ w)
  forM_ w $ \c → when (elem c keychars) $ fail ("Can't use reserved character: " ++ [c])
  pure w

type Posed a = (SourcePos, a)

withPos ∷ Parser a → Parser (Posed a)
withPos p = (,) <$> getSourcePos <*> p

pBind    = pIdent <|> symbol "_"
pVar     = withPos (Varᴾ <$> pIdent)
pU       = withPos (Uᴾ <$ char 'U')

pLam ∷ Parser Tmᴾ
pLam = withPos $ do
  char 'λ' <|> char '\\'
  binders ← some (withPos pBind)
  symbol "→" <|> symbol "->"
  t ← pTm
  pure $ snd $ foldr (\(p, x) u → (p, Lamᴾ x u)) t binders

pSpine ∷ Parser Tmᴾ
pSpine = withPos $ do
  head  ← pAtom
  spine ← many (withPos pAtom)
  pure $ snd $ foldl' (\t (p, u) → (p, Appᴾ t u)) head spine

pPiBinder ∷ Parser (Posed ([Posed Name], Tmᴾ))
pPiBinder = withPos (parens ((,) <$> some (withPos pBind) <*> (char ':' *> pTm)))

pPi ∷ Parser Tmᴾ
pPi = withPos $ do
  dom ← try (Right <$> some pPiBinder) <|> (Left <$> pSpine)
  symbol "→" <|> symbol "->"
  b ← pTm
  case dom of
    Right binders → do
      pure $ snd $ foldr (\(p, (xs, a)) b → foldr (\(p, x) b → (p, Piᴾ x a b)) b xs) b binders
    Left dom → do
      pure (Piᴾ "_" dom b)

pRefl ∷ Parser Tmᴾ
pRefl = withPos ((Reflᴾ <$ symbol "refl") <*> pTm)

pId ∷ Parser Tmᴾ
pId = withPos ((Idᴾ <$ symbol "Id") <*> pAtom <*> pAtom)

pJmotive ∷ Parser Tmᴾ
pJmotive = do
  char '('
  (px, x) ← withPos (pBind <* char '.')
  (py, y) ← withPos (pBind <* char '.')
  (pt, t) ← pTm
  char ')'
  pure (px, Lamᴾ x (py, Lamᴾ y (pt, t)))

pJ ∷ Parser Tmᴾ
pJ = withPos ((Jᴾ <$ symbol "J") <*> pJmotive <*> pAtom <*> pAtom)

pAtom ∷ Parser Tmᴾ
pAtom = pVar <|> pU <|> pId <|> pRefl <|> pJ <|> parens pTm

pTm ∷ Parser Tmᴾ
pTm = try pPi <|> pSpine <|> pLam

pInput ∷ Parser ([(Name, Tmᴾ)], [(Name, Tmᴾ)])
pInput = do
  meta ← optional $ do
    symbol "assume"
    many ((,) <$> pIdent <*> (char ':' *> pTm <* char ';'))
  symbol "constructors"
  cs   ← many ((,) <$> pIdent <*> (char ':' *> pTm <* char ';'))
  pure (maybe [] id meta, cs)

parseTmᴾ ∷ String → String → Either _ Tmᴾ
parseTmᴾ = parse (sc *> pTm <* eof)

parseInput ∷ String → String → Either _ ([(Name, Tmᴾ)], [(Name, Tmᴾ)])
parseInput = parse (sc *> pInput <* eof)

--------------------------------------------------------------------------------

tmᴾ'toAgda :: Int → Tmᴾ' → ShowS
tmᴾ'toAgda prec = go (prec /= 0) where

  goLam ∷ Tmᴾ' → ShowS
  goLam (Lamᴾ x (snd → t)) = (' ':)   . (x++) . goLam t
  goLam t                  = (" → "++) . go False t

  goPi ∷ Bool → Tmᴾ' → ShowS
  goPi p (Piᴾ x (snd → a) (snd → b))
    | x /= "_" = ('(':) . (x++) . (" : "++) . go False a . (')':) . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of Piᴾ{} → True; _ → False) a .
       (" → "++) . go False b
  goPi p t = (if p then (" → "++) else id) . go False t

  go ∷ Bool → Tmᴾ' → ShowS
  go p = \case
    Varᴾ x → (x++)
    Appᴾ (snd → Appᴾ (snd → t) (snd → u)) (snd → u') →
      showParen p (go False t . (' ':) . go True u . (' ':) . go True u')
    Appᴾ (snd → t) (snd → u) → showParen p (go True t . (' ':) . go True u)
    Lamᴾ x (snd → t)  → showParen p (("λ "++) . (x++) . goLam t)
    Piᴾ x a b → showParen p (goPi False (Piᴾ x a b))
    Reflᴾ (snd → t) → showParen p (("refl "++) . go True t)
    Jᴾ (snd → p') (snd → pr) (snd → eq) →
      showParen p (("J "++) . go True p' . (' ':) . go True pr . (' ':) . go True eq)
    Idᴾ (snd → t) (snd → u) → showParen p (("Id "++). go True t . (' ':) . go True u)
    Uᴾ → ('U':)

instance Show Tmᴾ' where showsPrec = tmᴾ'toAgda
