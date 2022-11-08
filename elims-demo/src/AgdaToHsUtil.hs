{-# language UnicodeSyntax, LambdaCase,
    TupleSections, ViewPatterns, Strict,
    PatternSynonyms, PartialTypeSignatures #-}

{-# options_ghc -Wincomplete-patterns -Wno-partial-type-signatures #-}

{-| Parse a small Agda subset. Only lambdas, J, Id, refl and Set are parsed.
    No implicit functions and applications.

    The purpose of this module is to convert the shallow Agda formalization of the
    eliminator translation into embedded Haskell implementation.
-}

module AgdaToHsUtil (
  agdaToTmᴾ
  ) where

import Control.Applicative hiding (some, many)
import Control.Monad
import Data.List
import Data.Void
import Data.Char

import qualified Data.HashSet as HS

import           Text.Megaparsec
import qualified Text.Megaparsec.Char  as C
import qualified Text.Megaparsec.Char.Lexer as L

import Presyntax

-- Parser
--------------------------------------------------------------------------------

type Parser = Parsec Void String

sc ∷ Parser ()
sc = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme   = L.lexeme sc
symbol   = L.symbol sc
char c   = lexeme (C.char c)
parens p = lexeme (char '(' *> p <* char ')')
pIdent   = try $ lexeme $ some C.alphaNumChar

withPos ∷ Parser a → Parser (Posed a)
withPos p = (,) <$> getSourcePos <*> p

pBind    = pIdent <|> symbol "_"
pVar     = withPos (Varᴾ <$> pIdent)
pSet     = withPos (Uᴾ <$ symbol "Set")

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

pAtom ∷ Parser Tmᴾ
pAtom = pSet <|> pVar <|> parens pTm

pTm ∷ Parser Tmᴾ
pTm = pLam <|> try pPi <|> pSpine

agdaToTmᴾ ∷ String -> Either _ Tmᴾ
agdaToTmᴾ = parse pTm ""

--------------------------------------------------------------------------------

infixl 6 :∙
pattern (:∙) t u   ← Appᴾ (_, t) (_, u)
pattern Lamᴾ' x t  ← Lamᴾ x (_, t)
pattern Piᴾ' x a b ← Piᴾ x (_, a) (_, b)

quote' ∷ String → String
quote' x = '"':x++"'\""

jParams ∷ [String]
jParams = [
  "a", "aᴹ", "aᴱ",
  "t", "tᴹ", "tᴱ",
  "p", "pᴹ", "pᴱ",
  "pr", "prᴹ", "prᴱ",
  "u", "uᴹ", "uᴱ",
  "eq", "eqᴹ", "eqᴱ"
  ]

-- | Convert preterms to embedded Haskell.
--   We use this to generate Jᴱ implementation from the shallow Agda formalization.
toHaskell ∷ [String] → Tmᴾ' → String
toHaskell params t = go False t [] where
  go ∷ Bool → Tmᴾ' → ShowS
  go p = \case
    Varᴾ "refl" → ("Refl'"++)
    Varᴾ "Id" :∙ t :∙ u →
      showParen p (("Id' "++) . go True t . (' ':) . go True u)
    Varᴾ "J"  :∙ p' :∙ pr :∙ eq →
      showParen p (("J "++) . go True p' . (' ':) . go True pr . (' ':) . go True eq)
    Varᴾ x → if elem x params then (x++) else (quote' x++)
    t :∙ u :∙ u' →
      showParen p (go False t . (" ∙ "++) . go True u . (" ∙ "++) . go True u')
    t :∙ u → showParen p (go True t . (" ∙ "++) . go True u)
    Lamᴾ' x t  →
      showParen p (("Lam' "++). (quote' x++). (' ':) . go True t)
      -- showParen p (("LAM_("++). (x++) . (") "++) . go False t)
    Piᴾ' "_" a b →
      showParen p (go True a . (" ==> "++) . go False b)
    Piᴾ' x a b →
      showParen p (("Pi' "++) . (quote' x++) . (' ':) . go True a . (' ':) . go True b)
      -- showParen p (("PI_("++).(x++).(", "++).go True a.(") "++).go False b)
    Uᴾ → ("U"++)
    t  → error (show t)

-- printJE ∷ IO ()
-- printJE = mapM_ putStrLn (toHaskell jParams . snd <$> agdaToTmᴾ jE)

-- jE ∷ String
-- jE =
--   "J\n\
--   (λ eqᴹ₁ eqᴱ₁ →\n\
--      Id (pᴱ u uᴹ uᴱ eq eqᴹ₁ eqᴱ₁ (J p pr eq))\n\
--      (J (λ xᴹ zᴹ → pᴹ u xᴹ eq zᴹ (J p pr eq))\n\
--       (J (λ x z → pᴹ x (J (λ u₁ p₁ → aᴹ u₁) tᴹ z) z refl (J p pr z)) prᴹ\n\
--        eq)\n\
--       eqᴹ₁))\n\
--   (J\n\
--    (λ uᴹ₁ uᴱ₁ →\n\
--       Id\n\
--       (pᴱ u uᴹ₁ uᴱ₁ eq\n\
--        (J (λ u₁ p₁ → Id (J (λ u₂ p₂ → aᴹ u₂) u₁ eq) uᴹ₁)\n\
--         (J (λ u₁ p₁ → Id (J (λ u₂ p₂ → aᴹ u₂) (aᴱ t) eq) u₁)\n\
--          (J (λ y p₁ → Id (J (λ u₁ p₂ → aᴹ u₁) (aᴱ t) p₁) (aᴱ y)) refl eq)\n\
--          uᴱ₁)\n\
--         tᴱ)\n\
--        refl (J p pr eq))\n\
--       (J (λ xᴹ zᴹ → pᴹ u xᴹ eq zᴹ (J p pr eq))\n\
--        (J (λ x z → pᴹ x (J (λ u₁ p₁ → aᴹ u₁) tᴹ z) z refl (J p pr z)) prᴹ\n\
--         eq)\n\
--        (J (λ u₁ p₁ → Id (J (λ u₂ p₂ → aᴹ u₂) u₁ eq) uᴹ₁)\n\
--         (J (λ u₁ p₁ → Id (J (λ u₂ p₂ → aᴹ u₂) (aᴱ t) eq) u₁)\n\
--          (J (λ y p₁ → Id (J (λ u₁ p₂ → aᴹ u₁) (aᴱ t) p₁) (aᴱ y)) refl eq)\n\
--          uᴱ₁)\n\
--         tᴱ)))\n\
--    (J\n\
--     (λ u₁ eq₁ →\n\
--        Id\n\
--        (pᴱ u₁ (aᴱ u₁) refl eq₁\n\
--         (J (λ u₂ p₁ → Id (J (λ u₃ p₂ → aᴹ u₃) u₂ eq₁) (aᴱ u₁))\n\
--          (J (λ y p₁ → Id (J (λ u₂ p₂ → aᴹ u₂) (aᴱ t) p₁) (aᴱ y)) refl eq₁)\n\
--          tᴱ)\n\
--         refl (J p pr eq₁))\n\
--        (J (λ xᴹ zᴹ → pᴹ u₁ xᴹ eq₁ zᴹ (J p pr eq₁))\n\
--         (J (λ x z → pᴹ x (J (λ u₂ p₁ → aᴹ u₂) tᴹ z) z refl (J p pr z)) prᴹ\n\
--          eq₁)\n\
--         (J (λ u₂ p₁ → Id (J (λ u₃ p₂ → aᴹ u₃) u₂ eq₁) (aᴱ u₁))\n\
--          (J (λ y p₁ → Id (J (λ u₂ p₂ → aᴹ u₂) (aᴱ t) p₁) (aᴱ y)) refl eq₁)\n\
--          tᴱ)))\n\
--     (J\n\
--      (λ tᴹ₁ tᴱ₁ →\n\
--         (pᴹ₁\n\
--          : (x : a) (xᴹ : aᴹ x) (z : Id t x) →\n\
--            Id (J (λ u₁ p₁ → aᴹ u₁) tᴹ₁ z) xᴹ → p x z → Set)\n\
--         (pᴱ₁\n\
--          : (x : a) (xᴹ : aᴹ x) (xᴱ : Id (aᴱ x) xᴹ) (z : Id t x)\n\
--            (zᴹ : Id (J (λ u₁ p₁ → aᴹ u₁) tᴹ₁ z) xᴹ) →\n\
--            Id\n\
--            (J (λ u₁ p₁ → Id (J (λ u₂ p₂ → aᴹ u₂) u₁ z) xᴹ)\n\
--             (J (λ u₁ p₁ → Id (J (λ u₂ p₂ → aᴹ u₂) (aᴱ t) z) u₁)\n\
--              (J (λ y p₁ → Id (J (λ u₁ p₂ → aᴹ u₁) (aᴱ t) p₁) (aᴱ y)) refl z) xᴱ)\n\
--             tᴱ₁)\n\
--            zᴹ →\n\
--            (x₁ : p x z) → pᴹ₁ x xᴹ z zᴹ x₁)\n\
--         (prᴹ₁ : pᴹ₁ t tᴹ₁ refl refl pr) →\n\
--         Id\n\
--         (pᴱ₁ t tᴹ₁ tᴱ₁ refl refl\n\
--          (J\n\
--           (λ xᴹ xᴱ →\n\
--              Id (J (λ u₁ p₁ → Id u₁ xᴹ) (J (λ u₁ p₁ → Id (aᴱ t) u₁) refl xᴱ) xᴱ)\n\
--              refl)\n\
--           refl tᴱ₁)\n\
--          pr)\n\
--         prᴹ₁ →\n\
--         Id\n\
--         (pᴱ₁ t (aᴱ t) refl refl (J (λ u₁ p₁ → Id u₁ (aᴱ t)) refl tᴱ₁) refl\n\
--          pr)\n\
--         (J (λ xᴹ zᴹ → pᴹ₁ t xᴹ refl zᴹ pr) prᴹ₁\n\
--          (J (λ u₁ p₁ → Id u₁ (aᴱ t)) refl tᴱ₁)))\n\
--      (λ pᴹ₁ pᴱ₁ prᴹ₁ prᴱ₁ → prᴱ₁) tᴱ pᴹ pᴱ prᴹ prᴱ)\n\
--     eq)\n\
--    uᴱ)\n\
--   eqᴱ\n"
