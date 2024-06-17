{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module SOP where

import Codec.CBOR.FlatTerm
import Codec.Serialise
import Codec.Serialise.Encoding
import Codec.Serialise.Decoding
import Generics.SOP as SOP
import Generics.SOP.NP
import Generics.SOP.NS
import qualified GHC.Generics as GHC

data Expr =
    Var String
  | App Expr Expr
  | Lam String Expr
  deriving stock Show
  deriving stock GHC.Generic
  deriving anyclass SOP.Generic

expr :: Expr
expr = Lam "x" (App (Var "x") (Var "y"))

{- Uncomment the following to use our hand-rolled encoding/decoding logic, no generics: -}
-- instance Serialise Expr where
--   encode = encodeExpr
--   decode = decodeExpr

instance Serialise Expr where
  encode = gencode
  decode = gdecode

{- Normally, would have to write all the following manually to encode expressions -}
encodeExpr :: Expr -> Encoding
encodeExpr (Var x)     = encodeListLen 2 <> encodeWord 0 <> encode x
encodeExpr (App e1 e2) = encodeListLen 3 <> encodeWord 1 <> encodeExpr e1 <> encodeExpr e2
encodeExpr (Lam x e)   = encodeListLen 3 <> encodeWord 2 <> encode x <> encodeExpr e

{- Similarly, would have to write all this manually to decode -}
decodeExpr :: Decoder s Expr
decodeExpr = do
  len <- decodeListLen
  tag <- decodeWord
  case (len, tag) of
    (2, 0) -> Var <$> decode
    (3, 1) -> App <$> decodeExpr <*> decodeExpr
    (3, 2) -> Lam <$> decode <*> decodeExpr
    _ -> fail "cannot decode"

{- Generics.SOP allows you to treat things as if you're just doing
   the standard functional programming we know and love!
-}

-- >>> from (Var "x")
-- SOP (Z (I "x" :* Nil))
-- >>> from (App (Var "x") (Var "y"))
-- SOP (S (Z (I (Var "x") :* I (Var "y") :* Nil)))

{- NP is a "product", essentially a heterogeneous list of the arguments -}
-- >>> :t I True :* I (Just False) :* I 'x' :* Nil
-- I True :* I (Just False) :* I 'x' :* Nil :: NP I '[Bool, Maybe Bool, Char]

{- NS is a "sum", essentially enumerating the different type constructors -}
-- >>> :t S (Z (I True))
-- S (Z (I True)) :: NS I (x : Bool : xs)

{- Together, we have an SOP (sum of products) describing the different type constructors for Expr.
   So, SOP f = NS (NP f)
-}
-- >>> :kind! Rep Expr
-- Rep Expr :: *
-- = SOP I '[ '[[Char]], '[Expr, Expr], '[[Char], Expr]]

countArgs :: NP f xs -> Int {- Think of NP f xs as [ f x ] -}
countArgs Nil = 0
countArgs (_ :* xs) = 1 + countArgs xs

countArgs' :: All Top xs => NP f xs -> Int
countArgs' p = length (collapse_NP (map_NP (const (K ())) p))

-- >>> countArgs (I (Var "x") :* I (Var "y") :* Nil)
-- 2
-- >>> countArgs' (I (Var "x") :* I (Var "y") :* Nil)
-- 2

index :: NS f xs -> Int
index (Z _) = 0
index (S s) = 1 + index s

-- >>> index (S (Z undefined))
-- 1

recursivelyApplyEncode :: All Serialise xs => NP I xs -> NP (K Encoding) xs
recursivelyApplyEncode = cmap_NP (Proxy @Serialise) (\(I x) -> K (encode x))

encodeSum :: All (All Serialise) xss => Int -> NS (NP I) xss -> Encoding
encodeSum tag s = collapse_NS (cmap_NS
  (Proxy @(All Serialise))
  (\p -> K (encodeListLen (fromIntegral (countArgs p + 1))
    <> encodeWord (fromIntegral tag)
    <> (mconcat . collapse_NP . recursivelyApplyEncode) p))
  s)

gencode :: forall a. (Generic a, All (All Serialise) (Code a)) => a -> Encoding
gencode x =
  let x' :: NS (NP I) (Code a)
      SOP x' = from x

      tag :: Int
      tag = index x'
  in encodeSum tag x'

{- Our SOP.Generics serialization logic... -}
-- === serialise expr
-- "\131\STXax\131\SOH\130\NULax\130\NULay"

{- ...versus the hand-rolled/GHC generic deriving one. -}
-- === serialise expr
-- "\131\STXax\131\SOH\130\NULax\130\NULay"

decodeCalls :: All (All Serialise) xss => POP (Decoder s) xss
decodeCalls = cpure_POP (Proxy @Serialise) decode

decodeCallsInjected :: All (All Serialise) xss => NP (K (SOP (Decoder s) xss)) xss
decodeCallsInjected = apInjs'_POP decodeCalls

lookupIndex :: Int -> NP (K a) xs -> Maybe a
lookupIndex 0 (K x :* _) = Just x
lookupIndex i (_ :* xs)  = lookupIndex (i - 1) xs
lookupIndex _ Nil        = Nothing

extractDecoder :: All (All Top) xss => SOP (Decoder s) xss -> Decoder s (SOP I xss)
extractDecoder = sequence_SOP

gdecode :: (Generic a, All (All Serialise) (Code a)) => Decoder s a
gdecode = do
  _len <- decodeListLen
  tag <- decodeWord
  let r = lookupIndex (fromIntegral tag) decodeCallsInjected
  case r of
    Nothing -> fail "Could not decode"
    Just r' -> to <$> extractDecoder r'

{- Our SOP.Generics deserialization logic... -}
-- === deserialise (serialise expr) :: Expr
-- Lam "x" (App (Var "x") (Var "y"))

{- ...versus the hand-rolled/GHC generic deriving one. -}
-- === deserialise (serialise expr) :: Expr
-- Lam "x" (App (Var "x") (Var "y"))
