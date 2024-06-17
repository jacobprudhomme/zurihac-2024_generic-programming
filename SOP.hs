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

instance Serialise Expr where
  encode = encodeExpr
  decode = decodeExpr

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

expr :: Expr
expr = Lam "x" (App (Var "x") (Var "y"))

-- >>> serialise expr
-- "\131\STXax\131\SOH\130\NULax\130\NULay"
-- >>> deserialise (serialise expr) :: Expr
-- Lam "x" (App (Var "x") (Var "y"))

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
