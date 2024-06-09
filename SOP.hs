--
-- If you want to follow along, you can git clone
--
-- https://github.com/well-typed/generic-programming-zurihac2024
--
-- and look at SOP.hs ...


{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
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

-- serialise

data Expr =
    Var String
  | App Expr Expr
  | Lam String Expr
  deriving stock Show
  deriving stock GHC.Generic
  deriving anyclass SOP.Generic
  -- deriving anyclass Serialise

instance Serialise Expr where
  encode = gencode
  decode = gdecode

-- === serialise expr
-- "\131\STXax\131\SOH\130\NULax\130\NULay"
-- >>> serialise expr
-- "\131\STXax\131\SOH\130\NULax\130\NULay"
-- >>> deserialise (serialise expr) :: Expr
-- Lam "x" (App (Var "x") (Var "y"))

encodeExpr :: Expr -> Encoding
encodeExpr (Var x)     = encodeListLen 2 <> encodeWord 0 <> encode x
encodeExpr (App e1 e2) = encodeListLen 3 <> encodeWord 1 <> encodeExpr e1 <> encodeExpr e2
encodeExpr (Lam x e)   = encodeListLen 3 <> encodeWord 2 <> encode x <> encodeExpr e

gencode :: forall a. (Generic a, All (All Serialise) (Code a)) => a -> Encoding
gencode x = 
  let
    x' :: NS (NP I) (Code a)
    SOP x' = from x

    tag :: Int
    tag = index x'
  in
    encodeSum tag x'

encodeSum :: All (All Serialise) xss => Int -> NS (NP I) xss -> Encoding
encodeSum tag s =
  collapse_NS (cmap_NS (Proxy @(All Serialise))  
    (\ p -> 
          K (encodeListLen (fromIntegral (countArgs p + 1))
       <> encodeWord (fromIntegral tag)
       <> mconcat (collapse_NP (recursivelyApplyEncode p)))
    )
    s)

-- >>> from (Var "x")
-- SOP (Z (I "x" :* Nil))
-- >>> from (App (Var "x") (Var "y"))
-- SOP (S (Z (I (Var "x") :* I (Var "y") :* Nil)))

countArgs :: NP f xs -> Int
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

-- >>> :t encode
-- encode :: Serialise a => a -> Encoding

recursivelyApplyEncode :: All Serialise xs => NP I xs -> NP (K Encoding) xs
recursivelyApplyEncode p = cmap_NP (Proxy @Serialise) (\ (I x) -> K (encode x)) p

-- >>> :t cmap_NP
-- cmap_NP
--   :: forall {k} (c :: k -> Constraint) (xs :: [k])
--             (proxy :: (k -> Constraint) -> *) (f :: k -> *) (g :: k -> *).
--      All c xs =>
--      proxy c
--      -> (forall (a :: k). c a => f a -> g a) -> NP f xs -> NP g xs

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

-- >>> :t I True :* I (Just False) :* I 'x' :* Nil
-- I True :* I (Just False) :* I 'x' :* Nil :: NP I '[Bool, Maybe Bool, Char]
--
-- >>> :t S (Z (I True))
-- S (Z (I True)) :: NS I (x : Bool : xs)
--
-- >>> :kind! Rep Expr
-- Rep Expr :: *
-- = SOP I '[ '[[Char]], '[Expr, Expr], '[[Char], Expr]]
--
-- newtype SOP f = SOP (NS (NP f))
--
-- >>> :t from
-- from :: Generic a => a -> Rep a

{-
data NP f xs where
  Nil  :: NP f '[]
  (:*) :: f x -> NP f xs -> NP f (x : xs)

data NS f xs where
  Z :: f x -> NS f (x : xs)
  S :: NS f xs -> NS f (x : xs)
-}

class Default a where
  def :: a

instance Default Bool where def = False
instance Default Int where def = 42
instance Default Char where def = 'x'

-- >>> cpure_NP (Proxy @Default) (I def) :: NP I '[Bool, Int, Char]
-- I False :* I 42 :* I 'x' :* Nil
--
-- >>> :t cpure_POP (Proxy @Serialise) decode :: POP (Decoder s) (Code Expr)
-- cpure_POP (Proxy @Serialise) decode :: POP (Decoder s) (Code Expr) :: POP (Decoder s) (Code Expr)

decodeCalls :: All (All Serialise) xss => POP (Decoder s) xss
decodeCalls =
  cpure_POP (Proxy @Serialise) decode

decodeCallsInjected :: All (All Serialise) xss => NP (K (SOP (Decoder s) xss)) xss
decodeCallsInjected =
  apInjs'_POP decodeCalls

lookupIndex :: Int -> NP (K a) xs -> Maybe a
lookupIndex 0 (K x :* _) = Just x
lookupIndex i (_ :* xs) = lookupIndex (i - 1) xs
lookupIndex _ Nil = Nothing

gdecode :: (Generic a, All (All Serialise) (Code a)) => Decoder s a
gdecode = do
  _len <- decodeListLen
  tag <- decodeWord
  let r = lookupIndex (fromIntegral tag) decodeCallsInjected
  case r of
    Nothing -> fail "could not decode"
    Just r' -> to <$> sequence_SOP r'

-- [IO a] -> IO [a]
--
-- >>> :t sequence_SOP
-- sequence_SOP :: (All SListI xss, Applicative f) => SOP f xss -> f (SOP I xss)

extractDecoder :: All (All Top) xss => SOP (Decoder s) xss -> Decoder s (SOP I xss)
extractDecoder = sequence_SOP

-- >>> :t apInjs'_POP
-- apInjs'_POP
--   :: forall {k} (xss :: [[k]]) (f :: k -> *).
--      SListI xss =>
--      POP f xss -> NP (K (SOP f xss)) xss

