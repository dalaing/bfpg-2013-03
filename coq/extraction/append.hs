module Append where

import qualified Prelude

data List a =
   Nil
 | Cons a (List a)

append :: (List a1) -> (List a1) -> List a1
append xs ys =
  case xs of {
   Nil -> ys;
   Cons h t -> Cons h (append t ys)}

