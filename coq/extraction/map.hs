module Map where

import qualified Prelude

data List a =
   Nil
 | Cons a (List a)

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

