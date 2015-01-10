module Iso where

import Prelude hiding ((.), id)

import Data.List
import Control.Monad

import Control.Category
infix 5 <$>


data Iso alpha beta 
  = Iso (alpha -> Maybe beta) (beta -> Maybe alpha)


inverse :: Iso alpha beta -> Iso beta alpha
inverse (Iso f g) = Iso g f

apply :: Iso alpha beta -> alpha -> Maybe beta
apply (Iso f g) = f

unapply  ::  Iso alpha beta -> beta -> Maybe alpha
unapply  =   apply . inverse


instance Category Iso where
  g . f  =  Iso  (apply f >=> apply g) 
                 (unapply g >=> unapply f)
  id     =  Iso  Just Just

class IsoFunctor f where
  (<$>) :: Iso alpha beta -> (f alpha -> f beta)

