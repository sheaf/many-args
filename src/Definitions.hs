{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE DerivingVia            #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE LexicalNegation        #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Definitions
  ( Module(..)
  , R1(..), R3(..)
  , D3A1(..), D3A3(..)
  ) where

-- base
import Data.Coerce
  ( coerce )
import Data.Monoid
  ( Sum(..) )
import GHC.Generics
  ( Generic, Generic1, Generically1(..) )

-- rounded-hw
import Numeric.Rounded.Hardware
  ( Rounded(..) )
import Numeric.Rounded.Hardware.Interval.NonEmpty
  ( Interval )
import qualified Numeric.Rounded.Hardware.Interval.NonEmpty as Interval
  ( Interval(..) )
import qualified Numeric.Rounded.Hardware.Interval.NonEmpty as Interval
  ( sup, inf )

-- this
import Representable
  ( Representable(   tabulate,    index), Dim, Fin(..)
  , MonomialBasis(monTabulate, monIndex), Deg, Vars, Mon(..)
  )

--------------------------------------------------------------------------------

infixl 6 ^+^, ^-^
infix  9 ^*, *^

class Num r => Module r m | m -> r where

  {-# MINIMAL origin, (^+^), ( (^*) | (*^) ) #-}

  origin :: m
  (^+^) :: m -> m -> m
  (^-^) :: m -> m -> m
  (*^) :: r -> m -> m
  (^*) :: m -> r -> m

  (*^) = flip (^*)
  (^*) = flip (*^)
  m ^-^ n = m ^+^ -1 *^ n

instance Num a => Module a ( Sum a ) where
  origin = Sum 0
  (^+^) = coerce $ (+) @a
  (^-^) = coerce $ (-) @a
  c *^ Sum x = Sum ( c * x )
  Sum x ^* c = Sum ( x * c )

--------------------------------------------------------------------------------

newtype R1 = R1 { unR1 :: Double }
  deriving stock   ( Generic )
  deriving newtype ( Eq, Ord )
data    R3 = R3 { _R3_x, _R3_y, _R3_z :: {-# UNPACK #-} !Double }
  deriving stock    Generic
  deriving stock    ( Eq, Ord )

deriving via Sum Double
  instance Module Double Double

instance Module Double R3 where
  origin = R3 0 0 0
  R3 x1 y1 z1 ^+^ R3 x2 y2 z2 = R3 (x1+x2) (y1+y2) (z1+z2)
  R3 x1 y1 z1 ^-^ R3 x2 y2 z2 = R3 (x1-x2) (y1-y2) (z1-z2)
  k *^ R3 x y z = R3 (k*x) (k*y) (k*z)

deriving via Sum ( Interval Double )
  instance Module ( Interval Double ) ( Interval Double )

type instance Dim R1 = 1
instance Representable Double R1 where
  tabulate f = [|| R1 $$( f ( Fin 1 ) ) ||]
  index p _ = [|| unR1 $$p ||]

type instance Dim R3 = 3
instance Representable Double R3 where
  tabulate f = [|| R3 $$( f ( Fin 1 ) ) $$( f ( Fin 2 ) ) $$( f ( Fin 3 ) ) ||]
  index p = \ case
    Fin 1 -> [|| _R3_x $$p ||]
    Fin 2 -> [|| _R3_y $$p ||]
    _     -> [|| _R3_z $$p ||]

--------------------------------------------------------------------------------

type instance Dim ( Interval u ) = Dim u
instance Representable r u => Representable ( Interval r ) ( Interval u ) where
  tabulate f =
    let !lo = tabulate @r @u ( \ i -> [|| getRounded $ Interval.inf $$( f i ) ||] )
        !hi = tabulate @r @u ( \ i -> [|| getRounded $ Interval.sup $$( f i ) ||] )
    in [|| Interval.I ( Rounded $$lo ) ( Rounded $$hi ) ||]

  index d i =
    [|| case $$d of
          Interval.I ( Rounded lo ) ( Rounded hi ) ->
            let !lo_i = $$( index @r @u [|| lo ||] i )
                !hi_i = $$( index @r @u [|| hi ||] i )
            in Interval.I ( Rounded lo_i ) ( Rounded hi_i )
    ||]

--------------------------------------------------------------------------------

-- | \( \mathbb{Z}[x]/(x)^4 \).
data D3A1 v =
  D31 { _D31_v :: !v
      , _D31_dx :: !v
      , _D31_dxdx :: !v
      , _D31_dxdxdx :: !v
      }
  deriving stock ( Show, Eq, Functor, Foldable, Traversable, Generic, Generic1 )
  deriving Applicative
    via Generically1 D3A1

-- | \( \mathbb{Z}[x, y, z]/(x, y, z)^4 \).
data D3A3 v =
  D33 { _D33_v :: !v
      , _D33_dx, _D33_dy, _D33_dz :: !v
      , _D33_dxdx, _D33_dxdy, _D33_dydy, _D33_dxdz, _D33_dydz, _D33_dzdz :: !v
      , _D33_dxdxdx, _D33_dxdxdy, _D33_dxdydy, _D33_dydydy
         , _D33_dxdxdz, _D33_dxdydz, _D33_dxdzdz, _D33_dydydz, _D33_dydzdz, _D33_dzdzdz :: !v
      }
  deriving stock ( Show, Eq, Functor, Foldable, Traversable, Generic, Generic1 )
  deriving Applicative
    via Generically1 D3A3

type instance Deg  D3A1 = 3
type instance Vars D3A1 = 1
instance MonomialBasis D3A1 where
  monTabulate f =
    [|| let
          !_D31_v      = $$( f $ Mon ( 0 : [] ) )
          !_D31_dx     = $$( f $ Mon ( 1 : [] ) )
          !_D31_dxdx   = $$( f $ Mon ( 2 : [] ) )
          !_D31_dxdxdx = $$( f $ Mon ( 3 : [] ) )
        in D31 { .. }
      ||]

  monIndex d = \ case
    Mon ( 1 : [] ) -> [|| _D31_dx     $$d ||]
    Mon ( 2 : [] ) -> [|| _D31_dxdx   $$d ||]
    Mon ( 3 : [] ) -> [|| _D31_dxdxdx $$d ||]
    _              -> [|| _D31_v      $$d ||]

type instance Deg  D3A3 = 3
type instance Vars D3A3 = 3
instance MonomialBasis D3A3 where
  monTabulate f =
    [|| let
          !_D33_v      = $$( f $ Mon ( 0 : 0 : 0 : [] ) )
          !_D33_dx     = $$( f $ Mon ( 1 : 0 : 0 : [] ) )
          !_D33_dy     = $$( f $ Mon ( 0 : 1 : 0 : [] ) )
          !_D33_dz     = $$( f $ Mon ( 0 : 0 : 1 : [] ) )
          !_D33_dxdx   = $$( f $ Mon ( 2 : 0 : 0 : [] ) )
          !_D33_dxdy   = $$( f $ Mon ( 1 : 1 : 0 : [] ) )
          !_D33_dydy   = $$( f $ Mon ( 0 : 2 : 0 : [] ) )
          !_D33_dxdz   = $$( f $ Mon ( 1 : 0 : 1 : [] ) )
          !_D33_dydz   = $$( f $ Mon ( 0 : 1 : 1 : [] ) )
          !_D33_dzdz   = $$( f $ Mon ( 0 : 0 : 2 : [] ) )
          !_D33_dxdxdx = $$( f $ Mon ( 3 : 0 : 0 : [] ) )
          !_D33_dxdxdy = $$( f $ Mon ( 2 : 1 : 0 : [] ) )
          !_D33_dxdydy = $$( f $ Mon ( 1 : 2 : 0 : [] ) )
          !_D33_dydydy = $$( f $ Mon ( 0 : 3 : 0 : [] ) )
          !_D33_dxdxdz = $$( f $ Mon ( 2 : 0 : 1 : [] ) )
          !_D33_dxdydz = $$( f $ Mon ( 1 : 1 : 1 : [] ) )
          !_D33_dxdzdz = $$( f $ Mon ( 1 : 0 : 2 : [] ) )
          !_D33_dydydz = $$( f $ Mon ( 0 : 2 : 1 : [] ) )
          !_D33_dydzdz = $$( f $ Mon ( 0 : 1 : 2 : [] ) )
          !_D33_dzdzdz = $$( f $ Mon ( 0 : 0 : 3 : [] ) )
       in D33 { .. } ||]

  monIndex d = \ case
    Mon ( 1 : 0 : 0 : [] ) -> [|| _D33_dx     $$d ||]
    Mon ( 0 : 1 : 0 : [] ) -> [|| _D33_dy     $$d ||]
    Mon ( 0 : 0 : 1 : [] ) -> [|| _D33_dz     $$d ||]
    Mon ( 2 : 0 : 0 : [] ) -> [|| _D33_dxdx   $$d ||]
    Mon ( 1 : 1 : 0 : [] ) -> [|| _D33_dxdy   $$d ||]
    Mon ( 0 : 2 : 0 : [] ) -> [|| _D33_dydy   $$d ||]
    Mon ( 1 : 0 : 1 : [] ) -> [|| _D33_dxdz   $$d ||]
    Mon ( 0 : 1 : 1 : [] ) -> [|| _D33_dydz   $$d ||]
    Mon ( 0 : 0 : 2 : [] ) -> [|| _D33_dzdz   $$d ||]
    Mon ( 3 : 0 : 0 : [] ) -> [|| _D33_dxdxdx $$d ||]
    Mon ( 2 : 1 : 0 : [] ) -> [|| _D33_dxdxdy $$d ||]
    Mon ( 1 : 2 : 0 : [] ) -> [|| _D33_dxdydy $$d ||]
    Mon ( 0 : 3 : 0 : [] ) -> [|| _D33_dydydy $$d ||]
    Mon ( 2 : 0 : 1 : [] ) -> [|| _D33_dxdxdz $$d ||]
    Mon ( 1 : 1 : 1 : [] ) -> [|| _D33_dxdydz $$d ||]
    Mon ( 1 : 0 : 2 : [] ) -> [|| _D33_dxdzdz $$d ||]
    Mon ( 0 : 1 : 2 : [] ) -> [|| _D33_dydzdz $$d ||]
    Mon ( 0 : 0 : 3 : [] ) -> [|| _D33_dzdzdz $$d ||]
    _                      -> [|| _D33_v      $$d ||]
