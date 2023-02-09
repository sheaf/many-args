{-# LANGUAGE BlockArguments       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

{-# OPTIONS_GHC -ddump-to-file -ddump-simpl -ddump-cmm -dno-typeable-binds -dsuppress-unfoldings #-}

module Implementation where

-- base
import Control.Applicative
  ( liftA2 )

-- rounded-hw
import Numeric.Rounded.Hardware.Interval.NonEmpty
  ( Interval )

-- this
import Definitions
  ( Module(..)
  , R3, D3A1(..), D3A3(..)
  )
import Representable
  ( Representable(tabulate, index)
  , prodRuleQ, chainRule1NQ
  )

--------------------------------------------------------------------------------

instance Module ( Interval Double ) ( Interval R3 ) where
  origin  = $$( tabulate \ _ -> [|| origin ||] )
  a ^+^ b = $$( tabulate \ i -> [|| $$( index [|| a ||] i ) ^+^ $$( index [|| b ||] i ) ||] )
  a ^-^ b = $$( tabulate \ i -> [|| $$( index [|| a ||] i ) ^-^ $$( index [|| b ||] i ) ||] )
  k *^ a  = $$( tabulate \ i -> [|| k *^ $$( index [|| a ||] i ) ||] )

instance Num r => Num ( D3A3 r ) where
  (+) = liftA2 (+)
  !dr1 * !dr2 =
    let
      o :: r
      !o = fromInteger 0
      p :: r -> r -> r
      !p = (+) @r
      m :: r -> r -> r
      !m = (*) @r
   in
       $$( prodRuleQ
             [|| o ||] [|| p ||] [|| m ||]
             [|| dr1 ||] [|| dr2 ||] )
  {-# SPECIALISE instance Num ( D3A3 Double ) #-}
  {-# SPECIALISE instance Num ( D3A3 ( Interval Double ) ) #-}


chainRule33 :: forall w. Module Double w => D3A1 R3 -> D3A3 w -> D3A1 w
chainRule33 !df !dg =
    let !o = origin @Double @w
        !p = (^+^)  @Double @w
        !s = (^*)   @Double @w
    in $$( chainRule1NQ
         [|| o ||] [|| p ||] [|| s ||]
         [|| df ||] [|| dg ||] )

chainRule33I :: forall w. Module ( Interval Double ) w => D3A1 ( Interval R3 ) -> D3A3 w -> D3A1 w
chainRule33I !df !dg =
  let !o = origin @( Interval Double ) @w
      !p = (^+^)  @( Interval Double ) @w
      !s = (^*)   @( Interval Double ) @w
  in $$( chainRule1NQ
       [|| o ||] [|| p ||] [|| s ||]
       [|| df ||] [|| dg ||] )
