{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE BlockArguments         #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}

module Representable where

-- base
import Data.Coerce
  ( coerce )
import Data.Kind
  ( Type, Constraint )
import GHC.Exts
  ( proxy# )
import GHC.TypeNats
  ( Nat, KnownNat, natVal' )

-- template-haskell
import Language.Haskell.TH
  ( CodeQ )
import Language.Haskell.TH.Syntax
  ( Lift(liftTyped) )

-- this
import THUtils
  ( foldQ, powQ )

--------------------------------------------------------------------------------

-- | @'Representable' r v@ exhibits @v@ as a free @r@-module of dimension
-- @'Dim' v@.
type Representable :: Type -> Type -> Constraint
class Representable r v | v -> r where
  tabulate :: ( Fin ( Dim v ) -> CodeQ r ) -> CodeQ v
  index    :: CodeQ v -> Fin ( Dim v ) -> CodeQ r
type Dim :: k -> Nat
type family Dim v

-- | @'MonomialBasis' f@ exhibits @f u@ as a free @r@-module with basis the
-- monomials in @Vars u@ variables, of degree up to (and including) @Deg u@.
type MonomialBasis :: ( Type -> Type ) -> Constraint
class MonomialBasis f where
  monTabulate :: ( ( Mon ( Deg f ) ( Vars f ) ) -> CodeQ u ) -> CodeQ ( f u )
  monIndex :: CodeQ ( f u ) -> Mon ( Deg f ) ( Vars f ) -> CodeQ u
type Deg  :: ( Type -> Type ) -> Nat
type Vars :: ( Type -> Type ) -> Nat
type family Deg  f
type family Vars f

--------------------------------------------------------------------------------
-- Monomials

-- | 1, ..., n
type Fin :: Nat -> Type
newtype Fin n = Fin Word
  deriving stock ( Show, Eq, Ord )

-- | @Mon k n@ is the set of monomials in @n@ variables of degree less than or equal to @k@.
type Mon :: Nat -> Nat -> Type
newtype Mon k n = Mon { monDegs :: [ Word ] } -- length degs == n, sum degs <= k
  deriving stock ( Show, Eq, Ord )

zeroMonomial :: forall k n. KnownNat n => Mon k n
zeroMonomial = Mon $ replicate ( fromIntegral $ word @n ) 0

isZeroMonomial :: Mon k n -> Bool
isZeroMonomial ( Mon [] ) = True
isZeroMonomial ( Mon ( i : is ) )
  | i == 0
  = isZeroMonomial ( Mon is )
  | otherwise
  = False

totalDegree :: Mon k n -> Word
totalDegree ( Mon [] ) = 0
totalDegree ( Mon ( i : is ) ) = i + totalDegree ( Mon is )

isLinear :: Mon k n -> Maybe ( Fin n )
isLinear = fmap Fin . go 1
  where
    go :: forall k' n'. Word -> Mon k' n' -> Maybe Word
    go _ ( Mon [] )
      = Nothing
    go j ( Mon ( i : is ) )
      | i == 0
      = go ( j + 1 ) ( Mon is )
      | i == 1 && isZeroMonomial ( Mon is )
      = Just j
      | otherwise
      = Nothing

-- | Comultiplication of monomials.
split :: Mon k n -> [ ( Mon k n, Mon k n ) ]
split ( Mon [] ) = [ ( Mon [], Mon [] ) ]
split ( Mon ( d : ds ) ) =
      [ ( Mon ( i : as ), Mon ( ( d - i ) : bs ) )
      | i <- [ 0 .. d ]
      , ( Mon as, Mon bs ) <- ( split ( Mon ds ) )
      ]

-- | All monomials of degree less than or equal to @k@ in @n@ variables,
-- in lexicographic order.
mons :: forall k n. ( KnownNat n ) => Word -> [ Mon k n ]
mons k = coerce ( mons' k ( word @n ) )

mons' :: Word -> Word -> [ [ Word ] ]
mons' k _ | k < 0 = []
mons' _ 0 = [ [] ]
mons' 0 n = [ replicate ( fromIntegral n ) 0 ]
mons' k n = [ i : is | i <- reverse [ 0 .. k ], is <- mons' ( k - i ) ( n - 1 ) ]

subs :: Mon k n -> [ ( Mon k n, Word ) ]
subs ( Mon [] ) = [ ( Mon [], maxBound ) ]
subs ( Mon ( i : is ) )
  = [ ( Mon ( j : js )
      , if j == 0 then mult else min ( i `quot` j ) mult )
    | j <- [ 0 .. i ]
    , ( Mon js, mult ) <- subs ( Mon is )
    ]

word :: forall n. KnownNat n => Word
word = fromIntegral $ natVal' @n proxy#

-- | The factorial function \( n! = n \cdot (n-1) \cdot `ldots` \cdot 2 `cdot` 1 \).
factorial :: Word -> Word
factorial i = product [ 1 .. i ]

vecFactorial :: [ Word ] -> Word
vecFactorial [] = 1
vecFactorial ( i : is ) = factorial i * vecFactorial is


--------------------------------------------------------------------------------

-- | The product rule.
prodRuleQ :: forall f r. MonomialBasis f
          => CodeQ r -> CodeQ ( r -> r -> r ) -> CodeQ ( r -> r -> r )
            -- Ring r constraint (circumvent TH constraint problem)
          -> CodeQ ( f r ) -> CodeQ ( f r ) -> CodeQ ( f r )
prodRuleQ zero plus times df1 df2 =
  monTabulate @f \ mon ->
    [|| $$( foldQ plus zero
           [ [|| $$times $$( monIndex @f df1 m1 ) $$( monIndex @f df2 m2 ) ||]
           | (m1, m2) <- split mon
           ] )
    ||]

--------------------------------------------------------------------------------

-- | The chain rule for a composition \( \mathbb{R}^1 \to \mathbb{R}^n \to W \)
--
-- (To be spliced in using Template Haskell.)
chainRule1NQ :: forall dr1 dv v r w d
             .  ( Num r, Representable r v
                , MonomialBasis dr1, Vars dr1 ~ 1
                , MonomialBasis dv , Vars dv  ~ Dim v
                , Deg dr1 ~ Deg dv
                , d ~ Vars dv, KnownNat d
                )
             => CodeQ ( w )           -- Module r w
             -> CodeQ ( w -> w -> w ) --
             -> CodeQ ( w -> r -> w ) -- (circumvent TH constraint issue)
             -> CodeQ ( dr1 v )
             -> CodeQ ( dv  w )
             -> CodeQ ( dr1 w )
chainRule1NQ zero_w sum_w scale_w df dg =
    monTabulate @dr1 \ case
      Mon ( 0 : _ ) -> monIndex @dv dg zeroMonomial
      Mon ( k : _ ) ->
        [|| $$( foldQ sum_w zero_w
                [ [|| $$scale_w $$( monIndex @dv dg m_g )
                        $$( foldQ [|| (+) ||] [|| 0 ||]
                              [ [|| fromInteger $$( liftTyped $ fromIntegral $ multiSubsetSumFaà k is ) *
                                   $$( foldQ [|| (*) ||] [|| 1 ||]
                                      [ foldQ [|| (*) ||] [|| 1 ||]
                                        [ ( index @r @v ( monIndex @dr1 df ( Mon $ f_deg : [] ) ) v_index )
                                              `powQ` pow
                                        | ( f_deg, pow ) <- pows
                                        ]
                                      | ( v_index, pows ) <- zipIndices is
                                      ]
                                    ) ||]
                              | is <- mss
                              ]
                         )
                    ||]
                | m_g <- mons @_ @d k
                , let mss = multiSubsetsSum [ 1 .. k ] k ( monDegs m_g )
                , not ( null mss ) -- avoid terms of the form x * 0
                ]
            ) ||]
      _ -> error "impossible"

--------------------------------------------------------------------------------
-- Computations for the chain rule R^1 -> R^n -> R^m

-- | Faà di Bruno coefficient (naive implementation).
multiSubsetSumFaà :: Word -> [ [ ( Word, Word ) ] ] -> Word
multiSubsetSumFaà k multisubsets =
  factorial k `div`
    product [ factorial p * ( factorial i ) ^ p
            | multisubset <- multisubsets
            , ( i, p ) <- multisubset ]

-- | Computes the multisubsets of the given set which have the specified sum
-- and number of elements.
multiSubsetSum :: Word -- ^ size of multisubset
               -> Word -- ^ desired sum
               -> [ Word ] -- ^ set to pick from
               -> [ [ ( Word, Word ) ] ]
multiSubsetSum 0 0 _  = [ [] ]
multiSubsetSum 0 _ _  = []
multiSubsetSum _ _ [] = []
multiSubsetSum n s ( i : is ) =
  [ if j == 0 then js else ( i, j ) : js
  | j <- [ 0 .. n ]
  , js <- multiSubsetSum ( n - j ) ( s - i * j ) is
  ]

-- | @multiSubsetsSum is s ns@ computes all collection of multisubsets of @is@,
-- with sizes specified by @ns@, such that the total sum is @s@.
multiSubsetsSum :: [ Word ] -- ^ set to pick from
                -> Word     -- ^ desired total sum
                -> [ Word ] -- ^ sizes of each multisets
                -> [ [ [ ( Word, Word ) ] ] ]
multiSubsetsSum is = goMSS
  where
    goMSS :: Word -> [ Word ] -> [ [ [ ( Word, Word ) ] ] ]
    goMSS 0 [] = [ [] ]
    goMSS _ [] = [ ]
    goMSS s (n : ns) =
      [ multi : rest
      | s_i <- [ n * i_min .. s ]
      , multi <- multiSubsetSum n s_i is
      , rest <- goMSS ( s - s_i ) ns ]
    i_min = case is of
      [] -> 0
      _  -> max 0 $ minimum is

zipIndices :: forall n a
           .  [ a ] -- ^ must have length n
           -> [ ( Fin n, a ) ]
zipIndices = zipIndices_ 1
  where
    zipIndices_ :: Word -> [ a ] -> [ ( Fin n, a ) ]
    zipIndices_ _ [] = []
    zipIndices_ i (a : as) = ( Fin i, a ) : zipIndices_ ( i + 1 ) as

