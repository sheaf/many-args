{-# LANGUAGE TemplateHaskell #-}

module THUtils ( foldQ, powQ ) where

-- template-haskell
import Language.Haskell.TH
  ( CodeQ )

--------------------------------------------------------------------------------

foldQ :: CodeQ ( a -> a -> a ) -> CodeQ a -> [ CodeQ a ] -> CodeQ a
foldQ _ a0 []  = a0
foldQ _ _  [a] = a
foldQ f a0 (a:as) = [|| $$f $$a $$( foldQ f a0 as ) ||]

powQ :: Num a => CodeQ a -> Word -> CodeQ a
powQ _ 0 = [|| 1 ||]
powQ x 1 = x
powQ x n = [|| $$x ^ ( n :: Word ) ||]
