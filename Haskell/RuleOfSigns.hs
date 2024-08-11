#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck

import Data.List
import Test.QuickCheck

-- cubeVol q r h - cubeVol q r (h*2/3) = cubeVol q r (h * (Rpower 19 (1/3))/3).
-- h^3 - (h*2/3)^3 = cubeVol q r (h * (Rpower 19 (1/3))/3).
-- (h^3 - (h*2/3)^3) = cubeVol q r (h * (Rpower 19 (1/3))/3).
-- (h^3 - h^3*(2/3)^3) = cubeVol q r (h * (Rpower 19 (1/3))/3).
-- h^3 * (1 - (2/3)^3) = cubeVol q r (h * (Rpower 19 (1/3))/3).
-- h^3 * 19/3^3 = cubeVol q r (h * (Rpower 19 (1/3))/3).
-- h^3 * (19^(1/3))^3/3^3 = cubeVol q r (h * (Rpower 19 (1/3))/3).
-- h^3 * (19^(1/3)/3)^3 = cubeVol q r (h * (Rpower 19 (1/3))/3).
-- (h*19^(1/3)/3)^3 = cubeVol q r (h * (Rpower 19 (1/3))/3).
-- cubeVol q r (h*(19^(1/3))/3) = cubeVol q r (h * (Rpower 19 (1/3))/3).

cubeVol :: Double -> Double -> Double -> Double
cubeVol = \q r' h' -> h' ** 3 * (pi/3) * q

x1 = let q = 5 in let r = 2 in let h = 3 in cubeVol q r h - cubeVol q r (h*2/3)
x2 = let q = 5 in let r = 2 in let h = 3 in cubeVol q r (h * (19 ** (1/3))/3)