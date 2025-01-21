
module Lib.Universes.README where

{-
Agda supplement to the paper "Generalized Universe Hierarchies and First-Class Universe Levels".

This module was checked using Agda 2.6.1, with standard library version 1.3.

For instructions on installing the standard library, see the following:
https://agda.readthedocs.io/en/v2.6.1.3/tools/package-system.html
-}

import Lib.Universes.Lib          -- library, for equational reasoning and exporting some definitions
import Lib.Universes.IRUniverse   -- semantic inductive-recursive universes over level structures
import Lib.Universes.TTGUModel    -- model of type theory with generalized levels
import Lib.Universes.TTFLModel    -- model of type theory with first-class levels, where levels are strictly the same as internal Nat
import Lib.Universes.Super        -- some notes on Palmgren's super universes and transfinite hierarchies
