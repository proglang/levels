-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

       Fredrik Nordvall Forsberg  and  Chuangjie Xu

We present three ordinal notation systems representing ordinals below
ε₀ in type theory, using recent type-theoretical innovations such as
mutual inductive-inductive definitions and higher inductive types.  As
case studies, we show how basic ordinal arithmetic can be developed
for these systems, and how they admit a transfinite induction
principle.  We prove that all three notation systems are equivalent,
so that we can transport results between them using the univalence
principle.

All the files are tested with

• Agda development version 2.6.1
  (commit: 4af7b92663d2eb1dd94383b140eb7acfeb1b1eb0)

• Cubical Agda library
  (commit: d7e345d3bcaefbc066d057487fca9677de7e29c7)

Marius Weidner: Compatibility with
• Agda development version 2.7.0.1
• Cubical Agda library version 0.7
• The project structure 

\begin{code}

{-# OPTIONS --cubical --safe #-}

module Lib.Ordinals.index where

-----------------------
-- Table of contents --
-----------------------

-- §2 Cubical Agda
import Lib.Ordinals.Preliminaries

-- §3 Notation systems for ordinals below ε₀

-- §3.1 The subset approach
import Lib.Ordinals.SigmaOrd

-- §3.2 The mutual approach
import Lib.Ordinals.MutualOrd

-- MutualOrd can also be defined without nested and
-- inductive-recursive definitions
import Lib.Ordinals.MutualOrdWithoutNestednessAndRecursion

-- §3.3 The higher inductive approach
import Lib.Ordinals.HITOrd

-- §3.4 Equivalences between the three approaches
import Lib.Ordinals.Equivalences

-- §4 Ordinal arithmetic
import Lib.Ordinals.Arithmetic

-- §5 Transfinite induction
import Lib.Ordinals.TransfiniteInduction

\end{code}
