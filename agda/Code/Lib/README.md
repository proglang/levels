# Lib

The Agda code in this directory originates from other papers:

- Ordinals: 
  - Paper: "Three equivalent ordinal notation systems in cubical Agda"
  - Code: https://zenodo.org/records/3588624 (for README see `Ordinals/index.lagda`)
  - Changes: 
    - Adjusted to work with Agda version 2.7.1.0, the standard library version 2.1.1 and cubical version 0.7
    - Added more examples of ordinal notations in `Code.Lib.Ordinals.MutualOrd`

- Universes: 
  - Paper: Agda supplement to the paper "Generalized Universe Hierarchies and First-Class Universe Levels"
  - Code: `https://github.com/AndrasKovacs/universes/tree/fe91a04d3b2ae88ddc35c32ccb672a4cafa5c61e/agda` (for README see `Universes/README.md`)
  - Changes: 
    - Adjusted to work with Agda version 2.7.1.0 and the standard-library version 2.1.1
    - Added `IR-Universe`, `Ordinal` and `IR-Univ-Ordinal` record instances for `MutualOrd` (`Code.Lib.Ordinals.MutualOrd`) data type 