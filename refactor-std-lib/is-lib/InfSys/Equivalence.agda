--------------------------------------------------------------------------------
-- This is part of Agda Inference Systems 

{-# OPTIONS --sized-types --guardedness #-}

open import Agda.Builtin.Equality
open import Data.Product
open import Data.Sum
open import Codata.Thunk
open import Size
open import Level
open import Relation.Unary using (_⊆_)

module is-lib.InfSys.Equivalence {𝓁} where

  open import is-lib.InfSys.Base {𝓁}
  open import is-lib.InfSys.Coinduction {𝓁}
  open import is-lib.InfSys.SCoinduction {𝓁}
  open IS

  private
    variable
      U : Set 𝓁
      𝓁c 𝓁p 𝓁n : Level
  
  {- Equivalence CoInd and SCoInd -}

  coind-size : {is : IS {𝓁c} {𝓁p} {𝓁n} U} → 
               CoInd⟦ is ⟧ ⊆ λ u → ∀ {i} → SCoInd⟦ is ⟧ u i
  coind-size p-coind with CoInd⟦_⟧.unfold p-coind
  ... | rn , c , refl , pr = 
    sfold (rn , c , refl , λ i → λ where .force → coind-size (pr i))

  size-coind : {is : IS {𝓁c} {𝓁p} {𝓁n} U} → 
               (λ u → ∀ {i} → SCoInd⟦ is ⟧ u i) ⊆ CoInd⟦ is ⟧
  size-coind {is = is} p-scoind = 
    coind[ is ] (λ u → ∀ {j} → SCoInd⟦ is ⟧ u j) scoind-postfix p-scoind