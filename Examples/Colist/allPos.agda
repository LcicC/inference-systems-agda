open import Data.Product
open import Data.List
open import Data.Unit
open import Codata.Colist
open import Agda.Builtin.Equality
open import Size
open import Data.Nat
open import Data.Fin
open import Codata.Thunk
open import Examples.Colist.Auxiliary.Colist_memberOf

open import is-lib.InfSys

module Examples.Colist.allPos where

  U : Set
  U = Colist ℕ ∞

  data allPosRN : Set where
    allp-Λ allp-t : allPosRN

  allP-Λ : MetaRule U
  allP-Λ .C = ⊤
  allP-Λ .comp c =
    [] ,
    -----------------
    [] , ⊤

  allP-t : MetaRule U
  allP-t .C = ℕ × Thunk (Colist ℕ) ∞
  allP-t .comp (x , xs) =
    ((xs .force) ∷ []) ,
    -----------------
    (x ∷ xs) , (x > 0)

  allP-IS : IS U
  allP-IS .Names = allPosRN
  allP-IS .rules allp-Λ = allP-Λ
  allP-IS .rules allp-t = allP-t

  allPos : U → Set
  allPos = CoInd⟦ allP-IS ⟧

  allP-S : U → Set
  allP-S xs = ∀{x} → x ∈ xs → x > 0

  allP-sound : ∀{xs} → allPos xs → allP-S xs
  allP-sound {x ∷ xs} ap mem with ap .CoInd⟦_⟧.unfold
  allP-sound {x ∷ xs} ap here | allp-t , (.x , .xs) , refl , x>0 , prem = x>0
  allP-sound {x ∷ xs} ap (there mem) | allp-t , (.x , .xs) , refl , x>0 , prem = allP-sound (prem zero) mem

  allP-cons : ∀{xs} → allP-S xs → ISF[ allP-IS ] allP-S xs
  allP-cons {[]} _ = allp-Λ , (tt , (refl , tt , λ ()))
  allP-cons {(x ∷ xs)} Sxs = allp-t , ((x , xs) , (refl , (Sxs here , λ {Fin.zero → λ mem → Sxs (there mem)})))

  allP-complete : ∀{xs} → allP-S xs → allPos xs
  allP-complete ap = coind[ allP-IS ] allP-S allP-cons ap