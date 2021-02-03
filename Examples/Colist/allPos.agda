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

  allPosIS : IS U
  allPosIS .Names = allPosRN
  allPosIS .rules allp-Λ = allP-Λ
  allPosIS .rules allp-t = allP-t

  allPos : U → Set
  allPos = CoInd⟦ allPosIS ⟧

  allPosSpec : U → Set
  allPosSpec xs = ∀{x} → x ∈ xs → x > 0

  allPosSound : ∀{xs} → allPos xs → allPosSpec xs
  allPosSound {x ∷ xs} ap mem with ap .CoInd⟦_⟧.unfold
  allPosSound {x ∷ xs} ap here | allp-t , (.x , .xs) , refl , x>0 , prem = x>0
  allPosSound {x ∷ xs} ap (there mem) | allp-t , (.x , .xs) , refl , x>0 , prem = allPosSound (prem zero) mem

  allPosSpecCons : ∀{xs} → allPosSpec xs → ISF[ allPosIS ] allPosSpec xs
  allPosSpecCons {[]} _ = allp-Λ , (tt , (refl , tt , λ ()))
  allPosSpecCons {(x ∷ xs)} Sxs = allp-t , ((x , xs) , (refl , (Sxs here , λ {Fin.zero → λ mem → Sxs (there mem)})))

  allPosComplete : ∀{xs} → allPosSpec xs → allPos xs
  allPosComplete = coind[ allPosIS ] allPosSpec allPosSpecCons