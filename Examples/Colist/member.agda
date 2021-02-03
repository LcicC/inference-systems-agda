open import Data.Product
open import Data.List
open import Data.Unit
open import Codata.Colist as Colist
open import Agda.Builtin.Equality
open import Size
open import Codata.Thunk
open import Data.Fin
open import Data.Nat
open import Data.Maybe
open import Examples.Colist.Auxiliary.Colist_memberOf

open import is-lib.InfSys

module Examples.Colist.member {A : Set} where

  U = A × Colist A ∞

  data memberRN : Set where
    mem-h mem-t : memberRN

  mem-h-r : MetaRule U
  mem-h-r .C = A × Thunk (Colist A) ∞
  mem-h-r .comp (x , xs) =
    [] ,
    ----------------
    (x , x ∷ xs) , ⊤

  mem-t-r : MetaRule U
  mem-t-r .C = A × A × Thunk (Colist A) ∞
  mem-t-r .comp (x , y , xs) =
    ((x , xs .force) ∷ []) ,
    ----------------
    (x , y ∷ xs) , ⊤

  memberIS : IS U
  memberIS .Names = memberRN
  memberIS .rules mem-h = mem-h-r
  memberIS .rules mem-t = mem-t-r

  _member_ : A → Colist A ∞ → Set
  x member xs = Ind⟦ memberIS ⟧ (x , xs)
  
  memSpec : U → Set
  memSpec (x , xs) = Σ[ i ∈ ℕ ] (Colist.lookup i xs ≡ just x)

  memSpecClosed : ISClosed memberIS memSpec
  memSpecClosed mem-h tt _ = zero , refl
  memSpecClosed mem-t tt pr =
    let (i , proof) = pr Fin.zero in
    (suc i) , proof

  memberSound : ∀ {x xs} → x member xs → memSpec (x , xs)
  memberSound = ind[ memberIS ] memSpec memSpecClosed

  -- Completeness using memSpec does not terminate
  -- Product implemented as record. Record projections do not decrease
  memSpec' : U → ℕ → Set
  memSpec' (x , xs) i = Colist.lookup i xs ≡ just x

  mem-compl : ∀{x xs i} → memSpec' (x , xs) i → x member xs
  mem-compl {.x} {x ∷ _} {zero} refl = apply-ind mem-h tt λ ()
  mem-compl {x} {y ∷ xs} {suc i} eq = apply-ind mem-t tt λ{zero → mem-compl eq}

  memberComplete : ∀{x xs} → memSpec (x , xs) → x member xs
  memberComplete (i , eq) = mem-compl eq

  {- Correctness wrt to Agda DataType -}

  ∈-sound : ∀{x xs} → x ∈ xs → x member xs
  ∈-sound here = apply-ind mem-h tt λ ()
  ∈-sound (there mem) = apply-ind mem-t tt λ{zero → ∈-sound mem}

  ∈-complete : ∀{x xs} → x member xs → x ∈ xs
  ∈-complete (fold (mem-h , _ , refl , _)) = here
  ∈-complete (fold (mem-t , _ , refl , _ , prem)) = there (∈-complete (prem zero))