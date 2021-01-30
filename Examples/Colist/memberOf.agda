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

module Examples.Colist.memberOf {A : Set} where

  U = A × Colist A ∞

  data memberOfRN : Set where
    mem-h mem-t : memberOfRN

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

  mem-is : IS U
  mem-is .Names = memberOfRN
  mem-is .rules mem-h = mem-h-r
  mem-is .rules mem-t = mem-t-r

  _memberOf_ : A → Colist A ∞ → Set
  x memberOf xs = Ind⟦ mem-is ⟧ (x , xs)
  
  mem-S : U → Set
  mem-S (x , xs) = Σ[ i ∈ ℕ ] (Colist.lookup i xs ≡ just x)

  mem-Closed : ISClosed mem-is mem-S
  mem-Closed mem-h tt _ = zero , refl
  mem-Closed mem-t tt pr =
    let (i , proof) = pr Fin.zero in
    (suc i) , proof

  mem-sound : ∀ {x xs} → x memberOf xs → mem-S (x , xs)
  mem-sound = ind[ mem-is ] mem-S mem-Closed

  -- Completeness using mem-S does not terminate
  -- Product implemented as record. Record projections do not decrease
  mem-S' : U → ℕ → Set
  mem-S' (x , xs) i = Colist.lookup i xs ≡ just x

  mem-compl : ∀{x xs i} → mem-S' (x , xs) i → x memberOf xs
  mem-compl {.x} {x ∷ _} {zero} refl = apply-ind mem-h tt λ ()
  mem-compl {x} {y ∷ xs} {suc i} eq = apply-ind mem-t tt λ{zero → mem-compl eq}

  mem-complete : ∀{x xs} → mem-S (x , xs) → x memberOf xs
  mem-complete (i , eq) = mem-compl eq

  {- Correctness wrt to Agda DataType -}

  ∈-sound : ∀{x xs} → x ∈ xs → x memberOf xs
  ∈-sound here = apply-ind mem-h tt λ ()
  ∈-sound (there mem) = apply-ind mem-t tt λ{zero → ∈-sound mem}

  ∈-complete : ∀{x xs} → x memberOf xs → x ∈ xs
  ∈-complete (fold (mem-h , _ , refl , _)) = here
  ∈-complete (fold (mem-t , _ , refl , _ , prem)) = there (∈-complete (prem zero))
