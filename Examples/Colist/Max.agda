open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Bool
open import Data.Empty
open import Codata.Colist
open import Codata.Thunk
open import Size
open import Examples.Colist.Auxiliary.Colist_memberOf
open import Examples.Colist.Auxiliary.MaxOf

open import is-lib.InfSys

module Examples.Colist.Max where

  U : Set
  U = ℕ × Colist ℕ ∞

  data MaxElemIS-RN : Set where 
    max-h max-t : MaxElemIS-RN

  data MaxElemCOIS-RN : Set where 
    co-max-h : MaxElemCOIS-RN

  max-h-r : MetaRule U
  max-h-r .C = ℕ × Thunk (Colist ℕ) ∞
  max-h-r .comp (x , xs) =
    [] ,
    --------------
    (x , x ∷ xs) , (xs .force ≡ [])

  max-t-r : MetaRule U
  max-t-r .C = ℕ × ℕ × ℕ × Thunk (Colist ℕ) ∞
  max-t-r .comp (x , y , z , xs) =
    (x , xs .force) ∷ [] ,
    --------------
    (z , y ∷ xs) , (z ≡ max x y)

  co-max-h-r : MetaRule U
  co-max-h-r .C = ℕ × Thunk (Colist ℕ) ∞
  co-max-h-r .comp (x , xs) =
    [] ,
    --------------
    (x , x ∷ xs) , ⊤


  MaxElemIS : IS U
  MaxElemIS .IS.Names = MaxElemIS-RN
  MaxElemIS .IS.rules max-h = max-h-r
  MaxElemIS .IS.rules max-t = max-t-r

  MaxElemCOIS : IS U
  MaxElemCOIS .IS.Names = MaxElemCOIS-RN
  MaxElemCOIS .IS.rules co-max-h = co-max-h-r

  _MaxElem_ : ℕ → Colist ℕ ∞ → Set
  x MaxElem xs = FCoInd⟦ MaxElemIS , MaxElemCOIS ⟧ (x , xs)

  _MaxElemᵢ_ : ℕ → Colist ℕ ∞ → Set
  x MaxElemᵢ xs = Ind⟦ MaxElemIS ∪ MaxElemCOIS ⟧ (x , xs)

  MaxElem-S MaxElem-S-in MaxElem-S-gr : U → Set
  MaxElem-S-in (x , xs) = x ∈ xs
  MaxElem-S-gr (x , xs) = ∀{n} → n ∈ xs → x ≡ max x n
  MaxElem-S u = MaxElem-S-in u × MaxElem-S-gr u

  max-sound-in-ind : ∀{x xs} → x MaxElemᵢ xs → MaxElem-S-in (x , xs)
  max-sound-in-ind (fold (inj₁ max-h , _ , refl , _)) = here
  max-sound-in-ind (fold (inj₁ max-t , _ , refl , eq , prem)) with max-refl-eq eq
  max-sound-in-ind (fold (inj₁ max-t , _ , refl , eq , prem)) | inj₁ refl = there (max-sound-in-ind (prem zero))
  max-sound-in-ind (fold (inj₁ max-t , _ , refl , eq , prem)) | inj₂ refl = here
  max-sound-in-ind (fold (inj₂ co-max-h , _ , refl , _)) = here

  max-sound-in : ∀{x xs} → x MaxElem xs → MaxElem-S-in (x , xs)
  max-sound-in max = max-sound-in-ind (fcoind-to-ind max)

  max-sound-gr : ∀{x xs} → x MaxElem xs → MaxElem-S-gr (x , xs)
  max-sound-gr max here with max .CoInd⟦_⟧.unfold
  max-sound-gr max here | max-h , _ , refl , _ = max-self
  max-sound-gr max here | max-t , _ , refl , (eq , _) , _ with max-refl-eq eq
  ... | inj₁ refl = eq
  ... | inj₂ refl = max-self 
  max-sound-gr max (there mem) with max .CoInd⟦_⟧.unfold
  max-sound-gr max (there mem) | max-h , _ , refl , (eq , _) , _ = ⊥-elim (mem-abs mem eq)
  max-sound-gr max (there mem) | max-t , _ , refl , (eq , _) , pr with max-refl-eq eq
  ... | inj₁ refl = max-sound-gr (pr zero) mem
  ... | inj₂ refl =
    let rec = max-sound-gr (pr zero) mem in
    max-trans rec (max-comm eq)

  max-sound : ∀{x xs} → x MaxElem xs → MaxElem-S (x , xs)
  max-sound max = max-sound-in max , max-sound-gr max

  S-bounded : ∀{x xs} → MaxElem-S-in (x , xs) → MaxElem-S-gr (x , xs) → x MaxElemᵢ xs
  S-bounded here _ = apply-ind (inj₂ co-max-h) tt λ ()
  S-bounded (there mem) gr = apply-ind (inj₁ max-t) (gr here) λ{zero → S-bounded mem λ m → gr (there m)}

  postulate
    old-max : ∀{n x y xs ys} → Thunk.force xs ≡ (y ∷ ys) →
                    MaxElem-S (n , (x ∷ xs)) → Σ[ m ∈ ℕ ] MaxElem-S (m , (y ∷ ys))

  S-consistent : ∀{x xs} → MaxElem-S-in (x , xs) → MaxElem-S-gr (x , xs) → ISF[ MaxElemIS ] MaxElem-S (x , xs)
  S-consistent {x} {x ∷ xs} here gr with xs .force | inspect (λ t → t .force) xs
  S-consistent {x} {x ∷ xs} here gr | [] | [ eq ] = max-h , _ , refl , eq , λ ()
  S-consistent {x} {x ∷ xs} here gr | _ ∷ _ | [ eq ] =
    let old , mem , gr' = old-max eq (here , gr) in
    let mem-xs = subst (λ xs → old ∈ xs) (sym eq) mem in
    max-t , _ , refl , max-comm (gr (there mem-xs)) , λ{zero → mem-xs , λ m → gr' (subst (λ xs → _ ∈ xs) eq m)}
  S-consistent {x} {.(_ ∷ _)} (there mem) gr = max-t , _ , refl , gr here , λ{zero → mem , λ m → gr (there m)}


  max-complete : ∀{x xs} → MaxElem-S (x , xs) → x MaxElem xs
  max-complete =
    bounded-coind[ MaxElemIS , MaxElemCOIS ] MaxElem-S (λ{(x , xs) → S-bounded x xs}) λ{(x , xs) → S-consistent x xs}