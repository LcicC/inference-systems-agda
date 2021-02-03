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

module Examples.Colist.maxElem where

  U : Set
  U = ℕ × Colist ℕ ∞

  data maxElemRN : Set where 
    max-h max-t : maxElemRN

  data maxElemCoRN : Set where 
    co-max-h : maxElemCoRN

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


  maxElemIS : IS U
  maxElemIS .IS.Names = maxElemRN
  maxElemIS .IS.rules max-h = max-h-r
  maxElemIS .IS.rules max-t = max-t-r

  maxElemCoIS : IS U
  maxElemCoIS .IS.Names = maxElemCoRN
  maxElemCoIS .IS.rules co-max-h = co-max-h-r

  _maxElem_ : ℕ → Colist ℕ ∞ → Set
  x maxElem xs = FCoInd⟦ maxElemIS , maxElemCoIS ⟧ (x , xs)

  _maxElemᵢ_ : ℕ → Colist ℕ ∞ → Set
  x maxElemᵢ xs = Ind⟦ maxElemIS ∪ maxElemCoIS ⟧ (x , xs)

  maxSpec inSpec geqSpec : U → Set
  inSpec (x , xs) = x ∈ xs
  geqSpec (x , xs) = ∀{n} → n ∈ xs → x ≡ max x n
  maxSpec u = inSpec u × geqSpec u

  maxSound-in-ind : ∀{x xs} → x maxElemᵢ xs → inSpec (x , xs)
  maxSound-in-ind (fold (inj₁ max-h , _ , refl , _)) = here
  maxSound-in-ind (fold (inj₁ max-t , _ , refl , eq , prem)) with max-refl-eq eq
  maxSound-in-ind (fold (inj₁ max-t , _ , refl , eq , prem)) | inj₁ refl = there (maxSound-in-ind (prem zero))
  maxSound-in-ind (fold (inj₁ max-t , _ , refl , eq , prem)) | inj₂ refl = here
  maxSound-in-ind (fold (inj₂ co-max-h , _ , refl , _)) = here

  maxSound-in : ∀{x xs} → x maxElem xs → inSpec (x , xs)
  maxSound-in max = maxSound-in-ind (fcoind-to-ind max)

  maxSound-gr : ∀{x xs} → x maxElem xs → geqSpec (x , xs)
  maxSound-gr max here with max .CoInd⟦_⟧.unfold
  maxSound-gr max here | max-h , _ , refl , _ = max-self
  maxSound-gr max here | max-t , _ , refl , (eq , _) , _ with max-refl-eq eq
  ... | inj₁ refl = eq
  ... | inj₂ refl = max-self 
  maxSound-gr max (there mem) with max .CoInd⟦_⟧.unfold
  maxSound-gr max (there mem) | max-h , _ , refl , (eq , _) , _ = ⊥-elim (mem-abs mem eq)
  maxSound-gr max (there mem) | max-t , _ , refl , (eq , _) , pr with max-refl-eq eq
  ... | inj₁ refl = maxSound-gr (pr zero) mem
  ... | inj₂ refl =
    let rec = maxSound-gr (pr zero) mem in
    max-trans rec (max-comm eq)

  maxElemSound : ∀{x xs} → x maxElem xs → maxSpec (x , xs)
  maxElemSound max = maxSound-in max , maxSound-gr max

  maxSpecBounded : ∀{x xs} → inSpec (x , xs) → geqSpec (x , xs) → x maxElemᵢ xs
  maxSpecBounded here _ = apply-ind (inj₂ co-max-h) tt λ ()
  maxSpecBounded (there mem) gr = apply-ind (inj₁ max-t) (gr here) λ{zero → maxSpecBounded mem λ m → gr (there m)}

  postulate
    old-max : ∀{n x y xs ys} → Thunk.force xs ≡ (y ∷ ys) →
                    maxSpec (n , (x ∷ xs)) → Σ[ m ∈ ℕ ] maxSpec (m , (y ∷ ys))

  maxSpecCons : ∀{x xs} → inSpec (x , xs) → geqSpec (x , xs) → ISF[ maxElemIS ] maxSpec (x , xs)
  maxSpecCons {x} {x ∷ xs} here gr with xs .force | inspect (λ t → t .force) xs
  maxSpecCons {x} {x ∷ xs} here gr | [] | [ eq ] = max-h , _ , refl , eq , λ ()
  maxSpecCons {x} {x ∷ xs} here gr | _ ∷ _ | [ eq ] =
    let old , mem , gr' = old-max eq (here , gr) in
    let mem-xs = subst (λ xs → old ∈ xs) (sym eq) mem in
    max-t , _ , refl , max-comm (gr (there mem-xs)) , λ{zero → mem-xs , λ m → gr' (subst (λ xs → _ ∈ xs) eq m)}
  maxSpecCons {x} {.(_ ∷ _)} (there mem) gr = max-t , _ , refl , gr here , λ{zero → mem , λ m → gr (there m)}


  maxElemComplete : ∀{x xs} → maxSpec (x , xs) → x maxElem xs
  maxElemComplete =
    bounded-coind[ maxElemIS , maxElemCoIS ] maxSpec (λ{(x , xs) → maxSpecBounded x xs}) λ{(x , xs) → maxSpecCons x xs}