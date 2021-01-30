open import Data.Nat
open import Data.List
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Size

open import is-lib.SInfSys
open import Examples.Lambda.Lambda

module Examples.Lambda.BigStep where

  data Value∞ : Set where
    val : Value → Value∞
    v∞ : Value∞

  U : Set
  U = Term 0 × Value∞

  data BigStepIS-RN : Set where
    VAL APP L-DIV R-DIV : BigStepIS-RN

  data BigStepCOIS-RN : Set where
    COA : BigStepCOIS-RN

  coa-r : MetaRule U
  coa-r .MetaRule.C = Term 0
  coa-r .MetaRule.comp t =
    [] ,
    -------------------------
    (t , v∞) , ⊤

  val-r : MetaRule U
  val-r .MetaRule.C = Value
  val-r .MetaRule.comp v =
    [] ,
    -------------------------
    (inj-val-term v , val v) , ⊤

  app-r : MetaRule U
  app-r .MetaRule.C = Term 0 × Term 1 × Term 0 × Value × Value∞
  app-r .MetaRule.comp (t1 , t1' , t2 , v , v-∞) =
    (t1 , val (lambda t1'))  ∷ (t2 , val v) ∷ (subst-0 t1' (inj-val-term v) , v-∞) ∷ [] ,
    -------------------------
    (app t1 t2 , v-∞) , ⊤
  
  l-div-r : MetaRule U
  l-div-r .MetaRule.C = Term 0 × Term 0
  l-div-r .MetaRule.comp (t1 , t2) =
    (t1 , v∞) ∷ [] ,
    -------------------------
    (app t1 t2 , v∞) , ⊤
  
  r-div-r : MetaRule U
  r-div-r .MetaRule.C = Term 0 × Term 0 × Value
  r-div-r .MetaRule.comp (t1 , t2 , v) =
    (t1 , val v) ∷ (t2 , v∞) ∷ [] ,
    -------------------------
    (app t1 t2 , v∞) , ⊤
  
  BigStepIS : IS U
  BigStepIS .IS.Names = BigStepIS-RN
  BigStepIS .IS.rules VAL = val-r
  BigStepIS .IS.rules APP = app-r
  BigStepIS .IS.rules L-DIV = l-div-r
  BigStepIS .IS.rules R-DIV = r-div-r
  
  BigStepCOIS : IS U
  BigStepCOIS .IS.Names  = BigStepCOIS-RN
  BigStepCOIS .IS.rules COA = coa-r
  
  _⇓_ : Term 0 → Value∞ → Size → Set
  (t ⇓ v) i = SFCoInd⟦ BigStepIS , BigStepCOIS ⟧ (t , v) i
  
  _⇓ᵢ_ : Term 0 → Value∞ → Set
  t ⇓ᵢ v = Ind⟦ BigStepIS ∪ BigStepCOIS ⟧ (t , v)
  
  {- Properties -}
  
  val-not-reduce⇓ : ∀{v} → ¬ (∀{i} → ((inj-val-term v) ⇓ v∞) i)
  val-not-reduce⇓ {lambda _} bs with bs
  val-not-reduce⇓ {lambda _} bs | (sfold (VAL , _ , () , _ , _))
  
  val-⇓ᵢ-≡ : ∀{v v'} → inj-val-term v ⇓ᵢ val v' → v ≡ v'
  val-⇓ᵢ-≡ {lambda x} {lambda .x} (fold (inj₁ VAL , .(lambda x) , refl , _)) = refl
  val-⇓ᵢ-≡ {lambda x} {lambda x₁} (fold (inj₁ APP , c , () , _))
  val-⇓ᵢ-≡ {v} {v'} (fold (inj₂ COA , c , () , _))
  
  val-⇓-≡ : ∀{v v'} → (∀{i} → (inj-val-term v ⇓ val v') i) → v ≡ v'
  val-⇓-≡ bs = val-⇓ᵢ-≡ (sfcoind-to-ind bs)