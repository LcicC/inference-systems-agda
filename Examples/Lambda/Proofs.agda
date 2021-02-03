open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Nat
open import Data.List
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Size
open import Codata.Thunk
open import Axiom.ExcludedMiddle
open import Level renaming (zero to ∅ ; suc to ++)

open import is-lib.SInfSys as IS
open import Examples.Lambda.Lambda
open import Examples.Lambda.BigStep renaming (U to BigStepU)
open import Examples.Lambda.SmallStep

module Examples.Lambda.Proofs where

  Spec : BigStepU → Set
  Spec (e , val x) = e ⇒* inj-val-term x
  Spec (e , v∞) = ∀{i} → ⇒∞ e i

  {- Soundness -}
  Spec-val : BigStepU → Set
  Spec-val (e , v) = ∀{v'} → v ≡ val v' → Spec (e , v)

  Spec-closed : ISClosed (BigStepIS ∪ BigStepCOIS) Spec-val
  Spec-closed (inj₁ VAL) tt _ refl = ε
  Spec-closed (inj₁ APP) tt prem refl =
    let s-e1 = prem zero refl in
    let s-e2 = prem (suc zero) refl in
    let s-subst = prem (suc (suc zero)) refl in
    let subst = IS.fold (β , _ , refl , tt , λ ()) in
    inj-l-app _ (prem zero refl) ◅◅ inj-r-app _ (prem (suc zero) refl) ◅◅ subst ◅ prem (suc (suc zero)) refl
  Spec-closed (inj₂ COA) s_ _ ()

  ⇓ᵢ-to-⇒* : ∀{e v} → e ⇓ᵢ v → Spec-val (e , v)
  ⇓ᵢ-to-⇒* = ind[ BigStepIS ∪ BigStepCOIS ] Spec-val Spec-closed

  bs-sound-v : ∀{e v} → (∀{i} → (e ⇓ (val v)) i) → e ⇒* (inj-val-term v)
  bs-sound-v r = ⇓ᵢ-to-⇒* (sfcoind-to-ind r) refl

  subject-red-⇓ : ∀{e e' v} → (∀{i} → (e ⇓ v) i) → e ⇒ e' → (∀{i} → (e' ⇓ v) i)
  subject-red-⇓ bs (fold (β , (e , v) , eq , tt , _)) with bs
  subject-red-⇓ bs (fold (β , (e , v) , () , tt , _)) | sfold (VAL , lambda x , refl , _ , prem)
  subject-red-⇓ bs (fold (β , (e , lambda x) , refl , tt , _)) | sfold (APP , (.(lambda e) , _ , .(lambda x) , v , _) , refl , _ , prem)
    with val-⇓-≡ (prem zero .force) | val-⇓-≡ (prem (suc zero) .force)
  subject-red-⇓ bs (fold (β , (e , lambda x) , refl , tt , _)) | sfold (APP , (.(lambda e) , .e , .(lambda x) , .(lambda x) , _) , refl , _ , prem) | refl | refl = prem (suc (suc zero)) .force
  subject-red-⇓ bs (fold (β , (e , v) , refl , tt , _)) | sfold (L-DIV , _ , refl , _ , prem) = ⊥-elim (val-not-reduce⇓ (prem zero .force))
  subject-red-⇓ bs (fold (β , (e , v) , refl , tt , _)) | sfold (R-DIV , _ , refl , _ , prem) = ⊥-elim (val-not-reduce⇓ (prem (suc zero) .force))
  subject-red-⇓ bs (fold (L-APP , c , eq , tt , _)) with bs
  subject-red-⇓ bs (fold (L-APP , _ , () , tt , _)) | sfold (VAL , lambda _ , refl , _ , _)
  subject-red-⇓ bs (fold (L-APP , (e1 , e1' , e2) , refl , tt , pr)) | sfold (APP , (.e1 , e1'' , .e2 , lambda _ , _) , refl , (tt , ind) , prem) =
    let rec = subject-red-⇓ (prem zero .force) (pr zero) in
    let prems = λ{zero → rec ; (suc zero) → prem (suc zero) .force ; (suc (suc zero)) → prem (suc (suc zero)) .force} in
    apply-sfcoind APP tt prems
  subject-red-⇓ bs (fold (L-APP , (e1 , e1' , e2) , refl , tt , pr)) | sfold (L-DIV , (.e1 , .e2) , refl , (tt , ind) , prem) =
    let rec = subject-red-⇓ (prem zero .force) (pr zero) in
    apply-sfcoind L-DIV tt λ{zero → rec}
  subject-red-⇓ bs (fold (L-APP , (e1 , e1' , e2) , refl , tt , pr)) | sfold (R-DIV , (.e1 , .e2 , lambda v) , refl , (tt , ind) , prem) =
    let rec = subject-red-⇓ (prem zero .force) (pr zero) in
    let prems = λ{zero → rec ; (suc zero) → prem (suc zero) .force} in
    apply-sfcoind R-DIV tt prems
  subject-red-⇓ bs (fold (R-APP , (lambda _ , e2 , e2') , eq , tt , pr)) with bs
  subject-red-⇓ bs (fold (R-APP , (lambda _ , _ , _) , refl , tt , _)) | sfold (VAL , lambda _ , () , _ , _)
  subject-red-⇓ bs (fold (R-APP , (lambda e1 , e2 , e2') , refl , tt , pr)) | sfold (APP , (.(lambda _) , e1' , .e2 , lambda _ , _) , refl , (tt , ind) , prem)
    with val-⇓-≡ (prem zero .force)
  subject-red-⇓ bs (fold (R-APP , (lambda e1 , e2 , e2') , refl , tt , pr)) | sfold (APP , (.(lambda e1) , .e1 , .e2 , lambda _ , _) , refl , (tt , ind) , prem) | refl =
    let rec = subject-red-⇓ (prem (suc zero) .force) (pr zero) in
    let prems = λ{zero → prem zero .force ; (suc zero) → rec ; (suc (suc zero)) → prem (suc (suc zero)) .force} in
    apply-sfcoind APP tt prems
  subject-red-⇓ bs (fold (R-APP , (lambda _ , e2 , e2') , refl , tt , _)) | sfold (L-DIV , (.(lambda _) , .e2) , refl , _ , prem) = ⊥-elim (val-not-reduce⇓ (prem zero .force))
  subject-red-⇓ bs (fold (R-APP , (lambda e , e2 , e2') , refl , tt , pr)) | sfold (R-DIV , (.(lambda e) , .e2 , v) , refl , (tt , ind) , prem) with val-⇓-≡ (prem zero .force)
  subject-red-⇓ bs (fold (R-APP , (lambda e , e2 , e2') , refl , tt , pr)) | sfold (R-DIV , (.(lambda e) , .e2 , .(lambda e)) , refl , (tt , ind) , prem) | refl =
    let rec = subject-red-⇓ (prem (suc zero) .force) (pr zero) in
    let prems = λ{zero → prem zero .force ; (suc zero) → rec} in
    apply-sfcoind R-DIV tt prems

  progress : ∀{e} →(∀{i} → (e ⇓ v∞) i) → Σ[ e' ∈ Term 0 ] (e ⇒ e')
  progress {e} bs with bs
  progress  bs | sfold (APP , _ , refl , _ , prem) with bs-sound-v (prem zero .force)
  progress  bs | sfold (APP , (_ , e1' , _ , _ , .v∞) , refl , _ , prem) | ε with bs-sound-v (prem (suc zero) .force)
  progress  bs | sfold (APP , (.(lambda e1') , e1' , _ , v , .v∞) , refl , _ , prem) | ε | ε =
    _ , apply-ind β tt λ ()
  progress  bs | sfold (APP , (.(lambda e1') , e1' , e2 , _ , .v∞) , refl , _ , prem) | ε | x ◅ _ =
    app (lambda e1') _ , apply-ind R-APP tt λ{zero → x}
  progress  bs | sfold (APP , (e1 , _ , e2 , _ , .v∞) , refl , _ , prem) | x ◅ _ =
    app _ e2 , apply-ind L-APP tt λ{zero → x}
  progress  bs | sfold (L-DIV , (e1 , e2) , refl , _ , prem) =
    let e1' , e1⇒e1' = progress (prem zero .force) in
    app e1' e2 , apply-ind L-APP tt λ{zero → e1⇒e1'}
  progress  bs | sfold (R-DIV , (e1 , e2 , v) , refl , _ , prem) with bs-sound-v (prem zero .force)
  progress  bs | sfold (R-DIV , (.(inj-val-term _) , e2 , (lambda e)) , refl , _ , prem) | ε =
    let e2' , e2⇒e2' = progress (prem (suc zero) .force) in
    app (lambda e) e2' , apply-ind R-APP tt λ{zero → e2⇒e2'}
  progress  bs | sfold (R-DIV , (e1 , e2 , (lambda e)) , refl , _ , prem) | x ◅ _ =
    app _ e2 , apply-ind L-APP tt λ{zero → x}

  bs-sound-∞ : ∀{e} → (∀{i} → (e ⇓ v∞) i) → (∀{i} → ⇒∞ e i)
  bs-sound-∞ bs with progress bs
  ... | e' , ss = step ss λ where .force → bs-sound-∞ (subject-red-⇓ bs ss)

  bs-sound : ∀{e v} → (∀{i} → (e ⇓ v) i) → Spec (e , v)
  bs-sound {_} {val _} = bs-sound-v
  bs-sound {_} {v∞} = bs-sound-∞


  {- Completeness -}
  inv-app : ∀{e1 e2 v} → (app e1 e2) ⇓ᵢ (val v) →
    Σ[ e1' ∈ Term 1 ] Σ[ e2' ∈ Value ]
      (e1 ⇓ᵢ val (lambda e1')) ×
      (e2 ⇓ᵢ (val e2')) ×
      (subst-0 e1' (inj-val-term e2') ⇓ᵢ val v)
  -- Using consistency of inductive interpretation
  inv-app bs with ind-postfix bs
  inv-app bs | inj₁ VAL , lambda _ , () , _ , _
  inv-app bs | inj₁ APP , _ , refl , _ , pr = _ , _ , pr zero , pr (suc zero) , pr (suc (suc zero))
  inv-app bs | inj₂ COA , _ , () , _ , _

  subject-exp : ∀{e e' v} → e ⇒ e' → e' ⇓ᵢ v → e ⇓ᵢ v
  subject-exp {.(app (lambda e1) (inj-val-term v))} {_} {v'} (fold (β , (e1 , v) , refl , tt , _)) bs =
    let prem-e1 = IS.fold (inj₁ VAL , lambda e1 , refl , tt , λ ()) in
    let prem-e2 = IS.fold (inj₁ VAL , v , refl , tt , λ ()) in
    let prems = λ{zero → prem-e1 ; (suc zero) → prem-e2 ; (suc (suc zero)) → bs} in
    apply-ind (inj₁ APP) tt prems
  subject-exp {.(app e1 e2)} {.(app e1' e2)} {val x} (fold (L-APP , (e1 , e1' , e2) , refl , tt , pr)) bs =
    let e1'' , e2' , bs-e1' , bs-e2 , bs-subst = inv-app bs in
    let prems = λ{zero → subject-exp (pr zero) bs-e1' ; (suc zero) → bs-e2 ; (suc (suc zero)) → bs-subst} in
    apply-ind (inj₁ APP) tt prems
  subject-exp {.(app e1 e2)} {.(app e1' e2)} {v∞} (fold (L-APP , (e1 , e1' , e2) , refl , tt , pr)) bs =
    apply-ind (inj₂ COA) tt λ ()
  subject-exp {.(app (inj-val-term v) e2)} {.(app (inj-val-term v) e2')} {val x} (fold (R-APP , (v , e2 , e2') , refl , tt , pr)) bs =
    let e1' , e2'' , bs-e1 , bs-e2' , bs-subst = inv-app bs in
    let prems = λ{zero → bs-e1 ; (suc zero) → subject-exp (pr zero) bs-e2' ; (suc (suc zero)) → bs-subst} in
    apply-ind (inj₁ APP) tt prems
  subject-exp {.(app (inj-val-term v) e2)} {.(app (inj-val-term v) e2')} {v∞} (fold (R-APP , (v , e2 , e2') , refl , _)) bs =
    apply-ind (inj₂ COA) tt λ ()

  bounded-v : ∀{e v} → e ⇒* inj-val-term v → e ⇓ᵢ val v
  bounded-v ε = apply-ind (inj₁ VAL) tt λ ()
  bounded-v (x ◅ ss) = subject-exp x (bounded-v ss)

  bounded-∞ : ∀{e} → (∀{i} → ⇒∞ e i) → e ⇓ᵢ v∞
  bounded-∞ {e} ss = apply-ind (inj₂ COA) tt λ ()
  
  bounded : ∀{e v} → Spec (e , v) → e ⇓ᵢ v
  bounded {_} {val _} = bounded-v
  bounded {_} {v∞} = bounded-∞

  get-prem-cons : ∀{e1 e2 v} → app e1 e2 ⇒* (inj-val-term v) →
    Σ[ e1' ∈ Term 1 ] Σ[ e2' ∈ Value ]
      (e1 ⇒* lambda e1') ×
      (e2 ⇒* inj-val-term e2') ×
      (subst-0 e1' (inj-val-term e2') ⇒* (inj-val-term v))
  get-prem-cons {.(lambda e1)} {.(inj-val-term v)} {lambda _} (fold (β , (e1 , v) , refl , _ , _) ◅ ss) =
    e1 , v , ε , ε , ss
  get-prem-cons {.e1} {.e2} {lambda _} (fold (L-APP , (e1 , e1' , e2) , refl , _ , pr) ◅ ss) =
    let e1'' , e2' , rec-e1' , rec-e2 , rec-subst = get-prem-cons ss in
    e1'' , e2' , pr zero ◅ rec-e1' , rec-e2 , rec-subst
  get-prem-cons {.(inj-val-term v)} {.e2} {lambda _} (fold (R-APP , (v , e2 , e2') , refl , _ , pr) ◅ ss) =
    let e1' , e2'' , rec-e1 , rec-e2' , rec-subst = get-prem-cons ss in
    e1' , e2'' , rec-e1 , pr zero ◅ rec-e2' , rec-subst

  consistent-v : ∀{e v} → e ⇒* inj-val-term v → IS.ISF[ BigStepIS ] Spec (e , val v)
  consistent-v {.(lambda _)} {lambda _} ε = VAL , _ , refl , tt , λ ()
  consistent-v {lambda _} {lambda _} (x ◅ ss) = ⊥-elim (val-not-reduce⇒ x)
  consistent-v {app e1 e2} {lambda _} (x ◅ ss) =
    let e1' , e2' , e1⇒* , e2⇒* , subst⇒* = get-prem-cons (x ◅ ss) in
    let prems = λ{zero → e1⇒* ; (suc zero) → e2⇒* ; (suc (suc zero)) → subst⇒*} in
    APP , (e1 , e1' , e2 , e2' , _) , refl , tt , prems
    
  postulate
    excluded-middle : ExcludedMiddle ∅
  
  lemma-divergence : ∀{e1 e2} → (∀{i} → ⇒∞ (app e1 e2) i) →
    (∀{i} → ⇒∞ e1 i) ⊎
    e1 ConvergesSS × (∀{i} → ⇒∞ e2 i) ⊎
    Σ[ t1 ∈ Term 1 ] Σ[ v ∈ Value ] (e1 ⇒* lambda t1) × (e2 ⇒* inj-val-term v) × (∀{i} → ⇒∞ (subst-0 t1 (inj-val-term v)) i)
  lemma-divergence {e1} {e2} ss with excluded-middle {e1 ConvergesSS}
  lemma-divergence {e1} {e2} ss | no ¬e1-conv = inj₁ (div-app-l-not-conv ss ¬e1-conv)
  lemma-divergence {e1} {e2} ss | yes e1-conv with excluded-middle {e2 ConvergesSS}
  lemma-divergence {e1} {e2} ss | yes e1-conv | no ¬e2-conv =
    inj₂ (inj₁ (e1-conv , div-app-r-not-conv ss (proj₂ e1-conv) ¬e2-conv))
  lemma-divergence {e1} {e2} ss | yes (lambda _ , red-e1) | yes (_ , red-e2) =
    inj₂ (inj₂ (_ , _ , ( red-e1 , red-e2 , app-subst-⇒∞₁ red-e1 red-e2 ss)))

  consistent-∞ : ∀{e} → (∀{i} → ⇒∞ e i) → IS.ISF[ BigStepIS ] Spec (e , v∞)
  consistent-∞ {e} ss with ss
  consistent-∞ {lambda e} ss | step x _ = ⊥-elim (val-not-reduce⇒ x)
  consistent-∞ {app e₁ e₂} ss | step x x₁ with lemma-divergence (step x x₁)
  consistent-∞ {app e₁ e₂} ss | step x x₁ | inj₁ e1-div =
    L-DIV , _ , refl , tt , λ{zero → e1-div}
  consistent-∞ {app e₁ e₂} ss | step x x₁ | inj₂ (inj₁ (e1-conv , e2-div)) =
    R-DIV , _ , refl , tt , λ{zero → proj₂ e1-conv ; (suc zero) → e2-div}
  consistent-∞ {app e₁ e₂} ss | step x x₁ | inj₂ (inj₂ (_ , _ , red-e1 , red-e2 , subst-div)) =
    APP , _ , refl , tt , λ{zero → red-e1 ; (suc zero) → red-e2 ; (suc (suc zero)) → subst-div}

  consistent : ∀{e v} → Spec (e , v) → IS.ISF[ BigStepIS ] Spec (e , v)
  consistent {_} {val _} = consistent-v
  consistent {_} {v∞} = consistent-∞

  complete : ∀{e v} → Spec (e , v) → (∀{i} → (e ⇓ v) i)
  complete = bounded-scoind[ BigStepIS , BigStepCOIS ] Spec bounded consistent