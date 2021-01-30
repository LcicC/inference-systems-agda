open import Data.Nat
open import Data.List
open import Data.Fin
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Size
open import Codata.Thunk
open import Relation.Binary.PropositionalEquality as ≡


open import is-lib.SInfSys as IS
open import Examples.Lambda.Lambda

module Examples.Lambda.SmallStep where

  U : Set
  U = Term 0 × Term 0

  data SmallStepRN : Set where
    β L-APP R-APP : SmallStepRN

  β-r : MetaRule U
  β-r .MetaRule.C = Term 1 × Value
  β-r .MetaRule.comp (t1 , v) =
    [] ,
    -------------------------
    (app (lambda t1) (inj-val-term v) , subst-0 t1 (inj-val-term v)) , ⊤

  l-app-r : MetaRule U
  l-app-r .MetaRule.C = Term 0 × Term 0 × Term 0
  l-app-r .MetaRule.comp (t1 , t1' , t2) =
    (t1 , t1') ∷ [] ,
    -------------------------
    ((app t1 t2) , (app t1' t2)) , ⊤

  r-app-r : MetaRule U
  r-app-r .MetaRule.C = Value × Term 0 × Term 0
  r-app-r .MetaRule.comp (v , t2 , t2') =
    (t2 , t2') ∷ [] ,
    -------------------------
    ((app (inj-val-term v) t2) , app (inj-val-term v) t2') , ⊤

  SmallStep : IS U
  SmallStep .IS.Names = SmallStepRN
  SmallStep .IS.rules β = β-r
  SmallStep .IS.rules L-APP = l-app-r
  SmallStep .IS.rules R-APP = r-app-r

  _↓_ : Term 0 → Term 0 → Set
  t ↓ t' = Ind⟦ SmallStep ⟧ (t , t')

  _↓*_ : Term 0 → Term 0 → Set
  _↓*_ = Star _↓_

  _ConvergesSS : Term 0 → Set
  t ConvergesSS = Σ[ v ∈ Value ] (t ↓* inj-val-term v)

  data ∞SS : Term 0 → Size → Set where
    step : ∀{t t' i} → t ↓ t' → Thunk (∞SS t') i → ∞SS t i

  {- Properties -}
  inj-l-app : ∀{t1 t1'} t2 → t1 ↓* t1' → (app t1 t2) ↓* (app t1' t2)
  inj-l-app _ ε = ε
  inj-l-app {t1} t2 (fold x ◅ red) =
    apply-ind L-APP tt (λ {zero → IS.fold x}) ◅ inj-l-app t2 red
  
  inj-r-app : ∀{t2 t2'} v → t2 ↓* t2' → (app (inj-val-term v) t2) ↓* (app (inj-val-term v) t2')
  inj-r-app _ ε = ε
  inj-r-app {t2} v (fold x ◅ red) =
    apply-ind R-APP tt (λ {zero → IS.fold x}) ◅ inj-r-app v red
    
  val-not-reduce↓ : ∀{v e'} → ¬ (inj-val-term v ↓ e')
  val-not-reduce↓ {lambda _} (fold (β , c , () , pr))
  val-not-reduce↓ {lambda _} (fold (L-APP , c , () , pr))
  val-not-reduce↓ {lambda _} (fold (R-APP , c , () , pr))

  ↓-deterministic : ∀{e e' e''} → e ↓ e' → e ↓ e'' → e' ≡ e''
  ↓-deterministic (fold (β , (_ , lambda _) , refl , _)) (fold (β , (_ , lambda _) , refl , _)) = refl
  ↓-deterministic (fold (β , (_ , lambda _) , refl , _)) (fold (L-APP , _ , refl , _ , pr)) = ⊥-elim (val-not-reduce↓ (pr zero))
  ↓-deterministic (fold (β , (_ , lambda _) , refl , _)) (fold (R-APP , (lambda _ , _) , refl , _ , pr)) = ⊥-elim (val-not-reduce↓ (pr zero))
  ↓-deterministic (fold (L-APP , _ , refl , _ , pr)) (fold (β , _ , refl , _)) = ⊥-elim (val-not-reduce↓ (pr zero))
  ↓-deterministic (fold (L-APP , _ , refl , _ , pr)) (fold (L-APP , _ , refl , _ , pr')) = cong (λ x → app x _) (↓-deterministic (pr zero) (pr' zero))
  ↓-deterministic (fold (L-APP , _ , refl , _ , pr)) (fold (R-APP , _ , refl , _)) = ⊥-elim (val-not-reduce↓ (pr zero))
  ↓-deterministic (fold (R-APP , (lambda _ , _) , refl , _ , pr)) (fold (β , _ , refl , _)) = ⊥-elim (val-not-reduce↓ (pr zero))
  ↓-deterministic (fold (R-APP , (lambda _ , _) , refl , _ , _)) (fold (L-APP , _ , refl , _ , pr)) = ⊥-elim (val-not-reduce↓ (pr zero))
  ↓-deterministic (fold (R-APP , (lambda _ , _) , refl , _ , pr)) (fold (R-APP , (lambda _ , _) , refl , _ , pr')) = cong (λ x → app _ x) (↓-deterministic (pr zero) (pr' zero))

  ↓*-preserves-∞SS : ∀{e e'} → (∀{i} → ∞SS e i) → e ↓* e' → (∀{i} → ∞SS e' i)
  ↓*-preserves-∞SS ss ε = ss
  ↓*-preserves-∞SS ss (x ◅ red-e) with ss
  ↓*-preserves-∞SS ss (x ◅ red-e) | step x₁ x₂ =
    let e'-eq = ↓-deterministic x₁ x in
    ↓*-preserves-∞SS (≡.subst (λ x → (∀{i} → ∞SS x i)) e'-eq (x₂ .force)) red-e

  app-subst-∞SS : ∀{e v} → (∀{i} → ∞SS (app (lambda e) (inj-val-term v)) i) → (∀{i} → ∞SS (subst-0 e (inj-val-term v)) i)
  app-subst-∞SS ss with ss
  app-subst-∞SS {_} {lambda _} ss | step (fold (β , (_ , lambda _) , refl , _)) rec = rec .force
  app-subst-∞SS {_} {lambda _} ss | step (fold (L-APP , _ , refl , _ , pr)) _ = ⊥-elim (val-not-reduce↓ (pr zero))
  app-subst-∞SS {_} {lambda _} ss | step (fold (R-APP , (lambda _ , _) , refl , _ , pr)) rec = ⊥-elim (val-not-reduce↓ (pr zero))

  app-subst-∞SS₁ : ∀{e1 e1' e2 v} → e1 ↓* lambda e1' → e2 ↓* inj-val-term v → (∀{i} → ∞SS (app e1 e2) i) → (∀{i} → ∞SS (subst-0 e1' (inj-val-term v)) i)
  app-subst-∞SS₁ red-e1 red-e2 ss =
    let red-left = ↓*-preserves-∞SS ss (inj-l-app _ red-e1) in
    let red-right = ↓*-preserves-∞SS red-left (inj-r-app _ red-e2) in
    app-subst-∞SS red-right

  not-conv-next : ∀{e e'} → ¬ (Σ[ v ∈ Value ] e ↓* inj-val-term v) → e ↓ e' → ¬ (Σ[ v ∈ Value ] e' ↓* inj-val-term v)
  not-conv-next {e} {e'} n ss-e (v , ss-e') = ⊥-elim (n (v , ss-e ◅ ss-e'))
  
  div-app-l-not-conv : ∀{e1 e2} → (∀{i} → ∞SS (app e1 e2) i) → ¬ (e1 ConvergesSS) → (∀{i} → ∞SS e1 i)
  div-app-l-not-conv ss n-conv with ss
  div-app-l-not-conv ss n-conv | step (fold (β , _ , refl , _)) _ = ⊥-elim (n-conv (_ , ε))
  div-app-l-not-conv ss n-conv | step (fold (L-APP , _ , refl , _ , pr)) x₁ =
    step (pr zero) λ where .force → div-app-l-not-conv (x₁ .force) (not-conv-next n-conv (pr zero))
  div-app-l-not-conv ss n-conv | step (fold (R-APP , _ , refl , _)) _ = ⊥-elim (n-conv (_ , ε))

  div-app-r-not-conv : ∀{e1 e2 v} → (∀{i} → ∞SS (app e1 e2) i) → e1 ↓* inj-val-term v → ¬ (e2 ConvergesSS) → (∀{i} → ∞SS e2 i)
  div-app-r-not-conv ss red-e1 ¬e2-conv with ss
  div-app-r-not-conv ss red-e1 ¬e2-conv | step (fold (β , _ , refl , _)) _ = ⊥-elim (¬e2-conv (_ , ε))
  div-app-r-not-conv ss ε ¬e2-conv | step (fold (L-APP , _ , refl , _ , pr)) _ = ⊥-elim (val-not-reduce↓ (pr zero))
  div-app-r-not-conv ss (x ◅ red-e1) ¬e2-conv | step (fold (L-APP , _ , refl , _ , pr)) x₁ =
    div-app-r-not-conv (λ {i} → ≡.subst (λ x → ∞SS (app x _) i) (↓-deterministic (pr zero) x) (x₁ .force)) red-e1 ¬e2-conv
  div-app-r-not-conv ss red-e1 ¬e2-conv | step (fold (R-APP , (lambda _ , _) , refl , _ , pr)) x₁ =
    step (pr zero) λ where .force → div-app-r-not-conv (x₁ .force) red-e1 (not-conv-next ¬e2-conv (pr zero))

  ∞SS-reduce-↓ : ∀{e} → (∀{i} → ∞SS e i) → Σ[ e' ∈ Term 0 ] e ↓ e' × (∀{i} → ∞SS e' i)
  ∞SS-reduce-↓ ss with ss
  ∞SS-reduce-↓ ss | step s s' = _ , s , s' .force
  
  val-not-∞SS : ∀{e v} → e ↓ inj-val-term v → ¬ (∀{i} → ∞SS e i)
  val-not-∞SS {e} {v} ss ss' with ss'
  val-not-∞SS {.(app (lambda (var zero)) (lambda _))} {lambda _} (fold (β , (var zero , lambda _) , refl , _)) ss' | step (fold (β , (.(var zero) , lambda _) , refl , _)) rec =
    ⊥-elim (val-not-reduce↓ (proj₁ (proj₂ (∞SS-reduce-↓ (rec .force)))))
  val-not-∞SS {.(app (lambda (lambda _)) (lambda _))} {lambda _} (fold (β , (lambda _ , lambda _) , refl , _)) ss' | step (fold (β , (.(lambda _) , lambda _) , refl , _)) rec =
    ⊥-elim (val-not-reduce↓ (proj₁ (proj₂ (∞SS-reduce-↓ (rec .force)))))
  val-not-∞SS {.(app (lambda e1) e2)} {lambda _} (fold (β , (_ , lambda _) , _)) ss' | step (fold (L-APP , (lambda e1 , e1' , e2) , refl , _ , pr)) rec =
    ⊥-elim (val-not-reduce↓ (pr zero))
  val-not-∞SS {.(app e1 e2)} {lambda _} (fold (L-APP , _ , () , _)) ss' | step (fold (L-APP , (e1 , e1' , e2) , refl , _ , _)) _
  val-not-∞SS {.(app e1 e2)} {lambda _} (fold (R-APP , (lambda _ , _) , () , _)) ss' | step (fold (L-APP , (e1 , e1' , e2) , refl , _ , pr)) _
  val-not-∞SS {.(app (lambda _) (lambda e2))} {lambda _} (fold (β , (_ , lambda _) , _ , _)) ss' | step (fold (R-APP , (lambda _ , lambda e2 , e2') , refl , _ , pr)) rec =
    ⊥-elim (val-not-reduce↓ (pr zero))