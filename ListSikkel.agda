open import Data.Bool
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat

open import Model.BaseCategory
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Context hiding (_⟨_⟩; _⟪_⟫_)
open import Model.CwF-Structure.ContextExtension
open import Model.CwF-Structure.Term
open import Model.Helpers
open import Model.Type.Discrete
open import Model.Type.Sum
open import Model.Type.Product
open import Model.Type.Function

open import Level using (0ℓ)

open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Applications.UnaryParametricity.Model

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

module Thesis.ListSikkel {C : BaseCategory} (A : Ty {C} ◇) where

S : Set
S = Bool

Sm : S → Ty {C} ◇
Sm false = Unit'
Sm true = A

P : S → Set
P false = ⊥
P true = ⊤

open import Thesis.InductiveSikkel C S Sm P

Con : {Γ : Ctx C} → Ty Γ
Con {Γ} = A [ !◇ Γ ]

equivalenceF : {Γ : Ctx C} → {T : Ty Γ} → F T ≅ᵗʸ Unit' ⊞ ( Con ⊠ T )
func (from equivalenceF) (true , Sm , P) = inj₂ ( Sm , P tt)
func (from equivalenceF) (false , Sm , P) = inj₁ tt
_↣_.naturality (from equivalenceF) {t = false , sm , p} = cong inj₁ refl
_↣_.naturality (from equivalenceF) {t = true , sm , p} =
    cong inj₂ (cong₂ _,_ (ty-cong A refl) refl)
func (to equivalenceF) (inj₁ tt) = false , (tt , λ z → ⊥-elim z )
func (to equivalenceF) (inj₂ (con , t)) = true , (con , λ _ → t)
_↣_.naturality (to equivalenceF) {t = inj₁ tt} =
    Σ-≡-intro (refl , cong₂ _,_ refl (funext λ z → ⊥-elim z))
_↣_.naturality (to equivalenceF) {t = inj₂ (con , t)} =
    Σ-≡-intro (refl , cong₂ _,_ (ty-cong A refl) refl)
eq (isoʳ equivalenceF) (inj₁ tt) = refl
eq (isoʳ equivalenceF) (inj₂ (con , t)) = refl
eq (isoˡ equivalenceF) (false , tt , p) =
    Σ-≡-intro (refl , cong₂ _,_ refl (funext λ z → ⊥-elim z))
eq (isoˡ equivalenceF) (true , sm , p) =
    Σ-≡-intro (refl , cong₂ _,_ refl (funext λ z → refl))

currySikkel : {Γ : Ctx C} → {A B C : Ty Γ} → Tm Γ (A ⊠ B ⇛ C) →
    Tm Γ (A ⇛ B ⇛ C)
currySikkel {Γ} {A} {B} {C} tm =
    lam A (ι[_]_ (⇛-natural π) (lam (B [ π ]) (app
          (ι⁻¹[_]_
            (≅ᵗʸ-trans (ty-subst-cong-ty π (⇛-natural π)) (⇛-natural π))
            ((tm [ π ]') [ π ]'))
          (ι[_]_
            (ty-subst-cong-ty π (⊠-natural π))
            (ι[_]_ (⊠-natural π)(prim-pair (_[_]' ξ π) ξ))))))

List : {Γ : Ctx C} → Ty Γ
List = μF

empty : {Γ : Ctx C} → Tm Γ List
empty = ι⁻¹[_]_ isomorphismF (ι[_]_ equivalenceF (inl tt'))

cons : {Γ : Ctx C} → Tm Γ (Con ⇛ List ⇛ List)
cons = currySikkel (↣-to-⇛ (from isomorphismF ⊙ (to equivalenceF ⊙ ⇛-to-↣ inr-func)))

recList : {Γ : Ctx C} → {X : Ty Γ} → Tm Γ ((Unit' ⊞ (Con ⊠ X) ⇛ X)) → Tm Γ (List ⇛ X)
recList tm = ↣-to-⇛ (rec (⇛-to-↣ tm ⊙ from equivalenceF))

appToEmpty : {Γ : Ctx C} → {X : Ty Γ} → {f : Tm Γ ((Unit' ⊞ (Con ⊠ X) ⇛ X))}
  → app (recList f) empty ≅ᵗᵐ app f (inl tt')
eq appToEmpty γ = refl

appToCons : {Γ : Ctx C} → {X : Ty Γ} → {f : Tm Γ (Unit' ⊞ (Con ⊠ X) ⇛ X)} → {l : Tm Γ List} → {a : Tm Γ Con}
  → app (recList f) (app (app cons a) l) ≅ᵗᵐ app f (inr (prim-pair a (app (recList f) l)))
eq (appToCons {Γ} {X} {f} {l} {a}) {x} γ =  cong (λ z → f ⟨ x , γ ⟩' $⟨ BaseCategory.hom-id C , ctx-id Γ ⟩ inj₂ z)
      {x = (A ⟪ BaseCategory.hom-id C , refl ⟫
       A ⟪ BaseCategory.hom-id C , refl ⟫ a ⟨ x , γ ⟩'
       ,
       func
       (rec 
        (⇛-to-↣ f ⊙ from equivalenceF))
       (μFEmpty ⟪ BaseCategory.hom-id C
        , cong (λ _ → tt) (trans (ctx-id Γ) (ctx-id Γ)) ⟫
        μFEmpty ⟪ BaseCategory.hom-id C
        , cong (λ _ → tt) (trans (ctx-id Γ) (sym (ctx-id Γ))) ⟫
        l ⟨ x , γ ⟩'))}
      ((cong₂ _,_ (trans (ty-id A) (ty-id A)) (cong (func (rec (⇛-to-↣ f ⊙ from equivalenceF))){y = l ⟨ x , γ ⟩'} (trans (strong-ty-id μFEmpty) (strong-ty-id μFEmpty)))))

helper : {Γ : Ctx C} → Tm Γ ( (Unit' ⊞ (Con ⊠ Nat')) ⇛ Nat' )
helper = ⊞-elim Nat' (unit-elim Nat' zero') (↣-to-⇛ (⇛-to-↣ suc' ⊙ ⇛-to-↣ snd))

length : {Γ : Ctx C} → Tm Γ (List ⇛ Nat')
length = recList helper

emptyHasLengthZero : {Γ : Ctx C} → app length (empty {Γ}) ≅ᵗᵐ zero'
eq emptyHasLengthZero γ = refl

consHasLengthOne : {Γ : Ctx C} → {a : Tm Γ Con} →
    app length (app (app cons a) empty) ≅ᵗᵐ one'
eq consHasLengthOne γ = refl

consHasLengthTwo : {Γ : Ctx C} → {a b : Tm Γ Con} →
    app length (app (app cons a) (app (app cons b) empty)) ≅ᵗᵐ app suc' one'
eq consHasLengthTwo γ = refl

