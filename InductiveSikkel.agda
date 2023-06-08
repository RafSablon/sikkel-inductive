open import Data.Product
open import Data.Unit
open import Model.BaseCategory
open import Model.CwF-Structure.Context hiding (_⟨_⟩; _⟪_⟫_)
open import Model.CwF-Structure.Type
open import Model.Helpers
open import Relation.Binary.PropositionalEquality hiding ([_])

module Thesis.InductiveSikkel (C : BaseCategory) (S : Set) (Sm : S → Ty {C} ◇)
  (P : S → Set) where

-- Definition functor

Σ-≡-intro :
  ∀ {α β}{A : Set α}{B : A → Set β}{a a' : A}{b : B a}{b' : B a'}
  → (Σ (a ≡ a') λ p → subst B p b ≡ b') → (a , b) ≡ (a' , b')
Σ-≡-intro (refl , refl) = refl

F : {Γ : Ctx C} → Ty Γ → Ty Γ
F T ⟨ x , γ ⟩ = Σ S (λ s → (Sm s ⟨ x , tt ⟩ × (P s → T ⟨ x , γ ⟩)))
F T ⟪ f , eγ ⟫ (s , sm , p) = s , Sm s ⟪ f , refl ⟫ sm , λ z → T ⟪ f , eγ ⟫  p z
ty-cong (F T) e-hom {t = s , sm , p} = Σ-≡-intro (refl ,
  cong₂ _,_ (ty-cong (Sm s) e-hom) (funext λ _ →  ty-cong T e-hom))
ty-id (F T) {t = s , sm , p} = Σ-≡-intro (refl ,
  cong₂ _,_ (strong-ty-id (Sm s) ) (funext λ _ → ty-id T))
ty-comp (F T) {t = s , sm , p} = Σ-≡-intro (refl ,
  cong₂ _,_ (ty-comp (Sm s)) (funext λ _ → ty-comp T) )

Fmap : {Γ : Ctx C} → {X : Ty Γ} → {Y : Ty Γ} → (X ↣ Y) → (F X ↣ F Y)
func (Fmap f) (s , sm , p) = s , sm , λ z → func f (p z)
_↣_.naturality (Fmap f) =
  Σ-≡-intro (refl , cong₂ _,_ refl (funext λ _ → _↣_.naturality f) )

-- Some lemma's about the functor

⊙-Fmap : {Γ : Ctx C} → {X Y Z : Ty Γ} → (f : X ↣ Y) → (g : Y ↣ Z) →
  (Fmap g) ⊙ (Fmap f) ≅ⁿ Fmap (g ⊙ f)
eq (⊙-Fmap f g) t = refl

≅ⁿ-Fmap : {Γ : Ctx C} → {X Y : Ty Γ} → {f g : X ↣ Y} → ( f ≅ⁿ g ) → (Fmap f) ≅ⁿ (Fmap g)
eq (≅ⁿ-Fmap equa) (s , sm , p) = Σ-≡-intro (refl , cong₂ _,_ refl (funext λ z → eq equa (p z)))

id-trans-Fmap : {Γ : Ctx C} → {X : Ty Γ} → Fmap (id-trans X) ≅ⁿ id-trans (F X)
eq id-trans-Fmap (s , sm , p) = Σ-≡-intro (refl , cong₂ _,_ refl (funext λ z → refl ))

-- Definition algebra of the functor

data μFData (x : BaseCategory.Ob C) : Set where
  fix : Σ S (λ s → (Sm s ⟨ x , tt ⟩ × (P s → μFData x))) → μFData x

μFEmpty : Ty {C} ◇
μFEmpty ⟨ x , γ ⟩ = μFData x
μFEmpty ⟪ f , eγ ⟫ fix (s , sm , p) =
  fix (s , Sm s ⟪ f , refl ⟫ sm , λ z → μFEmpty ⟪ f , eγ ⟫ p z )
ty-cong μFEmpty e-hom {t = fix (s , sm , p)} =
  cong fix (Σ-≡-intro (refl , cong₂ _,_ (ty-cong (Sm s) e-hom)
    (funext λ z → ty-cong μFEmpty e-hom {t = p z})
  ))
ty-id μFEmpty {t = fix (s , sm , p)} =
  cong fix (Σ-≡-intro (refl , cong₂ _,_ (ty-id (Sm s))
    (funext λ _ → ty-id μFEmpty)
  ))
ty-comp μFEmpty {t = fix (s , sm , p)} =
  cong fix (Σ-≡-intro (refl , cong₂ _,_ (ty-comp (Sm s))
    (funext λ o → ty-comp μFEmpty {t = p o})
  ))

μF : {Γ : Ctx C} → Ty Γ
μF {Γ} = μFEmpty [ !◇ Γ ]

-- Proof that μF is a weak initial algebra

rec : {Γ : Ctx C} → {X : Ty Γ} → ( F X ↣ X ) → (μF ↣ X) 
func (rec f) (fix (s , sm , p)) = func f (s , sm , λ z → func (rec f) (p z))
_↣_.naturality (rec {Γ} {X} f) {f = hom} {eγ = eγ} {t = fix (s , sm , p)} =
  begin
    X ⟪ hom , eγ ⟫ func f (s , sm , λ z → func (rec f) (p z))
  ≡⟨ _↣_.naturality f ⟩
    func f (F X ⟪ hom , eγ ⟫ (s , sm , (λ z → func (rec f) (p z))))
  ≡⟨ cong (func f) (Σ-≡-intro (refl , cong₂ _,_ refl
    (funext (λ z → _↣_.naturality (rec f) {t = p z}) )) )
  ⟩
    func (rec f) (μF {Γ} ⟪ hom , eγ ⟫ fix (s , sm , p)) ∎
  where open ≡-Reasoning

fixF : {Γ : Ctx C} → ( (F {Γ} μF) ↣ μF )
func fixF t = fix t
_↣_.naturality fixF {t = s , sm , p} = refl

commuteF : {Γ : Ctx C} → {X : Ty Γ} → { alg : F X ↣ X } →
  (rec {Γ} alg) ⊙ (fixF {Γ}) ≅ⁿ (alg) ⊙ (Fmap (rec {Γ} alg))
eq commuteF ( s , sm , p ) = refl

-- Proof that μF is an initial algebra

uniqueness : {Γ : Ctx C} → {X : Ty Γ} → { alg : F X ↣ X } → {g : μF ↣ X}
  → { commute : g ⊙ (fixF {Γ}) ≅ⁿ (alg) ⊙ (Fmap g) } → rec {Γ} alg ≅ⁿ g
eq (uniqueness {Γ} {X} {alg} {g} {comm}) {x} {γ} (fix (s , sm , p)) =
  begin
    func alg (s , sm , (λ z → func (rec alg) (p z)))
  ≡⟨ cong (func alg) (Σ-≡-intro (refl , cong₂ _,_ refl
      (funext λ o → eq (uniqueness {Γ} {X} {alg} {g} {comm}) (p o))))
  ⟩
    func alg (s , sm , (λ z → func g (p z)))
  ≡⟨ eq (≅ⁿ-sym comm) ((s , sm , p)) ⟩
    func g ( func {C} {Γ} {F μF} {μF} (fixF {Γ}) {x} {γ} (s , sm , p)) ∎
  where open ≡-Reasoning

-- Proof that μF is a fixpoint of the functor

fixFCommuteRec : {Γ : Ctx C}
  → fixF {Γ} ⊙ rec (Fmap fixF) ≅ⁿ rec (fixF {Γ})
fixFCommuteRec =
  ≅ⁿ-sym (uniqueness {alg = fixF}
                        {commute = record { eq = λ _ → refl }})

fromAfterToIsomorphismF : {Γ : Ctx C}
  → fixF {Γ} ⊙  rec (Fmap fixF) ≅ⁿ id-trans μF
fromAfterToIsomorphismF = ≅ⁿ-trans (fixFCommuteRec) (uniqueness {alg = fixF}
  {id-trans μF}
  {commute = ≅ⁿ-trans (⊙-id-transˡ fixF)
    (≅ⁿ-sym (≅ⁿ-trans (⊙-congˡ fixF id-trans-Fmap) (⊙-id-transʳ fixF)))}
  )

isomorphismF : {Γ : Ctx C} → F (μF {Γ}) ≅ᵗʸ μF {Γ}
from isomorphismF = fixF 
to isomorphismF = rec (Fmap fixF)
isoʳ isomorphismF = fromAfterToIsomorphismF
isoˡ isomorphismF = ≅ⁿ-trans commuteF (≅ⁿ-trans
  (⊙-Fmap (to isomorphismF) (from isomorphismF))
  (≅ⁿ-trans (≅ⁿ-Fmap (isoʳ isomorphismF)) id-trans-Fmap ))


