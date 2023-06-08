open import Data.Product

module Thesis.Inductive (S : Set) (P : S → Set) where

F : Set → Set
F T = Σ S (λ s → P s → T)

Fmap : {X : Set} → {Y : Set} → (X → Y) → (F X → F Y)
Fmap f (fst , snd) = fst , λ x → f (snd x) 

data μF : Set where
  fix : (F μF) → μF

rec : {X : Set} → ( F X → X ) → μF → X 
rec {X} f (fix (fst , snd)) = f (fst , λ x → rec f (snd x) )
