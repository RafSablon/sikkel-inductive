open import Data.Bool
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Empty 

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

module Thesis.List (A : Set) where

S : Set
S = ⊤ ⊎ A

P : S → Set
P (inj₁ tt) = ⊥
P (inj₂ a) = ⊤

open import Thesis.Inductive S P

List : Set
List = μF

empty : List
empty = fix (inj₁ tt , ⊥-elim)

cons : A → List → List
cons a l = fix (inj₂ a , λ _ → l)

f : F Nat → Nat
f (inj₁ x , snd) = 0
f (inj₂ y , snd) = 1 + snd tt

length : List → Nat
length x = rec f x

eqEmpty : length empty ≡ 0
eqEmpty = refl

eqList : {x y : A} → length (cons x (cons y empty)) ≡ 2
eqList = refl
