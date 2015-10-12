module VectorProperties where

open import Data.Vec

-- Define simple All and Any predicates over vectors.
data All {A : Set} (P : A → Set) : ∀ {n} → Vec A n → Set where
  All-[] : All P []
  All-∷ : ∀ {x n} {xs : Vec A n} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : ∀ {n} → Vec A n → Set where
  here : ∀ {x n} {xs : Vec A n} → (px : P x) → Any P (x ∷ xs)
  there : ∀ {x n} {xs : Vec A n} → (pxs : Any P xs) → Any P (x ∷ xs)
