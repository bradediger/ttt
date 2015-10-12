module NatLemmas where

open import Data.Empty using (⊥-elim)
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (Transitive)
open import Relation.Binary.PropositionalEquality

n≤n : ∀ n → n ≤ n
n≤n ℕ.zero = z≤n
n≤n (ℕ.suc n) = s≤s (n≤n n)

≤-trans : Transitive _≤_
≤-trans z≤n _ = z≤n
≤-trans (s≤s n≤m) (s≤s m≤o) = s≤s (≤-trans n≤m m≤o)

n∸x<1+n : ∀ n x → (n ∸ x) < (ℕ.suc n)
n∸x<1+n n x = ≤-trans (s≤s (n∸m≤n x n)) (n≤n (ℕ.suc n))

≢-suc-rewrite : ∀ {a b} → ℕ.suc a ≢ ℕ.suc b → a ≢ b
≢-suc-rewrite nope refl = nope refl

≢-pred-rewrite : ∀ {a b} → a ≢ b → ℕ.suc a ≢ ℕ.suc b
≢-pred-rewrite nope refl = nope refl

≤→< : ∀ a b → a ≤ b → a ≢ b → a < b
≤→< .0 0 z≤n a≢b = ⊥-elim (a≢b refl)
≤→< .0 (suc b) z≤n a≢b = s≤s z≤n
≤→< (suc a) (suc b) (s≤s a≤b) a≢b = s≤s (≤→< a b a≤b (≢-suc-rewrite a≢b))
