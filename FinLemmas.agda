module FinLemmas where

open import Data.Empty using (⊥-elim)
open import Data.Nat as ℕ
open import Data.Fin
open import Data.Fin.Properties
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality

open import NatLemmas

-- Unary inversion of the finite type. - (0 :: Fin n) = (n - 1 :: Fin n).
-_ : ∀ {n} → Fin n → Fin n
-_ {ℕ.zero} () -- no elements of Fin 0
-_ {ℕ.suc n} x = fromℕ≤ {n ℕ.∸ (toℕ x)} (n∸x<1+n n (toℕ x))

-- Shrink a Fin (n+1) to a Fin n, as long as the value will fit.
Fin-shrink : ∀ {n} → (k : Fin (ℕ.suc n)) → (toℕ k) ≢ n → Fin n
Fin-shrink {ℕ.zero} zero k≢n = ⊥-elim (k≢n refl)
Fin-shrink {ℕ.suc n} zero k≢n = zero
Fin-shrink {n} (suc k) k≢n = fromℕ≤ {ℕ.suc (toℕ k)} (≤→< (ℕ.suc (toℕ k)) n (bounded k) k≢n)

-- Advance a Fin n, modulo n.
advanceFin : ∀ {n} → Fin n → Fin n
advanceFin {ℕ.zero} ()
advanceFin {ℕ.suc n} k with (toℕ k) ℕ.≟ n
advanceFin {ℕ.suc n} k | yes p = zero
advanceFin {ℕ.suc n} k | no ¬p = Fin-shrink (suc k) (≢-pred-rewrite ¬p)
