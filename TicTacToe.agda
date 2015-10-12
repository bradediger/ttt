module TicTacToe where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.Fin.Properties using (bounded)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties using (0∸n≡0; n∸m≤n; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_; _[_]≔_; lookup; allFin; replicate)
open import Function using (_∘_)
open import Relation.Binary using (Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)

-- Define simple All and Any predicates over vectors.
data All {A : Set} (P : A → Set) : ∀ {n} → Vec A n → Set where
  All-[] : All P []
  All-∷ : ∀ {x n} {xs : Vec A n} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : ∀ {n} → Vec A n → Set where
  here : ∀ {x n} {xs : Vec A n} → (px : P x) → Any P (x ∷ xs)
  there : ∀ {x n} {xs : Vec A n} → (pxs : Any P xs) → Any P (x ∷ xs)

-- Lemma lemma lemma.
n≤n : ∀ n → n ℕ.≤ n
n≤n ℕ.zero = ℕ.z≤n
n≤n (ℕ.suc n) = ℕ.s≤s (n≤n n)

≤-trans : Transitive ℕ._≤_
≤-trans ℕ.z≤n _ = ℕ.z≤n
≤-trans (ℕ.s≤s n≤m) (ℕ.s≤s m≤o) = ℕ.s≤s (≤-trans n≤m m≤o)

n∸x<1+n : ∀ n x → (n ℕ.∸ x) ℕ.< (ℕ.suc n)
n∸x<1+n n x = ≤-trans (ℕ.s≤s (n∸m≤n x n)) (n≤n (ℕ.suc n))

-- Unary inversion of the finite type. - (0 :: Fin n) = (n - 1 :: Fin n).
-_ : ∀ {n} → Fin n → Fin n
-_ {ℕ.zero} () -- no elements of Fin 0
-_ {ℕ.suc n} x = fromℕ≤ {n ℕ.∸ (toℕ x)} (n∸x<1+n n (toℕ x))

≢-suc-rewrite : ∀ {a b} → ℕ.suc a ≢ ℕ.suc b → a ≢ b
≢-suc-rewrite nope refl = nope refl

≢-pred-rewrite : ∀ {a b} → a ≢ b → ℕ.suc a ≢ ℕ.suc b
≢-pred-rewrite nope refl = nope refl

≤→< : ∀ a b → a ℕ.≤ b → a ≢ b → a ℕ.< b
≤→< .0 ℕ.zero ℕ.z≤n a≢b = ⊥-elim (a≢b refl)
≤→< .0 (ℕ.suc b) ℕ.z≤n a≢b = ℕ.s≤s ℕ.z≤n
≤→< (ℕ.suc a) (ℕ.suc b) (ℕ.s≤s a≤b) a≢b = ℕ.s≤s (≤→< a b a≤b (≢-suc-rewrite a≢b))

-- Shrink a Fin (n+1) to a Fin n, as long as the value will fit.
Fin-shrink : ∀ {n} → (k : Fin (ℕ.suc n)) → (toℕ k) ≢ n → Fin n
Fin-shrink {ℕ.zero} zero k≢n = ⊥-elim (k≢n refl)
Fin-shrink {ℕ.suc n} zero k≢n = zero
Fin-shrink {n} (suc k) k≢n = fromℕ≤ {ℕ.suc (toℕ k)} (≤→< (ℕ.suc (toℕ k)) n (bounded k) k≢n)

-- Advance a Fin n, modulo n.
%1_ : ∀ {n} → Fin n → Fin n
%1_ {ℕ.zero} ()
%1_ {ℕ.suc n} k with (toℕ k) ℕ.≟ n
%1_ {ℕ.suc n} k | yes p = zero
%1_ {ℕ.suc n} k | no ¬p = Fin-shrink (suc k) (≢-pred-rewrite ¬p)

-- A generalized Tic-Tac-Toe game with a given size and number of players.
module GameConfiguration (size : ℕ) (numPlayers : ℕ) (initialPlayer : Fin numPlayers) where
  Player = Fin numPlayers
  Board = Vec (Vec (Maybe Player) size) size
  Coordinate = Fin size × Fin size

  emptyBoard : Board
  emptyBoard = replicate (replicate nothing)

  -- Look up a position on the board.
  _⟨_⟩ : Board → Coordinate → Maybe Player
  b ⟨ i , j ⟩ = lookup j (lookup i b)

  -- Mark a position <i,j> on the board for player p.
  _⟨_⟩≔_ : Board → Coordinate → Player → Board
  b ⟨ i , j ⟩≔ p = b [ i ]≔ (lookup i b [ j ]≔ just p)

  -- These are the ways to win at tic-tac-toe.
  data Win (p : Player) (b : Board) : Set where
    rowWin      :                      Any (All (_≡_ (just p))) b  → Win p b
    columnWin   : ∀ {col} → All ((_≡_ (just p)) ∘ (lookup col)) b  → Win p b
    diagDownWin : All (λ i → b ⟨ i ,   i ⟩ ≡ just p) (allFin size) → Win p b
    diagUpWin   : All (λ i → b ⟨ i , - i ⟩ ≡ just p) (allFin size) → Win p b

  -- Current game state is the state of the board plus the next player to make a move.
  record State : Set where
    constructor state
    field
      board : Board
      nextPlayer : Player
  open State

  emptyState : State
  emptyState = state emptyBoard initialPlayer

  record Move (state : State) : Set where
    constructor move
    field
      coord : Coordinate
      -- The space we are attempting to play must be empty.
      isLegal : board state ⟨ coord ⟩ ≡ nothing
      -- Note that we have no explicit player here -- the next player
      -- is encoded in the game state.

  advancePlayer : Player → Player
  advancePlayer p = %1 p

  -- Execute a move, returning the new game state.
  makeMove : (before : State) → Move before → State
  makeMove (state board player) (move coord isLegal) =
    record { board      = board ⟨ coord ⟩≔ player ;
             nextPlayer = advancePlayer player }

module BoringTicTacToe where open GameConfiguration 3 2 zero
