module TicTacToe where

open import Data.Fin using (Fin; zero)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_; _[_]≔_; lookup; allFin; replicate)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- Boring lemmas that we need, the details of which are not terribly
-- relevant to the problem at hand.
open import NatLemmas
open import FinLemmas
open import VectorProperties -- All / Any

-- TODO how much of this can be factored out into a generic N-player game?
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

  -- Execute a move, returning the new game state.
  makeMove : (before : State) → Move before → State
  makeMove (state board player) (move coord isLegal) =
    record { board      = board ⟨ coord ⟩≔ player ;
             nextPlayer = advanceFin player }

module BoringTicTacToe where open GameConfiguration 3 2 zero
