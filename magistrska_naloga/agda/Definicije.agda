module Definicije where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Data.Bool.Base

open import Relation.Nullary
open import Relation.Nullary using (¬_)
--open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.Membership.DecPropositional


module Atom (Atom : Set) 
    (_≟_ : (x y : Atom) → Dec (x ≡ y)) 
    -- (fresh : (xs : DistinctList Atom) → Σ Atom (λ (a : Atom) → a ∉d xs)) 
    where

    infixr 5 _∷_d_

    mutual
        data DistinctList : Set where
            []d  : DistinctList
            _∷_d_ : (l : DistinctList) → (a : Atom) → ((a ∈d l) ≡ false) → DistinctList
        
        Dec→Bool : {P : Set} → Dec P → Bool
        Dec→Bool (yes _) = true
        Dec→Bool (no  _) = false
        
        _==_ : Atom → Atom → Bool
        _==_ x y = Dec→Bool (_≟_ x y)

        _∈d_ : Atom → DistinctList → Bool
        _∈d_ n []d = false
        _∈d_ n (l ∷ m d p) = (_==_ n m) ∨ (n ∈d l)
        
        --n ∈d (l ∷ m d p) = (n ≡ m) ∨ (n ∈d l)
        
    {-
    infix  5  ƛ_⇒_
    infixl 7  _·_
    infix  9  `_

    data Term : Set where
      `_ : Atom → Term
      ƛ_⇒_ : Atom → Term → Term
      _·_ : Term → Term → Term
    -}
    
    Context = DistinctList

    infix  5  ƛ_⇒_
    infixl 7  _·_
    infix  9  `_
    
    data TermInContext : Context → Set where
      `_ : (Γ : Context) → (x : Atom) → ((x ∈d Γ) ≡ true) → TermInContext Γ
      _·_ : (Γ : Context) → TermInContext Γ → TermInContext Γ → TermInContext Γ
      ƛ_⇒_ : (Γ : Context) → (x : Atom) → (p : (x ∈d Γ) ≡ false) → TermInContext (Γ ∷ x d p) → TermInContext Γ
      
