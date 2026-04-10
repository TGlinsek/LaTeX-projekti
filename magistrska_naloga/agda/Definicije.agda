module Definicije where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.List

open import Relation.Nullary
open import Relation.Nullary using (¬_)
--open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.Membership.DecPropositional


infixr 5 _∷_d_

mutual
    data DistinctList (A : Set) : Set where
        []d  : DistinctList A
        _∷_d_ : (l : DistinctList A) → (a : A) → (a ∉d l) → DistinctList A

    data _∉d_ {A : Set} (n : A) : DistinctList A → Set where
        empty : n ∉d []d
        non-empty : {m : A} {l : DistinctList A} → (n ∉d l) → (p : m ∉d l) → ¬(n ≡ m) → n ∉d (l ∷ m d p)


module Atom (Atom : Set) 
    (_≟_ : (x y : Atom) → Dec (x ≡ y)) 
    (fresh : (xs : DistinctList Atom) → Σ Atom (λ (a : Atom) → a ∉d xs)) 
    where

    {-
    infix  5  ƛ_⇒_
    infixl 7  _·_
    infix  9  `_

    data Term : Set where
      `_ : Atom → Term
      ƛ_⇒_ : Atom → Term → Term
      _·_ : Term → Term → Term
    -}
    
    Context = DistinctList Atom

    infix  5  ƛ_⇒_
    infixl 7  _·_
    infix  9  `_
    
    data TermInContext : Context → Set where
      `_ : (Γ : Context) → (x : Atom) → ¬(x ∉d Γ) → TermInContext Γ
      _·_ : (Γ : Context) → TermInContext Γ → TermInContext Γ → TermInContext Γ
      ƛ_⇒_ : (Γ : Context) → (x : Atom) → (p : x ∉d Γ) → TermInContext (Γ ∷ x d p) → TermInContext Γ
      
