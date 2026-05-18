module Definicije where

open import Agda.Builtin.List
open import Data.Bool.Base
-- open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary  -- za dec


-- navaden ∈ za liste
-- open import Data.List.Membership.Propositional


_⇒_ : Bool → Bool → Bool
true  ⇒ b = b
false ⇒ _ = true

helper :
  {a b : Bool} →
  ((a ≡ true) → (b ≡ true)) →
  (a ⇒ b) ≡ true
helper {true}  f = f refl
helper {false} f = refl

helper2 :
  {a b : Bool} → ((a ⇒ b) ≡ true) → (a ≡ true) → (b ≡ true)  -- puščice → so desno asociativne, kot pričakovano
helper2 {true}  {b} p pa = p
helper2 {false} {b} p ()


b : {a b : Bool} → ((a ≡ true) → (b ≡ true)) → ((b ≡ true) → (a ≡ true)) → ((a ⇒ b) ∧ (b ⇒ a) ≡ true)
b = {!   !}

{-
c : {a b : Bool} → ((a ⇒ b) ≡ true) → ((b ⇒ a) ≡ true) → ((a ≡ true) → (b ≡ true)) × ((b ≡ true) → (a ≡ true))
c = ?
-}

∨-trueˡ : (b : Bool) → true ∨ b ≡ true
∨-trueˡ b = refl

∨-trueʳ : (b : Bool) → b ∨ true ≡ true
∨-trueʳ false = refl
∨-trueʳ true  = refl

∧-true : true ∧ true ≡ true
∧-true = refl

∨-false-elim : {b : Bool} → (false ∨ b ≡ true) → (b ≡ true)
∨-false-elim hyp = hyp

∨-falseˡ : (b : Bool) → false ∨ b ≡ b
∨-falseˡ b = refl

∨-trueʳ2 : {b c : Bool} → c ≡ true → (b ∨ c) ≡ true
∨-trueʳ2 {false} refl = refl
∨-trueʳ2 {true}  refl = refl

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

absurdizem : false ≡ true → ⊥
absurdizem ()

∧-true-elim1 : {p q : Bool} → {p ∧ q ≡ true} → (p ≡ true)
∧-true-elim1 {true}  {true}  = refl

∧-true-elim2 : {p q : Bool} → {p ∧ q ≡ true} → (q ≡ true)
∧-true-elim2 {true}  {true}  = refl

∧-true-from-components : {p q : Bool} → p ≡ true → q ≡ true → (p ∧ q ≡ true)
∧-true-from-components refl refl = refl

∧-true-intro : {p q : Bool} → (p ≡ true) → (q ≡ true) → (p ∧ q ≡ true)
∧-true-intro refl refl = refl

∧-falseʳ : {b : Bool} → (b ∧ false) ≡ false
∧-falseʳ {false} = refl
∧-falseʳ {true}  = refl

∨-congˡ : {b₁ b₂ c : Bool} → b₁ ≡ b₂ → (b₁ ∨ c) ≡ (b₂ ∨ c)
∨-congˡ refl = refl

∨-trueˡ' : {b c : Bool} → (p : b ≡ true) → ((b ∨ c) ≡ true)
∨-trueˡ' refl = refl

∨-falseˡ' : {b c : Bool} → b ≡ false → (b ∨ c) ≡ true → c ≡ true
∨-falseˡ' refl p = p

∧-false-from-left : {p q : Bool} → p ≡ false → (p ∧ q) ≡ false
∧-false-from-left refl = refl


∧-false-from-right : {p q : Bool} → q ≡ false → (p ∧ q) ≡ false
∧-false-from-right {false} refl = refl
∧-false-from-right {true}  refl = refl


∨-false-elim' : {p q : Bool} → p ≡ false → (p ∨ q ≡ true) → q ≡ true
∨-false-elim' refl pr = pr

∨-false-elim'' : {b c : Bool} → b ≡ false → (b ∨ c ≡ true) → c ≡ true
∨-false-elim'' refl p = p

kontrapozitiv1 : {a b : Bool} → (f : (a ≡ false) → (b ≡ false)) → (b ≡ true) → (a ≡ true)
kontrapozitiv1 {true}  f pb = refl
kontrapozitiv1 {false} f pb rewrite f refl = pb

kontrapozitiv2 : {a b : Bool} → (f : (a ≡ true) → (b ≡ true)) → (b ≡ false) → (a ≡ false)
kontrapozitiv2 {false} f pb = refl
kontrapozitiv2 {true} f pb rewrite f refl = pb

kontrapozitiv3 : {a b : Bool} → (f : (a ≡ true) → (b ≡ false)) → (b ≡ true) → (a ≡ false)
kontrapozitiv3 {false} f pb = refl
kontrapozitiv3 {true} f pb rewrite f refl = sym pb

kontrapozitiv4 : {a b : Bool} → (f : (a ≡ false) → (b ≡ true)) → (b ≡ false) → (a ≡ true)
kontrapozitiv4 {true} f pb = refl
kontrapozitiv4 {false} f pb rewrite f refl = sym pb

module Atom (Atom : Set)
    (_≟_ : (x y : Atom) → Dec (x ≡ y))
    where

    Dec→Bool : {P : Set} → Dec P → Bool
    Dec→Bool (yes _) = true
    Dec→Bool (no  _) = false
    
    _==_ : Atom → Atom → Bool
    _==_ x y = Dec→Bool (_≟_ x y)


    ∧-false-from-left2 : {a b x y : Atom} → (_==_ b y ≡ false) → (_==_ b y ∧ _==_ a x) ≡ false
    ∧-false-from-left2 p = ∧-false-from-left p

    ∧-false-from-right2 : {a b x y : Atom} → (_==_ a x ≡ false) → (_==_ b y ∧ _==_ a x) ≡ false
    ∧-false-from-right2 p = ∧-false-from-right p

    mutual
        infixr 10 _∷_d_


        data DistinctList : Set where
            []d  : DistinctList
            _∷_d_ : (l : DistinctList) → (a : Atom) → ((a ∈d l) ≡ false) → DistinctList
    
        infix 9 _∈d_
        
        _∈d_ : Atom → DistinctList → Bool
        _∈d_ n []d = false
        _∈d_ n (l ∷ m d p) = (_==_ n m) ∨ (n ∈d l)
    
    -- enakost distinct listov
    _==d_ : (Γ : DistinctList) → (Γ' : DistinctList) → Bool
    _==d_ []d []d = true
    _==d_ (l ∷ a d _) (l' ∷ b d _) = (a == b) ∧ (l ==d l')
    _==d_ _ _ = false

    toList : DistinctList → List Atom
    toList []d = []
    toList (l ∷ x d p) = x ∷ (toList l)

    infix 9 _∈_
    
    _∈_ : Atom → List Atom → Bool
    _∈_ a [] = false
    _∈_ a (x ∷ xs) = (_==_ a x) ∨ (a ∈ xs)


    Context = DistinctList

    infixr 6  ƛ_⇒_
    infixl 7  _·_
    -- infix  9  `_
    
    data TermInContext : Context → Set where
        `_ : {Γ : Context} → (x : Atom) → {(x ∈d Γ) ≡ true} → TermInContext Γ
        _·_ : {Γ : Context} → TermInContext Γ → TermInContext Γ → TermInContext Γ
        ƛ_⇒_ : {Γ : Context} → (x : Atom) → {p : (x ∈d Γ) ≡ false} → (TermInContext (Γ ∷ x d p)) → TermInContext Γ
    
    -- addAtomToDistinctList : (Γ : Context) → (x : Atom) → (p : (x ∈d Γ) ≡ false) → Context
    -- addAtomToDistinctList Γ x p = Γ ∷ x d p

    singleton : {A : Set} → A → List A
    singleton x = x ∷ []

    concat : {A : Set} → List A → List A → List A
    concat [] B = B
    concat (x ∷ xs) B = x ∷ (concat xs B)

    invertList : {A : Set} → List A → List A
    invertList [] = []
    invertList (x ∷ xs) = concat xs (singleton x)


    record Nosilec : Set where
        constructor ustvari
        field
            proste : DistinctList  -- proste so itak v kontekstu, ki je tipa DistinctList
            vezane : List Atom  -- vezane je treba še hraniti. Verjetno je lažje z navadnim seznamom, ker če dodajamo dva izraza, ki imata isto vezano spremenljivko, potem ni treba gledati duplikatov.
            -- tk da ja, lažje pisat z navadnim seznamom kot distinctlistom. Kontekst je pa že distinct list

    supp_ : {Γ : Context} → TermInContext Γ → Nosilec
    supp_ {Γ} (` x) = ustvari Γ []
    supp_ {Γ} (M · N) = ustvari Γ (concat (Nosilec.vezane (supp M)) (Nosilec.vezane (supp N)))
    supp_ {Γ} (ƛ x ⇒ M) = ustvari Γ (concat (singleton x) (Nosilec.vezane (supp M)))

    -- spremenljivka ne more biti prosta in vezana hkrati
    disjunktnost : {Γ : Context} → (M : TermInContext Γ) → (x : Atom) → (s : (x ∈d Nosilec.proste (supp M)) ≡ true) → ((x ∈ Nosilec.vezane (supp M)) ≡ false)
    disjunktnost = {!   !}

    disjunktnost2 : {Γ : Context} → (M : TermInContext Γ) → (x : Atom) → (s : (x ∈ Nosilec.vezane (supp M)) ≡ true) → ((x ∈d Nosilec.proste (supp M)) ≡ false)
    disjunktnost2 {Γ} M x s = kontrapozitiv3 (disjunktnost {Γ} M x) s

    record Par : Set where
        constructor _,_
        field
            x : Atom
            y : Atom
    
        
    Perm = List Par
    
    inverz : (π : Perm) → Perm
    inverz π = invertList π

    _preslika_ : Perm → Atom → Atom
    _preslika_ [] a = a
    _preslika_ ((x , y) ∷ xs) a with (_==_ a x)
    ... | true = y
    ... | false with (_==_ a y)
    ...     | true = x
    ...     | false = xs preslika a


    -- ali pa "JeKongruentna"
    permutacijaJeEnolična : {a : Atom} → {b : Atom} → {π : Perm} → (a ≡ b) → ((_preslika_ π a) ≡ (_preslika_ π b))
    permutacijaJeEnolična refl = refl

    permutacijaJeInjektivna : {a : Atom} → {b : Atom} → {π : Perm} → ((_preslika_ π a) ≡ (_preslika_ π b)) → (a ≡ b)
    permutacijaJeInjektivna p = {!   !}


    obstojInverza : {a b : Atom} → {π : Perm} → (_preslika_ π a ≡ b) → (_preslika_ (inverz π) b ≡ a)
    obstojInverza p = {!   !}

    enoličnostInverza : {a b : Atom} → {π : Perm} → (_preslika_ (inverz π) b ≡ a) → (_preslika_ π a ≡ b)
    enoličnostInverza p = {!   !}


    kompozicijaZInverzomZLeve : {a : Atom} → {π : Perm} → (_==_ a (_preslika_ (inverz π) (_preslika_ π a)) ≡ true)
    kompozicijaZInverzomZLeve = {!   !}

    kompozicijaZInverzomZDesne : {a : Atom} → {π : Perm} → (_==_ a (_preslika_ π (_preslika_ (inverz π) a)) ≡ true)
    kompozicijaZInverzomZDesne = {!   !}

    mutual
            
        _delujeNaKontekstu_ : Perm → Context → Context
        _delujeNaKontekstu_ π []d = []d
        _delujeNaKontekstu_ π (l ∷ x d p) = (π delujeNaKontekstu l) ∷ (π preslika x) d (aux2 {x} {l} {π} p)

        aux1 : {x : Atom} → {l : DistinctList} → {π : Perm} → (((π preslika x) ∈d (π delujeNaKontekstu l)) ≡ true) → ((x ∈d l) ≡ true)
        aux1 = {!   !}

        aux2 : {x : Atom} → {l : DistinctList} → {π : Perm} → (s : (x ∈d l) ≡ false) → (((π preslika x) ∈d (π delujeNaKontekstu l)) ≡ false)
        aux2 {x} {l} {π} s = kontrapozitiv2 (aux1 {x} {l} {π}) s

    -- map za distinct list (tega verjetno ne bomo rabili, ker je delujeNaKontekstu že točno to)
    preslikaDSeznam : (f : Atom → Atom) → (inj : (a x : Atom) → (_==_ a x ≡ false) → (_==_ (f a) (f x) ≡ false)) → DistinctList → DistinctList
    preslikaDSeznam f l = {!   !}

    -- map za list
    preslikaSeznam : (f : Atom → Atom) → List Atom → List Atom
    preslikaSeznam f []       = []
    preslikaSeznam f (b ∷ rs) = f b ∷ (preslikaSeznam f rs)


    obstojInverzaZaPermutacijeNaKontekstih : {a b : Atom} → {π : Perm} → (_preslika_ π a ≡ b) → (_preslika_ (inverz π) b ≡ a)
    obstojInverzaZaPermutacijeNaKontekstih p = {!   !}

    enoličnostInverzaZaPermutacijeNaKontekstih : {a b : Atom} → {π : Perm} → (_preslika_ (inverz π) b ≡ a) → (_preslika_ π a ≡ b)
    enoličnostInverzaZaPermutacijeNaKontekstih p = {!   !}


    kompozicijaZInverzomZaPermutacijeNaKontekstihZLeve : {Γ : Context} → {π : Perm} → (Γ ==d (_delujeNaKontekstu_ (inverz π) (_delujeNaKontekstu_ π Γ)) ≡ true)
    kompozicijaZInverzomZaPermutacijeNaKontekstihZLeve = {!  !} 

    kompozicijaZInverzomZaPermutacijeNaKontekstihZDesne : {Γ : Context} → {π : Perm} → (Γ ==d (_delujeNaKontekstu_ π (_delujeNaKontekstu_ (inverz π) Γ)) ≡ true)
    kompozicijaZInverzomZaPermutacijeNaKontekstihZDesne = {!  !} 



    ------------


    -- fold
    all : (Atom → Bool) → List Atom → Bool
    all p [] = true
    all p (x ∷ xs) = p x ∧ all p xs


    infix 5 _⊢_#_

    -- separatedness relation
    _⊢_#_ : {A B : Context} → (Γ : Context) → TermInContext A → TermInContext B → Bool
    _⊢_#_ {A} {B} Γ M N = all (
            λ x → (
                (
                    (_∈d_ x B) ∨ 
                    (_∈_ x (Nosilec.vezane (supp N)))
                ) 
                ⇒ (_∈d_ x Γ)
            )
        ) 
        (
            concat 
            (toList A) 
            (Nosilec.vezane (supp M))
        )

    separiranostSimetrična : {A B : Context} → (Γ : Context) → (M : TermInContext A) → (N : TermInContext B) → (p : Γ ⊢ M # N ≡ true) → (Γ ⊢ N # M ≡ true)
    separiranostSimetrična Γ M N = {!   !}

    
    substitucija : {Γ : Context} → (N : TermInContext Γ) → (x : Atom) → {p : (x ∈d Γ) ≡ false} → (M : TermInContext (Γ ∷ x d p)) → {s : Γ ⊢ M # N ≡ true} → (TermInContext Γ)
    substitucija {Γ} N x {p} M {s} = {!   !}

    _[_/_] : {Γ : Context} → {a : Atom} → {p : (a ∈d Γ) ≡ false} → (M : TermInContext (Γ ∷ a d p)) → (N : TermInContext Γ) → (x : Atom) → {q : _==_ a x ≡ true} → {s : Γ ⊢ M # N ≡ true} → (TermInContext Γ)
    _[_/_] {Γ} {a} {p} M N x {q} {s} =
        let
            p' : (x ∈d Γ) ≡ false  -- uporabi q, ki je tipa _==_ a x ≡ true, in p
            p' = {!   !}

            M' : TermInContext (Γ ∷ x d p')
            M' = {!   !}

            s' : Γ ⊢ M' # N ≡ true
            s' = {!   !}
        in
            substitucija {Γ} N x {p'} M' {s'}