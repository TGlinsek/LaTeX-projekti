module Definicije where


open import Agda.Builtin.List
open import Data.Bool.Base
-- open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong; cong₂)
open import Relation.Nullary  -- za dec

open import Data.Empty using (⊥-elim)
-- navaden ∈ za liste
-- open import Data.List.Membership.Propositional

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _,_)

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



{-
c : {a b : Bool} → ((a ⇒ b) ≡ true) → ((b ⇒ a) ≡ true) → ((a ≡ true) → (b ≡ true)) × ((b ≡ true) → (a ≡ true))
c = ?
-}

∨-trueˡ : (b : Bool) → true ∨ b ≡ true
∨-trueˡ b = refl

∨-trueˡ- : {b : Bool} → true ∨ b ≡ true
∨-trueˡ- = refl



∨-trueʳ : (b : Bool) → b ∨ true ≡ true
∨-trueʳ false = refl
∨-trueʳ true  = refl

∨-true3 : {b a : Bool} → (g : a ≡ true) → b ∨ a ≡ true
∨-true3 {b} g rewrite g with b
... | true  = refl
... | false = refl

∨-true4 : {b a : Bool} → (g : a ≡ true) → a ∨ b ≡ true
∨-true4 {b} g rewrite g with b
... | true  = refl
... | false = refl


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

⊥-elim2 : {A : Set} → ⊥ → A
⊥-elim2 ()

absurdizem : false ≡ true → ⊥
absurdizem ()

absurdizem2 : true ≡ false → ⊥
absurdizem2 p = absurdizem (sym p)  -- lahko bi tudi kar () napisali

∧-true-elim1 : {p q : Bool} → {p ∧ q ≡ true} → (p ≡ true)
∧-true-elim1 {true}  {true}  = refl

∧-true-elim2 : {p q : Bool} → {p ∧ q ≡ true} → (q ≡ true)
∧-true-elim2 {true}  {true}  = refl

∧-true-elim1' : {p q : Bool} → (p ∧ q ≡ true) → (p ≡ true)
∧-true-elim1' {true}  h = refl
∧-true-elim1' {false} ()

∧-true-elim2' : {p q : Bool} → (p ∧ q ≡ true) → (q ≡ true)
∧-true-elim2' {true} h = h
∧-true-elim2' {false} ()

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

∨-false-left : {a b : Bool} → a ∨ b ≡ false → a ≡ false
∨-false-left {false} h = refl
∨-false-left {true} ()

∨-false-right : {a b : Bool} → a ∨ b ≡ false → b ≡ false
∨-false-right {false} h = h
∨-false-right {true}  ()


∨-intro-false : {a b : Bool} → a ≡ false → b ≡ false → a ∨ b ≡ false
∨-intro-false {false} {false} a b = refl
∨-intro-false {true}  {false} ()
∨-intro-false {true}  {true} ()
∨-intro-false {false}  {true} a b = ⊥-elim2 (absurdizem2 b)

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







------ Atom ------

module Atom (Atom : Set)
    (_≟_ : (x y : Atom) → Dec (x ≡ y))
    where

    Dec→Bool : {P : Set} → Dec P → Bool
    Dec→Bool (yes _) = true
    Dec→Bool (no  _) = false
    
    _==_ : Atom → Atom → Bool
    _==_ x y = Dec→Bool (_≟_ x y)

    ==-refl : {a : Atom} → (_==_ a a ≡ true)
    ==-refl {a} with a ≟ a
    ... | yes _ = refl
    ... | no  ¬p = ⊥-elim (¬p refl)

    ≡-to-== : {a x : Atom} → a ≡ x → (_==_ a x ≡ true)
    -- ≡-to-== {a} {x} refl with a ≟ a
    -- ... | yes _ = refl
    -- ... | no ¬p = ⊥-elim (¬p refl)
    ≡-to-== {a} {x} refl = ==-refl

    ==-to-≡ : {a x : Atom} → (_==_ a x ≡ true) → a ≡ x
    ==-to-≡ {a} {x} p with a ≟ x
    ... | yes q = q
    ... | no  ¬q = ⊥-elim2 (absurdizem p)

    ==-sym : {a b : Atom} → (_==_ a b ≡ _==_ b a)
    ==-sym {a} {b} with a ≟ b in eq | b ≟ a in eq2
    ... | yes _ | yes _ = refl
    ... | no  _ | no  _ = refl
    ... | yes p | no np = ⊥-elim (np (sym p))
    ... | no np | yes p = ⊥-elim (np (sym p))

    ==-false-sym : {a b : Atom} → (_==_ a b ≡ false) → (_==_ b a ≡ false)
    ==-false-sym {a} {b} p rewrite sym (==-sym {a} {b}) = p

    ==-trans : {a b c : Atom} → (pab : _==_ a b ≡ true) → (pbc : _==_ b c ≡ true) → (_==_ a c ≡ true)
    ==-trans pab pbc = ≡-to-== (trans (==-to-≡ pab) (==-to-≡ pbc))

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
    
    -- dodaj : (Γ : Context) → (x : Atom) → (p : (x ∈d Γ) ≡ false) → Context
    -- dodaj Γ x p = Γ ∷ x d p

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
        `_ : {Γ : Context} → (x : Atom) → {q : (x ∈d Γ) ≡ true} → TermInContext Γ
        _·_ : {Γ : Context} → TermInContext Γ → TermInContext Γ → TermInContext Γ
        ƛ_⇒_ : {Γ : Context} → (x : Atom) → {p : (x ∈d Γ) ≡ false} → (TermInContext (Γ ∷ x d p)) → TermInContext Γ
    
    -- addAtomToDistinctList : (Γ : Context) → (x : Atom) → (p : (x ∈d Γ) ≡ false) → Context
    -- addAtomToDistinctList Γ x p = Γ ∷ x d p

    singleton : {A : Set} → A → List A
    singleton x = x ∷ []

    {-  smo zamenjali z ++
    concat : {A : Set} → List A → List A → List A
    concat [] B = B
    concat (x ∷ xs) B = x ∷ (concat xs B)
    -}

    invertList : {A : Set} → List A → List A
    invertList [] = []
    invertList (x ∷ xs) = _++_ xs (singleton x)

    ∨-false-from-right : {a b : Bool} → ((a ∨ b) ≡ false) → (b ≡ false)
    ∨-false-from-right {false} p = p

    ∨-false-from-left : {a b : Bool} → ((a ∨ b) ≡ false) → (a ≡ false)
    ∨-false-from-left {false} p = refl

    ∨-false : {a b : Bool} → (a ≡ false) → (b ≡ false) → ((a ∨ b) ≡ false)
    ∨-false refl refl = refl
    
    mutual

        remove : (x : Atom) → DistinctList → DistinctList
        remove x []d = []d
        remove x (ys ∷ y d p) with (_==_ y x)
        ... | true = ys
        ... | false = (remove x ys) ∷ y d (pomoznaFunkcija x y ys p) 

        pomoznaFunkcija : (x y : Atom) → (l : DistinctList) → ((y ∈d l) ≡ false) → ((y ∈d (remove x l)) ≡ false)
        pomoznaFunkcija x y []d q = q
        pomoznaFunkcija x y (zs ∷ z d p) q with (_==_ y z) in eq
        ... | true rewrite eq = ⊥-elim2 (absurdizem2 q)
        ... | false with (_==_ z x)
        ...     | true rewrite eq = ∨-false-from-right q
        ...     | false = 
                let
                    brr : (y ∈d zs) ≡ false
                    brr = q
                in
                    ∨-false eq (pomoznaFunkcija x y zs brr)


    ---------------- NomSet ------------------


    record NomSet : Set₁ where
        field
            USet : Set
            supp : USet → List Atom
    
    
    prod : NomSet → NomSet → NomSet
    prod A B = record {
            USet = (NomSet.USet A) × (NomSet.USet B);
            supp = (λ (a , b) → _++_ (NomSet.supp A a) (NomSet.supp B b))
        }
    
    
    
    Nosilec = List Atom

    supp_ : {Γ : Context} → TermInContext Γ → Nosilec
    supp_ {Γ} (` x) = toList Γ
    supp_ {Γ} (M · N) = _++_ (supp M) (supp N)
    supp_ {Γ} (ƛ x ⇒ M) = supp M


    NomTermInContext : (Γ : Context) → NomSet
    NomTermInContext Γ = (
        record {
            USet = TermInContext Γ;
            supp = supp_ {Γ}
        })
    

    NomContext : NomSet
    NomContext = (
        record {
            USet = Context;
            supp = toList
        })

    NomAtom : NomSet
    NomAtom = (
        record {
            USet = Atom;
            supp = (λ x → singleton x)
        })

    record Par : Set where
        constructor _,,_
        field
            x : Atom
            y : Atom
    
    
    Perm = List Par
    
    inverz : (π : Perm) → Perm
    inverz π = invertList π

    _preslika_ : Perm → Atom → Atom
    _preslika_ [] a = a
    _preslika_ ((x ,, y) ∷ xs) a with (_==_ a x)
    ... | true = y
    ... | false with (_==_ a y)
    ...     | true = x
    ...     | false = xs preslika a

    lemica : (l : DistinctList) → (y c : Atom) {p : c ∈d l ≡ false} → (y ∈d (l ∷ c d p) ≡ false) → (y ∈d l ≡ false)
    lemica = {!   !}

    
    mutual
        -- zamenjaj x, ki je v gami, v y
        zamenjaj : (Γ : Context) → (x y : Atom) → (px : x ∈d Γ ≡ true) → (py : y ∈d Γ ≡ false) → Context
        zamenjaj []d x y px py = ⊥-elim2 (absurdizem px)
        zamenjaj (l ∷ c d p) x y px py with (_==_ x c) in eq
        ... | true = l ∷ y d (lemica l y c {p} py)
        ... | false = 
            let
                g : (_==_ y c ≡ false)
                g = ∨-false-left py

                hx : x ∈d l ≡ true
                hx = px

                hy : y ∈d l ≡ false
                hy = ∨-false-right py

                zamenjan : Context
                zamenjan = zamenjaj l x y hx hy
                
                f : (l : Context) → (h : Atom) → (h ∈d l ≡ false) → (h == y ≡ false) -> (h ∈d zamenjan ≡ false)
                f = {!   !}
            in
                zamenjan ∷ c d (f l c p (==-false-sym g))
        
        zamenjajDokazX : (Γ : Context) → (x y : Atom) → (px : x ∈d Γ ≡ true) → (py : y ∈d Γ ≡ false) → (x ∈d (zamenjaj Γ x y px py) ≡ false)
        zamenjajDokazX = {!   !}
        
        zamenjajDokazY : (Γ : Context) → (x y : Atom) → (px : x ∈d Γ ≡ true) → (py : y ∈d Γ ≡ false) → (y ∈d (zamenjaj Γ x y px py) ≡ true)
        zamenjajDokazY = {!   !}
    
    
    {-
    switchContext : (Γ : Context) → (x y : Atom) → Context
    switchContext []d x y = []d
    switchContext (l ∷ c d p) x y with (_==_ x c) in eqX
    ... | true with (_==_ y c) in eqY
    ...     | true = l ∷ c d p
    ...     | false = l ∷ y
    ... | false with (_==_ y c)
    ...     | true = l ∷ x
    ...     | false = l ∷ c d p
    -}
    
    {-
    switch : (Γ : Context) → (M : TermInContext Γ) → (x y : Atom) → TermInContext (switchContext x y Γ)
    switch 
    -}
    pomoč1 : {Γ : Context} → {x z : Atom} → (px : x ∈d Γ ≡ false) → (pz : z ∈d Γ ≡ false) → (eq : x == z ≡ false) → (z ∈d (Γ ∷ x d px) ≡ false)
    pomoč1 = {!   !}

    pomoč2 : {Γ : Context} → {x z : Atom} → (px : x ∈d Γ ≡ false) → (pz : z ∈d Γ ≡ false) → (eq : x == z ≡ false) → (x ∈d (Γ ∷ z d pz) ≡ false)
    pomoč2 = {!   !}

    switch2 : {Γ : Context} → {x z : Atom} → (px : x ∈d Γ ≡ false) → (pz : z ∈d Γ ≡ false) → (eq : x == z ≡ false) → (M : TermInContext ((Γ ∷ x d px) ∷ z d (pomoč1 {Γ} {x} {z} px pz eq))) → (TermInContext ((Γ ∷ z d pz) ∷ x d (pomoč2 {Γ} {x} {z} px pz eq)))
    switch2 = {!   !}

    ------------


    -- fold
    all : (Atom → Bool) → List Atom → Bool
    all p [] = true
    all p (x ∷ xs) = p x ∧ all p xs

    vsebovanostVPreseku : (A : List Atom) → (B : List Atom) → (Γ : List Atom) → Bool  -- če je presek od A in B vsebovan v Gami
    vsebovanostVPreseku A B Γ = all (
            λ x → (
                (x ∈ B) ⇒ (_∈_ x Γ)
            )
        ) 
        A

    ---------------------------

    
    infix 5 _#_/_


    data _#_/_ {A B C : NomSet} : (a : NomSet.USet A) → (b : NomSet.USet B) → (c : NomSet.USet C) → Set where  -- set verzija
        konstrukt : (a : NomSet.USet A) → (b : NomSet.USet B) → (c : NomSet.USet C) → (vsebovanostVPreseku (NomSet.supp A a) (NomSet.supp B b) (NomSet.supp C c) ≡ true) → (a # b / c)
    

    aksiom1 : {a b c d : NomSet} → (x : NomSet.USet a) → (y : NomSet.USet b) → (z : NomSet.USet c) → (w : NomSet.USet d) → (separiranost : _#_/_ {A = a} {B = prod b c} {C = d} x (y , z) w) → (_#_/_ {A = a} {B = b} {C = prod c d} x y (z , w))
    aksiom1 = {!   !}

    aksiom2 : {a b c d : NomSet} → (x : NomSet.USet a) → (y : NomSet.USet b) → (z : NomSet.USet c) → (w : NomSet.USet d) → (separiranost : _#_/_ {A = a} {B = prod b c} {C = d} x (y , z) w) → (_#_/_ {A = a} {B = c} {C = d} x z w)
    aksiom2 = {!   !}

    aksiom3 : {a b c d : NomSet} → (x : NomSet.USet a) → (y : NomSet.USet b) → (z : NomSet.USet c) → (w : NomSet.USet d) → (separiranost : (_#_/_ {A = a} {B = b} {C = prod c d} x y (z , w))) → (s2 : (_#_/_ {A = a} {B = c} {C = d} x z w)) → (_#_/_ {A = a} {B = prod b c} {C = d} x (y , z) w)
    aksiom3 = {!   !}
    




    ∈-++-left : {x : Atom} {ys zs : List Atom} → 
        (x ∈ ys ≡ true) → 
        (x ∈ (ys ++ zs) ≡ true)
    ∈-++-left {ys = []} ()
    ∈-++-left {x} {y ∷ ys} {zs} h with _==_ x y
    ... | true = refl
    ... | false = ∈-++-left {x} {ys} {zs} h

    ∈-++-right : {x : Atom} {ys zs : List Atom} → 
        (x ∈ zs ≡ true) → 
        (x ∈ (ys ++ zs) ≡ true)
    ∈-++-right {ys = []} h = h
    ∈-++-right {x} {y ∷ ys} {zs} h with _==_ x y
    ... | true = refl
    ... | false = ∈-++-right {x} {ys} {zs} h

    head : {x : Atom} {ys zs : List Atom} → 
        ((x ∈ (ys ++ zs)) ⇒ false) ≡ true → 
        ((x ∈ ys) ⇒ false) ≡ true
    head {x} {ys} {zs} h with x ∈ ys in q
    ... | false = refl
    ... | true rewrite (∈-++-left {x} {ys} {zs} q) = 
        ⊥-elim2 (absurdizem h)

    head2 : {x : Atom} {ys zs : List Atom} → 
        ((x ∈ (ys ++ zs)) ⇒ false) ≡ true → 
        ((x ∈ zs) ⇒ false) ≡ true
    head2 {x} {ys} {zs} h with x ∈ zs in q
    ... | false = refl
    ... | true rewrite (∈-++-right {x} {ys} {zs} q) = 
        ⊥-elim2 (absurdizem h)

    presek-++-left : {xs ys zs : List Atom} → 
        vsebovanostVPreseku xs (ys ++ zs) [] ≡ true → 
        vsebovanostVPreseku xs ys [] ≡ true
    presek-++-left {xs = []} {ys} {zs} h = refl
    presek-++-left {xs = x ∷ xs} {ys} {zs} h = 
        ∧-true-intro (head {x} {ys} {zs} (∧-true-elim1' h)) (presek-++-left {xs} {ys} {zs} (∧-true-elim2' h))


    presek-++-right : {xs ys zs : List Atom} → 
        vsebovanostVPreseku xs (ys ++ zs) [] ≡ true → 
        vsebovanostVPreseku xs zs [] ≡ true
    presek-++-right {xs = []} {ys} {zs} h = refl
    presek-++-right {xs = x ∷ xs} {ys} {zs} h = 
        ∧-true-intro (head2 {x} {ys} {zs} (∧-true-elim1' h)) (presek-++-right {xs} {ys} {zs} (∧-true-elim2' h))





    

    {-
        supp_ : {Γ : Context} → TermInContext Γ → Nosilec
        supp_ {Γ} (` x) = toList Γ
        supp_ {Γ} (M · N) = _++_ (supp M) (supp N)
        supp_ {Γ} (ƛ x ⇒ M) = supp M
    -}
    
    lema-1 : (Γ : DistinctList) → (z : Atom) →
        (z ∈d Γ ≡ true) → 
        (z ∈ toList Γ ≡ true)
    lema-1 []d z p = ⊥-elim2 (absurdizem p)
    lema-1 (l ∷ x d q) z p with z == x in eq
    ... | true = refl
    ... | false =
        let
            h' : z ∈d l ≡ true
            h' = ∨-falseˡ' refl p
        in
        lema-1 l z h'

    ∈d-weaken : {Γ : Context} {x z : Atom} → 
        (q : x ∈d Γ ≡ true) → 
        (p : z ∈d Γ ≡ false) → 
        x ∈d (Γ ∷ z d p) ≡ true
    ∈d-weaken {gama} {x} {z} q p = ∨-true3 q



    lema-0-7 : (Γ : DistinctList) → (x : Atom) → (z : Atom) →
        (x ∈d Γ ≡ false) → 
        {q : z ∈d Γ ≡ false} →
        (s : x == z ≡ false) →
        (x ∈d Γ ∷ z d q ≡ false)
    lema-0-7 Γ x z px {q} s = ∨-intro-false s px

    lema0 : {Γ : Context} (x : Atom) (M : TermInContext Γ) →
        (x ∈d Γ ≡ true) →
        (x ∈ (supp_ M) ≡ true)
    lema0 {Γ} x (`_ {Γ = Γ} z {q = q}) p = lema-1 Γ x p
    lema0 {Γ} x (_·_ {Γ = Γ} N1 N2) p = ∈-++-left {x} {supp N1} {supp N2} (lema0 {Γ} x N1 p)
    lema0 {Γ} x (ƛ_⇒_ {Γ = Γ} z {q} M') p = lema0 {Γ ∷ z d q} x M' (∈d-weaken {Γ} {x} {z} p q)

    lema1 : {Γ : Context} (x : Atom) (M : TermInContext Γ) →
        (x ∈ (supp_ M) ≡ false) →
        (x ∈d Γ ≡ false)
    lema1 {Γ} x M p = kontrapozitiv2 (lema0 {Γ} x M) p


    helpp : {Γ : Context} {x : Atom} {N1 N2 : TermInContext Γ} (p : x ∈ (supp_ (_·_ {Γ = Γ} N1 N2)) ≡ false) -> (x ∈ ((supp N1) ++ (supp N2)) ≡ false)
    helpp p = {!   !}
    
    simpleWeaken : {Γ : Context} (z : Atom) → 
        (M : TermInContext Γ) → 
        (p : z ∈ (supp_ M) ≡ false) →
        TermInContext (Γ ∷ z d (lema1 {Γ} z M p))
    simpleWeaken {Γ} z M p = 
        let
            r : z ∈d Γ ≡ false
            r = lema1 {Γ} z M p
        in
            f′ Γ z p r M
            where
                f′ : (Γ : Context) → (z : Atom) → 
                        (p : z ∈ (supp_ M) ≡ false) →
                        (r : z ∈d Γ ≡ false) →
                        (M : TermInContext Γ) →
                        TermInContext (Γ ∷ z d r)
                f′ Γ z p r (`_ {Γ = Γ} x {q = q}) = `_ {Γ = Γ ∷ z d r} x {q = ∈d-weaken {Γ} {x} {z} q r}
                --f′ Γ z p r (_·_ {Γ = Γ} N1 N2) = _·_ (simpleWeaken {Γ} z N1 (kontrapozitiv2 (∈-++-left {z} {supp_ N1} {supp_ N2}) (helpp {Γ} {z} {N1} {N2} ?))) (simpleWeaken {Γ} z N2 (kontrapozitiv2 (∈-++-right {z} {supp_ N1} {supp_ N2}) (helpp {Γ} {z} {N1} {N2} ?)))
                {-
                f′ Γ z p r (ƛ_⇒_ {Γ = Γ} x {p = q} M') = 
                    let
                        g : x == z ≡ false
                        g = {!   !}

                        p' : z ∈ (supp M') ≡ false
                        p' = {!   !}
                    in
                        ƛ_⇒_ {Γ = Γ ∷ z d r} x {lema-0-7 Γ x z q {r} g} (switch2 {Γ} {x} {z} q r g (simpleWeaken {Γ ∷ x d q} z M' p'))
                -}
                f′ Γ z p r (_·_ {Γ = Γ} N1 N2) = {!   !}
                f′ Γ z p r (ƛ_⇒_ {Γ = Γ} x {p = q} M') = {!   !}
    
    weaken : {Γ : Context} (z : Atom) {p : z ∈d Γ ≡ false} → 
        (M : TermInContext Γ) → 
        (vsebovanostVPreseku (z ∷ []) (supp_ M) [] ≡ true) → 
        TermInContext (Γ ∷ z d p)
    weaken {Γ} z {p} (`_ {Γ = Γ} x {q = q}) _ = 
        `_ {Γ = Γ ∷ z d p} x {q = ∈d-weaken {Γ = Γ} {x = x} {z = z} q p}
    -- weaken z {p} (M · N) _ = weaken z {p} M · weaken z {p} N
    weaken z {p} (M · N) _ = {!   !}
    weaken z {p} (ƛ x ⇒ M) _ = {!   !}



    -- NomSet stvari

    pair-disjoint-left : {A B C : NomSet} {a : NomSet.USet A} {b : NomSet.USet B} {c : NomSet.USet C} → 
        (vsebovanostVPreseku (NomSet.supp A a) (NomSet.supp (prod B C) (b , c)) [] ≡ true) → 
        (vsebovanostVPreseku (NomSet.supp A a) (NomSet.supp B b) [] ≡ true)
    pair-disjoint-left {A} {B} {C} {a} {b} {c} h = 
        presek-++-left {NomSet.supp A a} {NomSet.supp B b} {NomSet.supp C c} h

    pair-disjoint-right : {A B C : NomSet} {a : NomSet.USet A} {b : NomSet.USet B} {c : NomSet.USet C} → 
        (vsebovanostVPreseku (NomSet.supp A a) (NomSet.supp (prod B C) (b , c)) [] ≡ true) → 
        (vsebovanostVPreseku (NomSet.supp A a) (NomSet.supp C c) [] ≡ true)
    pair-disjoint-right {A} {B} {C} {a} {b} {c} h = 
        presek-++-right {NomSet.supp A a} {NomSet.supp B b} {NomSet.supp C c} h

    {-
    singleton-notin : {Γ : Context} {z : Atom} →
        vsebovanostVPreseku (z ∷ []) (toList Γ) [] ≡ true →
        (z ∈d Γ) ≡ false

    singleton-notin {Γ} {z} h with z ∈d Γ
    ... | false = refl
    ... | true = 
        let
            h₁ :
                ((z ∈d Γ) ⇒ false) ≡ true
            h₁ = ∧-true-elim1' h
        in
            ⊥-elim2 (absurdizem h₁)
    -}

    vrne : (Γ : NomSet.USet NomContext) → 
        (z : Atom) → 
        (M : NomSet.USet (NomTermInContext Γ)) → 
        (separiranost : _#_/_ {A = NomAtom} {B = prod (NomTermInContext Γ) NomContext} {C = NomContext} z (M , Γ) []d) → 
        ((z ∈d Γ) ≡ false)
    -- vrne Γ z M (konstrukt z (M , Γ) []d proof) = singleton-notin (presek-++-right proof)
    --- uporabi presek-++-right
    vrne = {!   !}

    lema : {Γ : NomSet.USet NomContext} → 
        (M : NomSet.USet (NomTermInContext Γ)) → 
        (z : Atom) → 
        (separiranost : _#_/_ {A = NomAtom} {B = prod (NomTermInContext Γ) NomContext} {C = NomContext} z (M , Γ) []d) → 
        (NomSet.USet (NomTermInContext (Γ ∷ z d (vrne Γ z M separiranost))))
    lema {Γ} M z (konstrukt z (M , Γ) []d proof) = 
        weaken {Γ} z M (pair-disjoint-left {A = NomAtom} {B = NomTermInContext Γ} {C = NomContext} {a = z} {b = M} {c = Γ} proof)
    
    substitucija : {Γ : NomSet.USet NomContext} → 
        (N : NomSet.USet (NomTermInContext Γ)) → 
        (x : Atom) → 
        {p : (x ∈d Γ) ≡ false} → 
        (M : NomSet.USet (NomTermInContext (Γ ∷ x d p))) → 
        {s : _#_/_ {A = NomTermInContext (Γ ∷ x d p)} {B = NomTermInContext Γ} {C = NomContext} M N Γ} → 
        (TermInContext Γ)
    substitucija {Γ} N x {p} M {s} = {!   !}

    -- namesto splošnega M imamo le lambda abstrakcijo
    substitucijaNovo : {Γ : NomSet.USet NomContext} → 
        (N : NomSet.USet (NomTermInContext Γ)) → 
        (x : Atom) → 
        {p : (x ∈d Γ) ≡ false} → 
        (M : NomSet.USet (NomTermInContext (Γ ∷ x d p))) → 
        {s : _#_/_ {A = NomTermInContext Γ} {B = NomTermInContext Γ} {C = NomContext} (ƛ x ⇒ M) N Γ} → 
        (TermInContext Γ)
    substitucijaNovo {Γ} N x {p} M {s} = {!   !}   