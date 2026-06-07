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


    record NomSet : Set₁ where
        field
            USet : Set
            supp : USet → List Atom
    
    {-
    fst : {A B : Set} → A × B → A
    fst (a , b) = a

    snd : {A B : Set} → A × B → B
    snd (a , b) = b
    -}
    
    prod : NomSet → NomSet → NomSet
    prod A B = record {
            USet = (NomSet.USet A) × (NomSet.USet B);
            supp = (λ (a , b) → concat (NomSet.supp A a) (NomSet.supp B b))
        }
    
    
    
    Nosilec = List Atom

    supp_ : {Γ : Context} → TermInContext Γ → Nosilec
    supp_ {Γ} (` x) = toList Γ
    supp_ {Γ} (M · N) = concat (supp M) (supp N)
    supp_ {Γ} (ƛ x ⇒ M) = supp M


    NomTermInContext : (Γ : Context) → NomSet
    NomTermInContext Γ = (
        record {
            USet = TermInContext Γ;
            supp = supp_ {Γ}
        })
    
    suppp_ : (Γ : Context) → Nosilec
    suppp_ Γ = toList Γ

    NomContext : NomSet
    NomContext = (
        record {
            USet = Context;
            supp = toList
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


    map-preserves-head2 : (f : Atom → Atom) → (==-kong : (a x : Atom) → (_==_ a x ≡ true) → (_==_ (f a) (f x) ≡ true)) → (inj : (a x : Atom) → (_==_ a x ≡ false) → (_==_ (f a) (f x) ≡ false)) → (a x : Atom) (ps : DistinctList) → (pogoj : _∈d_ x ps ≡ false) → {_==_ a x ≡ true} → (_∈d_ (f a) (preslikaDSeznam f inj (ps ∷ x d pogoj)) ≡ true)
    map-preserves-head2 f kong inj a x ps pogoj {ax≡true} =
        let
            head : (_==_ (f a) (f x)) ≡ true
            head = kong a x ax≡true
        in
            -- ∨-trueˡ' head
            {!   !}
    
    bbb : (f : Atom → Atom) → (==-kong : (a x : Atom) → (_==_ a x ≡ true) → (_==_ (f a) (f x) ≡ true)) → (inj : (a x : Atom) → (_==_ a x ≡ false) → (_==_ (f a) (f x) ≡ false)) → (a : Atom) (l : DistinctList) → (_∈d_ a l ≡ true) → (_∈d_ (f a) (preslikaDSeznam f inj l) ≡ true)
    bbb f kong inj a []d p = ⊥-elim2 (absurdizem p)
    bbb f kong inj a (xs ∷ x d q) p with (_==_ a x) in eq
    ... | true = map-preserves-head2 f kong inj a x xs q {eq}
    ... | false =
        let
            tail : (a ∈d xs) ≡ true
            -- tail = ∨-false-elim refl p
            tail = {!   !}

            ih : ((f a) ∈d (preslikaDSeznam f inj xs)) ≡ true
            ih = bbb f kong inj a xs tail
        in
            {!   !}
            --∨-trueʳ ih
    
    
    kongruentnostVsebovanostiZaDistinctList : (f : Atom → Atom) → 
        (==-kong : 
            (a x : Atom) → 
            (_==_ a x ≡ true) → 
            (_==_ (f a) (f x) ≡ true)
        ) → (inj : (a x : Atom) → (_==_ a x ≡ false) → (_==_ (f a) (f x) ≡ false)) →
        (a : Atom) → 
        (l : Context) → 
        (p : _∈d_ a l ≡ true) → 
        (_∈d_ (f a) (preslikaDSeznam f inj l) ≡ true)
    kongruentnostVsebovanostiZaDistinctList = {!   !}

    kongruentnostVsebovanostiZaDistinctList2 : (f : Atom → Atom) → 
        (==-kong : 
            (a x : Atom) → 
            (_==_ a x ≡ true) → 
            (_==_ (f a) (f x) ≡ true)
        ) → (inj : (a x : Atom) → (_==_ a x ≡ false) → (_==_ (f a) (f x) ≡ false)) →
        (a : Atom) → 
        (l : Context) → 
        (p : _∈d_ a l ≡ false) → 
        (_∈d_ (f a) (preslikaDSeznam f inj l) ≡ false)
    kongruentnostVsebovanostiZaDistinctList2 = {!   !}

    kongruentnostVsebovanostiZaDistinctList3 : (f : Atom → Atom) → 
        (==-kong : 
            (a x : Atom) → 
            (_==_ a x ≡ true) → 
            (_==_ (f a) (f x) ≡ true)
        ) → (inj : (a x : Atom) → (_==_ a x ≡ false) → (_==_ (f a) (f x) ≡ false)) →
        (a : Atom) → 
        (l : Context) → 
        (p : _∈d_ (f a) (preslikaDSeznam f inj l) ≡ true) →
        (_∈d_ a l ≡ true)
    kongruentnostVsebovanostiZaDistinctList3 = {!   !}

    kongruentnostVsebovanostiZaDistinctList4 : (f : Atom → Atom) → 
        (==-kong : 
            (a x : Atom) → 
            (_==_ a x ≡ true) → 
            (_==_ (f a) (f x) ≡ true)
        ) → (inj : (a x : Atom) → (_==_ a x ≡ false) → (_==_ (f a) (f x) ≡ false)) →
        (a : Atom) → 
        (l : Context) → 
        (p : _∈d_ (f a) (preslikaDSeznam f inj l) ≡ false) →
        (_∈d_ a l ≡ false)
    kongruentnostVsebovanostiZaDistinctList4 = {!   !}

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

    
    infix 5 _#_/g_


    data _#_/g_ {A B C : NomSet} : (a : NomSet.USet A) → (b : NomSet.USet B) → (c : NomSet.USet C) → Set where  -- set verzija
        konstrukt : (a : NomSet.USet A) → (b : NomSet.USet B) → (c : NomSet.USet C) → (vsebovanostVPreseku (NomSet.supp A a) (NomSet.supp B b) (NomSet.supp C c) ≡ true) → (a # b /g c)
    

    -- posebna oznaka, če sta oba izraza nad istim kontekstom Γ, glede na katerega gledamo relacijo
    _⊢_#_ : (Γ : Context) → TermInContext Γ → TermInContext Γ → Set
    _⊢_#_ Γ M N = {!   !}  -- M # N /g Γ

    separiranostSimetrična2 : (Γ : Context) → (M : TermInContext Γ) → (N : TermInContext Γ) → (p : Γ ⊢ M # N) → (Γ ⊢ N # M)
    separiranostSimetrična2 Γ M N = {!   !}

    substitucija : {Γ : NomSet.USet NomContext} → (N : NomSet.USet (NomTermInContext Γ)) → (x : Atom) → {p : (x ∈d Γ) ≡ false} → (M : NomSet.USet (NomTermInContext (Γ ∷ x d p))) → {s : _#_/g_ {A = NomTermInContext (Γ ∷ x d p)} {B = NomTermInContext Γ} {C = NomContext} M N Γ} → (TermInContext Γ)
    substitucija {Γ} N x {p} M {s} = {!   !}