open import Agda.Builtin.Equality

open import Data.List hiding (last; tail; _++_; head)
                    renaming ([_] to ηList; map to fmapList; concat to μList)
                    
open import Data.Vec hiding (head; toList)
open import Agda.Builtin.Nat hiding (_<_)

infix 0 case_of_
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

id : {A : Set} → A → A
id a = a

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ a → g (f a)

-- From the theory of vulnerability to verified policy advice
postulate State Evolution V W   : Set
postulate F                     : Set → Set
postulate fmap                  : {A B : Set} → (A → B) → F A → F B
postulate possible              : State → F Evolution
postulate harm                  : Evolution → V
-- postulate measure               : F V → W


-- vulnerability : State → W
-- vulnerability = measure ∘ (fmap harm ∘ possible)

-- deterministic system
DetSys : Set → Set 
DetSys X = X → X

-- deterministic evolution, iterating over a deterministic system
detFlow : {X : Set} → DetSys X → Nat → DetSys X
detFlow f zero = id
detFlow f (suc n) = detFlow f n ∘ f


-------------------
-- ex 4.4
-------------------
postulate next1 : State → State
possible1 : State → Vec State 5
possible1 s = map (λ n → detFlow next1 n s) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])

-------------------
-- ex 4.5
-------------------

-- transitivity of equality
trans : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → x ≡ z
trans refl refl = refl

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix   1 begin_
infix   3 _end
infixr  2 _=⟨_⟩_
infixr  2 _=⟨⟩_

detFlowP1 : {X : Set} (f : DetSys X) (m n : Nat) (x : X) → 
            detFlow f (m + n) x ≡ detFlow f n (detFlow f m x)
detFlowP1 f zero n x = 
    begin
        detFlow f (zero + n) x
    =⟨⟩
        detFlow f n x
    =⟨⟩ -- apply id
        detFlow f n (id x)
    =⟨⟩ -- apply detFlow first clause
        detFlow f n (detFlow f zero x)
    end
detFlowP1 f (suc m) n x =
    begin
        detFlow f (suc m + n) x 
    =⟨⟩ -- suc apply def
        detFlow f (suc (m + n)) x 
    =⟨⟩ -- detFlow apply second clause
        detFlow f (m + n) (f x) 
    =⟨ detFlowP1 f m n (f x) ⟩  -- induction hypothesis
        detFlow f n (detFlow f m (f x)) 
    =⟨⟩ -- undo detFlow second clause
        detFlow f n (detFlow f (suc m) x) 
    end

-------------------
-- ex 4.7
-------------------

detTrj : {X : Set} → DetSys X → (n : Nat) → X → Vec X (suc n)
detTrj f     zero    x  = x ∷ []
detTrj f  (  suc n)  x  = x ∷ detTrj f n (f x)

-- tail : {X : Set} {n : Nat} → Vec X (suc n) → Vec X n
-- tail (x :: xs) = xs

postulate detTrjP1 : {X : Set} (f : DetSys X) (m n : Nat) (x : X) →
                detTrj f (m + n) x ≡ detTrj f m x ++ tail (detTrj f n (detFlow f m x))

-- lastLemma  :  {A : Set} → {n : Nat} →
--               (a : A) → (as : Vec A (suc n)) → last (a ∷ as) ≡ last as
-- lastLemma a (x ∷ as) = refl


-------------------
-- ex 4.8
-------------------


detFlowTrjP1  :  {X : Set} → (n : Nat) → (f : DetSys X) →
                 (x : X) → last (detTrj f n x) ≡ detFlow f n x
detFlowTrjP1 zero f x = 
    begin
        last (detTrj f zero x)
    =⟨⟩ -- detTrj first clause
        last (x ∷ [])
    =⟨⟩ -- last def
        x 
    =⟨⟩ -- apply id
        id x 
    =⟨⟩ -- detFlow first clause
        detFlow f zero x
    end
detFlowTrjP1 (suc n) f x =
    begin 
        last (detTrj f (suc n) x) 
    =⟨⟩
        last (detTrj f n (f x)) 
    =⟨ detFlowTrjP1 n f (f x) ⟩ -- induction step
        detFlow f n (f x) 
    =⟨⟩
        detFlow f (suc n) x
    end


-------------------
-- exs 4.9 & 4.10
-------------------

-- list functions renaming
-- [_] to ηList; map to fmapList; concat to μList

infixr 1 _>=>List_
_>=>List_ : {A B C : Set} → (A → List B) → (B → List C) → (A → List C)
f >=>List g = μList ∘ ((fmapList g) ∘ f)

NonDetSys : Set → Set
NonDetSys X = X → List X

nonDetFlow  :  {X : Set} → NonDetSys X → Nat → NonDetSys X
nonDetFlow f     zero    =  ηList
nonDetFlow f  (suc n)  =  f >=>List nonDetFlow f n

-------------------
-- ex 4.11
-------------------

ηListNatTrans  :  {A B : Set} → (f : A → B) → (a : A) → fmapList f (ηList a) ≡ ηList (f a)
ηListNatTrans f a = refl

-------------------
-- ex 4.12
-------------------

nonDetTrj : {X : Set} → NonDetSys X → (n : Nat) → X → List (Vec X (suc n))
nonDetTrj f   zero    x  =  fmapList (x ∷_) (ηList [])
nonDetTrj f ( suc n)  x  =  fmapList (x ∷_) ((f >=>List (nonDetTrj f n)) x)


rw : Nat → List Nat
rw    zero    =  zero ∷ suc zero ∷ []
rw (  suc m)  =  m ∷ suc m ∷ suc (suc m) ∷ []

-------------------
-- ex 4.13
-------------------

detToNonDet : {X : Set} → DetSys X → NonDetSys X
detToNonDet f = ηList ∘ f

postulate triangleLeftList : {A : Set} → (as : List A) → μList (ηList as) ≡ as
postulate triangleLeftList2 : {A : Set} → (as : List A) → as ≡ μList (ηList as)

Det≡NonDet  : {X : Set} → (f : DetSys X) → (n : Nat) → (x : X) →
              ηList (detFlow f n x) ≡ nonDetFlow (detToNonDet f) n x
Det≡NonDet f zero x = 
    begin
        ηList (detFlow f zero x)
    =⟨⟩
        ηList x
    =⟨⟩
        nonDetFlow (detToNonDet f) zero x
    end
Det≡NonDet f (suc n) x =
    begin
        ηList (detFlow f (suc n) x)
    =⟨⟩
        ηList ((detFlow f n ∘ f) x)
    =⟨⟩
        ηList (detFlow f n (f x))
    =⟨ Det≡NonDet f n (f x) ⟩
        nonDetFlow (detToNonDet f) n (f x)
    =⟨ triangleLeftList2 (nonDetFlow (detToNonDet f) n (f x)) ⟩
        μList (ηList ((nonDetFlow (detToNonDet f) n) (f x)))
    =⟨⟩ -- ηListNatTrans  :  fmapList f (ηList a) ≡ ηList (f a)
        μList (fmapList (nonDetFlow (detToNonDet f) n) (ηList (f x)))
    =⟨⟩
        (nonDetFlow (detToNonDet f) (suc n)) x
    end

-------------------------
-- ex 4.14  Monadic laws
-------------------------
postulate M     : Set → Set
postulate fmapM : {A B : Set}  → (A → B)   → (M A → M B)
postulate ηM    : {A : Set}    → A         → M A
postulate μM    : {A : Set}    → M (M A)   → M A

-- Extensional equality
-- infixr 1 _≗_
-- _≗_ : {A : Set} {B : A → Set} (f g : (x : A) → B x) → Set
-- f ≗ g = ∀ x → f x ≡ g x

-- Bind operator
infixl 40 _>>=M_
_>>=M_ : { A B : Set} → M A → (A → M B) → M B 
ma >>=M f = μM (fmapM f ma)

infixl 50 _>=>M_
_>=>M_ : {A B C : Set} → (A → M B) → (B → M C) → (A → M C)
f >=>M g = (λ a → (f a) >>=M g)

postulate ηMNatTrans    : {X : Set}     → (f : X → M X)       → (x : X)                     → ηM (f x) ≡ fmapM f (ηM x)
postulate ηMNatTrans'   : {X : Set}     → (f : X → M X)       → (x : X)                     → μM (ηM (f x)) ≡ μM (fmapM f (ηM x))
postulate leftTriangle  : {A : Set}     → (ma : M A)                                        → ma ≡ (μM ∘ ηM) ma     --(left triangle)
postulate lawTriangle   : {A : Set}     → (ma : M A)                                        → (μM ∘ ηM) ma ≡ (μM ∘ fmapM ηM) ma
postulate lawRectangle1 : {A : Set}     → (ma : M (M (M A)))                                → μM (μM ma) ≡ μM (fmapM μM ma)
postulate lawRectangle2 : {X Y : Set}   → (x : X)           → (f : X → Y)                   → (ηM ∘ f) x ≡ ((fmapM f) ∘ ηM) x
postulate lawRectangle3 : {X Y : Set}   → (mx : M (M X))    → (f : X → Y)                   → μM (fmapM (fmapM f) mx) ≡ fmapM f (μM mx)
postulate lawBow        : {A B C : Set} → (a : A)           → (f : A → M B) → (g : B → M C) → μM (fmapM g (f a)) ≡ (f >=>M g) a
-------------------------------------------------------------------------

MonSys : Set → Set
MonSys X = X → M X

monFlow : {X : Set} → MonSys X → Nat → MonSys X
monFlow f zero = ηM
monFlow f (suc n) = f >=>M monFlow f n

monTrj : {X : Set} → MonSys X → (n : Nat) → X → M (Vec X (suc n))
monTrj f zero x = fmapM (x ∷_) (ηM [])
monTrj f (suc n) x = fmapM (x ∷_) (f x >>=M (monTrj f n))

detToMon : {X : Set} → DetSys X → MonSys X
detToMon f = ηM ∘ f

monToDet : {X : Set} → MonSys X → DetSys (M X)
monToDet f mx = mx >>=M f

-------------------
-- ex 4.15
-------------------

Det≡Mon : {X : Set} → (f : DetSys X) → (n : Nat) → (x : X) →
            ηM (detFlow f n x) ≡ monFlow (detToMon f) n x
Det≡Mon f zero x = -- refl
    begin
        ηM (detFlow f zero x)
    =⟨⟩
        ηM x
    =⟨⟩
        monFlow (detToMon f) zero x
    end
Det≡Mon f (suc n) x =
    begin
        ηM (detFlow f (suc n) x)
    =⟨⟩
        ηM ((detFlow f n ∘ f) x)
    =⟨⟩
        ηM (detFlow f n (f x))
    =⟨⟩
        (ηM (detFlow f n (f x)))
    =⟨ Det≡Mon f n (f x) ⟩
        (monFlow (detToMon f) n) (f x)
    =⟨ leftTriangle ((monFlow (detToMon f) n) (f x)) ⟩
        μM (ηM ((monFlow (detToMon f) n) (f x)))
    =⟨ ηMNatTrans' (monFlow (detToMon f) n) (f x) ⟩     -- μM (ηM (f x)) ≡ μM (fmapM f (ηM x))  
        μM (fmapM (monFlow (detToMon f) n) (ηM (f x)))
    =⟨⟩    
        ((detToMon f) >=>M monFlow (detToMon f) n) x
    =⟨⟩
        monFlow (detToMon f) (suc n) x
    end 

---------------------------------------------------------
-- Seminar 7
---------------------------------------------------------

-- Set of states
postulate X : Nat → Set

-- Set of controls
postulate Y : (t : Nat) → X t → Set 

-- M-structure pf possible next states
postulate next : (t : Nat) → (x : X t) → Y t x → M (X (suc t))

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

-- Dependent pair type
data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (x : A) → B x → Σ A B
infix 4 _,_

-- Each decision step yields a reward in a value set Val
postulate Val       : Set
postulate 0Val : Val
postulate _⊕_ : Val → Val → Val
_⊕l_ : {A : Set} → (A → Val) → (A → Val) → (A → Val)
f ⊕l g = (λ x → f x ⊕ g x)

-- transitivity for inequality  
postulate _≤_       : {A : Set} → A → A → Set
postulate refl≤     : {A : Set} → ∀ {a : A} → a ≤ a
postulate trans≤    : {A : Set} → ∀ {a b c : A} → a ≤ b → b ≤ c → a ≤ c
-- postulate total≤    : {A : Set} → (x y : A) → Either (x ≤ y ) (y ≤ x )

begin≤_ : {A : Set} → {x y : A} → x ≤ y → x ≤ y
begin≤ p = p

_end≤ : {A : Set} → (x : A) → x ≤ x
x end≤ = refl≤

_≤⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≤ y → y ≤ z → x ≤ z
x ≤⟨ p ⟩ q = trans≤ p q

_≤⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≤ y → x ≤ y
x ≤⟨⟩ q = x ≤⟨ refl≤ ⟩ q

infix   1 begin≤_
infix   3 _end≤
infixr  2 _≤⟨_⟩_
infixr  2 _≤⟨⟩_

-- Rewards
postulate reward : (t : Nat) → (x : X t) → Y t x → X (suc t) → Val

-- A policy maps states to controls
Policy : (t : Nat) → Set
Policy t = (x : X t) → Y t x

-- Policy Sequence
data PolicySeq : (t n : Nat) → Set where
    Nil : {t : Nat} → PolicySeq t zero
    _::_ : {t n : Nat} → Policy t → PolicySeq (suc t) n → PolicySeq t (suc n)

-- possible trajectories of a policy sequence = sequences of state-control pairs
data XYSeq : (t n : Nat) → Set where
    Last : {t : Nat} → X t → XYSeq t (suc zero)
    _||_ : {t n : Nat} → Σ (X t) (Y t) → XYSeq (suc t) (suc n) → XYSeq t (suc (suc n))

-- possible trajectories of a policy sequence
trj : {t n : Nat} → PolicySeq t n → X t → M (XYSeq t (suc n))
trj {t} Nil x = ηM (Last x)
trj {t} (p :: ps) x = 
    let y       = p x in 
    let mx'     = next t x y in
    fmapM ((x , y) ||_) (mx' >>=M trj ps)

-- head: state of the first pair of XYseq
head : {t n : Nat} → XYSeq t (suc n) → X t
head (Last x) = x
head ((x , y) || xys) = x

-- ⊕-sum of the rewards
sumR : {t n : Nat} → XYSeq t n → Val
sumR {t } (Last x )         = 0Val
sumR {t } ((x , y ) || xys) = reward t x y (head xys) ⊕ sumR xys

postulate measure : M Val → Val

-- measure of the ⊕-sum of the rewards along all possible trajectories (measured total reward)
val : {t n : Nat} → (ps : PolicySeq t n) → (x : X t) → Val
val ps = measure ∘ (fmapM sumR ∘ trj ps)

-- preorder between functions A → Val
_≤l_ : {A B : Set} → (A → B) → (A → B) → Set
f ≤l g = ∀ x → (f x ≤ g x)

OptPolicySeq : {t n : Nat} → PolicySeq t n → Set
OptPolicySeq {t } {n} ps = ∀ (ps' : PolicySeq t n) → val ps' ≤l val ps

---------------------------------------------------------
-- 7.3-7.7 SimpleProb example
---------------------------------------------------------

open import Data.Float using (Float) renaming (_+_ to _+Float_; _*_ to _*Float_)
open import Data.Product using (Σ; _×_; _,_)

SP  : Set → Set
SP X = List (X × Float)

-- Val = R, but we use Float instead
ValSP   : Set
ValSP = Float

-- Val = 0
0ValSP : ValSP
0ValSP = 0.0

-- usual addition
_⊕SP_ : ValSP → ValSP → ValSP
a ⊕SP b = a +Float b

-- Rewards
postulate rewardSP : (t : Nat) → (x : X t) → Y t x → X (suc t) → ValSP

-- Same definition as for fmapList but keep the prob coordinate untouched
fmapSP : {A B : Set} → (A → B) → SP A → SP B
fmapSP f [] = []
fmapSP f ((x , p) ∷ xps) = (f x , p) ∷ (fmapSP f xps)

-- Singleton equivalent, p = 1
ηSP : {X : Set} → X → SP X
ηSP x = (x , 1.0) ∷ []

postulate μSP : {X : Set} → SP (SP X) → SP X

_>>=SP_ : {A B : Set} → SP A → (A → SP B) → SP B 
ma >>=SP f = μSP (fmapSP f ma)

-- measure = expected value (7.5)
ev : SP ValSP → ValSP
ev [] = 0ValSP
ev ((x , p) ∷ xps) = (x *Float p) +Float (ev xps)

-- M-structure pf possible next states
postulate nextSP : (t : Nat) → (x : X t) → Y t x → SP (X (suc t))

-- possible trajectories of a policy sequence
trjSP : {t n : Nat} → PolicySeq t n → X t → SP (XYSeq t (suc n))
trjSP {t} Nil x = ηSP (Last x)
trjSP {t} (p :: ps) x = 
    let y       = p x in 
    let spx'     = nextSP t x y in
    fmapSP ((x , y) ||_) (spx' >>=SP trjSP ps)

-- ⊕-sum of the rewards for SP
sumRSP : {t n : Nat} → XYSeq t n → ValSP
sumRSP {t } (Last x )         = 0ValSP
sumRSP {t } ((x , y ) || xys) = rewardSP t x y (head xys) ⊕SP sumRSP xys

valSP : {t n : Nat} → (ps : PolicySeq t n) → ((x : X t) → ValSP)
valSP ps = ev ∘ (fmapSP sumRSP ∘ trjSP ps)

-- postulate bellmaneq : (p0 : Policy (suc (suc zero))) → (p1 : Policy (suc zero)) → (x0 : X (suc zero)) → (y0 : Y (suc zero) x0) → val (p1 :: (p0 :: Nil)) x0 ≡ ev (fmapSP (rewardSP (suc zero) x0 (y0 ⊕SP valSP (p1 :: Nil))) (nextSP (suc zero) x0 y0 ))

---------------------------------------------------------------------
-- 7.8 Bellman's equation deterministic case
---------------------------------------------------------------------
-- Identity Monad
Id  : Set → Set
Id X = X

postulate ValId : Set
postulate 0ValId : ValId
postulate _⊕Id_ : ValId → ValId → ValId

-- Rewards
postulate rewardId : (t : Nat) → (x : X t) → Y t x → X (suc t) → ValId

-- Id fmap
fmapId : {A B : Set} → (A → B) → Id A → Id B
fmapId f a = f a

-- Id η 
ηId : {X : Set} → X → Id X
ηId x = x

postulate μId : {X : Set} → Id (Id X) → Id X

_>>=Id_ : {A B : Set} → Id A → (A → Id B) → Id B 
ma >>=Id f = μId (fmapId f ma)

-- measure = id (already defined)
measureId : Id ValId → ValId
measureId x = x

-- id-structure of possible next states
postulate nextId : (t : Nat) → (x : X t) → Y t x → Id (X (suc t))

-- possible trajectories of a policy sequence
trjId : {t n : Nat} → PolicySeq t n → X t → Id (XYSeq t (suc n))
trjId {t} Nil x = ηId (Last x)
trjId {t} (p :: ps) x = 
    let y       = p x in 
    let spx'     = nextId t x y in
    fmapId ((x , y) ||_) (spx' >>=Id trjId ps)

-- ⊕-sum of the rewards for Id
sumRId : {t n : Nat} → XYSeq t n → ValId
sumRId {t } (Last x )         = 0ValId
sumRId {t } ((x , y ) || xys) = rewardId t x y (head xys) ⊕Id sumRId xys

valId : {t n : Nat} → (ps : PolicySeq t n) → (x : X t) → ValId
valId ps = measureId ∘ fmapId (sumRId ∘ trjId ps)

postulate Lemma7 : (t n : Nat) → (p : Policy t) → (ps : PolicySeq (suc t) n) → (x : X t) → 
                sumRId (trjId (p :: ps) x ) ≡ rewardId t x (p x ) (nextId t x (p x )) ⊕Id (valId ps (nextId t x (p x )))

_⊕lId_ : {t : Nat} → (X t → ValId) → (X t → ValId) → (X t → ValId)
f ⊕lId g = (λ x → f x ⊕Id g x)

BellmanEq : (t n : Nat) → (p : Policy t) → (ps : PolicySeq (suc t) n) → (x : X t) →
            valId (p :: ps) x ≡ measureId (fmapId (rewardId t x (p x) ⊕lId valId ps) (nextId t x (p x)))
BellmanEq t n p Nil x = 
    begin
        valId (p :: Nil) x
    =⟨⟩
        sumRId (trjId (p :: Nil) x)
    =⟨ Lemma7 t n p Nil x ⟩
        rewardId t x (p x ) (nextId t x (p x )) ⊕Id (valId Nil (nextId t x (p x)))
    =⟨⟩ -- def of ⊕lId
        (rewardId t x (p x) ⊕lId valId Nil) (nextId t x (p x))
    =⟨⟩
        measureId (fmapId (rewardId t x (p x) ⊕lId valId Nil) (nextId t x (p x)))
    end
BellmanEq t n p1 (p0 :: ps) x = 
    begin
        valId (p1 :: (p0 :: ps)) x
    =⟨⟩
        sumRId (trjId (p1 :: (p0 :: ps)) x)
    =⟨ Lemma7 t n p1 (p0 :: ps) x ⟩
        rewardId t x (p1 x) (nextId t x (p1 x )) ⊕Id (valId (p0 :: ps) (nextId t x (p1 x)))
    =⟨⟩
        (rewardId t x (p1 x) ⊕lId valId (p0 :: ps)) (nextId t x (p1 x))
    =⟨⟩
        measureId (fmapId (rewardId t x (p1 x) ⊕lId valId (p0 :: ps)) (nextId t x (p1 x)))
    end

---------------------------------------------------------------------
-- 7.9 Bellman's principle, optimal extensions
---------------------------------------------------------------------
-- value of a policy sequence through Bellman's equation
valBell : {t n : Nat} → PolicySeq t n → X t → Val
valBell {t} Nil x = 0Val
valBell {t} (p :: ps) x =    let y = p x in
                            let mx' = next t x y in
                            measure (fmapM (reward t x y ⊕l valBell ps) mx')

-- p is an optimal extension of ps iff p is at least as good as any other policy
OptExt : {t n : Nat} → PolicySeq (suc t) n → Policy t → Set
OptExt ps p = ∀ p' → valBell (p' :: ps) ≤l valBell (p :: ps)

postulate Finite    : Set → Set
postulate toList    : {A : Set } → Finite A         → List A
postulate max       : {A : Set } → (f : A → Val)    → List A → Val
postulate argmax    : {A : Set } → (f : A → Val)    → List A → A

-- Computing an optimal extension p : Policy t of a policy sequence ps requires 
-- computing a control p x : Y t x that maximizes val (p :: ps) x for every x : X t. 

postulate finiteY : {t : Nat} (x : X t) → Finite (Y t x)
postulate finiteP : {t : Nat} (x : X t) → Finite (Policy t)

-- case A = Policy t
-- optExt : {t n : Nat} → PolicySeq (suc t) n → Policy t
-- optExt ps = 
--     λ x → (argmax (λ p → val (p :: ps) x) (toList (finiteP x))) x

-- case A = Y t x
optExt : {t n : Nat} → PolicySeq (suc t) n → Policy t
optExt {t} ps x = 
    argmax (λ y → measure (fmapM (reward t x y ⊕l valBell ps) (next t x y))) (toList (finiteY x))

-- postulate fmapM : {A B : Set}  → (A → B)  → M A → M B
-- postulate next : (t : Nat) → (x : X t) → Y t x → M (X (suc t))

---------------------------------------------------------------------
-- 7.10 
---------------------------------------------------------------------
-- Formulate minimal requirements on toList, max and argmax for optExt to satisfy optExtSpec
-- optExtSpec says that for all ps, optExt ps is an optimal extension of ps.

postulate maxSpec : {t : Nat} → {x : X t} → (y : Y t x) → (f : Y t x → Val) → List (Y t x) 
                    → f y ≤ max f (toList (finiteY x))

postulate argmaxSpec : {t : Nat} → {x : X t} → (f : Y t x → Val) → List (Y t x) 
                    → f (argmax f (toList (finiteY x))) ≡ max f (toList (finiteY x))

postulate optExtSpec : {t n : Nat} → (ps : PolicySeq (suc t) n) → OptExt ps (optExt ps)

-- optExtSpec : {t n : Nat} → (ps : PolicySeq (suc t) n) → OptExt ps (optExt ps)
-- optExtSpec {t} {n} ps p' x =
--     begin≤ 
--         valBell (p' :: ps) x 
--     =⟨⟩
--         measure (fmapM (reward t x (p' x) ⊕l valBell ps) (next t x (p' x)))
--     ≤⟨ maxSpec (p' x) (λ y → measure (fmapM (reward t x y ⊕l valBell ps) (next t x y))) (toList (finiteY x)) ⟩
--         max (λ y → measure (fmapM (reward t x y ⊕l valBell ps) (next t x y))) (toList (finiteY x))
--     ⟨ argmaxSpec (λ y → measure (fmapM (reward t x y ⊕l valBell ps) (next t x y))) (toList (finiteY x)) ⟩
--         measure (fmapM (reward t x (optExt {t} ps x) ⊕l valBell ps) (next t x (optExt {t} ps x)))
--     ≤⟨⟩
--         valBell (optExt ps :: ps) x
--     end≤

---------------------------------------------------------------------
-- 7.11
---------------------------------------------------------------------

OptPolicySeqBell : {t n : Nat} → PolicySeq t n → Set
OptPolicySeqBell {t } {n} ps = ∀ (ps' : PolicySeq t n) → (x : X t) → valBell ps' x ≤ valBell ps x

-- To prove Bellman's optimality principle one needs two monotonicity conditions
postulate measureMon : {A : Set } → (f g : A → Val) → (f ≤l g) → (ma : M A) → measure (fmapM f ma) ≤ measure (fmapM g ma)
postulate plusMon : {a b c d : Val } → a ≤ b → c ≤ d → (a ⊕ c) ≤ (b ⊕ d)

-- Optimal extensions of optimal policy sequences are optimal
postulate Bellman : {t n : Nat} → (p : Policy t) → (ps : PolicySeq (suc t) n) →
                    OptExt ps p → OptPolicySeqBell ps → OptPolicySeqBell (p :: ps)
-- Bellman {t} {n} p ps optext optpol x = trans≤ ? ?
---------------------------------------------------------------------
-- 7.12 Verified backward induction
---------------------------------------------------------------------

-- With optExt one can solve SDPs by backward induction
bi : (t n : Nat) → PolicySeq t n
bi t zero = Nil
bi t (suc n) = let ps = bi (suc t) n in optExt ps :: ps

postulate refl≤l : {A B : Set} → (f : A → B) → f ≤l f 

-- By reflexivity of ≤
postulate nilIsOptPolicySeq : {t : Nat} → OptPolicySeqBell {t} Nil 
-- nilIsOptPolicySeq {t} x = refl≤

-- With Bellman and optExtSpec one can verify that bi yields optimal policy sequences
biOptVal : (t n : Nat)  → OptPolicySeqBell (bi t n)
biOptVal t zero         = nilIsOptPolicySeq
biOptVal t (suc n)      = Bellman (optExt (bi (suc t) n)) (bi (suc t) n) (optExtSpec (bi (suc t) n)) (biOptVal (suc t) n)

---------------------------------------------------------------------
-- Generation dilemma

data StateGen : Set where
    GU    : StateGen -- good unsafe
    GS    : StateGen -- good safe
    BT    : StateGen -- bad temporary
    B     : StateGen -- bad permanent

data ControlGen : Set where
    a   : ControlGen
    b   : ControlGen -- bad permanent

-- List monad
postulate Mgen : StateGen → List StateGen

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

-- Admisible states depending on the current state
AdmissibleStateGen : {t : Nat} → StateGen → List StateGen
AdmissibleStateGen {zero} x  = (GU ∷ [])
AdmissibleStateGen GU   = (GU ∷ BT ∷ B ∷ [])
AdmissibleStateGen GS   = (GS ∷ [])
AdmissibleStateGen BT   = (GS ∷ [])
AdmissibleStateGen B    = (B ∷ [])


-- Set of states as a dependent type on the previous states
--postulate Xgen : (t : Nat) → Σ (StateGen) (λ s → AdmissibleStateGen s)
postulate XGen : Nat → Set

-- Set of controls
postulate YGen : (t : Nat) → XGen t → Set 

-- nextGen
postulate nextGen : (t : Nat) → (x : XGen t) → YGen t x → M (XGen (suc t))

postulate rewardGen : (t : Nat) → (x : XGen t) → YGen t x → XGen (suc t) → Val     
