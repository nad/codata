------------------------------------------------------------------------
-- An implementation of the Thue-Morse sequence
------------------------------------------------------------------------

-- The paper "Productivity of stream definitions" by Endrullis et al.
-- (TCS 2010) uses a certain definition of the Thue-Morse sequence as
-- a running example.

-- Note that the code below makes use of the fact that Agda's
-- termination checker allows "swapping of arguments", which was not
-- mentioned when the termination checker was described in the paper
-- "Beating the Productivity Checker Using Embedded Languages".

module ThueMorse where

open import Coinduction
open import Data.Bool using (Bool; not); open Data.Bool.Bool
open import Data.Stream as S using (Stream; _≈_)
open S.Stream; open S._≈_
open import Function
open import Relation.Binary
import Relation.Binary.EqReasoning as EqReasoning

private
  module SS {A : Set} = Setoid (S.setoid A)
  open module EqR {A : Set} = EqReasoning (S.setoid A)
    using (begin_; _∎) renaming (_≈⟨_⟩_ to _≈⟨_⟩′_)

------------------------------------------------------------------------
-- Moduli of productivity

-- A modulus describes how a stream is generated. Note that an
-- infinite sequence of empty chunks is not allowed.

data Modulus : Set where
  -- Start the next chunk.
  next : (m :   Modulus) → Modulus
  -- Output an element in the current chunk.
  put  : (m : ∞ Modulus) → Modulus

-- Equality of moduli.

infix 4 _≈M_

data _≈M_ : Modulus → Modulus → Set where
  next : ∀ {m m′} (m≈m′ :      m ≈M   m′ ) → next m ≈M next m′
  put  : ∀ {m m′} (m≈m′ : ∞ (♭ m ≈M ♭ m′)) → put  m ≈M put  m′

------------------------------------------------------------------------
-- Modulus transformers

tailM : Modulus → Modulus
tailM (next m) = next (tailM m)
tailM (put  m) = ♭ m

mutual

  evensM : Modulus → Modulus
  evensM (next m) = next (evensM m)
  evensM (put  m) = put (♯ oddsM (♭ m))

  oddsM : Modulus → Modulus
  oddsM (next m) = next (oddsM m)
  oddsM (put  m) = evensM (♭ m)

infixr 5 _⋎M_

-- Note that care is taken to create as few and large chunks as
-- possible (see also _⋎W_).

_⋎M_ : Modulus → Modulus → Modulus
next m ⋎M next m′ = next (m ⋎M     m′)   -- Two chunks in, one out.
next m ⋎M put  m′ = next (m ⋎M put m′)
put  m ⋎M      m′ = put (♯ (m′ ⋎M ♭ m))

------------------------------------------------------------------------
-- Stream programs

-- StreamP m A encodes programs which generate streams with chunk
-- sizes given by m.

infixr 5 _∷_ _⋎_

data StreamP : Modulus → Set → Set₁ where
  [_]     : ∀ {m A} (xs : ∞ (StreamP m A)) → StreamP (next m) A
  _∷_     : ∀ {m A} (x : A) (xs : StreamP (♭ m) A) → StreamP (put m) A
  tail    : ∀ {m A} (xs : StreamP m A) → StreamP (tailM m) A
  evens   : ∀ {m A} (xs : StreamP m A) → StreamP (evensM m) A
  odds    : ∀ {m A} (xs : StreamP m A) → StreamP (oddsM m) A
  _⋎_     : ∀ {m m′ A} (xs : StreamP m A) (ys : StreamP m′ A) →
            StreamP (m ⋎M m′) A
  map     : ∀ {m A B} (f : A → B) (xs : StreamP m A) → StreamP m B
  cast    : ∀ {m m′ A} (ok : m ≈M m′) (xs : StreamP m A) → StreamP m′ A

data StreamW : Modulus → Set → Set₁ where
  [_] : ∀ {m A} (xs : StreamP m A) → StreamW (next m) A
  _∷_ : ∀ {m A} (x : A) (xs : StreamW (♭ m) A) → StreamW (put m) A

program : ∀ {m A} → StreamW m A → StreamP m A
program [ xs ]   = [ ♯ xs ]
program (x ∷ xs) = x ∷ program xs

tailW : ∀ {m A} → StreamW m A → StreamW (tailM m) A
tailW [ xs ]   = [ tail xs ]
tailW (x ∷ xs) = xs

mutual

  evensW : ∀ {m A} → StreamW m A → StreamW (evensM m) A
  evensW [ xs ]   = [ evens xs ]
  evensW (x ∷ xs) = x ∷ oddsW xs

  oddsW : ∀ {m A} → StreamW m A → StreamW (oddsM m) A
  oddsW [ xs ]   = [ odds xs ]
  oddsW (x ∷ xs) = evensW xs

infixr 5 _⋎W_

-- Note: Uses swapping of arguments.

_⋎W_ : ∀ {m m′ A} → StreamW m A → StreamW m′ A → StreamW (m ⋎M m′) A
[ xs ]   ⋎W [ ys ]   = [ xs ⋎ ys ]
[ xs ]   ⋎W (y ∷ ys) = [ xs ⋎ program (y ∷ ys) ]
(x ∷ xs) ⋎W ys       = x ∷ ys ⋎W xs

mapW : ∀ {m A B} → (A → B) → StreamW m A → StreamW m B
mapW f [ xs ]   = [ map f xs ]
mapW f (x ∷ xs) = f x ∷ mapW f xs

castW : ∀ {m m′ A} → m ≈M m′ → StreamW m A → StreamW m′ A
castW (next m≈m′) [ xs ]   = [ cast m≈m′ xs ]
castW (put  m≈m′) (x ∷ xs) = x ∷ castW (♭ m≈m′) xs

whnf : ∀ {m A} → StreamP m A → StreamW m A
whnf [ xs ]         = [ ♭ xs ]
whnf (x ∷ xs)       = x ∷ whnf xs
whnf (tail xs)      = tailW (whnf xs)
whnf (evens xs)     = evensW (whnf xs)
whnf (odds xs)      = oddsW (whnf xs)
whnf (xs ⋎ ys)      = whnf xs ⋎W whnf ys
whnf (map f xs)     = mapW f (whnf xs)
whnf (cast m≈m′ xs) = castW m≈m′ (whnf xs)

mutual

  ⟦_⟧W : ∀ {m A} → StreamW m A → Stream A
  ⟦ [ xs ] ⟧W = ⟦ xs ⟧P
  ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧W

  ⟦_⟧P : ∀ {m A} → StreamP m A → Stream A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

------------------------------------------------------------------------
-- The Thue-Morse sequence

thueMorseM₂ : Modulus
thueMorseM₂ = put (♯ put (♯ next thueMorseM₂))

thueMorseM₁ : Modulus
thueMorseM₁ = put (♯ next (put (♯ next thueMorseM₂)))

thueMorseM : Modulus
thueMorseM = put (♯ next thueMorseM₁)

lemma₁ : oddsM thueMorseM₂ ⋎M thueMorseM₂ ≈M thueMorseM₂
lemma₁ = put (♯ put (♯ next (put (♯ put (♯ next lemma₁)))))

lemma : evensM thueMorseM ⋎M tailM thueMorseM ≈M thueMorseM₁
lemma = put (♯ next (put (♯ next (put (♯ put (♯ next lemma₁))))))

thueMorse : StreamP thueMorseM Bool
thueMorse =
  false ∷ [ ♯ cast lemma (map not (evens thueMorse) ⋎ tail thueMorse) ]

------------------------------------------------------------------------
-- Equality programs

infix  4 _≈[_]P_ _≈[_]W_
infixr 2 _≈⟨_⟩P_ _≈⟨_⟩_

data _≈[_]P_ : {A : Set} → Stream A → Modulus → Stream A → Set₁ where
  [_]     : ∀ {m A} {xs ys : Stream A}
            (xs≈ys : ∞ (xs ≈[ m ]P ys)) → xs ≈[ next m ]P ys
  _∷_     : ∀ {m A} (x : A) {xs ys}
            (xs≈ys : ♭ xs ≈[ ♭ m ]P ♭ ys) → x ∷ xs ≈[ put m ]P x ∷ ys
  tail    : ∀ {m A} {xs ys : Stream A} (xs≈ys : xs ≈[ m ]P ys) →
            S.tail xs ≈[ tailM m ]P S.tail ys
  evens   : ∀ {m A} {xs ys : Stream A} (xs≈ys : xs ≈[ m ]P ys) →
            S.evens xs ≈[ evensM m ]P S.evens ys
  odds    : ∀ {m A} {xs ys : Stream A} (xs≈ys : xs ≈[ m ]P ys) →
            S.odds xs ≈[ oddsM m ]P S.odds ys
  _⋎_     : ∀ {m m′ A} {xs xs′ ys ys′ : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) (xs′≈ys′ : xs′ ≈[ m′ ]P ys′) →
            (xs ⟨ S._⋎_ ⟩ xs′) ≈[ m ⋎M m′ ]P (ys ⟨ S._⋎_ ⟩ ys′)
  map     : ∀ {m A B} (f : A → B) {xs ys : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) → S.map f xs ≈[ m ]P S.map f ys
  cast    : ∀ {m m′ A} (ok : m ≈M m′) {xs ys : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) → xs ≈[ m′ ]P ys
  _≈⟨_⟩P_ : ∀ {m A} xs {ys zs : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) (ys≈zs : ys ≈ zs) → xs ≈[ m ]P zs
  _≈⟨_⟩_  : ∀ {m A} xs {ys zs : Stream A}
            (xs≈ys : xs ≈ ys) (ys≈zs : ys ≈[ m ]P zs) → xs ≈[ m ]P zs

data _≈[_]W_ : {A : Set} → Stream A → Modulus → Stream A → Set₁ where
  [_]     : ∀ {m A} {xs ys : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) → xs ≈[ next m ]W ys
  _∷_     : ∀ {m A} (x : A) {xs ys}
            (xs≈ys : ♭ xs ≈[ ♭ m ]W ♭ ys) → x ∷ xs ≈[ put m ]W x ∷ ys

program≈ : ∀ {m A} {xs ys : Stream A} → xs ≈[ m ]W ys → xs ≈[ m ]P ys
program≈ [ xs≈ys ]   = [ ♯ xs≈ys ]
program≈ (x ∷ xs≈ys) = x ∷ program≈ xs≈ys

tail-congW : ∀ {m A} {xs ys : Stream A} → xs ≈[ m ]W ys →
             S.tail xs ≈[ tailM m ]W S.tail ys
tail-congW [ xs≈ys ]   = [ tail xs≈ys ]
tail-congW (x ∷ xs≈ys) = xs≈ys

mutual

  evens-congW : ∀ {m A} {xs ys : Stream A} →
                xs ≈[ m ]W ys → S.evens xs ≈[ evensM m ]W S.evens ys
  evens-congW [ xs≈ys ]   = [ evens xs≈ys ]
  evens-congW (x ∷ xs≈ys) = x ∷ odds-congW xs≈ys

  odds-congW : ∀ {m A} {xs ys : Stream A} →
               xs ≈[ m ]W ys → S.odds xs ≈[ oddsM m ]W S.odds ys
  odds-congW [ xs≈ys ]   = [ odds xs≈ys ]
  odds-congW (x ∷ xs≈ys) = evens-congW xs≈ys

infixr 5 _⋎-congW_

-- Note: Uses swapping of arguments.

_⋎-congW_ : ∀ {m m′ A} {xs xs′ ys ys′ : Stream A} →
            xs ≈[ m ]W ys → xs′ ≈[ m′ ]W ys′ →
            (xs ⟨ S._⋎_ ⟩ xs′) ≈[ m ⋎M m′ ]W (ys ⟨ S._⋎_ ⟩ ys′)
[ xs≈ys ]   ⋎-congW [ xs′≈ys′ ]   = [ xs≈ys ⋎ xs′≈ys′ ]
[ xs≈ys ]   ⋎-congW (y ∷ xs′≈ys′) = [ xs≈ys ⋎ program≈ (y ∷ xs′≈ys′) ]
(x ∷ xs≈ys) ⋎-congW xs′≈ys′       = x ∷ xs′≈ys′ ⋎-congW xs≈ys

map-congW : ∀ {m A B} (f : A → B) {xs ys : Stream A} →
            xs ≈[ m ]W ys → S.map f xs ≈[ m ]W S.map f ys
map-congW f [ xs≈ys ]   = [ map f xs≈ys ]
map-congW f (x ∷ xs≈ys) = f x ∷ map-congW f xs≈ys

cast-congW : ∀ {m m′ A} (ok : m ≈M m′) {xs ys : Stream A} →
             xs ≈[ m ]W ys → xs ≈[ m′ ]W ys
cast-congW (next m≈m′) [ xs≈ys ]   = [ cast m≈m′ xs≈ys ]
cast-congW (put  m≈m′) (x ∷ xs≈ys) = x ∷ cast-congW (♭ m≈m′) xs≈ys

transPW : ∀ {m A} {xs ys zs : Stream A} →
          xs ≈[ m ]W ys → ys ≈ zs → xs ≈[ m ]W zs
transPW [ xs≈ys ]   ys≈zs        = [ _ ≈⟨ xs≈ys ⟩P ys≈zs ]
transPW (x ∷ xs≈ys) (.x ∷ ys≈zs) = x ∷ transPW xs≈ys (♭ ys≈zs)

transW : ∀ {m A} {xs ys zs : Stream A} →
         xs ≈ ys → ys ≈[ m ]W zs → xs ≈[ m ]W zs
transW (x ∷ xs≈ys) [ ys≈zs ]    = [ _ ≈⟨ x ∷ xs≈ys ⟩ ys≈zs ]
transW (x ∷ xs≈ys) (.x ∷ ys≈zs) = x ∷ transW (♭ xs≈ys) ys≈zs

whnf≈ : ∀ {m A} {xs ys : Stream A} → xs ≈[ m ]P ys → xs ≈[ m ]W ys
whnf≈ [ xs ]                 = [ ♭ xs ]
whnf≈ (x ∷ xs)               = x ∷ whnf≈ xs
whnf≈ (tail xs)              = tail-congW (whnf≈ xs)
whnf≈ (evens xs)             = evens-congW (whnf≈ xs)
whnf≈ (odds xs)              = odds-congW (whnf≈ xs)
whnf≈ (xs ⋎ ys)              = whnf≈ xs ⋎-congW whnf≈ ys
whnf≈ (map f xs)             = map-congW f (whnf≈ xs)
whnf≈ (cast m≈m′ xs)         = cast-congW m≈m′ (whnf≈ xs)
whnf≈ (xs ≈⟨ xs≈ys ⟩P ys≈zs) = transPW (whnf≈ xs≈ys) ys≈zs
whnf≈ (xs ≈⟨ xs≈ys ⟩  ys≈zs) = transW xs≈ys (whnf≈ ys≈zs)

mutual

  soundW : ∀ {m A} {xs ys : Stream A} → xs ≈[ m ]W ys → xs ≈ ys
  soundW [ xs≈ys ]   = soundP xs≈ys
  soundW (x ∷ xs≈ys) = x ∷ ♯ soundW xs≈ys

  soundP : ∀ {m A} {xs ys : Stream A} → xs ≈[ m ]P ys → xs ≈ ys
  soundP xs≈ys = soundW (whnf≈ xs≈ys)

------------------------------------------------------------------------
-- The definition is correct

-- The proof consists mostly of boiler-plate code.

program-hom : ∀ {m A} (xs : StreamW m A) → ⟦ program xs ⟧P ≈ ⟦ xs ⟧W
program-hom [ xs ]   = SS.refl
program-hom (x ∷ xs) = x ∷ ♯ program-hom xs

mutual

  tailW-hom : ∀ {A : Set} {m} (xs : StreamW m A) →
               ⟦ tailW xs ⟧W ≈ S.tail ⟦ xs ⟧W
  tailW-hom [ xs ]   = tail-hom xs
  tailW-hom (x ∷ xs) = SS.refl

  tail-hom : ∀ {A : Set} {m} (xs : StreamP m A) →
              ⟦ tail xs ⟧P ≈ S.tail ⟦ xs ⟧P
  tail-hom xs = tailW-hom (whnf xs)

mutual

  infixr 5 _⋎W-hom_ _⋎-hom_

  -- Note: Uses swapping of arguments.

  _⋎W-hom_ : ∀ {A : Set} {m m′} (xs : StreamW m A) (ys : StreamW m′ A) →
             ⟦ xs ⋎W ys ⟧W ≈[ m ⋎M m′ ]P (⟦ xs ⟧W ⟨ S._⋎_ ⟩ ⟦ ys ⟧W)
  (x ∷ xs) ⋎W-hom ys       = x ∷ ys ⋎W-hom xs
  [ xs ]   ⋎W-hom [ ys ]   = [ ♯ (xs ⋎-hom ys) ]
  [ xs ]   ⋎W-hom (y ∷ ys) =
    [ ♯ (⟦ xs ⋎ program (y ∷ ys) ⟧P                 ≈⟨ xs ⋎-hom program (y ∷ ys) ⟩P (begin
         (⟦ xs ⟧P ⟨ S._⋎_ ⟩ ⟦ program (y ∷ ys) ⟧P)  ≈⟨ SS.refl ⟨ S._⋎-cong_ ⟩ program-hom (y ∷ ys) ⟩′
         (⟦ xs ⟧P ⟨ S._⋎_ ⟩ ⟦ y ∷ ys ⟧W)            ∎)) ]

  _⋎-hom_ : ∀ {A : Set} {m m′} (xs : StreamP m A) (ys : StreamP m′ A) →
            ⟦ xs ⋎ ys ⟧P ≈[ m ⋎M m′ ]P (⟦ xs ⟧P ⟨ S._⋎_ ⟩ ⟦ ys ⟧P)
  xs ⋎-hom ys = whnf xs ⋎W-hom whnf ys

mutual

  evensW-hom : ∀ {A : Set} {m} (xs : StreamW m A) →
               ⟦ evensW xs ⟧W ≈ S.evens ⟦ xs ⟧W
  evensW-hom [ xs ]   = evens-hom xs
  evensW-hom (x ∷ xs) = x ∷ ♯ oddsW-hom xs

  evens-hom : ∀ {A : Set} {m} (xs : StreamP m A) →
              ⟦ evens xs ⟧P ≈ S.evens ⟦ xs ⟧P
  evens-hom xs = evensW-hom (whnf xs)

  oddsW-hom : ∀ {A : Set} {m} (xs : StreamW m A) →
              ⟦ oddsW xs ⟧W ≈ S.odds ⟦ xs ⟧W
  oddsW-hom [ xs ]   = odds-hom xs
  oddsW-hom (x ∷ xs) = evensW-hom xs

  odds-hom : ∀ {A : Set} {m} (xs : StreamP m A) →
             ⟦ odds xs ⟧P ≈ S.odds ⟦ xs ⟧P
  odds-hom xs = oddsW-hom (whnf xs)

mutual

  mapW-hom : ∀ {A B : Set} {m} (f : A → B) (xs : StreamW m A) →
             ⟦ mapW f xs ⟧W ≈ S.map f ⟦ xs ⟧W
  mapW-hom f [ xs ]   = map-hom f xs
  mapW-hom f (x ∷ xs) = f x ∷ ♯ mapW-hom f xs

  map-hom : ∀ {A B : Set} {m} (f : A → B) (xs : StreamP m A) →
            ⟦ map f xs ⟧P ≈ S.map f ⟦ xs ⟧P
  map-hom f xs = mapW-hom f (whnf xs)

mutual

  castW-hom : ∀ {m m′ A} (m≈m′ : m ≈M m′) (xs : StreamW m A) →
              ⟦ castW m≈m′ xs ⟧W ≈ ⟦ xs ⟧W
  castW-hom (next m≈m′) [ xs ]   = cast-hom m≈m′ xs
  castW-hom (put  m≈m′) (x ∷ xs) = x ∷ ♯ castW-hom (♭ m≈m′) xs

  cast-hom : ∀ {m m′ A} (m≈m′ : m ≈M m′) (xs : StreamP m A) →
             ⟦ cast m≈m′ xs ⟧P ≈ ⟦ xs ⟧P
  cast-hom m≈m′ xs = castW-hom m≈m′ (whnf xs)

-- The intended definition of the Thue-Morse sequence is bs = rhs bs.

rhs : Stream Bool → Stream Bool
rhs bs = false ∷ ♯ (S.map not (S.evens bs) ⟨ S._⋎_ ⟩ S.tail bs)

-- The definition above satisfies the intended defining equation.

correct : ⟦ thueMorse ⟧P ≈[ thueMorseM ]P rhs ⟦ thueMorse ⟧P
correct = false ∷ [ ♯ cast lemma (
  ⟦ cast lemma (map not (evens thueMorse) ⋎ tail thueMorse) ⟧P          ≈⟨ cast-hom lemma (map not (evens thueMorse) ⋎ tail thueMorse) ⟩
  ⟦ map not (evens thueMorse) ⋎ tail thueMorse ⟧P                       ≈⟨ map not (evens thueMorse) ⋎-hom tail thueMorse ⟩P (begin
  (⟦ map not (evens thueMorse) ⟧P ⟨ S._⋎_ ⟩ ⟦ tail thueMorse ⟧P)        ≈⟨ SS.trans (map-hom not (evens thueMorse))
                                                                                    (S.map-cong not (evens-hom thueMorse))
                                                                             ⟨ S._⋎-cong_ ⟩
                                                                           tail-hom thueMorse ⟩′
  (S.map not (S.evens ⟦ thueMorse ⟧P) ⟨ S._⋎_ ⟩ S.tail ⟦ thueMorse ⟧P)  ∎ )) ]

-- The defining equation has at most one solution.

unique : ∀ bs bs′ → bs ≈ rhs bs → bs′ ≈ rhs bs′ → bs ≈[ thueMorseM ]P bs′
unique bs bs′ bs≈ bs′≈ =
  bs      ≈⟨ bs≈ ⟩
  rhs bs  ≈⟨ false ∷ [ ♯ cast lemma
                           (map not (evens (unique bs bs′ bs≈ bs′≈))
                              ⋎
                            tail (unique bs bs′ bs≈ bs′≈)) ] ⟩P (begin
  rhs bs′ ≈⟨ SS.sym bs′≈ ⟩′
  bs′     ∎)
