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
-- However, it is easy to rewrite the code into a form which does not
-- make use of swapping, at the cost of some code duplication.

module ThueMorse where

open import Codata.Musical.Notation
open import Codata.Musical.Stream as S using (Stream; _≈_)
open S.Stream; open S._≈_
open import Data.Bool using (Bool; not); open Data.Bool.Bool
open import Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P
import Relation.Binary.Reasoning.Setoid as EqReasoning

private
  module SS {A : Set} = Setoid (S.setoid A)
  open module EqR {A : Set} = EqReasoning (S.setoid A)
    using (begin_; _∎) renaming (_≈⟨_⟩_ to _≈⟨_⟩′_)

------------------------------------------------------------------------
-- Chunks

-- A value of type Chunks describes how a stream is generated. Note
-- that an infinite sequence of empty chunks is not allowed.

data Chunks : Set where
  -- Start the next chunk.
  next : (m :   Chunks) → Chunks
  -- Cons an element to the current chunk.
  cons : (m : ∞ Chunks) → Chunks

-- Equality of chunks.

infix 4 _≈C_

data _≈C_ : Chunks → Chunks → Set where
  next : ∀ {m m′} (m≈m′ :      m ≈C   m′ ) → next m ≈C next m′
  cons : ∀ {m m′} (m≈m′ : ∞ (♭ m ≈C ♭ m′)) → cons m ≈C cons m′

------------------------------------------------------------------------
-- Chunk transformers

tailC : Chunks → Chunks
tailC (next m) = next (tailC m)
tailC (cons m) = ♭ m

mutual

  evensC : Chunks → Chunks
  evensC (next m) = next (evensC m)
  evensC (cons m) = cons (♯ oddsC (♭ m))

  oddsC : Chunks → Chunks
  oddsC (next m) = next (oddsC m)
  oddsC (cons m) = evensC (♭ m)

infixr 5 _⋎C_

-- Note that care is taken to create as few and large chunks as
-- possible (see also _⋎W_).

_⋎C_ : Chunks → Chunks → Chunks
next m ⋎C next m′ = next (m ⋎C      m′)   -- Two chunks in, one out.
next m ⋎C cons m′ = next (m ⋎C cons m′)
cons m ⋎C      m′ = cons (♯ (m′ ⋎C ♭ m))

------------------------------------------------------------------------
-- Stream programs

-- StreamP m A encodes programs which generate streams with chunk
-- sizes given by m.

infixr 5 _∷_ _⋎_

data StreamP : Chunks → Set → Set₁ where
  [_]     : ∀ {m A} (xs : ∞ (StreamP m A)) → StreamP (next m) A
  _∷_     : ∀ {m A} (x : A) (xs : StreamP (♭ m) A) → StreamP (cons m) A
  tail    : ∀ {m A} (xs : StreamP m A) → StreamP (tailC m) A
  evens   : ∀ {m A} (xs : StreamP m A) → StreamP (evensC m) A
  odds    : ∀ {m A} (xs : StreamP m A) → StreamP (oddsC m) A
  _⋎_     : ∀ {m m′ A} (xs : StreamP m A) (ys : StreamP m′ A) →
            StreamP (m ⋎C m′) A
  map     : ∀ {m A B} (f : A → B) (xs : StreamP m A) → StreamP m B
  cast    : ∀ {m m′ A} (ok : m ≈C m′) (xs : StreamP m A) → StreamP m′ A

data StreamW : Chunks → Set → Set₁ where
  [_] : ∀ {m A} (xs : StreamP m A) → StreamW (next m) A
  _∷_ : ∀ {m A} (x : A) (xs : StreamW (♭ m) A) → StreamW (cons m) A

program : ∀ {m A} → StreamW m A → StreamP m A
program [ xs ]   = [ ♯ xs ]
program (x ∷ xs) = x ∷ program xs

tailW : ∀ {m A} → StreamW m A → StreamW (tailC m) A
tailW [ xs ]   = [ tail xs ]
tailW (x ∷ xs) = xs

mutual

  evensW : ∀ {m A} → StreamW m A → StreamW (evensC m) A
  evensW [ xs ]   = [ evens xs ]
  evensW (x ∷ xs) = x ∷ oddsW xs

  oddsW : ∀ {m A} → StreamW m A → StreamW (oddsC m) A
  oddsW [ xs ]   = [ odds xs ]
  oddsW (x ∷ xs) = evensW xs

infixr 5 _⋎W_

-- Note: Uses swapping of arguments.

_⋎W_ : ∀ {m m′ A} → StreamW m A → StreamW m′ A → StreamW (m ⋎C m′) A
[ xs ]   ⋎W [ ys ]   = [ xs ⋎ ys ]
[ xs ]   ⋎W (y ∷ ys) = [ xs ⋎ program (y ∷ ys) ]
(x ∷ xs) ⋎W ys       = x ∷ ys ⋎W xs

mapW : ∀ {m A B} → (A → B) → StreamW m A → StreamW m B
mapW f [ xs ]   = [ map f xs ]
mapW f (x ∷ xs) = f x ∷ mapW f xs

castW : ∀ {m m′ A} → m ≈C m′ → StreamW m A → StreamW m′ A
castW (next m≈m′) [ xs ]   = [ cast m≈m′ xs ]
castW (cons m≈m′) (x ∷ xs) = x ∷ castW (♭ m≈m′) xs

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

[ccn]ω : Chunks
[ccn]ω = cons (♯ cons (♯ next [ccn]ω))

[cn]²[ccn]ω : Chunks
[cn]²[ccn]ω = cons (♯ next (cons (♯ next [ccn]ω)))

[cn]³[ccn]ω : Chunks
[cn]³[ccn]ω = cons (♯ next [cn]²[ccn]ω)

-- Explanation of the proof of lemma₁:
--
-- odds [ccn]ω ≈ [cn]ω
--
-- [cn]ω ⋎ [ccn]ω ≈
-- c ([ccn]ω ⋎ n[cn]ω) ≈
-- c c (n[cn]ω ⋎ cn[ccn]ω) ≈
-- c c n ([cn]ω ⋎ cn[ccn]ω) ≈
-- c c n c (cn[ccn]ω ⋎ n[cn]ω) ≈
-- c c n c c (n[cn]ω ⋎ n[ccn]ω) ≈
-- c c n c c n ([cn]ω ⋎ [ccn]ω)

lemma₁ : oddsC [ccn]ω ⋎C [ccn]ω ≈C [ccn]ω
lemma₁ = cons (♯ cons (♯ next (cons (♯ cons (♯ next lemma₁)))))

-- Explanation of the proof of lemma:
--
-- evens [cn]³[ccn]ω ≈ cnn[cn]ω
-- tail  [cn]³[ccn]ω ≈ n[cn]²[ccn]ω
--
-- cnn[cn]ω ⋎ n[cn]²[ccn]ω ≈
-- c (n[cn]²[ccn]ω ⋎ nn[cn]ω) ≈
-- c n ([cn]²[ccn]ω ⋎ n[cn]ω) ≈
-- c n c (n[cn]ω ⋎ ncn[ccn]ω) ≈
-- c n c n ([cn]ω ⋎ cn[ccn]ω) ≈
-- c n c n c (cn[ccn]ω ⋎ n[cn]ω) ≈
-- c n c n c c (n[cn]ω ⋎ n[ccn]ω) ≈
-- c n c n c c n ([cn]ω ⋎ [ccn]ω)

lemma : evensC [cn]³[ccn]ω ⋎C tailC [cn]³[ccn]ω ≈C [cn]²[ccn]ω
lemma = cons (♯ next (cons (♯ next (cons (♯ cons (♯ next lemma₁))))))

thueMorse : StreamP [cn]³[ccn]ω Bool
thueMorse =
  false ∷ [ ♯ cast lemma (map not (evens thueMorse) ⋎ tail thueMorse) ]

------------------------------------------------------------------------
-- Equality programs

infix  4 _≈[_]P_ _≈[_]W_
infixr 2 _≈⟨_⟩P_ _≈⟨_⟩_

data _≈[_]P_ : {A : Set} → Stream A → Chunks → Stream A → Set₁ where
  [_]     : ∀ {m A} {xs ys : Stream A}
            (xs≈ys : ∞ (xs ≈[ m ]P ys)) → xs ≈[ next m ]P ys
  _∷_     : ∀ {m A} (x : A) {xs ys}
            (xs≈ys : ♭ xs ≈[ ♭ m ]P ♭ ys) → x ∷ xs ≈[ cons m ]P x ∷ ys
  tail    : ∀ {m A} {xs ys : Stream A} (xs≈ys : xs ≈[ m ]P ys) →
            S.tail xs ≈[ tailC m ]P S.tail ys
  evens   : ∀ {m A} {xs ys : Stream A} (xs≈ys : xs ≈[ m ]P ys) →
            S.evens xs ≈[ evensC m ]P S.evens ys
  odds    : ∀ {m A} {xs ys : Stream A} (xs≈ys : xs ≈[ m ]P ys) →
            S.odds xs ≈[ oddsC m ]P S.odds ys
  _⋎_     : ∀ {m m′ A} {xs xs′ ys ys′ : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) (xs′≈ys′ : xs′ ≈[ m′ ]P ys′) →
            (xs ⟨ S._⋎_ ⟩ xs′) ≈[ m ⋎C m′ ]P (ys ⟨ S._⋎_ ⟩ ys′)
  map     : ∀ {m A B} (f : A → B) {xs ys : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) → S.map f xs ≈[ m ]P S.map f ys
  cast    : ∀ {m m′ A} (ok : m ≈C m′) {xs ys : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) → xs ≈[ m′ ]P ys
  _≈⟨_⟩P_ : ∀ {m A} xs {ys zs : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) (ys≈zs : ys ≈ zs) → xs ≈[ m ]P zs
  _≈⟨_⟩_  : ∀ {m A} xs {ys zs : Stream A}
            (xs≈ys : xs ≈ ys) (ys≈zs : ys ≈[ m ]P zs) → xs ≈[ m ]P zs

data _≈[_]W_ : {A : Set} → Stream A → Chunks → Stream A → Set₁ where
  [_]     : ∀ {m A} {xs ys : Stream A}
            (xs≈ys : xs ≈[ m ]P ys) → xs ≈[ next m ]W ys
  _∷_     : ∀ {m A} (x : A) {xs ys}
            (xs≈ys : ♭ xs ≈[ ♭ m ]W ♭ ys) → x ∷ xs ≈[ cons m ]W x ∷ ys

program≈ : ∀ {m A} {xs ys : Stream A} → xs ≈[ m ]W ys → xs ≈[ m ]P ys
program≈ [ xs≈ys ]   = [ ♯ xs≈ys ]
program≈ (x ∷ xs≈ys) = x ∷ program≈ xs≈ys

tail-congW : ∀ {m A} {xs ys : Stream A} → xs ≈[ m ]W ys →
             S.tail xs ≈[ tailC m ]W S.tail ys
tail-congW [ xs≈ys ]   = [ tail xs≈ys ]
tail-congW (x ∷ xs≈ys) = xs≈ys

mutual

  evens-congW : ∀ {m A} {xs ys : Stream A} →
                xs ≈[ m ]W ys → S.evens xs ≈[ evensC m ]W S.evens ys
  evens-congW [ xs≈ys ]   = [ evens xs≈ys ]
  evens-congW (x ∷ xs≈ys) = x ∷ odds-congW xs≈ys

  odds-congW : ∀ {m A} {xs ys : Stream A} →
               xs ≈[ m ]W ys → S.odds xs ≈[ oddsC m ]W S.odds ys
  odds-congW [ xs≈ys ]   = [ odds xs≈ys ]
  odds-congW (x ∷ xs≈ys) = evens-congW xs≈ys

infixr 5 _⋎-congW_

-- Note: Uses swapping of arguments.

_⋎-congW_ : ∀ {m m′ A} {xs xs′ ys ys′ : Stream A} →
            xs ≈[ m ]W ys → xs′ ≈[ m′ ]W ys′ →
            (xs ⟨ S._⋎_ ⟩ xs′) ≈[ m ⋎C m′ ]W (ys ⟨ S._⋎_ ⟩ ys′)
[ xs≈ys ]   ⋎-congW [ xs′≈ys′ ]   = [ xs≈ys ⋎ xs′≈ys′ ]
[ xs≈ys ]   ⋎-congW (y ∷ xs′≈ys′) = [ xs≈ys ⋎ program≈ (y ∷ xs′≈ys′) ]
(x ∷ xs≈ys) ⋎-congW xs′≈ys′       = x ∷ xs′≈ys′ ⋎-congW xs≈ys

map-congW : ∀ {m A B} (f : A → B) {xs ys : Stream A} →
            xs ≈[ m ]W ys → S.map f xs ≈[ m ]W S.map f ys
map-congW f [ xs≈ys ]   = [ map f xs≈ys ]
map-congW f (x ∷ xs≈ys) = f x ∷ map-congW f xs≈ys

cast-congW : ∀ {m m′ A} (ok : m ≈C m′) {xs ys : Stream A} →
             xs ≈[ m ]W ys → xs ≈[ m′ ]W ys
cast-congW (next m≈m′) [ xs≈ys ]   = [ cast m≈m′ xs≈ys ]
cast-congW (cons m≈m′) (x ∷ xs≈ys) = x ∷ cast-congW (♭ m≈m′) xs≈ys

transPW : ∀ {m A} {xs ys zs : Stream A} →
          xs ≈[ m ]W ys → ys ≈ zs → xs ≈[ m ]W zs
transPW [ xs≈ys ]   ys≈zs            = [ _ ≈⟨ xs≈ys ⟩P ys≈zs ]
transPW (x ∷ xs≈ys) (P.refl ∷ ys≈zs) = x ∷ transPW xs≈ys (♭ ys≈zs)

transW : ∀ {m A} {xs ys zs : Stream A} →
         xs ≈ ys → ys ≈[ m ]W zs → xs ≈[ m ]W zs
transW (x ∷ xs≈ys)      [ ys≈zs ]   = [ _ ≈⟨ x ∷ xs≈ys ⟩ ys≈zs ]
transW (P.refl ∷ xs≈ys) (x ∷ ys≈zs) = x ∷ transW (♭ xs≈ys) ys≈zs

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
  soundW (x ∷ xs≈ys) = P.refl ∷ ♯ soundW xs≈ys

  soundP : ∀ {m A} {xs ys : Stream A} → xs ≈[ m ]P ys → xs ≈ ys
  soundP xs≈ys = soundW (whnf≈ xs≈ys)

------------------------------------------------------------------------
-- The definition is correct

-- The proof consists mostly of boiler-plate code.

program-hom : ∀ {m A} (xs : StreamW m A) → ⟦ program xs ⟧P ≈ ⟦ xs ⟧W
program-hom [ xs ]   = SS.refl
program-hom (x ∷ xs) = P.refl ∷ ♯ program-hom xs

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
             ⟦ xs ⋎W ys ⟧W ≈[ m ⋎C m′ ]P (⟦ xs ⟧W ⟨ S._⋎_ ⟩ ⟦ ys ⟧W)
  (x ∷ xs) ⋎W-hom ys        = x ∷ ys ⋎W-hom xs
  [ xs ]   ⋎W-hom [ ys ]    = [ ♯ (xs ⋎-hom ys) ]
  [ xs ]   ⋎W-hom (y ∷ ys′) =
    [ ♯ (⟦ xs ⋎ program ys ⟧P                 ≈⟨ xs ⋎-hom program ys ⟩P (begin
         (⟦ xs ⟧P ⟨ S._⋎_ ⟩ ⟦ program ys ⟧P)  ≈⟨ SS.refl ⟨ S._⋎-cong_ ⟩ program-hom ys ⟩′
         (⟦ xs ⟧P ⟨ S._⋎_ ⟩ ⟦ ys ⟧W)          ∎)) ]
    where ys = y ∷ ys′

  _⋎-hom_ : ∀ {A : Set} {m m′} (xs : StreamP m A) (ys : StreamP m′ A) →
            ⟦ xs ⋎ ys ⟧P ≈[ m ⋎C m′ ]P (⟦ xs ⟧P ⟨ S._⋎_ ⟩ ⟦ ys ⟧P)
  xs ⋎-hom ys = whnf xs ⋎W-hom whnf ys

mutual

  evensW-hom : ∀ {A : Set} {m} (xs : StreamW m A) →
               ⟦ evensW xs ⟧W ≈ S.evens ⟦ xs ⟧W
  evensW-hom [ xs ]   = evens-hom xs
  evensW-hom (x ∷ xs) = P.refl ∷ ♯ oddsW-hom xs

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
  mapW-hom f (x ∷ xs) = P.refl ∷ ♯ mapW-hom f xs

  map-hom : ∀ {A B : Set} {m} (f : A → B) (xs : StreamP m A) →
            ⟦ map f xs ⟧P ≈ S.map f ⟦ xs ⟧P
  map-hom f xs = mapW-hom f (whnf xs)

mutual

  castW-hom : ∀ {m m′ A} (m≈m′ : m ≈C m′) (xs : StreamW m A) →
              ⟦ castW m≈m′ xs ⟧W ≈ ⟦ xs ⟧W
  castW-hom (next m≈m′) [ xs ]   = cast-hom m≈m′ xs
  castW-hom (cons m≈m′) (x ∷ xs) = P.refl ∷ ♯ castW-hom (♭ m≈m′) xs

  cast-hom : ∀ {m m′ A} (m≈m′ : m ≈C m′) (xs : StreamP m A) →
             ⟦ cast m≈m′ xs ⟧P ≈ ⟦ xs ⟧P
  cast-hom m≈m′ xs = castW-hom m≈m′ (whnf xs)

-- The intended definition of the Thue-Morse sequence is bs = rhs bs.

rhs : Stream Bool → Stream Bool
rhs bs = false ∷ ♯ (S.map not (S.evens bs) ⟨ S._⋎_ ⟩ S.tail bs)

-- The definition above satisfies the intended defining equation.

correct : ⟦ thueMorse ⟧P ≈[ [cn]³[ccn]ω ]P rhs ⟦ thueMorse ⟧P
correct = false ∷ [ ♯ cast lemma (
  ⟦ cast lemma (map not (evens thueMorse) ⋎ tail thueMorse) ⟧P          ≈⟨ cast-hom lemma (map not (evens thueMorse) ⋎ tail thueMorse) ⟩
  ⟦ map not (evens thueMorse) ⋎ tail thueMorse ⟧P                       ≈⟨ map not (evens thueMorse) ⋎-hom tail thueMorse ⟩P (begin
  (⟦ map not (evens thueMorse) ⟧P ⟨ S._⋎_ ⟩ ⟦ tail thueMorse ⟧P)        ≈⟨ SS.trans (map-hom not (evens thueMorse))
                                                                                    (S.map-cong not (evens-hom thueMorse))
                                                                             ⟨ S._⋎-cong_ ⟩
                                                                           tail-hom thueMorse ⟩′
  (S.map not (S.evens ⟦ thueMorse ⟧P) ⟨ S._⋎_ ⟩ S.tail ⟦ thueMorse ⟧P)  ∎ )) ]

-- The defining equation has at most one solution.

unique : ∀ bs bs′ → bs ≈ rhs bs → bs′ ≈ rhs bs′ → bs ≈[ [cn]³[ccn]ω ]P bs′
unique bs bs′ bs≈ bs′≈ =
  bs      ≈⟨ bs≈ ⟩
  rhs bs  ≈⟨ false ∷ [ ♯ cast lemma
                           (map not (evens (unique bs bs′ bs≈ bs′≈))
                              ⋎
                            tail (unique bs bs′ bs≈ bs′≈)) ] ⟩P (begin
  rhs bs′ ≈⟨ SS.sym bs′≈ ⟩′
  bs′     ∎)
