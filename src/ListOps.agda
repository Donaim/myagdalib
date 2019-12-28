open import Data.String renaming (_≟_ to string=)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_) renaming (_++_ to append)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_ ; ∃)
open import Data.Sum renaming (_⊎_ to Either ; inj₁ to Left ; inj₂ to Right)
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Sigma
open import Agda.Primitive
open import Relation.Nullary

open import Utils

_!_ : ∀{A : Set} → List A → Nat → Maybe A
[] ! _           = nothing
(x ∷ xs) ! zero    = just x
(x ∷ xs) ! (suc n) = xs ! n

infix 6 _!_

data _∈_ {A : Set}(x : A) : List A → Set where
  first : (y : A) (ys : List A) → x ≡ y -> x ∈ (y ∷ ys)
  later : (y : A) (ys : List A) → x ∈ ys → x ∈ (y ∷ ys)

infix 4 _∈_

data ListNth {A : Set} : (index : Nat) (x : A) -> (List A) -> Set where
  ListNthHead : (x : A) -> (xs : List A) -> ListNth 0 x (x ∷ xs)
  ListNthTail : (x : A) -> (lst : List A) -> (n : Nat)
    -> (prev : ListNth n x lst) -> (y : A) -> ListNth (suc n) x (y ∷ lst)

nth-means-contained : ∀ {A} {index : Nat} {x : A} {xs : List A}
  -> ListNth {A} index x xs -> x ∈ xs
nth-means-contained {A} {0} {x} {lst} (ListNthHead x xs) =
  first x xs refl
nth-means-contained {A} {suc n} {xx} {.(y ∷ lst)} (ListNthTail .xx lst .n prev y) =
  let ih = nth-means-contained {A} {n} {xx} {lst} prev
  in later y lst ih

decideMemq : ∀ {A} -> DecidableEquality A -> (x : A) -> (lst : List A) -> Dec (x ∈ lst)
decideMemq eq x [] = no absurd
  where
  absurd : x ∈ [] -> ⊥
  absurd ()
decideMemq eq x (y ∷ ys) with (projectDecidableEq eq x y)
decideMemq eq x (y ∷ ys) | yes p = yes (first y ys p)
decideMemq eq x (y ∷ ys) | no  z = help eq x y ys z
  where
  help2 : ∀ {A} {x : A} {ys : List A} {y : A} →
          (x ≡ y -> ⊥) -> (x ∈ ys -> ⊥) -> x ∈ (y ∷ ys) → ⊥
  help2 p1 p2 (first y ys mp) = p1 mp
  help2 p1 p2 (later y ys mp) = p2 mp

  help : ∀ {A} -> DecidableEquality A -> (x y : A) -> (ys : List A) → ¬ (x ≡ y) -> Dec (x ∈ (y ∷ ys))
  help eq x y ys prf with (decideMemq eq x ys)
  help eq x y ys prf | yes p = yes (later y ys p)
  help eq x y ys prf | no  z = no (help2 prf z)

indexLemma : ∀ {A} {x : A} {y : A} {ys : List A} {n : Nat}
           -> (¬ n ≡ zero) -> (y ∷ ys) ! n ≡ just x -> ys ! (pred n) ≡ just x
indexLemma {A} {x} {y} {ys} {zero} np p = ⊥-elim (np refl)
indexLemma {A} {x} {y} {ys} {suc n} np p = p

indexLemmaSuc : ∀ {A} {x : A} {y : A} {ys : List A} {n : Nat}
           -> ys ! n ≡ just x -> (y ∷ ys) ! (suc n) ≡ just x
indexLemmaSuc p = p

lookup : ∀ {A}{x : A}(xs : List A) → x ∈ xs → Σ Nat (λ n → xs ! n ≡ just x)
lookup {A} {x} [] prf = ⊥-elim (absurd prf)
  where
  absurd : ∀ {A} {x : A} → x ∈ [] -> ⊥
  absurd ()
lookup {A} {x} (y ∷ ys) (first .y .ys prf) rewrite prf = (zero , refl)
lookup {A} {x} (y ∷ ys) (later .y .ys prf) =
  let ih = lookup {A} {x} ys prf
  in let (n , nprf) = ih
  in let lm = indexLemmaSuc {A} {x} {y} {ys} {n} nprf
  in (suc n , lm)

lookup-to-element : {A : Set}{x : A}(xs : List A)
    → Σ Nat (λ n → xs ! n ≡ just x) -> Σ A (λ a -> a ≡ x)
lookup-to-element lst (zero , snd) with (lst ! zero)
lookup-to-element {A} {x} lst (zero , refl) | just k = (k , refl)
lookup-to-element {A} {x} lst (zero , snd) | nothing = help2 A lst x snd
    where
    help2 : (A : Set) (lst : List A) (x : A)
          (snd : nothing ≡ just x) → Σ A (λ a -> a ≡ x)
    help2 a x lst ()
lookup-to-element {A} {x} [] (suc fst , ())
lookup-to-element {A} {x} (y ∷ ys) (suc fst , snd) = lookup-to-element {A} {x} ys (fst , snd)

list-at-p : ∀ {A} -> (lst : List A) -> (n : Nat) -> Dec (Σ A (\y -> ListNth n y lst))
list-at-p [] n = no help
  where
  help : ∀ {A} {n} → ¬ Σ A (λ x → ListNth n x [])
  help (fst₁ , ())
list-at-p (x ∷ lst) zero = yes (x , ListNthHead x lst)

list-at-p (x ∷ lst) (suc n) with (list-at-p lst n)
list-at-p (z ∷ lst) (suc n) | yes (m , mp) =
  yes ( m , ListNthTail m lst n mp z )
list-at-p (x ∷ lst) (suc n) | no np = no (help x lst n np)
  where
  help : ∀ {A} -> (x : A) -> (lst : List A) -> (n : Nat)
       -> (¬ Σ A (λ y → ListNth n y lst))
       -> (¬ Σ A (λ y → ListNth (suc n) y (x ∷ lst)))
  help x lst n p (n2 , (ListNthTail .n2 .lst .n cp .x)) =
    let neg = negate-exists p
    in neg n2 cp

index-of-p : ∀ {A} -> (DecidableEquality A) -> (lst : List A) -> (x : A) -> Dec (Σ Nat (\n -> ListNth n x lst))
index-of-p eq [] x = no help
  where
  help : ∀ {A} {x : A} → ¬ Σ ℕ (λ n → ListNth n x [])
  help (n , ())
index-of-p eq (y ∷ lst) x with (index-of-p eq lst x)
index-of-p eq (y ∷ lst) x | yes (i , snd₁) = yes (suc i , ListNthTail x lst i snd₁ y)
index-of-p {A} eq (y ∷ lst) x | no p = help {A} eq y lst x p
  where
  help : ∀ {A} -> (DecidableEquality A) -> (y : A) -> (lst : List A) -> (x : A) →
         (¬ Σ Nat (λ n -> ListNth n x lst)) ->
         (Dec (Σ Nat (λ n -> ListNth n x (y ∷ lst))))
  help {A} (decidableFunc eq) y lst x p with (eq x y)
  help {A} (decidableFunc eq) y lst x p | yes pz = yes (help2 pz)
    where
    help2 : ∀ {A} {y x : A} {lst : List A} →
          (x ≡ y) ->
          (Σ ℕ (λ n → ListNth n x (y ∷ lst)))
    help2 {A} {y} {x} {lst} eqp rewrite eqp = (0 , ListNthHead y lst)

  help {A} (decidableFunc eq) y lst x p | no py = no (help2 py p)
    where
    help2 : ∀ {A} {y x : A} {lst : List A} →
          (¬ (x ≡ y)) ->
          (¬ (Σ Nat (\n -> ListNth n x lst))) ->
          (¬ (Σ ℕ (λ n → ListNth n x (y ∷ lst))))
    help2 {A} {y} {.y} {lst} eqp ih (.0 , (ListNthHead .y .lst)) = eqp refl
    help2 {A} {y} {x} {lst} eqp ih (.(suc n) , (ListNthTail .x .lst n pp .y))
      =
      let all = negate-exists ih
      in all n pp

PairList : ∀ {w l} -> (A : Set w) -> (B : Set l) -> Set (w Agda.Primitive.⊔ l)
PairList a b = List (a × b)

data _∈[key]_ {w l} {A : Set w} {B : Set l} (x : A) : PairList A B → Set (w Agda.Primitive.⊔ l) where
  first[key] : {y : A × B} {ys : PairList A B} → x ≡ fst y -> x ∈[key] (y ∷ ys)
  later[key] : {y : A × B} {ys : PairList A B} → x ∈[key] ys → x ∈[key] (y ∷ ys)

infix 4 _∈[key]_

decide-∈[key] : {A B : Set} (eq : DecidableEquality A) (x : A) (lst : PairList A B) → Dec (x ∈[key] lst)
decide-∈[key] eq x [] = no (λ ())
decide-∈[key] (decidableFunc eq) x (y ∷ lst)
  with (eq x (fst y)) | decide-∈[key] (decidableFunc eq) x lst
decide-∈[key] (decidableFunc eq) x (y ∷ lst) | yes p | ih =
  yes (first[key] p)
decide-∈[key] (decidableFunc eq) x (y ∷ lst) | no p  | yes ih =
  yes (later[key] ih)
decide-∈[key] (decidableFunc eq) x (y ∷ lst) | no p  | no ih =
  no (λ { (first[key] x) → p x ;
          (later[key] pp) → ih pp })

data AreEqualInPList {K V} (a : K) (b : K) : PairList K V -> Set where
  -- AreEqualInListNMW : (c : PairList K V) -> a ≡ b -> AreEqualInPList a b c -- Not sure
  AreEqualInPListH
    : (y : K × V)
    -> (ys : PairList K V)
    -> fst y ≡ a
    -> (b , (snd y)) ∈ (y ∷ ys)
    -> AreEqualInPList a b (y ∷ ys)
  AreEqualInPListT
    : (y : K × V)
    -> (ys : PairList K V)
    -> AreEqualInPList a b ys
    -> AreEqualInPList a b (y ∷ ys)

decideEqualInPList
  : ∀ {K V}
  -> (DecidableEquality K)
  -> (DecidableEquality (K × V))
  -> (a : K)
  -> (b : K)
  -> (lst : PairList K V)
  -> Dec (AreEqualInPList a b lst)
decideEqualInPList eq eq2 a b [] = no (λ ())
decideEqualInPList eq eq2 a b (x ∷ lst) with (decideEqualInPList eq eq2 a b lst)
decideEqualInPList eq eq2 a b (x ∷ lst) | yes p =
  yes (AreEqualInPListT x lst p)
decideEqualInPList {K} {V} eq eq2 a b (x ∷ lst) | no p = help {K} {V} eq eq2 a b x lst p
  where
  help : ∀ {K V}
         -> (DecidableEquality K)
         -> (DecidableEquality (K × V))
         -> (a : K)
         -> (b : K)
         -> (x : K × V)
         -> (lst : List (K × V))
         -> (¬ (AreEqualInPList a b lst))
         -> Dec (AreEqualInPList a b (x ∷ lst))
  help {K} {V} (decidableFunc eq) eq2 a b x lst p with (eq (fst x) a) | (decideMemq eq2 (b , (snd x)) (x ∷ lst))
  help {K} {V} (decidableFunc eq) eq2 a b x lst p | yes peq | yes peq2 = yes (AreEqualInPListH x lst peq peq2)
  help {K} {V} (decidableFunc eq) eq2 a b x lst p | yes peq | no peq2 =
    no (λ {
         (AreEqualInPListH y ys x pp) → peq2 pp ;
         (AreEqualInPListT y ys pp) → p pp
         })

  help {K} {V} (decidableFunc eq) eq2 a b x lst p | no peq | peq2 =
    no (λ {
         (AreEqualInPListH y ys x x₁) → peq x ;
         (AreEqualInPListT y ys pp) → p pp
         })

-- firstKey :
--   ∀ {w l} ->
--   ∀ {K : Set l} ->
--   ∀ {V : Set w} ->
--   ∀ (a : K) ->
--   ∀ (lst : PairList K V) ->
--   Dec (Σ (PairList K V × PairList K V)
--          (λ plist -> (((a ∈[key] (fst plist))) , (append (fst plist) (snd plist) ≡ lst))))
-- firstKey = ?

