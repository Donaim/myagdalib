
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_ ; ∃)
open import Data.Sum renaming (_⊎_ to Either ; inj₁ to Left ; inj₂ to Right)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Builtin.Sigma
open import Relation.Nullary

_|>_ : forall {a b} {A : Set a} {B : Set b} -> (x : A) -> (f : (A -> B)) -> B
x |> f = f x

infixl 1 _|>_

data DecidableEquality {l} (A : Set l) : Set l where
  decidableFunc : (eq : (a : A) -> (b : A) -> (Dec (a ≡ b))) -> DecidableEquality A

projectDecidableEq : ∀ {l} {A : Set l} -> DecidableEquality A -> (a : A) -> (b : A) -> Dec (a ≡ b)
projectDecidableEq (decidableFunc eq) = eq

pairFstInj :
  ∀ {w} ->
  ∀ {l} ->
  {A : Set w} ->
  {B : Set l} ->
  {a : A × B} ->
  {b : A × B} ->
  (a ≡ b) ->
  (fst a ≡ fst b)
pairFstInj refl = refl

pairSndInj :
  ∀ {w} ->
  ∀ {l} ->
  {A : Set w} ->
  {B : Set l} ->
  {a : A × B} ->
  {b : A × B} ->
  (a ≡ b) ->
  (snd a ≡ snd b)
pairSndInj refl = refl

decidePairEq :
  ∀ {w l} ->
  {A : Set w} ->
  {B : Set l} ->
  (DecidableEquality A) ->
  (DecidableEquality B) ->
  (a : A × B) ->
  (b : A × B) ->
  Dec (a ≡ b)
decidePairEq (decidableFunc eqa) (decidableFunc eqb) a b with (eqa (fst a) (fst b)) | (eqb (snd a) (snd b))
decidePairEq (decidableFunc eqa) (decidableFunc eqb) a b | no p  | any =
  no (λ pp ->
    let fsteq = pairFstInj pp
    in p fsteq)
decidePairEq {w} {l} {A} {B} (decidableFunc eqa) (decidableFunc eqb) a b | yes pa | yes pb =
  yes (cong₂ _,_ pa pb)
decidePairEq {w} {l} {A} {B} (decidableFunc eqa) (decidableFunc eqb) a b | yes pa | no p =
  no (λ pp ->
    let fsteq = pairSndInj pp
    in p fsteq)

negate-exists : {A : Set} {B : A → Set} →
      ¬ (∃ λ a → B a) →
      (∀ a → ¬ (B a))
negate-exists prf a b = prf (a , b)

negate-forall : {A : Set} {B : A → Set} →
      (∀ a → ¬ (B a)) ->
      (¬ (∃ λ a → B a))
negate-forall {A} {B} forall-prf existance-pair =
  let exists = fst existance-pair
  in let kek = forall-prf exists
  in let existance-prf = (snd existance-pair)
  in kek existance-prf

imply-closure : ∀ {p q r} {A : Set p} {B : Set q} {C : Set r}
              -> (A -> B) -> (B -> ⊥) -> (A -> ⊥)
imply-closure ab b- a = b- (ab a)

