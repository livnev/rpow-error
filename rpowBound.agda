module rpowBound where

open import Data.Empty
open import Data.Bool.Base
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product
open import Data.Nat as ℕ using (ℕ; suc) renaming (zero to 0ℕ; _+_ to _+ℕ_; _*_ to _*ℕ_; _^_ to _^ℕ_; _≥_ to _≥ℕ_; _<_ to _<ℕ_)
open import Data.Integer as ℤ using (∣_∣) renaming (_⊖_ to _-ℕ_)
open import Data.Nat.DivMod using (_divMod_; DivMod)

1ℕ = suc 0ℕ
2ℕ = (suc (suc 0ℕ))

data Evenℕ : ℕ → Set where
  double : (n : ℕ) → Evenℕ (2ℕ *ℕ n)

data ℕ₊ : Set where
  1ℕ₊ : ℕ₊
  sucℕ₊ : ℕ₊ → ℕ₊

asℕ : ℕ₊ → ℕ
asℕ 1ℕ₊ = 1ℕ
asℕ (sucℕ₊ n) = (suc (asℕ n))

suc-is-nonzero : (n : ℕ) → ((suc n) ≢ 0ℕ)
suc-is-nonzero n = λ ()

nonzero-is-suc : (n : ℕ) → (n ≢ 0ℕ) → ∃[ m ] (suc m ≡ n)
nonzero-is-suc 0ℕ nonzero = 0ℕ , ⊥-elim (nonzero refl)
nonzero-is-suc (suc n) nonzero = n , refl

asℕ₊ : (n : ℕ) → (n ≢ 0ℕ) → ℕ₊
asℕ₊ 0ℕ nonzero = ⊥-elim (nonzero refl)
asℕ₊ (suc 0ℕ) nonzero = 1ℕ₊
asℕ₊ (suc (suc n)) nonzero = sucℕ₊ (asℕ₊ (suc n) (suc-is-nonzero n))
                         
ℕ₊nonzero : (n : ℕ₊) → ((asℕ n) ≢ 0ℕ)
ℕ₊nonzero 1ℕ₊ = λ ()
ℕ₊nonzero (sucℕ₊ m) = λ ()

-- flooring integer division
_//_ : ℕ → ℕ₊ → ℕ
_//_ a b = DivMod.quotient (_divMod_ a (asℕ b) {{!!} (no (ℕ₊nonzero))})

-- (no (ℕ₊nonzero b)) : Dec ((asℕ b) ≡ 0ℕ)
-- need term ≢0 : False ((asℕ b) =? 0)
-- False ((asℕ b) =? 0) = T (not ⌊ ((asℕ b) =? 0) ⌋ )
-- ((asℕ b) =? 0) : Dec ((asℕ b ≡ 0))
-- yes (ℕ₊nonzero b) : Dec ((asℕ b) ≢ 0ℕ)
-- ⌊ (yes (ℕ₊nonzero b)) ⌋ : Bool


infix 8 _//_

2ℕ₊ = sucℕ₊ 1ℕ₊

half : ℕ → ℕ
half n = n // 2ℕ₊

rmul : ℕ → ℕ → ℕ₊ → ℕ
rmul x y b = (x *ℕ y +ℕ (asℕ b) // 2ℕ₊) // b

rpow-spec-axiom-1 : (rpow : ℕ → ℕ → ℕ → ℕ₊ → ℕ) → Set
rpow-spec-axiom-1 rpow = (z x : ℕ) → (b : ℕ₊)
                       → ((rpow z x 0ℕ b) ≡ z)

rpow-spec-axiom-2 : (rpow : ℕ → ℕ → ℕ → ℕ₊ → ℕ) → Set
rpow-spec-axiom-2 rpow = (z x : ℕ) → (b : ℕ₊)
                       → ((rpow z x 1ℕ b) ≡ (rmul z x b))

rpow-spec-axiom-3 : (rpow : ℕ → ℕ → ℕ → ℕ₊ → ℕ) → Set
rpow-spec-axiom-3 rpow = (z x n : ℕ) → (b : ℕ₊)
                       → ((rpow (rmul z x b) x (n // 2ℕ₊) b) ≡ (rpow z x n b))

rpow-spec-axiom-4 : (rpow : ℕ → ℕ → ℕ → ℕ₊ → ℕ) → Set
rpow-spec-axiom-4 rpow = (z x n : ℕ) → (b : ℕ₊)
                       → ¬(Evenℕ n) → (n ≥ℕ 2ℕ)
                       → ((rpow (rmul z x b) (rmul x x b) (n // 2ℕ₊) b) ≡ (rpow z x n b))

rpow-spec-axiom-5 : (rpow : ℕ → ℕ → ℕ → ℕ₊ → ℕ) → Set
rpow-spec-axiom-5 rpow = (z x n : ℕ) → (b : ℕ₊)
                       → (Evenℕ n) → (n ≥ℕ 2ℕ)
                       → ((rpow z (rmul x x b) (n // 2ℕ₊) b) ≡ (rpow z x n b))

rpow-bound :  (rpow : ℕ → ℕ → ℕ → ℕ₊ → ℕ)
              → (rpow-spec-axiom-1 rpow)
              → (rpow-spec-axiom-2 rpow)
              → (rpow-spec-axiom-3 rpow)
              → (rpow-spec-axiom-4 rpow)
              → (rpow-spec-axiom-5 rpow)
              → (z x : ℕ) → (n : ℕ) → (b : ℕ₊)
              → (∣ (((asℕ b) ^ℕ n) *ℕ (rpow z x n b) -ℕ z *ℕ (x ^ℕ n)) ∣ <ℕ {!!})
rpow-bound = {!!}
