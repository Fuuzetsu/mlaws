module MonadLaws where

open import Level
open import Category.Monad
open import Relation.Binary.PropositionalEquality

left-identity : ∀ {ℓ} {M : Set ℓ → Set ℓ}
  → RawMonad {ℓ} M
  → Set (suc ℓ)
left-identity {ℓ} {M} M-inst = {A B : Set ℓ} {f : A → M B}
  → (a : A)
  → (return a >>= f) ≡ f a
  where _>>=_  = RawMonad._>>=_  M-inst
        return = RawMonad.return M-inst

right-identity : ∀ {ℓ} {M : Set ℓ → Set ℓ}
  → RawMonad {ℓ} M
  → Set (suc ℓ)
right-identity {ℓ} {M} M-inst = {A : Set ℓ}
  → (x : M A)
  → (x >>= return) ≡ x
  where _>>=_  = RawMonad._>>=_  M-inst
        return = RawMonad.return M-inst

associativity : ∀ {ℓ} {M : Set ℓ → Set ℓ}
  → RawMonad {ℓ} M
  → Set (suc ℓ)
associativity {ℓ} {M} M-inst = {A B C : Set ℓ} {f : A → M B} {g : B → M C}
  → (a : M A)
  → ((a >>= f) >>= g) ≡ (a >>= (λ x → f x >>= g))
  where _>>=_  = RawMonad._>>=_  M-inst

data IsMonad {ℓ : Level} : (M : Set ℓ → Set ℓ) → (RawMonad {ℓ} M) → Set (suc ℓ) where
  isMonad : {M : Set ℓ → Set ℓ} {inst : RawMonad {ℓ} M}
    → right-identity {ℓ} inst
    → left-identity  {ℓ} inst
    → associativity  {ℓ} inst
    → IsMonad M inst
