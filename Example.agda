-- Module showing an example of using the MonadLaws to construct
-- an instance of a Maybe monad and prove that the laws hold.
module Example where

open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Tuple
open import Data.Maybe
open import Category.Monad
open import Function
open import MonadLaws

monad-Maybe : ∀ {f} → RawMonad {f} Maybe
monad-Maybe = record { return = just
                     ; _>>=_  = λ{ (just x) f → f x; nothing _ → nothing }
                     }

rid-Maybe : ∀ {ℓ} → right-identity {ℓ} monad-Maybe
rid-Maybe (just _) = refl
rid-Maybe nothing  = refl

lid-Maybe : ∀ {ℓ} → left-identity {ℓ} monad-Maybe
lid-Maybe _ = refl

ass-Maybe : ∀ {ℓ} → associativity {ℓ} monad-Maybe
ass-Maybe (just _) = refl
ass-Maybe nothing  = refl

Maybe-is-monad : ∀ {ℓ} → IsMonad {ℓ} Maybe monad-Maybe
Maybe-is-monad = isMonad rid-Maybe lid-Maybe ass-Maybe
