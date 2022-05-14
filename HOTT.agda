{-# OPTIONS --cubical --type-in-type --no-import-sorts #-}
module HOTT where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

1-1-Corr : (A B : Type) → Type
1-1-Corr A B = Σ[ R ∈ (A → B → Type) ]
    ((a : A) → isContr (Σ[ b ∈ B ] R a b)) ×
    ((b : B) → isContr (Σ[ a ∈ A ] R a b))

record Corr (A B : Type) : Type where
    field
        _≈_ : A → B → Type

        trR : A → B
        fillR : (a : A) → a ≈ trR a
        contrR : (a : A) (b : B) (r : a ≈ b) → trR a ≡ b
        truncR : (a : A) (b : B) (r : a ≈ b)
            → PathP (λ i → a ≈ contrR a b r i) (fillR a) r

        trL : B → A
        fillL : (b : B) → trL b ≈ b
        contrL : (b : B) (a : A) (r : a ≈ b) → trL b ≡ a
        truncL : (b : B) (a : A) (r : a ≈ b)
            → PathP (λ i → contrL b a r i ≈ b) (fillL b) r

to : (A B : Type) → 1-1-Corr A B → Corr A B
Corr._≈_ (to A B c) = c .fst
Corr.trR (to A B c) a = c .snd .fst a .fst .fst
Corr.fillR (to A B c) a = c .snd .fst a .fst .snd
Corr.contrR (to A B c) a b r i = c .snd .fst a .snd (b , r) i .fst
Corr.truncR (to A B c) a b r i = c .snd .fst a .snd (b , r) i .snd
Corr.trL (to A B c) b = c .snd .snd b .fst .fst
Corr.fillL (to A B c) b = c .snd .snd b .fst .snd
Corr.contrL (to A B c) b a r i = c .snd .snd b .snd (a , r) i .fst
Corr.truncL (to A B c) b a r i = c .snd .snd b .snd (a , r) i .snd

from : (A B : Type) → Corr A B → 1-1-Corr A B
from A B c = _≈_ ,
        (λ a → (trR a , fillR a) ,
            λ br i →
                contrR a (br .fst) (br .snd) i ,
                truncR a (br .fst) (br .snd) i),
        (λ b → (trL b , fillL b) ,
            λ ar i →
                contrL b (ar .fst) (ar .snd) i ,
                truncL b (ar .fst) (ar .snd) i)
    where open Corr c


