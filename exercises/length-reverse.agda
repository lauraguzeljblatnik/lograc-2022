open import Relation.Binary.PropositionalEquality
open import Data.List hiding (reverse)
open import Data.Nat
open import Data.Nat.Properties

module length-reverse where

private
    rev : {A : Set} → List A → List A → List A
    rev xs [] = xs
    rev xs (x ∷ ys) = rev ( x ∷ xs ) ys 

reverse : {A : Set} → List A → List A
reverse {A} xs = rev [] xs

-- we want to prove this!
-- rabimo aux lemma about rev, ker je tako definiran reverse!
--  
length-reverse : {A : Set} {zs : List A} → length (reverse zs) ≡ length zs
length-reverse {A} {zs} =  length-rev [] zs
    where
        open ≡-Reasoning
        -- special case ce je rev [] zs, mi hocemo pokazat za vsak us
        -- najbolj pomembno, da ugotovis, da bo to vsota obeh sez za vsak korak!!!
        length-rev : (us vs : List A) → length (rev us vs) ≡ length us + length vs
        -- rev je induction on the second argument
        -- sym je symmetry
        length-rev us [] = sym (+-identityʳ (length us))
        -- reasoning line by line 
        length-rev us (x ∷ vs)  = 
            begin
            length (rev us (x ∷ vs)) ≡⟨ length-rev (x ∷ us) vs ⟩
            length (x ∷ us) + length vs  ≡˘⟨ +-suc (length us) (length vs) ⟩
            length us + length (x ∷ vs)
            ∎


-- rabimo suc(x+y) + x + suc y → uporabimo +-suc in sym 
-- \u{} da dobis to da obrne okrog dokaz (symm)        












