{-# OPTIONS --without-K --exact-split --safe #-}
module tt where

open import Agda.Primitive renaming (_⊔_ to lmax)
open import Agda.Builtin.Sigma renaming (Σ to exists)
open import Function using (flip; _$_) renaming (_∘_ to _of_)

Rel : Set -> Set1
Rel A = A -> A -> Set

-- Some properties
record Reflexive {A : Set} (R : Rel A) : Set where
    field refl : (a : A) -> (R a a)

record Symmetric {A : Set} (R : Rel A) : Set where
    field sym : (a b : A) -> (R a b) -> (R b a)

record Transitive {A : Set} (R : Rel A) : Set where
    field trans : (a b c : A) -> (R a b) -> (R b c) -> (R a c)

record Equivalent {A : Set} (R : Rel A) : Set where
    field
        {{refl}} : Reflexive {A} R
        {{sym}} : Symmetric {A} R
        {{trans}} : Transitive {A} R
open Equivalent {{...}}

data Top : Set where
    Triv : Top

case : {C : Top -> Set} -> (x : Top) -> C Triv -> C x
case Triv c = c

data Bot : Set where

abort : {A : Set} -> Bot -> A
abort ()

data N : Set where
    zero : N
    succ : N -> N

{-# BUILTIN NATURAL N #-}

prim : {C : N -> Set} -> (n : N) -> C 0 -> ((m : N) -> C m -> C (succ m)) -> C n
prim 0 c f = c
prim (succ n) c f = f n (prim n c f)

add : N -> N -> N
add 0 m = m
add (succ n) m = succ (add n m)

{-# BUILTIN NATPLUS add #-}

mult : N -> N -> N
mult 0 m = 0
mult (succ n) m = add m (mult n m)

{-# BUILTIN NATTIMES mult #-}

data I {A : Set} : Rel A where
    I-refl : (a : A) -> I a a

_==_ : {A : Set} -> A -> A -> Set
x == y = I x y

J : {A : Set} -> {a b : A} -> (C : (a b : A) -> I a b -> Set) -> (c : I a b) -> C a a (I-refl a) -> C a b c
J _ (I-refl a) d = d

I-reflexivity : {A : Set} -> Reflexive {A} I
I-reflexivity = record {refl = I-refl}

I-sym : {A : Set} -> (a b : A) -> (a == b) -> (b == a)
I-sym a b p = J C p (I-refl a)
    where C = \a b r -> I b a
I-symmetry : {A : Set} -> Symmetric {A} I
I-symmetry = record {sym = I-sym}

I-trans : {A : Set} -> (a b c : A) -> (I a b) -> (I b c) -> (I a c)
I-trans a b c p q = J C q p
    where C = \b c r -> I a c
I-transitivity : {A : Set} -> Transitive {A} I
I-transitivity = record {trans = I-trans}

instance
    I-equivalence : {A : Set} -> Equivalent {A} I
    refl {{I-equivalence}} = I-reflexivity
    sym {{I-equivalence}} = I-symmetry
    trans {{I-equivalence}} = I-transitivity

data _or_ (A : Set) (B : Set) : Set where
    inl : (x : A) -> A or B
    inr : (y : B) -> A or B

cases : {A B : Set} -> {C : A or B -> Set} -> (p : A or B) -> ((x : A) -> C (inl x)) -> ((y : B) -> C (inr y)) -> C p
cases (inl x) f g = f x
cases (inr y) f g = g y

Z : Set
Z = N or N
pattern pos n = inl n
pattern neg n = inr n

sgn : Z -> Z
sgn (pos 0) = pos 0
sgn (pos (succ n)) = pos 1
sgn (neg n) = neg 0

abs : Z -> N
abs (pos n) = n
abs (neg n) = succ n

negate : Z -> Z
negate (pos 0) = pos 0
negate (pos (succ n)) = neg n
negate (neg n) = pos n

addi' : N -> Z -> Z
addi' n (pos m) = pos (add n m)
addi' 0 (neg m) = neg m
addi' (succ n) (neg 0) = pos n
addi' (succ n) (neg (succ m)) = addi' n (neg m)

addi : Z -> Z -> Z
addi (pos n) m = addi' n m
addi (neg n) (pos m) = addi' m (neg n)
addi (neg n) (neg m) = neg (succ (add n m))

multi : Z -> Z -> Z
multi (pos n) (pos m) = pos (mult n m)
multi (pos n) (neg m) = negate (pos (mult n (abs (neg m))))
multi (neg n) (pos m) = negate (pos (mult (abs (neg n)) m))
multi (neg n) (neg m) = pos (mult (abs (neg n)) (abs (neg m)))
