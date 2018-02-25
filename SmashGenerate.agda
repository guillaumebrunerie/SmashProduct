{-# OPTIONS --no-termination-check #-}
{-
Program generating the code for the properties of the smash product.
-}

open import Data.Nat.Base
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List.Base renaming (_++_ to _++ₗ_)
open import Data.String renaming (_==_ to _==ₛ_) hiding (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool.Base
open import Data.Unit.Base
open import Data.Maybe.Base hiding (map)
open import Agda.Builtin.Nat
open import Agda.Builtin.IO

open import Sprintf

module SmashGenerate where

{- For compilation to Haskell, we use the following [putStr] function -}
{-# FOREIGN GHC import qualified Data.Text.IO as TextIO #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# FOREIGN GHC import qualified Debug.Trace as Trace #-}
postulate
  trace : {A : Set} → String → A → A
  putStr : String → IO ⊤
{-# COMPILE GHC trace = \ _ s x -> Trace.trace (Text.unpack s) x #-}
{-# COMPILE GHC putStr = TextIO.putStr #-}

{- Tagging something as either explicit or implicit -}
data Arg (A : Set) : Set where
  Exp : A → Arg A
  Imp : A → Arg A

unArg : {A : Set} → Arg A → A
unArg (Exp t) = t
unArg (Imp t) = t

hiding-app : {A B : Set} → Arg A → B → Arg B
hiding-app (Exp _) t = Exp t
hiding-app (Imp _) t = Imp t


record Declaration : Set

data LR : Set where
  L R : LR

choose : {A : Set} → LR → A → A → A
choose L a b = a
choose R a b = b

{- The datatype of terms (and types).
   It is designed in such a way that it is always possible to figure out the
   type of a term, without needing to refer to an environment. In particular,
   all variables are tagged with their type.
-}
data Term : Set where
  -- Variable and its type
  Var : (s : String) (t : Term) → Term
  -- Atoms
  Atom : (s : String) → Term
  -- Declaration and its parameters (note that it is in a η-contracted form)
  Dec : (dec : Declaration) (args : List Term) → Term
  -- Application which may be explicit or implicit
  AppEI : (f : Term) (arg : Arg Term) → Term
  -- The smash product and its constructors
  Smash : (A B : Term) → Term
  Proj : (a b : Term) → Term
  Base : (lr : LR) (A B : Term) → Term
  Glue : (lr : LR) (A B ab : Term) → Term
  -- Identity type and constant path
  Id : (a b : Term) → Term
  Idp : (a : Term) → Term
  -- Square type and constant square
  Square : (p q r s : Term) → Term
  Ids : (a : Term) → Term
  -- Cube type and constant cube
  Cube : (p q r s t u : Term) → Term
  Idc : (a : Term) → Term
  -- Base point of the type named "A", to take the base point of a Term, use the function [pt]
  Pt : (A : String) → Term
  -- Base point of the function named "f"
  Ptf : (f : String) (A B : Term) → Term
  -- Lambda abstraction
  Lam : (s : String) (A : Term) (t : Term) → Term
  -- Pi-types, explicit or implicit
  PiEI : (s : Arg String) (A B : Term) → Term
  -- Pointed types and types, [Ptd] should maybe be removed
  Ptd : Term
  Type : Term
  -- Pointed maps
  PtdMap : (A B : Term) → Term
  -- Error messages
  ERROR : String → Term

trerror : {A : Set} → String → A → A
trerror s x = trace ("Internal error: " ++ s) x

Error : String → Term
Error s = trerror s (ERROR s)

{- The types of arguments we support -}
data ArgType : Set where
  /_-_/ : String → Term → ArgType
  _[∧]_ : ArgType → ArgType → ArgType

{- Declaration for a non-dependent function.
   name : The name of the function to be defined
   params : The list of parameters
   argtype : The type of the argument
   type : The return type
   def : The definition when replacing the smash products by products
-}
record SparseDeclaration : Set where
  inductive
  constructor sparsedeclaration
  field
    name : String
    params : List (String × Term)
    argtype : ArgType
    type : Term
    def : Term
open SparseDeclaration public

{- A top-level definition, with its name, type, and the definition as a string -}
record Coherence : Set where
  inductive
  constructor coherence
  field
    name : String
    type : Term
open Coherence

{- A top-level definition, with its name, type, and the definition as a string -}
record Other : Set where
  inductive
  constructor other
  field
    name : String
    type : Term
    definition : String
open Other

data Definition : Set where
  Dec : Declaration → Definition
  Coh : Coherence → Definition
  Oth : Other → Definition

record DefinitionsAndTerm : Set where
  inductive
  constructor D&T
  field
    cohs : List Definition
    cohapp : Term
open DefinitionsAndTerm public

record Declaration where
  inductive
  constructor declaration
  field
    name : String
    params : List (String × Term)
    argtype : ArgType
    type : Term
    def-coh : DefinitionsAndTerm
    base-coh : LR → DefinitionsAndTerm
    glue-coh : LR → DefinitionsAndTerm
open Declaration public

pattern App f arg = AppEI f (Exp arg)
pattern AppI f arg = AppEI f (Imp arg)
pattern Pi x A B = PiEI (Exp x) A B
pattern PiI x A B = PiEI (Imp x) A B

pattern BaseL A B = Base L A B
pattern BaseR A B = Base R A B
pattern GlueL A B a = Glue L A B a
pattern GlueR A B b = Glue R A B b


argtype-to-type : ArgType → Term
argtype-to-type / _ - A / = A
argtype-to-type (A [∧] B) = Smash (argtype-to-type A) (argtype-to-type B)

{- Turn an ArgType into an actual variable name (always "x") and its type -}
argtype-to-arg : ArgType → String × Term
argtype-to-arg x = ("x" , argtype-to-type x)

{- Get the argument of a declaration -}
get-arg : Declaration → String × Term
get-arg dec = argtype-to-arg (argtype dec)

{- Get the argument of a declaration, as a variable -}
get-var : Declaration → Term
get-var dec = let (s , t) = get-arg dec in Var s t

{- Various notations to make terms easier to write -}

Aₜ   = Var "A" Type
A'ₜ  = Var "A'" Type
A''ₜ = Var "A''" Type
Bₜ   = Var "B" Type
B'ₜ  = Var "B'" Type
B''ₜ = Var "B''" Type
Cₜ   = Var "C" Type
C'ₜ  = Var "C'" Type
Dₜ   = Var "D" Type

aₜA  = Var "a" Aₜ
bₜB  = Var "b" Bₜ
cₜC  = Var "c" Cₜ
dₜD  = Var "d" Dₜ

fₜA→∙A' = Var "f" (PtdMap Aₜ A'ₜ)
gₜB→∙B' = Var "g" (PtdMap Bₜ B'ₜ)
f'ₜA'→∙A'' = Var "f'" (PtdMap A'ₜ A''ₜ)
g'ₜB'→∙B'' = Var "g'" (PtdMap B'ₜ B''ₜ)

A∧B = / "a" - Aₜ / [∧] / "b" - Bₜ /
[A∧B]∧C = A∧B [∧] / "c" - Cₜ /
[[A∧B]∧C]∧D = [A∧B]∧C [∧] / "d" - Dₜ /
A∧[B∧C] = / "a" - Aₜ / [∧] (/ "b" - Bₜ / [∧] / "c" - Cₜ /)

{------------}
{- Printing -}
{------------}

isCoh : String → Bool
isCoh s with toList s
... | '&' ∷ ' ' ∷ 'a' ∷ 'p' ∷ _ = false
... | '&' ∷ ' ' ∷ _ = true
... | _ = false

{- Parenthesize the argument in the argument is true -}
par : Bool → String → String
par false s = s
par true s = "(" ++ s ++ ")"

is-Pi : Term → Bool
is-Pi (PiEI _ _ _) = true
is-Pi _ = false

generate-body : Declaration → String

{- Print the term
   - parenthesizing it if the first argument is true (unless it’s clearly not needed)
-}
print-term-p : Bool → Term → String

print-term-P : Term → String
print-term-P = print-term-p true

print-term : Term → String
print-term = print-term-p false

{- Print a list of pairs of terms -}
print-list-term-p : Bool → List Term → String
print-list-term-p k [] = par k ""
print-list-term-p k (t ∷ []) = par k (print-term-P t)
print-list-term-p k (t ∷ ts) = par k (print-term-P t ++ " " ++ print-list-term-p false ts)

show-var = false
show-implicit = true
show-idp = false
show-pt = false

_[unless_then_] : {A : Set} → A → Bool → A → A
a [unless true then b ] = b
a [unless false then b ] = a

print-term-p k (Var s t) = s [unless show-var then par k (s ++ " {-" ++ print-term t ++ "-}") ]
print-term-p k (Atom s) = s
print-term-p k (Dec dec args) = par k (name dec ++ " " ++ print-list-term-p false args)
print-term-p k (App t arg) = par k (print-term t ++ " " ++ print-term-P arg)
print-term-p k (AppI t (App (Atom "axiom") _)) = print-term-p k t
print-term-p k (AppI t arg) = print-term-p k t [unless show-implicit then par k (print-term t ++ " {" ++ print-term arg ++ "}") ]
print-term-p k (Proj a b) = par k ("proj " ++ print-term-P a ++ " " ++ print-term-P b)
print-term-p k (BaseL _ _) = "basel"
print-term-p k (BaseR _ _) = "baser"
print-term-p k (GlueL _ _ a) = par k ("gluel " ++ print-term-P a)
print-term-p k (GlueR _ _ b) = par k ("gluer " ++ print-term-P b)
print-term-p k (Id a b) = par k (print-term a ++ " == " ++ print-term b)
print-term-p k (Idp a) = "idp" [unless show-idp then par k ("idp {" ++ print-term a ++ "}") ]
print-term-p k (Square p q r s) = par k ("Square " ++ print-term-P p ++ " " ++ print-term-P q ++ " " ++ print-term-P r ++ " " ++ print-term-P s)
print-term-p k (Ids _) = "ids"
print-term-p k (Cube p q r s t u) = par k ("Cube " ++ print-term-P p ++ " " ++ print-term-P q ++ " " ++ print-term-P r ++ " " ++ print-term-P s ++ " " ++ print-term-P t ++ " " ++ print-term-P u)
print-term-p k (Idc _) = "idc"
print-term-p k (Pt A) = "pt" [unless show-pt then par k ("pt {" ++ A ++ "}") ]
print-term-p k (Ptf f A B) = par k ("ptf " ++ f)
print-term-p k (Lam x A u) = par k ("λ " ++ x ++ " → " ++ print-term u)
print-term-p k (Pi s A B) = if s ==ₛ "_" then par k (print-term A ++ " → " ++ print-term B) else par k ("(" ++ s ++ " : " ++ print-term A ++ (if is-Pi B then ") " else ") → ") ++ print-term B)
print-term-p k (PiI s A B) = par k ("{" ++ s ++ " : " ++ print-term A ++ (if is-Pi B then "} " else "} → ") ++ print-term B)
print-term-p k Ptd = par k "Type i"
print-term-p k Type = par k "Type i"
print-term-p k (PtdMap A B) = par k (print-term-P A ++ " → " ++ print-term-P B)
print-term-p k (Smash A B) = par k (print-term-P A ++ " ∧ " ++ print-term-P B)
print-term-p k (ERROR s) = "{!ERROR (" ++ s ++ ")!}"

{- Print the parameter and its type, with a special treatment for pointed types and functions -}
print-param : String × Term → String
print-param (s , Ptd) = "(" ++ s ++ " : Type i) {{_ : Pointed " ++ s ++ "}}"
print-param (s , PtdMap A B) = "(" ++ s ++ " : " ++ print-term A ++ " → " ++ print-term B ++ ") {{_ : PointedFun " ++ s ++ "}}"
print-param (s , t) = "(" ++ s ++ " : " ++ print-term t ++ ")"

{- Print a list of parameters -}
print-params : List (String × Term) → String
print-params [] = ""
print-params (x ∷ []) = print-param x
print-params (x ∷ xs) = print-param x ++ " " ++ print-params xs

{- Print only the names of parameters -}
print-name-params : List (String × Term) → String
print-name-params [] = ""
print-name-params ((s , t) ∷ []) = s
print-name-params ((s , t) ∷ xs) = s ++ " " ++ print-name-params xs

{- Wrapper for tagging lists of String × Term for which we want to only print
   the names, for the instance arguments machinery -}
data OnlyNames : Set where
  onlyNames : List (String × Term) → OnlyNames

{- Print a list of strings, separated by spaces -}
print-list-strings : List String → String
print-list-strings [] = ""
print-list-strings (s ∷ []) = s
print-list-strings (s ∷ ss) = s ++ " " ++ print-list-strings ss

{- Print a boolean -}
print-bool : Bool → String
print-bool true = "true"
print-bool false = "false"

print-coherence : Coherence → String
print-coherence d = name d ++ " : Coh (" ++ print-term (type d) ++ ")\n" ++ name d ++ " = path-induction"

print-other : Other → String
print-other o = name o ++ " : " ++ print-term (type o) ++ "\n" ++ name o ++ definition o

print-definition : Definition → String
print-definition (Dec d) = generate-body d
print-definition (Coh c) = print-coherence c
print-definition (Oth o) = print-other o

print-list-definition : List Definition → String
print-list-definition [] = ""
print-list-definition (d ∷ []) = print-definition d
print-list-definition (d ∷ ds) = print-definition d ++ "\n\n" ++ print-list-definition ds

print-argtype : ArgType → String
print-argtype (/ _ - A /) = print-term A
print-argtype (A [∧] B) = "[" ++ print-argtype A ++ "∧" ++ print-argtype B ++ "]"

{- Make all of these functions instances, so that we can simply use [print] and [sprintf] -}
instance
  Termₚ : Printable Term
  Termₚ = record { print-p = print-term-p }

  ListTermₚ : Printable (List Term)
  ListTermₚ = record { print-p = print-list-term-p }

  Paramₚ : Printable (String × Term)
  Paramₚ = record { print-p = λ _ → print-param }

  Paramsₚ : Printable (List (String × Term))
  Paramsₚ = record { print-p = λ _ → print-params }

  NameParamsₚ : Printable OnlyNames
  NameParamsₚ = record { print-p = λ _ → λ { (onlyNames l) → print-name-params l } }

  Stringₚ : Printable String
  Stringₚ = record { print-p = λ _ → λ s → s }

  Natₚ : Printable ℕ
  Natₚ = record { print-p = λ _ → showℕ }

  ListStringₚ : Printable (List String)
  ListStringₚ = record { print-p = λ _ → print-list-strings }

  Boolₚ : Printable Bool
  Boolₚ = record { print-p = λ _ → print-bool }

  Definitionₚ : Printable Definition
  Definitionₚ = record { print-p = λ _ → print-definition }

  ListDefinitionₚ : Printable (List Definition)
  ListDefinitionₚ = record { print-p = λ _ → print-list-definition }

  Argtypeₚ : Printable ArgType
  Argtypeₚ = record { print-p = λ _ → print-argtype }

{- For C-u C-u C-c C-n to work as expected -}
show : String → String
show s = s

{- [is-fresh-in s t] is true if the variable [s] does not occur freely in the term [t] -}
is-fresh-in : String → Term → Bool
{- [is-fresh-inx s l] is true if the variable [s] does not occur freely in any of the terms in [l] -}
is-fresh-inx : String → List Term → Bool

is-fresh-in s (Var s' t) = not (s ==ₛ s') ∧ is-fresh-in s t
is-fresh-in s (Atom s') = true
is-fresh-in s (Dec dec args) = is-fresh-inx s args
is-fresh-in s (App t arg) = is-fresh-in s t ∧ is-fresh-in s arg
is-fresh-in s (AppI t arg) = is-fresh-in s t ∧ is-fresh-in s arg
is-fresh-in s (Proj a b) = is-fresh-in s a ∧ is-fresh-in s b
is-fresh-in s (Base lr A B) = is-fresh-in s A ∧ is-fresh-in s B
is-fresh-in s (Glue lr A B ab) = is-fresh-in s A ∧ is-fresh-in s B ∧ is-fresh-in s ab
is-fresh-in s (Id a b) = is-fresh-in s a ∧ is-fresh-in s b
is-fresh-in s (Idp a) = is-fresh-in s a
is-fresh-in s (Square p q r ss) = is-fresh-in s p ∧ is-fresh-in s q ∧ is-fresh-in s r ∧ is-fresh-in s ss
is-fresh-in s (Ids a) = is-fresh-in s a
is-fresh-in s (Cube p q r ss t u) = is-fresh-in s p ∧ is-fresh-in s q ∧ is-fresh-in s r ∧ is-fresh-in s ss ∧ is-fresh-in s t ∧ is-fresh-in s u
is-fresh-in s (Idc a) = is-fresh-in s a
is-fresh-in s (Pt A) = not (s ==ₛ A)
is-fresh-in s (Ptf f A B) = not (s ==ₛ f) ∧ is-fresh-in s A ∧ is-fresh-in s B
is-fresh-in s (Lam s' A t) = is-fresh-in s A ∧ ((s ==ₛ s') ∨ (not (s ==ₛ s') ∧ is-fresh-in s t))
is-fresh-in s (PiEI s' A B)  = is-fresh-in s A ∧ ((s ==ₛ unArg s') ∨ (not (s ==ₛ unArg s') ∧ is-fresh-in s B))
is-fresh-in s Ptd = true
is-fresh-in s Type = true
is-fresh-in s (PtdMap A B) = is-fresh-in s A ∧ is-fresh-in s B
is-fresh-in s (Smash A B) = is-fresh-in s A ∧ is-fresh-in s B
is-fresh-in s (ERROR x) = true

is-fresh-inx s [] = true
is-fresh-inx s (t ∷ ts) = is-fresh-in s t ∧ is-fresh-inx s ts

{- Returns a variable name which does not occur freely in any of the terms.
   The name is based on the second argument. -}
{-# NON_TERMINATING #-}
fresh : List Term → String → String
fresh l var = fresh-aux 0  where

  fresh-aux : ℕ → String
  fresh-aux n =
    let s = var ++ (if n == 0 then "" else showℕ n) in
    if is-fresh-inx s l then s else fresh-aux (suc n)

all-fresh-in : List String → Term → Bool
all-fresh-in [] _ = true
all-fresh-in (s ∷ ss) t = is-fresh-in s t ∧ all-fresh-in ss t

{- More notations for terms -}
pattern Xₜ = Var "X" Type
pattern xₜX = Var "x" Xₜ
pattern yₜX = Var "y" Xₜ
pattern zₜX = Var "z" Xₜ
aₜX = Var "a" Xₜ
bₜX = Var "b" Xₜ
cₜX = Var "c" Xₜ
dₜX = Var "d" Xₜ
a=bₜ = Id aₜX bₜX
b=aₜ = Id bₜX aₜX
a=cₜ = Id aₜX cₜX
b=cₜ = Id bₜX cₜX
c=bₜ = Id cₜX bₜX
a=dₜ = Id aₜX dₜX
d=cₜ = Id dₜX cₜX
c=dₜ = Id cₜX dₜX
b=dₜ = Id bₜX dₜX

get-type : Term → Term

{- Return the dimension of the given type (how many nested Id’s it consists of) -}
{-# NON_TERMINATING #-}
dimension : Term → ℕ
dimension (Id a _) = suc (dimension (get-type a))
dimension (Square p q r s) = suc (dimension (get-type p))
dimension (Cube p q r s t u) = suc (dimension (get-type p))
dimension _ = 0

{- Returns the domain of the given function type -}
get-domain : Term → Term
get-domain (PtdMap A _) = A
get-domain (PiEI _ A _) = A
get-domain t = Error ("get-domain " ++ print t)

{- Returns the domain and the variable of the given function type -}
get-domain-and-var : Term → String × Term
get-domain-and-var (PtdMap A _) = ("_" , A)
get-domain-and-var (PiEI s A _) = (unArg s , A)
get-domain-and-var t = ("error", Error ("get-domain-and-var " ++ print t))

{- Returns the codomain of the given function type -}
get-codomain : Term → Term
get-codomain (PtdMap _ B) = B
get-codomain (PiEI _ _ B) = B
get-codomain t = Error ("get-codomain " ++ print t)

{- Returns the lhs of the given identity type -}
lhs : Term → Term
lhs (Id a b) = a
lhs t = Error ("lhs " ++ print t)

{- Returns the rhs of the given identity type -}
rhs : Term → Term
rhs (Id a b) = b
rhs t = Error ("rhs " ++ print t)

{- Returns the mhs of the given identity type -}
mhs : Term → Term
mhs (Id a _) = get-type a
mhs (Square p q r s) = mhs (get-type p)
mhs (Cube p q r s t u) = mhs (get-type p)
mhs t = Error ("mhs " ++ print t)

first-side : Term → Term
first-side (Square p _ _ _) = p
first-side t = Error ("first-side " ++ print-P t)

second-side : Term → Term
second-side (Square _ q _ _) = q
second-side t = Error ("second-side " ++ print-P t)

third-side : Term → Term
third-side (Square _ _ r _) = r
third-side t = Error ("third-side " ++ print-P t)

fourth-side : Term → Term
fourth-side (Square _ _ _ s) = s
fourth-side t = Error ("fourth-side " ++ print-P t)

{- Returns the base point of a type -}
pt : Term → Term
pt (Smash A B) = Proj (pt A) (pt B)
pt (Var s Type) = Pt s
pt (Var s Ptd) = Pt s
pt t = Error ("pt " ++ print-P t)

ptf : Term → Term
ptf (Var f (PtdMap A B)) = Ptf f A B
ptf (Lam s A (Var s' A')) = if (s ==ₛ s') then Idp (pt A) else Error ("ptfVar " ++ print s ++ " " ++ print s')
ptf (Dec dec args) = Idp (pt (get-codomain (get-type (Dec dec args))))
ptf t = Error ("ptf " ++ print t)


find : String → List String → List Term → Maybe (Term × List String × List Term)
find s [] _ = nothing
find s (v ∷ vs) [] = trerror "find" nothing
find s (v ∷ vs) (t ∷ ts) with s ==ₛ v | find s vs ts
... | true  | _ = just (t , vs , ts)
... | false | nothing = nothing
... | false | just (t' , vs' , ts') = just (t' , v ∷ vs' , t ∷ ts')

{- Substitution -}
_[_/_] : Term → Term → String → Term
{- Simultaneous substitution -}
_[_/[]_] : Term → List Term → List String → Term
{- Apply the first term to the second term, performing β-reduction if needed -}
AppReduce : Term → Term → Term
{- Same for implicit application -}
AppIReduce : Term → Term → Term

u [ t / s ] = u [ [ t ] /[] [ s ] ]

{- Note: in [Lam s A u], [s] should *not* occur in [A], because [Var s A]
         probably occurs in [u] and the [s] will get captured there.
-}
{-# NON_TERMINATING #-}
(Var x u) [ t /[] s ] with find x s t
... | nothing = Var x (u [ t /[] s ])
... | just (k , _ , _) = k
(Atom x) [ t /[] s ] = Atom x
(Dec dec args) [ t /[] s ] = Dec dec (map (_[ t /[] s ]) args)
(App u arg) [ t /[] s ] = AppReduce (u [ t /[] s ]) (arg [ t /[] s ])
(AppI u arg) [ t /[] s ] = AppIReduce (u [ t /[] s ]) (arg [ t /[] s ])
(Proj a b) [ t /[] s ] = Proj (a [ t /[] s ]) (b [ t /[] s ])
(Base lr A B) [ t /[] s ] = Base lr (A [ t /[] s ]) (B [ t /[] s ])
(Glue lr A B ab) [ t /[] s ] = Glue lr (A [ t /[] s ]) (B [ t /[] s ]) (ab [ t /[] s ])
(Id a b) [ t /[] s ] = Id (a [ t /[] s ]) (b [ t /[] s ])
(Idp a) [ t /[] s ] = Idp (a [ t /[] s ])
(Square p q r ss) [ t /[] s ] = Square (p [ t /[] s ]) (q [ t /[] s ]) (r [ t /[] s ]) (ss [ t /[] s ])
(Ids a) [ t /[] s ] = Ids (a [ t /[] s ])
(Cube p q r ss ttt u) [ t /[] s ] = Cube (p [ t /[] s ]) (q [ t /[] s ]) (r [ t /[] s ]) (ss [ t /[] s ]) (ttt [ t /[] s ]) (u [ t /[] s ])
(Idc a) [ t /[] s ] = Idc (a [ t /[] s ])
(Pt x) [ t /[] s ] with find x s t
... | nothing = Pt x
... | just (k , _ , _) = pt k
(Ptf x A B) [ t /[] s ] with find x s t
... | nothing = Ptf x (A [ t /[] s ]) (B [ t /[] s ])
... | just (k , _ , _) = ptf k
(Lam x A u) [ t /[] s ] with find x s t
... | nothing = if all-fresh-in s (Lam x A u) then
                  Lam x A u
                else if is-fresh-inx x t then
                   Lam x (A [ t /[] s ]) (u [ t /[] s ])
                else
                   let x' = fresh (A ∷ (t ++ₗ map (λ k → Var k Type) s)) x in
                   let newA = A [ t /[] s ] in
                   Lam x' newA (u [ Var x' newA ∷ t /[] x ∷ s ])
... | just (k , [] , []) = Lam x A u
... | just (k , vs , ts) = (Lam x A u) [ ts /[] vs ]
(PiEI x A B) [ t /[] s ] with find (unArg x) s t
... | nothing = if all-fresh-in s (PiEI x A B) then
                  PiEI x A B
                else if is-fresh-inx (unArg x) t then
                  PiEI x (A [ t /[] s ]) (B [ t /[] s ])
                else
                  let x' = fresh (A ∷ (t ++ₗ map (λ k → Var k Type) s)) (unArg x) in
                  let newA = A [ t /[] s ] in
                  PiEI (hiding-app x x') newA (B [ Var x' newA ∷ t /[] unArg x ∷ s ])
... | just (_ , [] , []) = PiEI x A B
... | just (k , vs , ts) = (PiEI x A B) [ ts /[] vs ]
Ptd [ t /[] s ] = Ptd
Type [ t /[] s ] = Type
(PtdMap A B) [ t /[] s ] = PtdMap (A [ t /[] s ]) (B [ t /[] s ])
(Smash A B) [ t /[] s ] = Smash (A [ t /[] s ]) (B [ t /[] s ])
(ERROR x) [ t /[] s ] = ERROR x

AppEIReduce : Term → Arg Term → Term
AppEIReduce t (Exp u) = AppReduce t u
AppEIReduce t (Imp u) = AppIReduce t u

Pi[] : List (Arg String × Term) → Term → Term
Pi[] [] u = u
Pi[] ((s , t) ∷ ts) u = PiEI s t (Pi[] ts u)

PiE[] : List (String × Term) → Term → Term
PiE[] [] u = u
PiE[] ((s , t) ∷ ts) u = Pi s t (PiE[] ts u)

get-type-declaration : Declaration → List Term → Term
get-type-declaration dec args =
  (PiE[] [ get-arg dec ] (type dec)) [ args /[] map proj₁ (params dec) ]

{- The first argument is a function type, the second an argument, return the return type -}
app-type : Term → Term → Term
app-type (PiEI x A B) t = B [ t / unArg x ]
app-type (PtdMap A B) t = B
app-type t u = Error ("app-type " ++ print t ++ " to " ++ print u)

{-# NON_TERMINATING #-}
_==ₜ_ : Term → Term → Bool

{- Returns the term corresponding to [ap f p] -}
ap : Term → Term → Term
ap f p =
  if mhs (get-type p) ==ₜ get-domain (get-type f) then
    AppReduce (App (Atom "ap") f) p
  else
    Error ("ap error : " ++ print-P f ++ " " ++ print-P p ++ " / " ++ print-P (mhs (get-type p)) ++ " " ++ print-P (get-type f))

ap□ : Term → Term → Term
ap□ f sq = AppReduce (App (Atom "ap□") f) sq

ap-square : Term → Term → Term
ap-square f sq = AppReduce (App (Atom "ap-square") f) sq

ap-∘ : Term → Term → Term → Term
ap-∘ f g p = AppReduce (App (App (Atom "ap-∘") f) g) p

pattern apᵖ f p = App (App (Atom "ap") f) p
pattern ap□ᵖ k p = App (App (Atom "ap□") k) p
pattern ap-squareᵖ f sq = App (App (Atom "ap-square") f) sq
pattern ap-idf p = App (Atom "ap-idf") p
pattern ap-square-idf sq = App (Atom "ap-square-idf") sq
pattern ap-square-∘ g f sq = App (App (App (Atom "ap-square-∘") g) f) sq
pattern ap-cst a p = App (App (Atom "ap-cst") a) p
pattern ap□-cst q p = App (App (Atom "ap□-cst") q) p
pattern ap-∘ᵖ g f p = App (App (App (Atom "ap-∘") g) f) p
pattern ap-∘-idfl g p = App (App (Atom "ap-∘-idfl") g) p
pattern ap□-∘-eq g f p eq = App (App (App (App (Atom "ap□-∘-eq") g) f) p) eq
pattern ap□-∘-idf g p = App (App (Atom "ap□-∘-idf") g) p
pattern ap□-∘2 f g p = App (App (App (Atom "ap□-∘2") f) g) p
pattern ap-cube f cu = App (App (Atom "ap-cube") f) cu
pattern ap-∘3 f g h p = App (App (App (App (Atom "ap-∘3") f) g) h) p
pattern ap-∘-cst f b p = App (App (App (Atom "ap-∘-cst") f) b) p
pattern ap-∘-cst2 c f p = App (App (App (Atom "ap-∘-cst2") c) f) p
pattern ap-∘3-cst f c h p = App (App (App (App (Atom "ap-∘3-cst") f) c) h) p
pattern ap□-idp f p = App (App (Atom "ap□-idp") f) p
pattern ap□+ f sq = App (App (Atom "ap□+") f) sq
pattern ap□-= α p = App (App (Atom "ap□-=") α) p
pattern ap□-∘3 f g h p = App (App (App (App (Atom "ap□-∘3") f) g) h) p

pattern axiom term type = AppI term (App (Atom "axiom") type)

&coh∙□ = Var "& coh∙□" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (PiI "p" a=bₜ (PiI "q" a=bₜ (Pi "α" (Square (Var "p" a=bₜ) (Var "q" a=bₜ) (Idp aₜX) (Idp bₜX)) (PiI "r" a=bₜ (Pi "β" (Square (Var "q" a=bₜ) (Var "r" a=bₜ) (Idp aₜX) (Idp bₜX)) (Square (Var "p" a=bₜ) (Var "r" a=bₜ) (Idp aₜX) (Idp bₜX))))))))))

&coh!∙□ = Var "& coh!∙□" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (PiI "q" a=bₜ (PiI "p" a=bₜ (Pi "α" (Square (Var "q" a=bₜ) (Var "p" a=bₜ) (Idp aₜX) (Idp bₜX)) (PiI "r" a=bₜ (Pi "β" (Square (Var "q" a=bₜ) (Var "r" a=bₜ) (Idp aₜX) (Idp bₜX)) (Square (Var "p" a=bₜ) (Var "r" a=bₜ) (Idp aₜX) (Idp bₜX))))))))))

&hids = Var "& hids" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (Pi "p" a=bₜ (Square (Var "p" a=bₜ) (Var "p" a=bₜ) (Idp aₜX) (Idp bₜX))))))

&vids = Var "& vids" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (Pi "p" a=bₜ (Square (Idp aₜX) (Idp bₜX) (Var "p" a=bₜ) (Var "p" a=bₜ))))))

&hinv = Var "& hinv" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (PiI "p" a=bₜ (PiI "q" a=bₜ (Pi "sq" (Square (Var "p" a=bₜ) (Var "q" a=bₜ) (Idp aₜX) (Idp bₜX))
                     (Square (Var "q" a=bₜ) (Var "p" a=bₜ) (Idp aₜX) (Idp bₜX))))))))

App[] : Term → List (Arg Term) → Term
App[] t [] = t
App[] t (u ∷ us) = App[] (AppEIReduce t u) us

coh∙□ : Term → Term → Term
coh∙□ α β =
  let p = first-side (get-type α) in
  let q = second-side (get-type α) in
  let r = second-side (get-type β) in
  let X = mhs (get-type p) in
  let a = lhs (get-type p) in
  let b = rhs (get-type p) in
  App[] &coh∙□ (Imp X ∷ Imp a ∷ Imp b ∷ Imp p ∷ Imp q ∷ Exp α ∷ Imp r ∷ Exp β ∷ [])

coh!∙□ : Term → Term → Term
coh!∙□ α β =
  let q = first-side (get-type α) in
  let p = second-side (get-type α) in
  let r = second-side (get-type β) in
  let X = mhs (get-type p) in
  let a = lhs (get-type p) in
  let b = rhs (get-type p) in
  App[] &coh!∙□ (Imp X ∷ Imp a ∷ Imp b ∷ Imp q ∷ Imp p ∷ Exp α ∷ Imp r ∷ Exp β ∷ [])

hids : Term → Term
hids p =
  let X = mhs (get-type p) in
  let a = lhs (get-type p) in
  let b = rhs (get-type p) in
  App[] &hids (Imp X ∷ Imp a ∷ Imp b ∷ Exp p ∷ [])

vids : Term → Term
vids p =
  let X = mhs (get-type p) in
  let a = lhs (get-type p) in
  let b = rhs (get-type p) in
  App[] &vids (Imp X ∷ Imp a ∷ Imp b ∷ Exp p ∷ [])

hinv : Term → Term
hinv sq =
  let p = first-side (get-type sq) in
  let q = second-side (get-type sq) in
  let a = lhs (get-type p) in
  let b = rhs (get-type p) in
  let X = mhs (get-type p) in
  App[] &hinv (Imp X ∷ Imp a ∷ Imp b ∷ Imp p ∷ Imp q ∷ Exp sq ∷ [])

_∘_ : Term → Term → Term
g ∘ f =
  let X = get-domain (get-type f) in
  let x = fresh (f ∷ g ∷ []) "x" in
  Lam x X (AppReduce g (AppReduce f (Var x X)))

is-idf : Term → Bool
is-idf (Lam x X (Var x' _)) = x ==ₛ x'
is-idf _ = false

eta-expand : Term → Term
eta-expand f =
  let X = get-domain (get-type f) in
  let x = fresh [ f ] "x" in
  Lam x X (AppReduce f (Var x X))

eta-contract : Term → Term
eta-contract t@(Lam x X (App f (Var y Y))) =
  if (x ==ₛ y) ∧ (X ==ₜ Y) then
    eta-contract f
  else
    t
eta-contract t = t

apply-path-single : Declaration → List Term → Term → Term

glue-β-name : LR → String
glue-β-name L = ".gluel-β"
glue-β-name R = ".gluer-β"

glue-β : Declaration → List Term → LR → Term → Term → Term → Term
glue-β dec args lr A B ab =
  let cohapp = apply-path-single dec args (Glue lr A B ab) in
  let thing = ap (Dec dec args) (Glue lr A B ab) in
  axiom (App[] (Atom (name dec ++ glue-β-name lr)) (map Exp args ++ₗ [ Exp ab ]))
        (Square thing cohapp (Idp (lhs (get-type cohapp))) (Idp (rhs (get-type cohapp))))

glue-β□ : Declaration → List Term → LR → Term → Term → Term → Term
glue-β□ dec args lr A B ab =
  let cohapp = apply-path-single dec args (Glue lr A B ab) in
  axiom (App[] (Atom (name dec ++ glue-β-name lr)) (map Exp args ++ₗ [ Exp ab ]))
        (Cube (ap□ (Dec dec args) (Glue lr A B ab))
              cohapp
              (hids (first-side (get-type cohapp)))
              (hids (second-side (get-type cohapp)))
              (hids (third-side (get-type cohapp)))
              (hids (fourth-side (get-type cohapp))))

idf : Term → Term
idf A =
  let x = fresh [ A ] "x" in
  Lam x A (Var x A)

{-# NON_TERMINATING #-}
ap* : Term → Term → Term

{- Get the type of a term -}
get-type (Var s t) = t
get-type (Dec dec args) = get-type-declaration dec args
get-type (apᵖ f p) with get-type p
... | Id a b = if get-type a ==ₜ get-domain (get-type f) then Id (AppReduce f a) (AppReduce f b) else Error ("ap error : " ++ print-P f ++ " " ++ print-P p ++ " / " ++ print-P (mhs (get-type p)) ++ " " ++ print-P (get-type f))
... | _ = Error "get-type ap"

get-type (ap-squareᵖ f sq) with get-type sq
... | Square p q r s = Square (ap f p) (ap f q) (ap f r) (ap f s)
... | _ = Error ("get-type ap-square " ++ print sq ++ " / " ++ print (get-type sq))

get-type (ap□ᵖ k p) with get-type k | get-type p
... | Pi x A (Id f g) | Id a b =
  if get-type a ==ₜ A then
    Square (AppReduce k a) (AppReduce k b) (ap (eta-contract (Lam x A f)) p) (ap (eta-contract (Lam x A g)) p)
  else
    Error ("ap□ error " ++ print-P k  ++ " / " ++ print-P p ++ " / " ++ print-P (mhs (get-type p)) ++ " / " ++ print-P (get-domain (get-type k)))
... | _ | _ = Error ("get-type ap□ " ++ print-P k ++ " / " ++ print-P p)

get-type (ap-cst a p) =
  let X = mhs (get-type p) in
  let x = fresh (X ∷ a ∷ []) "x" in
  Square (ap (Lam x X a) p) (Idp a) (Idp a) (Idp a)

get-type (ap□-cst q p) =
  let X = get-type q in
  let x = fresh (mhs (get-type p) ∷ q ∷ []) "x" in
  let b = lhs X in
  let b' = rhs X in
  Cube (ap□ (Lam x (mhs (get-type p)) q) p) (hids q) (hids q) (hids q) (ap-cst b p) (ap-cst b' p)

get-type (ap-idf p) =
  let A = mhs (get-type p) in
  let a = lhs (get-type p) in
  let b = rhs (get-type p) in  
  Square (ap (idf A) p) p (Idp a) (Idp b)

get-type (ap-∘-idfl g p) =
  let A = mhs (get-type p) in
  let B = get-codomain (get-type g) in
  let a = lhs (get-type p) in
  let a' = rhs (get-type p) in
  Cube (ap-∘ (idf B) g p) (hids (ap g p)) (hids (ap g p)) (ap-idf (ap g p)) (Ids (AppReduce g a)) (Ids (AppReduce g a'))

get-type (ap-square-idf sq) with get-type sq
... | Square p q r s =
  let A = mhs (get-type p) in
  Cube (ap-square (idf A) sq) sq (ap-idf p) (ap-idf q) (ap-idf r) (ap-idf s)
... | _ = Error "get-type of ap-square-idf"

get-type (ap-square-∘ g f sq) with get-type sq
... | Square p q r s =
  Cube (ap-square (g ∘ f) sq) (ap-square g (ap-square f sq)) (ap-∘ g f p) (ap-∘ g f q) (ap-∘ g f r) (ap-∘ g f s)
... | _ = Error "get-type of ap-square-∘"

get-type (ap-∘ᵖ g f p) =
  let a = lhs (get-type p) in
  let b = rhs (get-type p) in
  Square (ap (g ∘ f) p) (ap g (ap f p)) (Idp (AppReduce g (AppReduce f a))) (Idp (AppReduce g (AppReduce f b)))

get-type (ap-∘3 f g h p) =
  let fgha = AppReduce f (AppReduce g (AppReduce h (lhs (get-type p)))) in
  let fghb = AppReduce f (AppReduce g (AppReduce h (rhs (get-type p)))) in
  Cube (ap-∘ (f ∘ g) h p) (ap-square f (ap-∘ g h p)) (ap-∘ f (g ∘ h) p) (ap-∘ f g (ap h p)) (Ids fgha) (Ids fghb)


get-type (ap□-∘-eq (Lam var Z g) f p (Lam v2 T eq)) =
  let a = eta-contract (Lam var Z (lhs (get-type g))) in
  let b = eta-contract (Lam var Z (rhs (get-type g))) in
  let y = lhs (get-type p) in
  let z = rhs (get-type p) in
  let res = eta-contract (Lam v2 T (second-side (get-type eq))) in
  Cube (ap□ res p)
       (ap-square f (ap□ (eta-contract (Lam var Z g)) p))
       (hinv (eq [ y / v2 ]))
       (hinv (eq [ z / v2 ]))
       (ap-∘ f a p)
       (ap-∘ f b p)

get-type (ap□-∘-idf (Lam var Z g) p) =
  let a = eta-contract (Lam var Z (lhs (get-type g))) in
  let b = eta-contract (Lam var Z (rhs (get-type g))) in
  let y = lhs (get-type p) in
  let z = rhs (get-type p) in
  Cube (ap□ (eta-contract (Lam var Z (ap (idf (mhs (get-type g))) g))) p)
       (ap□ (eta-contract (Lam var Z g)) p)
       (ap-idf (g [ y / var ]))
       (ap-idf (g [ z / var ]))
       (hids (ap a p))
       (hids (ap b p))

get-type (ap□-∘2 f@(Lam var Z f-inner) g p) =
  let y = lhs (get-type p) in
  let z = rhs (get-type p) in
  let a = eta-contract (Lam var Z (lhs (get-type f-inner))) in
  let b = eta-contract (Lam var Z (rhs (get-type f-inner))) in
  Cube (ap□ (f ∘ g) p) (ap□ f (ap g p)) (hids (AppReduce f (AppReduce g y))) (hids (AppReduce f (AppReduce g z))) (ap-∘ a g p) (ap-∘ b g p)

get-type (ap-cube f cu) with get-type cu
... | Cube p q r s t u = Cube (ap-square f p) (ap-square f q) (ap-square f r) (ap-square f s) (ap-square f t) (ap-square f u)
... | _ = Error "get-type ap-cube"

get-type (ap-∘-cst f b p) =
  let X = mhs (get-type p) in
  let x = fresh (X ∷ b ∷ []) "x" in
  let fb = AppReduce f b in
  Cube (ap-cst fb p) (ap-square f (ap-cst b p)) (ap-∘ f (Lam x X b) p) (Ids fb) (Ids fb) (Ids fb)

get-type (ap-∘-cst2 c f p) =
  let X = get-codomain (get-type f) in
  let x = fresh (X ∷ c ∷ []) "x" in
  Cube (ap-∘ (Lam x X c) f p) (Ids c) (ap-cst c p) (ap-cst c (ap f p)) (Ids c) (Ids c)

get-type (ap-∘3-cst f c h p) =
  let fc = AppReduce f c in
  let A = get-domain (get-type h) in
  let B = get-codomain (get-type h) in
  let x = fresh (A ∷ B ∷ f ∷ c ∷ []) "x" in
  Cube (ap-square f (ap-∘ (Lam x B c) h p)) (ap-square f (ap-cst c p)) (hids (ap f (ap (Lam x A c) p))) (ap-square f (ap-cst c (ap h p))) (Ids fc) (Ids fc)

get-type (ap□-idp f@(Lam var T f-in) p) =
  let x = lhs (get-type p) in
  let y = rhs (get-type p) in
  let X = mhs (get-type p) in
  Cube (ap□ (Lam var T (Idp f-in)) p) (vids (ap f p)) (Ids (AppReduce f x)) (Ids (AppReduce f y)) (hids (ap f p)) (hids (ap f p))

get-type (ap□+ α@(Lam x X α-in) sq) =
  let p = first-side (get-type sq) in
  let q = second-side (get-type sq) in
  let r = third-side (get-type sq) in
  let s = fourth-side (get-type sq) in
  let f = eta-contract (Lam x X (lhs (get-type α-in))) in
  let g = eta-contract (Lam x X (rhs (get-type α-in))) in
  Cube (ap□ α p) (ap□ α q) (ap□ α r) (ap□ α s) (ap-square f sq) (ap-square g sq)

get-type t@(ap□-= α p) with get-type α | get-type p
... | Pi x X (Square f g (Idp _) (Idp _)) | Id y z =
  Cube (ap□ (eta-contract (Lam x X f)) p) (ap□ (Lam x X g) p) (AppReduce α y) (AppReduce α z) (hids (ap (Lam x X (lhs (get-type f))) p)) (hids (ap (Lam x X (rhs (get-type f))) p))
... | _ | _ = Error ("get-type ap□-= " ++ print t)

get-type t@(ap□-∘3 f g h p) with get-type g | get-type p
... | Pi x A (Id a b) | Id y z =
  let X = get-domain (get-type h) in
  let v = fresh (f ∷ g ∷ h ∷ []) "x" in
  Cube (ap□ (Lam v X (ap f (AppReduce g (AppReduce h (Var v X))))) p)
       (ap□ (Lam v A (ap f (AppReduce g (Var v A)))) (ap (eta-contract h) p))
       (hids (ap f (AppReduce g (AppReduce h y))))
       (hids (ap f (AppReduce g (AppReduce h z))))
       (ap-∘ (f ∘ (eta-contract (Lam x A a))) h p)
       (ap-∘ (f ∘ (eta-contract (Lam x A b))) h p)
... | _ | _ = Error ("get-type ap□-∘3 " ++ print t)

get-type (axiom term type) = type

get-type (Atom s) = Error ("get-type of atom (" ++ s ++ ")")
get-type (AppEI t arg) = app-type (get-type t) (unArg arg)
get-type (Proj a b) = Smash (get-type a) (get-type b)
get-type (Base lr A B) = Smash A B
get-type (GlueL A B a) = Id (Proj a (pt B)) (BaseL A B)
get-type (GlueR A B b) = Id (Proj (pt A) b) (BaseR A B)
get-type (Id a b) = Type
get-type (Idp a) = Id a a
get-type (Square p q r s) = Type
get-type (Ids a) = Square (Idp a) (Idp a) (Idp a) (Idp a)
get-type (Cube p q r s t u) = Type
get-type (Idc a) = Cube (Ids a) (Ids a) (Ids a) (Ids a) (Ids a) (Ids a)
get-type (Pt s) = Var s Type
get-type (Ptf f A B) = Id (AppReduce (Var f (PtdMap A B)) (pt A)) (pt B)
get-type Ptd = Type
get-type Type = Type
get-type (PtdMap A B) = Type
get-type (Smash A B) = Type
get-type (Lam s A u) = Pi s A (get-type u)
get-type (ERROR s) = Error ("get-type " ++ s)
get-type (PiEI _ _ _) = Type


{- α-equivalence -}
Var s t ==ₜ Var s' t' = (s ==ₛ s') -- ∧ (t ==ₜ t')
Atom s ==ₜ Atom s' = (s ==ₛ s')
Dec dec args ==ₜ Dec dec' args' = (name dec ==ₛ name dec') ∧ (and (zipWith (_==ₜ_) args args'))
AppEI t arg ==ₜ AppEI t' arg' = t ==ₜ t' ∧ unArg arg ==ₜ unArg arg'
Proj a b ==ₜ Proj a' b' = a ==ₜ a' ∧ b ==ₜ b'
BaseL A B ==ₜ BaseL A' B' = A ==ₜ A' ∧ B ==ₜ B'
BaseR A B ==ₜ BaseR A' B' = A ==ₜ A' ∧ B ==ₜ B'
GlueL A B a ==ₜ GlueL A' B' a' = A ==ₜ A' ∧ B ==ₜ B' ∧ a ==ₜ a'
GlueR A B b ==ₜ GlueR A' B' b' = A ==ₜ A' ∧ B ==ₜ B' ∧ b ==ₜ b'
Id t u ==ₜ Id t' u' = t ==ₜ t' ∧ u ==ₜ u'
Idp a ==ₜ Idp a' = (a ==ₜ a')
Square p q r s ==ₜ Square p' q' r' s' = (p ==ₜ p') ∧ (q ==ₜ q') ∧ (r ==ₜ r') ∧ (s ==ₜ s')
Ids a ==ₜ Ids a' = (a ==ₜ a')
Cube p q r s t u ==ₜ Cube p' q' r' s' t' u' = (p ==ₜ p') ∧ (q ==ₜ q') ∧ (r ==ₜ r') ∧ (s ==ₜ s') ∧ (t ==ₜ t') ∧ (u ==ₜ u')
Idc a ==ₜ Idc a' = (a ==ₜ a')
Pt s ==ₜ Pt s' = s ==ₛ s'
Ptf f A B ==ₜ Ptf f' A' B' = (f ==ₛ f') ∧ (A ==ₜ A') ∧ (B ==ₜ B')
Lam s A t ==ₜ Lam s' A' t' =
  if s ==ₛ s' then (A ==ₜ A') ∧ (t ==ₜ t')
  else (A ==ₜ A') ∧ (let s'' = fresh [ A ] s in
                         (t [ Var s'' A / s ]) ==ₜ (t' [ Var s'' A / s' ]))
Lam x X (App (Dec dec args) (Var y Y)) ==ₜ Dec dec' args' = (x ==ₛ y) ∧ (X ==ₜ Y) ∧ (Dec dec args ==ₜ Dec dec' args')
Dec dec' args' ==ₜ Lam x X (App (Dec dec args) (Var y Y)) = (x ==ₛ y) ∧ (X ==ₜ Y) ∧ (Dec dec args ==ₜ Dec dec' args')
-- TODO: implicit Pi and explicit Pi are considered equal
PiEI s A B ==ₜ PiEI s' A' B' = 
  if unArg s ==ₛ unArg s' then (A ==ₜ A') ∧ (B ==ₜ B')
  else (A ==ₜ A') ∧ (let s'' = fresh [ A ] (unArg s) in
                         (B [ Var s'' A / unArg s ]) ==ₜ (B' [ Var s'' A / unArg s' ]))
Ptd ==ₜ Ptd = true
Ptd ==ₜ Type = true
Type ==ₜ Ptd = true
Type ==ₜ Type = true
PtdMap A B ==ₜ PtdMap A' B' = A ==ₜ A' ∧ B ==ₜ B'
PtdMap A B ==ₜ Pi _ A' B' = A ==ₜ A' ∧ B ==ₜ B'
Pi _ A B ==ₜ PtdMap A' B' = A ==ₜ A' ∧ B ==ₜ B'
Smash A B ==ₜ Smash A' B' = A ==ₜ A' ∧ B ==ₜ B'
_ ==ₜ _ = false





record Unapp : Set where
  constructor Appp
  field
    coh : String
    ty : Term
    args : List (Arg Term)

unapp : Term → Unapp
unapp t = unapp-aux t []  where

  unapp-aux : Term → List (Arg Term) → Unapp
  unapp-aux (Var s t) l = Appp s t l
  unapp-aux (Atom s) l = Appp s (Error "type of atom") l
  unapp-aux (AppEI f arg) l = unapp-aux f (arg ∷ l)
  unapp-aux _ l = trerror ("Error unapp " ++ print t) (Appp "error unapp" (Error "unapp") [])

recoh : String → Term → List (Arg Term) → Term
recoh s t l = App[] (Var s t) l

unPi : Term → List (Arg String × Term) × Term
unPi s = unPi-aux s []  where
  unPi-aux : Term → List (Arg String × Term) → List (Arg String × Term) × Term
  unPi-aux (PiEI s A B) l = unPi-aux B ((s , A) ∷ l)
  unPi-aux t l = (reverse l , t)

tail : {A : Set} → List A → List A
tail [] = []
tail (t ∷ ts) = ts

{-# NON_TERMINATING #-}
get-root-type : Term → Term
get-root-type (Id a b) = get-root-type (get-type a)
get-root-type (Square p q r s) = get-root-type (get-type p)
get-root-type (Cube p q r s t u) = get-root-type (get-type p)
get-root-type t = t

{- Given a function [f] and an element [u] in one of the iterated identity
   types of the domain of [f], returns the iterated ap of [f] applied to [u].
-}
ap* f u =
  let A = get-domain (get-type f) in
  let T = get-type u in
  if u ==ₜ A then -- Special case, so that we can simply map ap* on the arguments of a coherence
    get-codomain (get-type f)
  else if not (get-root-type T ==ₜ A) then
    Error ("ap* " ++ print (get-root-type T) ++ " different from " ++ print A ++ "[" ++ print f ++ " / " ++ print u ++ " / " ++ print (get-type u) ++ "]")
  else if T ==ₜ A then
    AppReduce f u
  else
    let z = fresh (f ∷ mhs T ∷ []) "z" in
    ap*-internal z T

  where
    ap*-internal : String → Term → Term
    ap*-internal z T@(Id v w) =
      ap        (Lam z (mhs T) (ap* f (Var z (mhs T)))) u
    ap*-internal z T@(Square p q r s) =
      ap-square (Lam z (mhs T) (ap* f (Var z (mhs T)))) u
    ap*-internal z T@(Cube p q r s t _) =
      ap-cube   (Lam z (mhs T) (ap* f (Var z (mhs T)))) u
    ap*-internal z _ = Error "ap*-internal"

ap*Arg : Term → Arg Term → Arg Term
ap*Arg f (Exp u) = Exp (ap* f u)
ap*Arg f (Imp u) = Imp (ap* f u)

vars : List (Arg String × Term) → List (Arg Term)
vars = map (λ {(s , t) → hiding-app s (Var (unArg s) t)})


Yₜ = Var "Y" Type
X→Yₜ = Pi "_" Xₜ Yₜ
fₜX→Y = Var "f" X→Yₜ

apcohify : String → Term → List (Arg Term) → Term → Term
ap/cohify : String → Term → Term → String → Term → List (Arg Term) → Term
ap□cohify : String → Term → List (Arg Term) → Term → Term

is-pt : Term → Bool
is-pt t with get-type t
... | Smash A B = (t ==ₜ pt (get-type t))
... | Var s _ = (t ==ₜ pt (get-type t))
... | _ = false

is-in-ctx : List (Term × Term) → Term → Bool
is-in-ctx [] t = is-pt t
is-in-ctx ((u , v) ∷ ts) t = (t ==ₜ u) ∨ (t ==ₜ v) ∨ (t ==ₜ Idp u) ∨ (t ==ₜ Idp v) ∨ is-in-ctx ts t



data Split : Set where
  Idf : Split
  Cst : Term → Split
  Projpt : LR → Term → Term → Split
  Proj : LR → Term → Term → Term → Split
  SingleDec : Declaration → List Term → Split
  InnerDec : Declaration → List Term → Term → Split

  SCoh : String → Term → String → Term → List (Arg Term) → Split
  SIdp : String → Term → Term → Split

  SomethingElse : Term → Split

ErrorS : String → Split
ErrorS s = trerror s (SomethingElse (Error s))

{- [split f] returns either
  - [Idf] if [f] is the identity function
  - [Cst k] if [f] is the constant function at [k]
  - [Proj lr A B ab] if [f] is [Lam x X (Proj u v)] with either [u] or [v] being [Var x X] and the other being [ab]
  - [SingleDec dec args] if [f] is [Dec dec args]
  - [InnerDec dec args g] if [f] is [g ∘ Dec dec args]
-}

TT : Declaration → List Term → Term
TT dec args = get-codomain (get-type (Dec dec args))

split : Term → Split
split (Dec dec args) = SingleDec dec args
split (Lam x X (Var y Y)) =
  if x ==ₛ y then
    Idf
  else
    Cst (Var y Y)
split t@(Lam x X (Proj u v)) with split (Lam x X u) | split (Lam x X v)
... | Cst _ | Cst _ = Cst (Proj u v)
... | Idf | Cst _ = if is-pt v then Projpt L (get-type u) (get-type v) else Proj L (get-type u) (get-type v) v
... | Cst _ | Idf = if is-pt u then Projpt R (get-type u) (get-type v) else Proj R (get-type u) (get-type v) u
... | SingleDec dec args | Cst _ = InnerDec dec args (Lam x (TT dec args) (Proj (Var x (TT dec args)) v))
... | Cst _ | SingleDec dec args = InnerDec dec args (Lam x (TT dec args) (Proj u (Var x (TT dec args))))
... | InnerDec dec args g | Cst _ = InnerDec dec args (Lam x (TT dec args) (Proj (AppReduce g (Var x (TT dec args))) v))
... | Cst _ | InnerDec dec args g = InnerDec dec args (Lam x (TT dec args) (Proj u (AppReduce g (Var x (TT dec args)))))
... | _ | _ = ErrorS ("split proj " ++ print t)
split t@(Lam x X (App f@(Dec _ _) arg)) with f | split (Lam x X arg)
... | _ | Cst k = Cst (AppReduce f k)
... | Dec dec args | Idf = SingleDec dec args
... | _ | SingleDec dec args = InnerDec dec args (Lam x (TT dec args) (AppReduce f (Var x (TT dec args))))
... | _ | InnerDec dec args g = InnerDec dec args (Lam x (TT dec args) (AppReduce f (AppReduce g (Var x (TT dec args)))))
... | _ | _ = ErrorS ("split App " ++ print t)
-- split t@(Lam x X (Idp u)) with split (Lam x X u)
-- ... | Idf = ErrorS ("split idp idf")
-- ... | Cst _ = Cst (Idp u)
-- ... | SingleDec dec args = InnerDec dec args (Lam x (TT dec args) (Idp (Var x (TT dec args))))
-- ... | InnerDec dec args g = InnerDec dec args (Lam x (TT dec args) (Idp (AppReduce g (Var x (TT dec args)))))
-- ... | _ = ErrorS ("split idp other " ++ print t)
-- split t@(Lam x X (Glue lr A B u)) with split (Lam x X u)
-- ... | Idf = ErrorS ("split glue idf")
-- ... | Cst _ = Cst (Glue lr A B u)
-- ... | SingleDec dec args = InnerDec dec args (Lam x (TT dec args) (Glue lr A B (Var x (TT dec args))))
-- ... | InnerDec dec args g = InnerDec dec args (Lam x (TT dec args) (Glue lr A B (AppReduce g (Var x (TT dec args)))))
-- ... | _ = ErrorS ("split glue other " ++ print t)
split t@(Lam x X (Glue lr A B u)) with split (Lam x X u)
... | Cst k = Cst (Glue lr A B k)
... | SingleDec dec args = InnerDec dec args (Lam x (choose lr A B) (Glue lr A B (Var x (choose lr A B))))
... | _ =  SomethingElse t
split (Lam x X (Idp u)) =
  SIdp x X u
split t@(Lam x X u) =
  if is-fresh-in x u then
    Cst u
  else (
    let Appp s ty args = unapp u in
    if isCoh s then
      SCoh x X s ty args
    else
      SomethingElse t)
split t = SomethingElse t


trim& : String → String
trim& l = fromList (tail (tail (toList l)))

find-Id-proj-pt : Term → Term → List (Term × Term) → Term
find-Id-proj-pt t f [] = Error ("find-Id-proj-pt " ++ print-P t)
find-Id-proj-pt t f ((t' , apᵖ f' q) ∷ ts) =
  if (t ==ₜ t') ∧ (f ==ₜ f') then
    q
  else
    find-Id-proj-pt t f ts
find-Id-proj-pt t f (_ ∷ ts) = find-Id-proj-pt t f ts

extend-CC : List (Term × Term) → Term → List (Term × Term)
extend-CC-aux : List (Term × Term) → Term → List (Term × Term)
get-CC :  Term → List (Term × Term)

extendx-CC : List (Term × Term) → List Term → List (Term × Term)
extendx-CC ctx [] = ctx
extendx-CC ctx (t ∷ ts) = extendx-CC (extend-CC ctx t) ts

extendx-CC-filter : List Term → Term → List (Term × Term) → List (Term × Term)
extendx-CC-filter [] u ctx = ctx
extendx-CC-filter (t ∷ ts) u ctx = extendx-CC-filter ts u (if t ==ₜ u then ctx else extend-CC ctx t)

test-or-concat : Term → Term → List (Term × Term) → List (Term × Term)
test-or-concat t u ctx =
  if is-in-ctx ctx t then
    trerror ("DUPLICATE " ++ print-P t) (extend-CC ctx u)
  else if is-in-ctx ctx u then
    trerror ("DUPLICATE2 " ++ print-P t ++ " / " ++ print-P u) ctx
  else
    (t , u) ∷ ctx

{- [extend-CC-with cA cB t u ctx] is similar to [(t , u) ∷ ctx], except that it also extends [ctx]
   for all sides of [u] which are not [t].
-}
{-# NON_TERMINATING #-}
extend-CC-with : Term → Term → List (Term × Term) → List (Term × Term)
extend-CC-with t u ctx with get-type u
... | Id a b = test-or-concat t u (extendx-CC-filter (a ∷ b ∷ []) t ctx)
... | Square p q r s = test-or-concat t u (extendx-CC-filter (p ∷ q ∷ r ∷ s ∷ []) t ctx)
... | Cube p q r s ttt uu = test-or-concat t u (extendx-CC-filter (p ∷ q ∷ r ∷ s ∷ ttt ∷ uu ∷ []) t ctx)
... | _ = trerror ("extend-CC-with " ++ print-P u) ctx

ap-CC : Term → List (Term × Term) → List (Term × Term) → List (Term × Term)
ap-CC f [] ctx = ctx
ap-CC f ((t , u) ∷ ts) ctx = extend-CC-with (ap* f t) (ap* f u) (ap-CC f ts ctx)

try-extend-CC-with : Term → List (Term × Term) → List (Term × Term) → List (Term × Term)
try-extend-CC-with t ctx [] = trerror ("Couldn’t find a way to add " ++ print-P t) ctx
try-extend-CC-with t₀ ctx ((t , u) ∷ tus) = if is-in-ctx ctx t then try-extend-CC-with t₀ ctx tus else extend-CC-with t u ctx

root-type : Term → Term
root-type (Id a b) = root-type a
root-type (Square p q r s) = root-type p
root-type (Cube p q r s t u) = root-type p
root-type t with get-type t
... | Id a b = root-type a
... | Square p q r s = root-type p
... | Cube p q r s ttt u = root-type p
... | _ = get-type t

add-sides : List (Term × Term) → Term → List (Term × Term)
add-sides ctx t with get-type t
... | Id a b = extendx-CC ctx (a ∷ b ∷ [])
... | Square p q r s = extendx-CC ctx (p ∷ q ∷ r ∷ s ∷ [])
... | Cube p q r s ttt u = extendx-CC ctx (p ∷ q ∷ r ∷ s ∷ ttt ∷ u ∷ [])
... | _ = ctx

extend-CC ctx t =
  if is-in-ctx ctx t then
    ctx
  else (
    let newctx = add-sides ctx t in
    if is-in-ctx newctx t then
      newctx
    else
      {- trace ("plum " ++ print-P t) -} (extend-CC-aux newctx t))

glue : Term → Term → LR → Term
glue A B lr = let xy = fresh (A ∷ B ∷ []) (choose lr "x" "y") in Lam xy (choose lr A B) (Glue lr A B (choose lr (Var xy A) (Var xy B)))

looks-trivial : Term → Bool
looks-trivial (Base _ _ _) = true
looks-trivial (Proj u v) = (looks-trivial u) ∨ (looks-trivial v)
looks-trivial (App f arg) = looks-trivial arg
looks-trivial t = is-pt t

{- Invariants:
   - The term we are adding is not already present
   - All of its sides are already present
-}
{-# NON_TERMINATING #-}
extend-CC-aux ctx (Id a b) = extendx-CC ctx (a ∷ b ∷ [])
extend-CC-aux ctx (Square p q r s) = extendx-CC ctx (p ∷ q ∷ r ∷ s ∷ [])
extend-CC-aux ctx (Cube p q r s ttt u) = extendx-CC ctx (p ∷ q ∷ r ∷ s ∷ ttt ∷ u ∷ [])
extend-CC-aux ctx (Idp a) = extend-CC ctx a
extend-CC-aux ctx (Ids a) = extend-CC ctx a
extend-CC-aux ctx (Idc a) = extend-CC ctx a

extend-CC-aux ctx (Base lr A B) = extend-CC-with (Base lr A B) (Glue lr A B (choose lr (pt A) (pt B))) ctx
extend-CC-aux ctx t@(Glue lr A B ab) =
    let xy = fresh (A ∷ B ∷ []) (choose lr "x" "y") in
    let pq = choose lr (find-Id-proj-pt (Proj ab (pt B)) (Lam xy A (Proj (Var xy A) (pt B))) ctx)
                       (find-Id-proj-pt (Proj (pt A) ab) (Lam xy B (Proj (pt A) (Var xy B))) ctx)
    in
    extend-CC-with (Glue lr A B ab) (ap□ (glue A B lr) pq) ctx

extend-CC-aux ctx (Proj a b) =
  if is-pt a then
    extend-CC-with (Proj a b) (GlueR (get-type a) (get-type b) b) ctx
  else if is-pt b then
    extend-CC-with (Proj a b) (GlueL (get-type a) (get-type b) a) ctx
  else if looks-trivial a then (
    let lA = get-CC a in
    let A = get-type a in
    let B = get-type b in
    let x = fresh (A ∷ b ∷ []) "x" in -- TODO?
    ap-CC (Lam x A (Proj (Var x A) b)) lA (extend-CC ctx (GlueR A B b)))
  else if looks-trivial b then (
    let lB = get-CC b in
    let A = get-type a in
    let B = get-type b in
    let y = fresh (B ∷ a ∷ []) "y" in -- TODO?
    ap-CC (Lam y B (Proj a (Var y B))) lB (extend-CC ctx (GlueL A B a)))
  else trerror ("BIG ERROR extend-CC (" ++ print a ++ " / " ++ print b ++ ")") ctx

extend-CC-aux ctx t@(apᵖ f p) with split f | p

... | Idf | Glue _ _ _ _ =
  extend-CC-with (ap f p) (ap-idf p) ctx

... | Cst k | Glue _ _ _ _ =
  extend-CC-with (ap f p) (ap-cst k p) ctx

... | Projpt lr A B | Glue _ _ _ _ =
  extend-CC-with (ap f p) (ap□ (glue A B lr) p) ctx

... | SingleDec dec args | Glue lr A B ab =
  extend-CC-with (ap f p) (glue-β dec args lr A B ab) ctx

... | InnerDec dec args g | Glue _ _ _ _ =
  extend-CC-with (ap f p) (ap-∘ g (Dec dec args) p) ctx

... | _ | apᵖ g q with split g | q

...   | SingleDec dec args | Glue lr A B ab =
  extend-CC-with (ap f p) (ap-square f (glue-β dec args lr A B ab)) ctx

...   | Cst k | Glue _ _ _ _ =
  extend-CC-with (ap f p) (ap-square f (ap-cst k q)) ctx

...   | _ | _ =
  extend-CC-with (ap f p) (ap-∘ f g q) ctx

extend-CC-aux ctx t@(apᵖ f p) | _ | _ =
  let Appp s ty args = unapp p in
  if isCoh s then
    extend-CC-with (ap f p) (apcohify s ty args f) ctx
  else
    trerror ("extend-CC 0 " ++ print (ap f p)) ctx

extend-CC-aux ctx t@(ap□ᵖ h@(Lam x X (apᵖ f p)) (apᵖ g q)) with split g | q

... | SingleDec dec args | Glue lr A B u =
  extend-CC-with t (ap□+ h (glue-β dec args lr A B u)) ctx

... | _ | _ =
  trerror ("TODO Y " ++ print t) ctx

extend-CC-aux ctx t@(ap□ᵖ (Lam x X (apᵖ f p)) q) with split f | p

... | Idf | Glue _ _ _ _ =
  extend-CC-with t (ap□-= (Lam x X (ap-idf p)) q) ctx

... | Cst k | Glue _ _ _ _ =
  extend-CC-with t (ap□-= (Lam x X (ap-cst k p)) q) ctx

... | SingleDec dec args | Glue lr A B ab =
  extend-CC-with t (ap□-= (Lam x X (glue-β dec args lr A B ab)) q) ctx

... | InnerDec dec args g | Glue _ _ _ _ =
  extend-CC-with t (ap□-= (Lam x X (ap-∘ g (Dec dec args) p)) q) ctx

... | _ | apᵖ g r with split g | r

...   | SingleDec dec args | Glue lr A B ab =
  extend-CC-with t (ap□-= (Lam x X (ap-square f (glue-β dec args lr A B ab))) q) ctx

...   | Cst k | Glue _ _ _ _ =
  extend-CC-with t (ap□-= (Lam x X (ap-cst k r)) q) ctx

...   | _ | _ =
  extend-CC-with t (ap□-= (Lam x X (ap-∘ f g r)) q) ctx

extend-CC-aux ctx t@(ap□ᵖ h@(Lam x X (apᵖ f p)) q) | _ | _ with split (Lam x X p) | q

...   | Cst k | Glue _ _ _ _ =
  extend-CC-with t (ap□-cst (ap f p) q) ctx

...   | SingleDec dec args | Glue _ _ _ _ =
  extend-CC-with t (ap□-∘-eq (eta-expand (Dec dec args)) f q (Lam x X (hids (ap f p)))) ctx

...   | InnerDec dec args rest | Glue _ _ _ _ =
  extend-CC-with t (ap□-∘3 f rest (Dec dec args) q) ctx

...   | SCoh _ _ s ty args | Glue _ _ _ _ =
  extend-CC-with t (ap□-= (Lam x X (apcohify s ty args f)) q) ctx

...   | _ | _ =
  let Appp s ty args = unapp q in
  if isCoh s then
    extend-CC-with t (ap□cohify s ty args h) ctx
  else
    trerror ("extend-CC 00 " ++ print t) ctx

extend-CC-aux ctx t@(ap□ᵖ f p) with split f | p
... | Cst k | Glue _ _ _ _ =
  extend-CC-with (ap□ f p) (ap□-cst k p) ctx

... | SingleDec dec args | Glue lr A B u =
  extend-CC-with (ap□ f p) (glue-β□ dec args lr A B u) ctx

... | InnerDec dec args rest | Glue _ _ _ _ =
  extend-CC-with t (ap□-∘2 rest (eta-expand (Dec dec args)) p) ctx

... | SCoh x X s ty args | _ =
  extend-CC-with (ap□ f p) (ap/cohify s ty p x X args) ctx

... | SIdp x X u | _ =
  extend-CC-with (ap□ f p) (ap□-idp (Lam x X u) p) ctx

... | _ | apᵖ (Dec dec args) (Glue lr A B u) =
  extend-CC-with t (ap□+ f (glue-β dec args lr A B u)) ctx

... | _ | apᵖ (Lam _ _ (App (Dec dec args) (Var _ _))) (Glue lr A B u) =
  extend-CC-with t (ap□+ f (glue-β dec args lr A B u)) ctx

... | _ | _ =
  let Appp s ty args = unapp p in
  if isCoh s then
    extend-CC-with t (ap□cohify s ty args f) ctx
  else
    trerror ("extend-CC 6 " ++ print t) ctx

extend-CC-aux ctx t@(ap-∘ᵖ f g p) with split f | split g
-- -- ... | Idf | _ =
-- --        extend-CC-with (ap-∘ f g p) (ap-∘-idfl g p) ctx

... | _ | Cst b =
       extend-CC-with (ap-∘ f g p) (ap-∘-cst f b p) ctx

-- ... | Cst a | _ =
--        extend-CC-with (ap-∘ f g p) (ap-∘-cst2 a g p) ctx

-- -- {- Debatable -}
-- -- ... | _ | apᵖ h q =
-- --   extend-CC-with (ap-∘ f g p) (ap-∘3 f g h q) ctx

... | _ | _ =
  trerror ("extend-CC 23 " ++ print t) ctx

-- -- extend-CC-aux ctx t@(ap-squareᵖ f (ap□ g@(Lam x X (apᵖ h q)) p@(Glue lr _ _ _))) =
-- --   extend-CC-with t (ap-cube f (ap□-∘-eq (Lam x X q) h p (Lam x X (hids (ap h q))))) ctx

-- {- Debatable -}
-- extend-CC-aux ctx (ap-cst k (apᵖ f p)) =
  

extend-CC-aux ctx t@(ap-squareᵖ f (ap-∘ᵖ g h p)) with split g | split h

... | _ | Cst b =
  extend-CC-with t (ap-cube f (ap-∘-cst g b p)) ctx

... | Cst a | _ =
  extend-CC-with t (ap-cube f (ap-∘-cst2 a h p)) ctx

... | _ | _ =
  extend-CC-with t (ap-∘3 f g h p) ctx

extend-CC-aux ctx t@(ap-squareᵖ f sq) with split f | sq

... | _ | ap□ᵖ (Dec dec args) (Glue lr A B u) =
  extend-CC-with t (ap-cube f (glue-β□ dec args lr A B u)) ctx

-- {- Debatable -}
-- ... | _ | ap-cst b p =
--   extend-CC-with (ap-square f sq) (ap-∘-cst f b p) ctx

-- ... | Cst _ | _ =
--   trerror ("TODO5 " ++ print t) ctx

-- ... | Idf | _ =
--   extend-CC-with (ap-square f sq) (ap-square-idf sq) ctx

... | SingleDec dec args | ap□ᵖ g@(Lam x X (Glue lr A B u)) p =
  extend-CC-with (ap-square f sq) (ap□-∘-eq g (Dec dec args) p (Lam x X (glue-β dec args lr A B u))) ctx

... | InnerDec dec args rest | ap□ᵖ (Lam _ _ (Glue _ _ _ _)) p =
  extend-CC-with (ap-square f sq) (ap-square-∘ rest (Dec dec args) sq) ctx

... | _ | ap□ᵖ g (apᵖ (Dec dec args) (Glue lr A B u)) =
  extend-CC-with t (ap-cube f (ap□+ (eta-expand g) (glue-β dec args lr A B u))) ctx

... | _ | ap-squareᵖ (Dec dec args) (ap□ᵖ g@(Lam x X (Glue lr A B u)) p) =
  extend-CC-with t (ap-cube f (ap□-∘-eq g (Dec dec args) p (Lam x X (glue-β dec args lr A B u)))) ctx

... | _ | ap□ᵖ g p =
  let X = get-domain (get-type g) in
  let x = fresh (X ∷ f ∷ g ∷ []) "x" in
  extend-CC-with t (ap□-∘-eq g f p (Lam x X (hids (ap f (AppReduce g (Var x X)))))) ctx

-- extend-CC-aux ctx t@(ap-squareᵖ f sq)
--     | _ | ap-squareᵖ g sq' with split g | sq'

-- -- {- Debatable -}
-- -- ...   | _ | ap-cst b p =
-- --   extend-CC-with (ap-square f sq) (ap-cube f (ap-∘-cst g b p)) ctx

-- ...   | SingleDec dec args | ap□ᵖ h@(Lam x X (Glue lr A B u)) p =
--   extend-CC-with (ap-square f sq) (ap-cube f (ap□-∘-eq h g p (Lam x X (glue-β dec args lr A B u)))) ctx

-- -- ...     | SingleDec dec' args' | Glue lr A B ab =
-- --   extend-CC-with (ap-square f sq) (ap-cube f (ap-cube g (glue-β□ dec' args' lr A B ab))) ctx

-- -- ...     | SCoh x X s ty' args' | _ =

-- -- extend-CC-aux ctx t@(ap-squareᵖ f sq) | _ | ap-squareᵖ g sq' | _ | ap-squareᵖ h sq'' with split h | sq''

-- -- ...     | SingleDec dec args | ap□ k p with split k | p

-- -- ...       | SGlue lr x X A B u | _ =
-- --   extend-CC-with (ap-square f sq) (ap-cube f (ap-cube g (ap□-∘-eq k h p (Lam x X (glue-β dec args lr A B u))))) ctx

-- -- ...       | _ | _ =
-- --   trerror ("TODO7 " ++ print t) ctx

-- -- extend-CC-aux ctx t@(ap-squareᵖ f sq) | _ | ap-squareᵖ g sq' | _ | ap-squareᵖ h sq'' | _ | _ =
-- --   trerror ("TODO8 " ++ print t) ctx

-- ...   | _ | _ =
--   extend-CC-with (ap-square f sq) (ap-square-∘ f g sq') ctx
--   -- let Appp s ty args = unapp sq' in
--   -- if isCoh s then
--   --   extend-CC-with (ap-square f sq) (ap-cube f (apcohify s ty args g)) ctx
--   -- else
--   --   trerror ("TODO9 " ++ print t) ctx


-- {- Debatable -}
-- extend-CC-aux ctx t@(ap-squareᵖ f sq) | _ | ap-∘ᵖ g h p with split g

-- ...       | Cst c = extend-CC-with (ap-square f sq) (ap-∘3-cst f c h p) ctx

-- ...       | _ = extend-CC-with (ap-square f sq) (ap-∘3 f g h p) ctx

-- extend-CC-aux ctx t@(ap-squareᵖ f sq) | _ | ap□ᵖ g p with split g | p

-- ... | Cst k | _ =
--   extend-CC-with t (ap-cube f (ap□-cst k p)) ctx

-- ... | SingleDec dec args | Glue lr A B u =
--   extend-CC-with t (ap-cube f (glue-β□ dec args lr A B u)) ctx

-- ... | InnerDec dec args rest | Glue _ _ _ _ =
--   extend-CC-with t (ap-cube f (ap□-∘2 rest (Dec dec args) p)) ctx

-- ... | SCoh x X s ty args | _ =
--   extend-CC-with t (ap□-∘-eq g f p (Lam x X (apcohify s ty args f))) ctx

-- ... | _ | apᵖ (Dec dec args) (Glue lr A B u) =
--   extend-CC-with t (ap-cube f (ap□+ g (glue-β dec args lr A B u))) ctx

-- ... | _ | _ =
--   let Appp s ty args = unapp p in
--   if isCoh s then
--     extend-CC-with t (ap-cube f (ap□cohify s ty args g)) ctx 
--   else
--     trerror ("TODO X " ++ print t) ctx

extend-CC-aux ctx t@(ap-squareᵖ f sq) | _ | _ =
  let Appp s ty args = unapp sq in
  if isCoh s then
    extend-CC-with (ap-square f sq) (apcohify s ty args f) ctx
  else
    trerror ("extend-CC 8 " ++ print t) ctx

-- extend-CC-aux ctx t@(ap-cst b (ap g p) q) =

extend-CC-aux ctx t@(App f arg) =
  let Appp s ty args = unapp t in
  if isCoh s then
    extendx-CC ctx (map unArg (tail args))
  else if is-pt arg then
    extend-CC-with t (ptf f) ctx
  else
   trerror ("extend-CC 3 " ++ print t) ctx

extend-CC-aux ctx t = trerror ("extend-CC 2 " ++ print t) ctx

get-CC t = extend-CC [] t

-- [is-in l t] checks if [t] is the second element of an element of [l], and
-- in that case it returns the corresponding string.
is-in : List (Arg String × Term × Term) → Term → Maybe (String × Term)
is-in ((s , u , t') ∷ xs) t = if u ==ₜ t then just (unArg s , t') else is-in xs t
is-in [] t = nothing

-- Auxiliary function
asubst : List (Arg String × Term × Term) → Term → Term

antisubst : List (Arg String × Term × Term) → Term → Term
antisubst l t with is-in l t
... | just (s , t') = Var s t'
... | nothing = asubst l t

asubst l (Var s' u) = Var s' (antisubst l u)
asubst l (Id a b) = Id (antisubst l a) (antisubst l b)
asubst l (Idp a) = Idp (antisubst l a)
asubst l (Square p q r s) = Square (antisubst l p) (antisubst l q) (antisubst l r) (antisubst l s)
asubst l (Ids a) = Ids (antisubst l a)
asubst l (Cube p q r s t u) = Cube (antisubst l p) (antisubst l q) (antisubst l r) (antisubst l s) (antisubst l t) (antisubst l u)
asubst l (Idc a) = Idc (antisubst l a)
asubst l t@(App _ _) with unapp t
... | Appp s ty args with toList s
...    | '&' ∷ ' ' ∷ _ = recoh s ty (map (λ t → hiding-app t (antisubst l (unArg t))) args)
...    | _ =  Error ("asubst not found " ++ print-P t)
asubst l t = Error ("asubst not found " ++ print-P t)

contractibilify-once : Arg String → List (Arg String × Term × Term) → Term → List (Arg String × Term × Term)
contractibilify-once s l t =
  ((s , t , antisubst l (get-type t)) ∷ l)

-- (s, t, t') in the results represents a variable named [s], corresponding to [t] in the real world
-- and whose type in the coherence is [t']
contractibilify : Term → List (Term × Term) → List (Arg String × Term × Term)
contractibilify A [] = (Imp "a" , pt A , Xₜ) ∷ (Exp "X" , A , Type) ∷ []
contractibilify A ((t , t') ∷ ts) =
  contractibilify-once (Exp ("p" ++ showℕ (length ts)))
    (contractibilify-once (Imp ("x" ++ showℕ (length ts)))
      (contractibilify A ts) t) t'

get-params : List (Arg String × Term × Term) → List (Arg String × Term)
get-params l = map (λ {(a , b , c) → (a , c)}) l

get-args : List (Arg String × Term × Term) → List (Arg Term)
get-args l = map (λ {(a , b , c) → hiding-app a b}) l

is-only-Id : Term → Bool
is-only-Id (PiEI _ Type B) = is-only-Id B
is-only-Id (PiEI _ (Var _ _) B) = is-only-Id B
is-only-Id (PiEI _ (Id _ _) B) = is-only-Id B
is-only-Id (Id _ _) = true
is-only-Id _ = false

is-only-Id-or-Square : Term → Bool
is-only-Id-or-Square (PiEI _ Type B) = is-only-Id-or-Square B
is-only-Id-or-Square (PiEI _ (Var _ _) B) = is-only-Id-or-Square B
is-only-Id-or-Square (PiEI _ (Id _ _) B) = is-only-Id-or-Square B
is-only-Id-or-Square (PiEI _ (Square _ _ _ _) B) = is-only-Id-or-Square B
is-only-Id-or-Square (Id _ _) = true
is-only-Id-or-Square (Square _ _ _ _) = true
is-only-Id-or-Square _ = false

mapArg : {A B : Set} (f : A → B) → List (Arg A) → List (Arg B)
mapArg f [] = []
mapArg f (Exp a ∷ rest) = Exp (f a) ∷ mapArg f rest
mapArg f (Imp a ∷ rest) = Imp (f a) ∷ mapArg f rest

head : List (Arg Term) → Arg Term
head [] = Exp (Error "head")
head (t ∷ ts) = t

cohify : String → Term → List (Arg Term) → Term
cohify s ty args = App[] (Var s ty) args


apcohtype : String → Term → Maybe Term
apcohtype s ty with is-only-Id ty
... | true =
  let (args , T) = unPi ty in
  let thing = ap* fₜX→Y (cohify s ty (vars args)) in
  let type = Square thing
                    (cohify s ty (mapArg (ap* fₜX→Y) (vars args)))
                    (Idp (lhs (get-type thing)))
                    (Idp (rhs (get-type thing))) in
  just (Pi[] ((Imp "X", Type) ∷ (Imp "Y", Type) ∷ (Exp "f", Pi "_" Xₜ Yₜ) ∷ tail args) type)
... | false with is-only-Id-or-Square ty | unPi ty
...    | true | (args , Square p q r ss) =
  let type = Cube (ap-square fₜX→Y (App[] (Var s ty) (vars args)))
                  (App[] (Var s ty) (mapArg adhoc (vars args)))
                  (adhoc3 p) (adhoc3 q) (adhoc3 r) (adhoc3 ss) in
                  
  just (Pi[] ((Imp "X", Type) ∷ (Imp "Y", Type) ∷ (Exp "f", Pi "_" Xₜ Yₜ) ∷ tail args) type)
    where
      adhoc : Term → Term
      adhoc t@(Var p (Square u v@(App _ _) (Idp _) (Idp _))) =
        let Appp a b c = unapp v in
        coh∙□ (ap* fₜX→Y t) (apcohify a b c fₜX→Y)
      adhoc t@(Var p (Square u@(App _ _) v (Idp _) (Idp _))) =
        let Appp a b c = unapp u in
        coh!∙□ (apcohify a b c fₜX→Y) (ap* fₜX→Y t)
      adhoc t = ap* fₜX→Y t

      adhoc3 : Term → Term
      adhoc3 t@(App _ _) =
        let Appp a b c = unapp t in
        apcohify a b c fₜX→Y
      adhoc3 (Idp a) = Ids (AppReduce fₜX→Y a)
      adhoc3 t = hids (ap fₜX→Y t)

...    | true | _ = trerror "What?" nothing
...    | _ | _ = nothing

apcohify s ty args f with apcohtype s ty
... | just apty = App[] (Var ("& ap" ++ trim& s) apty) (Imp (get-domain (get-type f)) ∷ Imp (get-codomain (get-type f)) ∷ Exp f ∷ tail args)
... | nothing = Error "apcohify"

generate-apcoh : Definition → List Definition
generate-apcoh (Coh (coherence s ty)) with apcohtype ("& " ++ s) ty
... | just apty = [ Coh (coherence ("ap" ++ s) apty) ]
... | nothing = []
generate-apcoh _ = trerror "generate-apcoh" []


coh□type : String → Term → Maybe Term
coh□type s ty with is-only-Id ty
... | true =
  let (args , T) = unPi ty in
  just (Pi[] (process-args args) (process-type args T))  where

    process-args : List (Arg String × Term) → List (Arg String × Term)
    process-args ((X , Type) ∷ (a , Xₜ) ∷ args) =
      let ua = "u" ++ unArg a in
      let va = "v" ++ unArg a in
      (X , Type) ∷ (Imp ua , Xₜ) ∷ (Imp va , Xₜ)
                 ∷ (a , Id (Var ua Xₜ) (Var va Xₜ))
                 ∷ process-args args
    process-args ((x , Xₜ) ∷ (p , Id (Var y Xₜ) (Var z Xₜ)) ∷ args) =
      let ux = "u" ++ unArg x in
      let vx = "v" ++ unArg x in
      let up = "u" ++ unArg p in
      let vp = "v" ++ unArg p in
      let uy = "u" ++ y in
      let vy = "v" ++ y in
      let uz = "u" ++ z in
      let vz = "v" ++ z in
      (Imp ux , Xₜ) ∷ (Imp up , Id (Var uy Xₜ) (Var uz Xₜ)) ∷
      (Imp vx , Xₜ) ∷ (Imp vp , Id (Var vy Xₜ) (Var vz Xₜ)) ∷
      (x , Id (Var ux Xₜ) (Var vx Xₜ)) ∷
      (p , Square (Var up (Id (Var uy Xₜ) (Var uz Xₜ)))
                  (Var vp (Id (Var vy Xₜ) (Var vz Xₜ)))
                  (Var y (Id (Var uy Xₜ) (Var vy Xₜ)))
                  (Var z (Id (Var uz Xₜ) (Var vz Xₜ)))) ∷ process-args args
    process-args [] = []
    process-args _ = trerror "process-args" []

    ify : String → Term → Term
    ify u (Var X Type) = Var X Type
    ify u (Var x Xₜ) = Var (u ++ x) Xₜ
    ify u (Var p (Id y z)) = Var (u ++ p) (Id (ify u y) (ify u z))
    ify u _ = Error "ify"

    process-type : List (Arg String × Term) → Term → Term
    process-type args (Id (Var y Xₜ) (Var z Xₜ)) =
      let uy = "u" ++ y in
      let vy = "v" ++ y in
      let uz = "u" ++ z in
      let vz = "v" ++ z in
      Square (cohify s ty (mapArg (ify "u") (vars args)))
             (cohify s ty (mapArg (ify "v") (vars args)))
             (Var y (Id (Var uy Xₜ) (Var vy Xₜ)))
             (Var z (Id (Var uz Xₜ) (Var vz Xₜ)))
    process-type args _ = Error "process-type"

... | false = nothing

coh□ify : String → Term → List (Arg Term) → Term
coh□ify s ty args with coh□type s ty
... | just ty□ = App[] (Var (s ++ "□") ty□) args
... | nothing = Error "coh□ify"

generate-coh□ : Definition → List Definition
generate-coh□ (Coh (coherence s ty)) with coh□type ("& " ++ s) ty
... | just ty□ = [ Coh (coherence (s ++ "□") ty□) ]
... | nothing = []
generate-coh□ _ = trerror "generate-coh□" []


ap/cohtype : String → Term → Maybe Term
ap/cohtype s ty with is-only-Id ty
... | true =
  let (args , T) = unPi ty in
  let newargs = (Imp "X" , Type) ∷ (Imp "Y" , Type) ∷ (Imp "y", Xₜ) ∷ (Imp "z", Xₜ) ∷ (Exp "r", Id yₜX zₜX) ∷ map functionify (tail args) in
  let args□ = process-args args in
  let squareleft = ap□ (Lam "x" Xₜ (cohify s ty (map (applyto xₜX) args))) (Var "r" (Id yₜX zₜX)) in
  let squareright = coh□ify s ty args□ in
  let newT = Cube squareleft squareright (hids (first-side (get-type squareleft))) (hids (second-side (get-type squareleft))) (hids (third-side (get-type squareleft))) (hids (fourth-side (get-type squareleft))) in
  just (Pi[] newargs newT)
  where

    functionify : Arg String × Term → Arg String × Term
    functionify (x , Xₜ) = (x , X→Yₜ)
    functionify (p , Id (Var y Xₜ) (Var z Xₜ)) = (p , Pi "x" Xₜ (Id (AppReduce (Var y X→Yₜ) xₜX) (AppReduce (Var z X→Yₜ) xₜX)))
    functionify _ = (Exp "Error functionify", Error "functionify")

    applyto : Term → Arg String × Term → Arg Term
    applyto a (X , Type) = hiding-app X Yₜ
    applyto a (x , t) = hiding-app x (AppReduce (Var (unArg x) (proj₂ (functionify (x , t)))) a)

    process-args : List (Arg String × Term) → List (Arg Term)
    process-args ((X , Type) ∷ (a , Xₜ) ∷ args) =
      let a' = Var (unArg a) X→Yₜ in
      let r = Var "r" (Id yₜX zₜX) in
      hiding-app X Yₜ ∷ Imp (AppReduce a' yₜX) ∷ Imp (AppReduce a' zₜX) ∷ hiding-app a (ap a' r) ∷ process-args args
    process-args ((x , Xₜ) ∷ (p , Id (Var y Xₜ) (Var z Xₜ)) ∷ args) =
      let x' = Var (unArg x) X→Yₜ in
      let p' = Var (unArg p) (Pi "x" Xₜ (Id (AppReduce (Var y X→Yₜ) xₜX) (AppReduce (Var z X→Yₜ) xₜX))) in
      let r = Var "r" (Id yₜX zₜX) in
      Imp (AppReduce x' yₜX) ∷ Imp (AppReduce p' yₜX) ∷ Imp (AppReduce x' zₜX) ∷ Imp (AppReduce p' zₜX) ∷ hiding-app x (ap x' r) ∷ hiding-app p (ap□ p' r) ∷ process-args args
    process-args [] = []
    process-args _ = trerror "process-args" []

... | false = nothing

ap/cohify s ty p y Y args with ap/cohtype s ty
... | just ap/ty = App[] (Var ("ap/" ++ trim& s) ap/ty) (Imp Y ∷ Imp (unArg (head args)) ∷ Imp (lhs (get-type p)) ∷ Imp (rhs (get-type p)) ∷ Exp p ∷ mapArg (Lam y Y) (tail args))
... | nothing = Error "ap/cohify"

generate-ap/coh : Definition → List Definition
generate-ap/coh (Coh (coherence s ty)) with ap/cohtype ("& " ++ s) ty
... | just ap/ty = [ Oth (other ("ap/" ++ s) ap/ty " = ?") ]
... | nothing = []
generate-ap/coh _ = trerror "generate-ap/coh" []


coh□'type : String → Term → Maybe Term
coh□'type s ty with is-only-Id ty
... | true =
  let (args , T) = unPi ty in
  just (Pi[] (process-args args) (process-type args T))  where

    process-args : List (Arg String × Term) → List (Arg String × Term)
    process-args ((X , Type) ∷ (a , Xₜ) ∷ args) =
      let ua = "u" ++ unArg a in
      let va = "v" ++ unArg a in
      (X , Type) ∷ (Imp ua , Xₜ) ∷ (Imp va , Xₜ)
                 ∷ (a , Id (Var ua Xₜ) (Var va Xₜ))
                 ∷ process-args args
    process-args ((x , Xₜ) ∷ (p , Id (Var y Xₜ) (Var z Xₜ)) ∷ args) =
      let ux = "u" ++ unArg x in
      let vx = "v" ++ unArg x in
      let up = "u" ++ unArg p in
      let vp = "v" ++ unArg p in
      let uy = "u" ++ y in
      let vy = "v" ++ y in
      let uz = "u" ++ z in
      let vz = "v" ++ z in
      (Imp ux , Xₜ) ∷ (Imp up , Id (Var uy Xₜ) (Var uz Xₜ)) ∷
      (Imp vx , Xₜ) ∷ (Imp vp , Id (Var vy Xₜ) (Var vz Xₜ)) ∷
      (x , Id (Var ux Xₜ) (Var vx Xₜ)) ∷
      (p , Square (Var y (Id (Var uy Xₜ) (Var vy Xₜ)))
                  (Var z (Id (Var uz Xₜ) (Var vz Xₜ)))
                  (Var up (Id (Var uy Xₜ) (Var uz Xₜ)))
                  (Var vp (Id (Var vy Xₜ) (Var vz Xₜ)))) ∷ process-args args
    process-args [] = []
    process-args _ = trerror "process-args" []

    ify : String → Term → Term
    ify u (Var X Type) = Var X Type
    ify u (Var x Xₜ) = Var (u ++ x) Xₜ
    ify u (Var p (Id y z)) = Var (u ++ p) (Id (ify u y) (ify u z))
    ify u _ = Error "ify"

    process-type : List (Arg String × Term) → Term → Term
    process-type args (Id (Var y Xₜ) (Var z Xₜ)) =
      let uy = "u" ++ y in
      let vy = "v" ++ y in
      let uz = "u" ++ z in
      let vz = "v" ++ z in
      Square (Var y (Id (Var uy Xₜ) (Var vy Xₜ)))
             (Var z (Id (Var uz Xₜ) (Var vz Xₜ)))
             (cohify s ty (mapArg (ify "u") (vars args)))
             (cohify s ty (mapArg (ify "v") (vars args)))
    process-type args _ = Error "process-type"

... | false = nothing

coh□'ify : String → Term → List (Arg Term) → Term
coh□'ify s ty args with coh□'type s ty
... | just ty□' = App[] (Var (s ++ "□'") ty□') args
... | nothing = Error "coh□'ify"

generate-coh□' : Definition → List Definition
generate-coh□' (Coh (coherence s ty)) with coh□'type ("& " ++ s) ty
... | just ty□' = [ Coh (coherence (s ++ "□'") ty□') ]
... | nothing = []
generate-coh□' _ = trerror "generate-coh□'" []


ap□cohtype : String → Term → Maybe Term
ap□cohtype s ty with is-only-Id ty
... | true =
  let (args , T) = unPi ty in
  let newargs = (Imp "X", Type) ∷ (Imp "Y", Type) ∷ (Imp "f", X→Yₜ) ∷ (Imp "g", X→Yₜ) ∷ (Exp "α", (Pi "x" Xₜ (Id (App (Var "f" X→Yₜ) xₜX) (App (Var "g" X→Yₜ) xₜX)))) ∷ tail args in
  let f = Var "f" X→Yₜ in
  let g = Var "g" X→Yₜ in
  let α = Var "α" (Pi "x" Xₜ (Id (App f xₜX) (App g xₜX))) in
  let a = lhs T in
  let b = rhs T in
  let args□ = process-args f g α args in
  let newT = Cube (ap□ α (cohify s ty (vars args)))
                  (coh□'ify s ty args□)
                  (hids (App α a))
                  (hids (App α b))
                  (apcohify s ty (vars args) f)
                  (apcohify s ty (vars args) g) in
  just (Pi[] newargs newT)
  where
    process-args : Term → Term → Term → List (Arg String × Term) → List (Arg Term)
    process-args f g α ((X , Type) ∷ (a , Xₜ) ∷ args) =
      hiding-app X Yₜ ∷ Imp (AppReduce f aₜX) ∷ Imp (AppReduce g aₜX) ∷ hiding-app a (AppReduce α aₜX) ∷ process-args f g α args
    process-args f g α ((x , Xₜ) ∷ (p , pT@(Id (Var y Xₜ) (Var z Xₜ))) ∷ args) =
      let x' = Var (unArg x) Xₜ in
      let p' = Var (unArg p) pT in
      Imp (AppReduce f x') ∷ Imp (ap f p') ∷ Imp (AppReduce g x') ∷ Imp (ap g p') ∷ hiding-app x (AppReduce α x') ∷ hiding-app p (ap□ α p') ∷ process-args f g α args
    process-args f g α [] = []
    process-args f g α _ = trerror "process-args" []

... | false = nothing

ap□cohify s ty args α with α | ap□cohtype s ty
... | Lam x X α-in | just ap□ty =
  let f = Lam x X (lhs (get-type α-in)) in
  let g = Lam x X (rhs (get-type α-in)) in
  let Y = get-codomain (get-type f) in
  App[] (Var ("ap□" ++ trim& s) ap□ty) (Imp X ∷ Imp Y ∷ Imp f ∷ Imp g ∷ Exp α ∷ tail args)
... | _ | _ = Error "ap□cohify"

generate-ap□coh : Definition → List Definition
generate-ap□coh (Coh (coherence s ty)) with ap□cohtype ("& " ++ s) ty
... | just ap□ty = [ Oth (other ("ap□" ++ s) ap□ty " = ?") ]
... | nothing = []
generate-ap□coh _ = trerror "generate-ap□coh" []


implicitify : List (Arg String × Term × Term) → List (Arg String × Term × Term) → List (Arg String × Term × Term)
implicitify [] acc = acc
implicitify (k@(Imp s , t , u) ∷ ts) acc = implicitify ts (k ∷ acc)
implicitify (k@(Exp s , t , u) ∷ ts) acc = implicitify ts ((if occurs-fully s acc then (Imp s , t , u) else k) ∷ acc)  where

  is-one-of : List Term → String → Bool
  is-one-of [] _ = false
  is-one-of (Var s' _ ∷ ts) s = (s ==ₛ s') ∨ is-one-of ts s
  is-one-of (_ ∷ ts) s = is-one-of ts s

  occurs-fully : String → List (Arg String × Term × Term) → Bool
  occurs-fully s [] = false
  occurs-fully s ((_ , _ , Id a b) ∷ ts) = is-one-of (a ∷ b ∷ []) s ∨ occurs-fully s ts
  occurs-fully s ((_ , _ , Square p q r ss) ∷ ts) = is-one-of (p ∷ q ∷ r ∷ ss ∷ []) s ∨ occurs-fully s ts
  occurs-fully s ((_ , _ , Cube p q r ss t u) ∷ ts) = is-one-of (p ∷ q ∷ r ∷ ss ∷ t ∷ u ∷ []) s ∨ occurs-fully s ts
  occurs-fully s ((_ , _ , Var "X" _) ∷ ts) = occurs-fully s ts
  occurs-fully s ((_ , _ , Type) ∷ ts) = false
  occurs-fully s ((_ , _ , t) ∷ ts) = trerror ("occurs-fully " ++ print-P t) (occurs-fully s ts)

generate-coh : String → Term → DefinitionsAndTerm
generate-coh s t =
  let args = get-CC t in
  let root = get-root-type t in
  let ct-big = contractibilify root args in
  let type = antisubst ct-big t in
--  let ct = reverse ct-big in
  let ct = implicitify ct-big [] in
  let cohtype = Pi[] (get-params ct) type in
  let appterm = App[] (Var ("& " ++ s) cohtype) (get-args ct) in
  let coh = Coh (coherence s cohtype) in

  if type ==ₜ get-type (Idp aₜX) then
    D&T [] (Idp (proj2 (second ct)))
  else if type ==ₜ proj3 (last ct) then
    D&T [] (proj2 (last ct))
  else
    D&T (coh ∷ generate-apcoh coh ++ₗ generate-coh□ coh ++ₗ generate-ap/coh coh ++ₗ generate-coh□' coh ++ₗ generate-ap□coh coh) appterm

    where
  
    proj2 : (Arg String × Term × Term) → Term
    proj2 (a , b , c) = b
  
    proj3 : (Arg String × Term × Term) → Term
    proj3 (a , b , c) = c

    second : List (Arg String × Term × Term) → Arg String × Term × Term
    second (x ∷ y ∷ xs) = y
    second _ = Exp "error" , Error "error" , Error "error"

    last : List (Arg String × Term × Term) → Arg String × Term × Term
    last [] = Exp "error" , Error "error" , Error "error"
    last (x ∷ []) = x
    last (x ∷ xs) = last xs

all-pt-subst : ArgType → Term → Term
all-pt-subst / a - A / u = u [ pt A / a ]
all-pt-subst (A [∧] B) u = all-pt-subst A (all-pt-subst B u)

all-proj : ArgType → Term
all-proj / a - A / = Var a A
all-proj (A [∧] B) = Proj (all-proj A) (all-proj B)


fill-declaration : SparseDeclaration → Declaration

D&T-fill : String → List (String × Term) → ArgType → Term → Term → List Definition → DefinitionsAndTerm
D&T-fill name params argtype type def c =
  let dec = fill-declaration (sparsedeclaration name params argtype type def) in
  D&T (c ++ₗ [ Dec dec ]) (Dec dec (map (λ {(s , t) → Var s t}) params))

to-str : LR → String
to-str L = "l"
to-str R = "r"

get-coh-base : SparseDeclaration → Term → Term → LR → DefinitionsAndTerm
get-coh-base dec A B lr =
  generate-coh (name dec ++ "-cohb" ++ to-str lr)
               (type dec [ Base lr A B / "x" ])

get-coh-0-A∧B : SparseDeclaration → Term → Term → String → String → LR → DefinitionsAndTerm
get-coh-0-A∧B dec A B a b lr =
  generate-coh (name dec ++ "-coh" ++ to-str lr)
               (Id (def dec [ choose lr (pt B) (pt A) / choose lr b a ]) (pt (type dec)))

get-coh-1-A∧B : SparseDeclaration → Term → Term → String → String → Term → LR → DefinitionsAndTerm
get-coh-1-A∧B dec A B a b cohapp lr =
  let var = choose lr (Var a A) (Var b B) in
  let side1 = ap (Lam "x" (Smash A B) (lhs (type dec))) (Glue lr A B var) in
  let side2 = ap (Lam "x" (Smash A B) (rhs (type dec))) (Glue lr A B var) in
  generate-coh (name dec ++ "-coh" ++ to-str lr)
               (Square (def dec [ choose lr (pt B) (pt A) / choose lr b a ]) cohapp side1 side2)

get-coh-2-A∧B : SparseDeclaration → Term → Term → String → String → Term → LR → DefinitionsAndTerm
get-coh-2-A∧B dec A B a b cohapp lr with type dec
... | Square pd qd rd sd =
  let p = def dec [ choose lr (pt B) (pt A) / choose lr b a ] in
  let q = cohapp in
  let var = choose lr (Var a A) (Var b B) in
  let r = ap□ (Lam "x" (Smash A B) pd) (Glue lr A B var) in
  let s = ap□ (Lam "x" (Smash A B) qd) (Glue lr A B var) in
  let t = ap□ (Lam "x" (Smash A B) rd) (Glue lr A B var) in
  let u = ap□ (Lam "x" (Smash A B) sd) (Glue lr A B var) in
  generate-coh (name dec ++ "-cohg" ++ to-str lr)
               (Cube p q r s t u)
... | _ = D&T [] (Error "get-coh-2-A∧B")

get-coh1-0-X∧C : SparseDeclaration → Term → String → DefinitionsAndTerm
get-coh1-0-X∧C dec C c = 
  generate-coh (name dec ++ "-coh1")
               (Id (def dec [ pt C / c ]) (pt (type dec)))

get-aux-0-X∧C : SparseDeclaration → ArgType → Term → String → DefinitionsAndTerm
get-aux-0-X∧C dec X C c =
  D&T-fill (name dec ++ "-aux")
           (params dec ++ₗ [ c , C ])
           X
           (type dec)
           (def dec)
           []

get-auxcoh-0-X∧C : SparseDeclaration → DefinitionsAndTerm → ArgType → Term → String → DefinitionsAndTerm
get-auxcoh-0-X∧C dec dec-aux X C c =
  let D&T coh1 coh1app = get-coh1-0-X∧C dec C c in
  D&T-fill (name dec ++ "-auxcoh")
           (params dec)
           X
           (Id (AppReduce ((cohapp dec-aux) [ pt C / c ])
                          (Var "x" (argtype-to-type X)))
               (pt (type dec)))
           coh1app
           coh1

get-coh2-0-X∧C : SparseDeclaration → ArgType → Term → String → DefinitionsAndTerm
get-coh2-0-X∧C dec X C c =
  generate-coh (name dec ++ "-coh2")
               (Id (all-pt-subst X (def dec)) (pt (type dec)))

get-aux-0-A∧X : SparseDeclaration → Term → ArgType → String → DefinitionsAndTerm
get-aux-0-A∧X dec A X a =
  D&T-fill (name dec ++ "-aux")
           (params dec ++ₗ [ a , A ])
           X
           (type dec)
           (def dec)
           []

get-coh1-0-A∧X : SparseDeclaration → Term → String → DefinitionsAndTerm
get-coh1-0-A∧X dec A a =
  generate-coh (name dec ++ "-coh1")
               (Id (def dec [ pt A / a ]) (pt (type dec)))

get-auxcoh-0-A∧X : SparseDeclaration → DefinitionsAndTerm → Term → ArgType → String → DefinitionsAndTerm
get-auxcoh-0-A∧X dec dec-aux A X a =
  let D&T coh1 coh1app = get-coh1-0-A∧X dec A a in
  D&T-fill (name dec ++ "-auxcoh")
           (params dec)
           X
           (Id (AppReduce (AppReduce (Lam a A (cohapp dec-aux)) (pt A))
                    (Var "x" (argtype-to-type X)))
               (pt (type dec)))
           coh1app
           coh1

get-coh2-0-A∧X : SparseDeclaration → Term → ArgType → String → DefinitionsAndTerm
get-coh2-0-A∧X dec A X a =
  generate-coh (name dec ++ "-coh2")
               (Id (all-pt-subst X (def dec)) (pt (type dec)))

get-aux-1-X∧C : SparseDeclaration → ArgType → Term → String → DefinitionsAndTerm
get-aux-1-X∧C dec X C c =
  D&T-fill (name dec ++ "-aux")
           (params dec ++ₗ [ c , C ])
           X
           (type dec [ Proj (Var "x" (argtype-to-type X)) (Var c C) / "x" ])
           (def dec)
           []

get-auxcoh-1-X∧C : SparseDeclaration → DefinitionsAndTerm → ArgType → Term → String → Term → DefinitionsAndTerm
get-auxcoh-1-X∧C dec dec-aux X C c coh1app =
  let Xt = argtype-to-type X in
  let side1 = ap (Lam "x" (Smash Xt C) (lhs (type dec))) (GlueL Xt C (Var "x" Xt)) in
  let side2 = ap (Lam "x" (Smash Xt C) (rhs (type dec))) (GlueL Xt C (Var "x" Xt)) in
  let type = Square (AppReduce (cohapp dec-aux [ pt C / c ]) (Var "x" Xt)) coh1app side1 side2 in
  let cohdef = generate-coh (name dec ++ "-cohdef")
                            (type [ all-proj X / "x" ]) in
  D&T-fill (name dec ++ "-auxcoh")
           (params dec)
           X
           type
           (cohapp cohdef)
           (cohs cohdef)

get-coh-gluer-1-X∧C : SparseDeclaration → DefinitionsAndTerm → ArgType → Term → String → Term → DefinitionsAndTerm
get-coh-gluer-1-X∧C dec def-coh X C c cohappb =
  let Xt = argtype-to-type X in
  let side1 = ap (Lam "x" (Smash Xt C) (lhs (type dec))) (GlueR Xt C (Var c C)) in
  let side2 = ap (Lam "x" (Smash Xt C) (rhs (type dec))) (GlueR Xt C (Var c C)) in
  let type = Square (AppReduce (cohapp def-coh) (pt Xt)) cohappb
                    side1 side2 in

  generate-coh (name dec ++ "-coh3")
               type

get-aux-1-A∧X : SparseDeclaration → Term → ArgType → String → DefinitionsAndTerm
get-aux-1-A∧X dec A X a =
  D&T-fill (name dec ++ "-aux")
           (params dec ++ₗ [ a , A ])
           X
           (type dec [ Proj (Var a A) (Var "x" (argtype-to-type X)) / "x" ])
           (def dec)
           []

get-auxcoh-1-A∧X : SparseDeclaration → DefinitionsAndTerm → Term → ArgType → String → Term → DefinitionsAndTerm
get-auxcoh-1-A∧X dec dec-aux A X a coh1app =
  let Xt = argtype-to-type X in
  let side1 = ap (Lam "x" (Smash A Xt) (lhs (type dec))) (GlueR A Xt (Var "x" Xt)) in
  let side2 = ap (Lam "x" (Smash A Xt) (rhs (type dec))) (GlueR A Xt (Var "x" Xt)) in
  let type = Square (AppReduce (cohapp dec-aux [ pt A / a ]) (Var "x" Xt)) coh1app side1 side2 in
  let cohdef = generate-coh (name dec ++ "-cohdef")
                            (type [ all-proj X / "x" ]) in
  D&T-fill (name dec ++ "-auxcoh")
           (params dec)
           X
           type
           (cohapp cohdef)
           (cohs cohdef)

get-coh-gluel-1-A∧X : SparseDeclaration → DefinitionsAndTerm → Term → ArgType → String → Term → DefinitionsAndTerm
get-coh-gluel-1-A∧X dec def-coh A X a cohappb =
  let Xt = argtype-to-type X in
  let side1 = ap (Lam "x" (Smash A Xt) (lhs (type dec))) (GlueL A Xt (Var a A)) in
  let side2 = ap (Lam "x" (Smash A Xt) (rhs (type dec))) (GlueL A Xt (Var a A)) in
  let type = Square (AppReduce (cohapp def-coh) (pt Xt)) cohappb
                    side1 side2 in

  generate-coh (name dec ++ "-coh3")
               type

AppReduce (Lam s A t) u = t [ u / s ]
AppReduce (Dec dec args) (Base lr _ _) with dimension (type dec)
... | 0 = pt (type dec [ args /[] map proj₁ (params dec) ])
... | 1 = cohapp (base-coh dec lr) [ args /[] map proj₁ (params dec) ]
... | _ = Error "Not implemented (AppReduce)"
AppReduce (Dec dec args) (Proj u v) with dimension (type dec) | argtype dec
... | _ | / a - A / [∧] / b - B / = cohapp (def-coh dec) [ u ∷ v ∷ args /[] a ∷ b ∷ map proj₁ (params dec) ]
... | 0 | X [∧] / c - C / = AppReduce (cohapp (def-coh dec) [ v ∷ args /[] c ∷ map proj₁ (params dec) ]) u
... | 0 | / a - A / [∧] X = AppReduce (cohapp (def-coh dec) [ u ∷ args /[] a ∷ map proj₁ (params dec) ]) v
... | _ | _ = Error ("TODO4(" ++ showℕ (dimension (type dec)) ++ ")")
AppReduce (App (Atom "ap") f) (Idp u) = Idp (AppReduce f u)
AppReduce (App (Atom "ap-square") f) (Ids u) = Ids (AppReduce f u)
AppReduce (App (Atom "ap□") f) (Idp u) = hids (AppReduce f u)
AppReduce (App (App (Atom "ap-∘") f) g) (Idp u) = Ids (AppReduce f (AppReduce g u))
AppReduce (AppI (AppI (AppI (Var "& hids" _) _) _) _) (Idp u) = Ids u
AppReduce (AppI (AppI (AppI (Var "& vids" _) _) _) _) (Idp u) = Ids u
AppReduce t u = App t u

AppIReduce (Lam s A t) u = t [ u / s ]
AppIReduce t u = AppI t u

is-Type : Term → Bool
is-Type Type = true
is-Type Ptd = true
is-Type _ = false

apply-path-single dec args t with argtype dec | t
... | / a - A / [∧] / b - B / | Glue lr _ _ u =
  let D&T coh cohapp = glue-coh dec lr in
  cohapp [ u ∷ args /[] choose lr a b ∷ map proj₁ (params dec) ]
... | / a - A / [∧] X | GlueL _ _ u =
  let D&T coh cohapp = glue-coh dec L in
  cohapp [ u ∷ args /[] a ∷ map proj₁ (params dec) ]
... | / a - A / [∧] X | GlueR _ _ x =
  let D&T coh cohapp = glue-coh dec R in
  AppReduce (cohapp [ args /[] map proj₁ (params dec) ]) x
... | X [∧] / c - C / | GlueL _ _ x =
  let D&T coh cohapp = glue-coh dec L in
  AppReduce (cohapp [ args /[] map proj₁ (params dec) ]) x
... | X [∧] / c - C / | GlueR _ _ w =
  let D&T coh cohapp = glue-coh dec R in
  cohapp [ w ∷ args /[] c ∷ map proj₁ (params dec) ]
... | _ | _ = trerror "apply-path-single" (ap (Dec dec args) t)

all-at-once : SparseDeclaration → DefinitionsAndTerm × (LR → DefinitionsAndTerm) × (LR → DefinitionsAndTerm)
all-at-once dec with dimension (type dec) | argtype dec
... | 0 | / a - A / [∧] / b - B / =
  (D&T [] (def dec),
   (λ _ → D&T [] (pt (type dec))),
   get-coh-0-A∧B dec A B a b)

... | 1 | / a - A / [∧] / b - B / =
  let base-coh = get-coh-base dec A B in
  (D&T [] (def dec),
   base-coh ,
   (λ lr → get-coh-1-A∧B dec A B a b (cohapp (base-coh lr)) lr))

... | 2 | / a - A / [∧] / b - B / =
  let base-coh = get-coh-base dec A B in
  let glue-coh = λ lr → get-coh-2-A∧B dec A B a b (cohapp (base-coh lr)) lr in
  (D&T [] (def dec),
   base-coh ,
   glue-coh)

... | 0 |  X [∧] / c - C / =
  let def-coh = get-aux-0-X∧C dec X C c in
  let gluel-coh = get-auxcoh-0-X∧C dec def-coh X C c in
  let gluer-coh = get-coh2-0-X∧C dec X C c in
  (def-coh ,
   (λ _ → D&T [] (pt (type dec))),
   (λ {L → gluel-coh ; R → gluer-coh}))

... | 0 | / a - A / [∧] X =
  let def-coh = get-aux-0-A∧X dec A X a in
  let gluel-coh = get-coh2-0-A∧X dec A X a in
  let gluer-coh = get-auxcoh-0-A∧X dec def-coh A X a in
  (def-coh ,
   (λ _ → D&T [] (pt (type dec))),
   (λ {L → gluel-coh ; R → gluer-coh}))

... | 1 | X [∧] / c - C / =
  let def-coh = get-aux-1-X∧C dec X C c in
  let base-coh = get-coh-base dec (argtype-to-type X) C in
  let gluel-coh = get-auxcoh-1-X∧C dec def-coh X C c (cohapp (base-coh L)) in
  let gluer-coh = get-coh-gluer-1-X∧C dec def-coh X C c (cohapp (base-coh R)) in
  (def-coh ,
   base-coh ,
   (λ {L → gluel-coh ; R → gluer-coh}))

... | 1 | / a - A / [∧] X =
  let def-coh = get-aux-1-A∧X dec A X a in
  let base-coh = get-coh-base dec A (argtype-to-type X) in
  let gluel-coh = get-coh-gluel-1-A∧X dec def-coh A X a (cohapp (base-coh L)) in
  let gluer-coh = get-auxcoh-1-A∧X dec def-coh A X a (cohapp (base-coh R)) in
  (def-coh ,
   base-coh ,
   (λ {L → gluel-coh ; R → gluer-coh}))

... | _ | _ = 
  (D&T [] (Error "unimplemented"),
   (λ _ → D&T [] (Error "unimplemented")),
   (λ _ → D&T [] (Error "unimplemented")))

fill-declaration dec =
  let (def-coh , base-coh , glue-coh) = all-at-once dec in
  declaration (name dec)
              (params dec)
              (argtype dec)
              (type dec)
              def-coh
              base-coh
              glue-coh

generate-body dec with dimension (type dec) | argtype dec
generate-body dec | 0 | / a - A / [∧] / b - B / =

  let D&T coh1 coh1app = glue-coh dec L in
  let D&T coh2 coh2app = glue-coh dec R in

  sprintf "%k\n\n%k

%k : %k %k → %k
%k %k = %k.f  module _ where

  module %k =
    SmashRec (λ %k %k → %k)
             pt
             (λ %k → %k)
             pt
             (λ %k → %k)

" (coh1 ∷ coh2
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec) ∷ name dec
  ∷ name dec
  ∷ a ∷ b ∷ cohapp (def-coh dec)
  ∷ a ∷ coh1app
  ∷ b ∷ coh2app
  ∷ [])
generate-body dec | 1 | / a - A / [∧] / b - B / =

  let D&T coh1 coh1app = def-coh dec in
  let D&T coh2 coh2app = base-coh dec L in
  let D&T coh3 coh3app = glue-coh dec L in
  let D&T coh4 coh4app = base-coh dec R in
  let D&T coh5 coh5app = glue-coh dec R in

  sprintf "%k\n\n%k\n\n%k\n\n%k\n\n%k

%k : %k %k → %k
%k %k = %k.f  module _ where

  module %k =
    SmashElimId {g = λ x → %k}
                {h = λ x → %k}
                (λ %k %k → %k)
                (%k)
                (λ %k → %k)
                (%k)
                (λ %k → %k)

" (coh1 ∷ coh2 ∷ coh3 ∷ coh4 ∷ coh5
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec) ∷ name dec
  ∷ name dec
  ∷ lhs (type dec)
  ∷ rhs (type dec)
  ∷ a ∷ b ∷ coh1app
  ∷ coh2app
  ∷ a ∷ coh3app
  ∷ coh4app
  ∷ b ∷ coh5app
  ∷ [])

generate-body dec | 2 | / a - A / [∧] / b - B / =

  let D&T coh1 coh1app = def-coh dec in
  let D&T coh2 coh2app = base-coh dec L in
  let D&T coh3 coh3app = glue-coh dec L in
  let D&T coh4 coh4app = base-coh dec R in
  let D&T coh5 coh5app = glue-coh dec R in

  sprintf "%k\n\n%k\n\n%k\n\n%k\n\n%k

%k : %k %k → %k
%k %k =
  Smash-elim (λ %k %k → %k)
             (%k)
             (λ %k → ↓-Square-in (%k))
             (%k)
             (λ %k → ↓-Square-in (%k))
" (coh1 ∷ coh2 ∷ coh3 ∷ coh4 ∷ coh5
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec)
  ∷ a ∷ b ∷ coh1app
  ∷ coh2app
  ∷ a ∷ coh3app
  ∷ coh4app
  ∷ b ∷ coh5app ∷ [])

generate-body dec | 0 | X [∧] / c - C / =

  let D&T coh1 coh1app = def-coh dec in
  let D&T coh2 coh2app = glue-coh dec L in
  let D&T coh3 coh3app = glue-coh dec R in

  sprintf "%k\n%k\n\n%k

%k : %k %k → %k
%k %k = %k.f  module _ where

  module %k =
    SmashRec (λ x %k → %k x) 
             pt
             (%k)
             pt
             (λ %k → %k)
" (coh1 ∷ coh2 ∷ coh3
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec) ∷ name dec
  ∷ name dec
  ∷ c ∷ coh1app
  ∷ coh2app
  ∷ c ∷ coh3app
  ∷ [])

generate-body dec | 0 | / a - A / [∧] X =

  let D&T coh1 coh1app = def-coh dec in
  let D&T coh2 coh2app = glue-coh dec L in
  let D&T coh3 coh3app = glue-coh dec R in

  sprintf "%k\n%k\n\n%k

%k : %k %k → %k
%k %k = %k.f  module _ where

 module %k =
     SmashRec (λ %k → %k)
             pt
             (λ %k → %k)
             pt
             (%k)
" (coh1 ∷ coh2 ∷ coh3
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec) ∷ name dec
  ∷ name dec
  ∷ a ∷ coh1app
  ∷ a ∷ coh2app
  ∷ coh3app
  ∷ [])

generate-body dec | 1 | X [∧] / c - C / =

  let D&T coh1 coh1app = def-coh dec in
  let D&T coh2 coh2app = base-coh dec L in
  let D&T coh3 coh3app = glue-coh dec L in
  let D&T coh4 coh4app = base-coh dec R in
  let D&T coh5 coh5app = glue-coh dec R in

  sprintf "%k\n%k\n\n%k\n\n%k\n%k

%k : %k %k → %k
%k %k = %k.f  module _ where

  module %k =
    SmashElimId {g = λ x → %k}
                {h = λ x → %k}
                (λ x %k → %k x)
                (%k)
                (%k)
                (%k)
                (λ %k → %k)
" (coh1 ∷ coh2 ∷ coh3 ∷ coh4 ∷ coh5
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec) ∷ name dec
  ∷ name dec
  ∷ lhs (type dec)
  ∷ rhs (type dec)
  ∷ c ∷  coh1app
  ∷ coh2app
  ∷ coh3app
  ∷ coh4app
  ∷ c ∷ coh5app
  ∷ [])

generate-body dec | 1 | / a - A / [∧] X =

  let D&T coh1 coh1app = def-coh dec in
  let D&T coh2 coh2app = base-coh dec L in
  let D&T coh3 coh3app = glue-coh dec L in
  let D&T coh4 coh4app = base-coh dec R in
  let D&T coh5 coh5app = glue-coh dec R in

  sprintf "%k\n%k\n\n%k\n\n%k\n%k

%k : %k %k → %k
%k %k = %k.f  module _ where

  module %k =
    SmashElimId {g = λ x → %k}
                {h = λ x → %k}
                (λ %k → %k)
                (%k)
                (λ %k → %k)
                (%k)
                (%k)
" (coh1 ∷ coh2 ∷ coh3 ∷ coh4 ∷ coh5
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec) ∷ name dec
  ∷ name dec
  ∷ lhs (type dec)
  ∷ rhs (type dec)
  ∷ a ∷  coh1app
  ∷ coh2app
  ∷ a ∷ coh3app
  ∷ coh4app
  ∷ coh5app
  ∷ [])

generate-body dec | _ | _ = "Not implemented yet"


{- The declarations we want to generate -}

{- Commutativity of the smash product -}
σ-sdec : SparseDeclaration
name σ-sdec = "σ"
params σ-sdec = ("A" , Ptd) ∷ ("B", Ptd) ∷ []
argtype σ-sdec = A∧B
type σ-sdec = Smash Bₜ Aₜ
def σ-sdec = Proj bₜB aₜA

σ-dec = fill-declaration σ-sdec

{- The identity function defined by induction -}
id-sdec : SparseDeclaration
name id-sdec = "idsmash"
params id-sdec = ("A" , Ptd) ∷ ("B", Ptd) ∷ []
argtype id-sdec = A∧B
type id-sdec = Smash Aₜ Bₜ
def id-sdec = Proj aₜA bₜB

id-dec = fill-declaration id-sdec

{- Functoriality of the smash product -}
∧-map-sdec : SparseDeclaration
name ∧-map-sdec = "∧-map"
params ∧-map-sdec = ("A", Ptd) ∷ ("A'", Ptd) ∷ ("B", Ptd) ∷ ("B'", Ptd) ∷ ("f", PtdMap Aₜ A'ₜ) ∷ ("g" , PtdMap Bₜ B'ₜ) ∷ []
argtype ∧-map-sdec = A∧B
type ∧-map-sdec = Smash A'ₜ B'ₜ
def ∧-map-sdec = Proj (App fₜA→∙A' aₜA) (App gₜB→∙B' bₜB)

∧-map-dec = fill-declaration ∧-map-sdec

{- Associativity of the smash product -}
α-sdec : SparseDeclaration
name α-sdec = "α"
params α-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype α-sdec = [A∧B]∧C
type α-sdec = Smash Aₜ (Smash Bₜ Cₜ)
def α-sdec = Proj aₜA (Proj bₜB cₜC)

α-dec = fill-declaration α-sdec

{- Inverse associator -}
αinv-sdec : SparseDeclaration
name αinv-sdec = "α⁻¹"
params αinv-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype αinv-sdec = A∧[B∧C]
type αinv-sdec = Smash (Smash Aₜ Bₜ) Cₜ
def αinv-sdec = Proj (Proj aₜA bₜB) cₜC

αinv-dec = fill-declaration αinv-sdec

{- Some random coherence -}
β-sdec : SparseDeclaration
name β-sdec = "β"
params β-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype β-sdec = [A∧B]∧C
type β-sdec = Smash (Smash Cₜ Bₜ) Aₜ
def β-sdec = Proj (Proj cₜC bₜB) aₜA

β-dec = fill-declaration β-sdec

{- Some random complicated coherence -}
γ-sdec : SparseDeclaration
name γ-sdec = "γ"
params γ-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype γ-sdec = [A∧B]∧C
type γ-sdec = Smash Aₜ (Smash (Smash Cₜ Bₜ) (Smash Aₜ Cₜ))
def γ-sdec = Proj aₜA (Proj (Proj cₜC bₜB) (Proj aₜA cₜC))

γ-dec = fill-declaration γ-sdec

{- Functoriality preserves identities -}
∧-map-id-sdec : SparseDeclaration
name ∧-map-id-sdec = "∧-map-id"
params ∧-map-id-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ []
argtype ∧-map-id-sdec = A∧B
type ∧-map-id-sdec = Id (App (Dec ∧-map-dec (Aₜ ∷ Aₜ ∷ Bₜ ∷ Bₜ ∷ Lam "y" Aₜ (Var "y" Aₜ) ∷ Lam "z" Bₜ (Var "z" Bₜ) ∷ []))
                            (Var "x" (argtype-to-type A∧B)))
                       (Var "x" (argtype-to-type A∧B))
def ∧-map-id-sdec = Idp (Proj aₜA bₜB)

∧-map-id-dec = fill-declaration ∧-map-id-sdec

{- Symmetry -}
σ-triangle-sdec : SparseDeclaration
name σ-triangle-sdec = "σ-triangle"
params σ-triangle-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ []
argtype σ-triangle-sdec = A∧B
type σ-triangle-sdec = Id (App (Dec σ-dec (Bₜ ∷ Aₜ ∷ []))
                              (App (Dec σ-dec (Aₜ ∷ Bₜ ∷ []))
                                   (Var "x" (argtype-to-type A∧B))))
                         (Var "x" (argtype-to-type A∧B))
def σ-triangle-sdec = Idp (Proj aₜA bₜB)

σ-triangle-dec = fill-declaration σ-triangle-sdec

{- Double symmetry! -}
σ-2triangle-sdec : SparseDeclaration
name σ-2triangle-sdec = "σ-2triangle"
params σ-2triangle-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ []
argtype σ-2triangle-sdec = A∧B
type σ-2triangle-sdec = Id (App (Dec σ-dec (Bₜ ∷ Aₜ ∷ []))
                               (App (Dec σ-dec (Aₜ ∷ Bₜ ∷ []))
                                    (App (Dec σ-dec (Bₜ ∷ Aₜ ∷ []))
                                         (App (Dec σ-dec (Aₜ ∷ Bₜ ∷ []))
                                              (Var "x" (argtype-to-type A∧B))))))
                          (Var "x" (argtype-to-type A∧B))
def σ-2triangle-sdec = Idp (Proj aₜA bₜB)

σ-2triangle-dec = fill-declaration σ-2triangle-sdec

{- Naturality of σ -}
σ-nat-sdec : SparseDeclaration
name σ-nat-sdec = "σ-nat"
params σ-nat-sdec = ("A", Ptd) ∷ ("A'", Ptd) ∷ ("B", Ptd) ∷ ("B'", Ptd) ∷ ("f", PtdMap Aₜ A'ₜ) ∷ ("g" , PtdMap Bₜ B'ₜ) ∷ []
argtype σ-nat-sdec = A∧B
type σ-nat-sdec = Id (App (Dec σ-dec (A'ₜ ∷ B'ₜ ∷ []))
                         (App (Dec ∧-map-dec (Aₜ ∷ A'ₜ ∷ Bₜ ∷ B'ₜ ∷ fₜA→∙A' ∷ gₜB→∙B' ∷ []))
                              (Var "x" (argtype-to-type A∧B))))
                    (App (Dec ∧-map-dec (Bₜ ∷ B'ₜ ∷ Aₜ ∷ A'ₜ ∷ gₜB→∙B' ∷ fₜA→∙A' ∷ []))
                         (App (Dec σ-dec (Aₜ ∷ Bₜ ∷ []))
                              (Var "x" (argtype-to-type A∧B))))
def σ-nat-sdec = Idp (Proj (App gₜB→∙B' bₜB) (App fₜA→∙A' aₜA))

σ-nat-dec = fill-declaration σ-nat-sdec

-- {- Functoriality of smash commutes with composition -}
-- ∧-map-comp-sdec : SparseDeclaration
-- name ∧-map-comp-sdec = "∧-map-comp"
-- params ∧-map-comp-sdec = ("A", Ptd) ∷ ("A'", Ptd) ∷ ("A''", Ptd) ∷ ("B", Ptd) ∷ ("B'", Ptd) ∷ ("B''", Ptd) ∷ ("f", PtdMap Aₜ A'ₜ) ∷ ("f'", PtdMap A'ₜ A''ₜ) ∷ ("g" , PtdMap Bₜ B'ₜ) ∷ ("g'" , PtdMap B'ₜ B''ₜ) ∷ []
-- argtype ∧-map-comp-sdec = A∧B
-- typelhs ∧-map-comp-sdec = [ ∧-map-dec , < Aₜ > ∷ < A''ₜ > ∷ < Bₜ > ∷ < B''ₜ > ∷ < Lam "z" Aₜ (App f'ₜA'→∙A'' (App fₜA→∙A' (Var "z" Aₜ))) > ∷ < Lam "z" Bₜ (App g'ₜB'→∙B'' (App gₜB→∙B' (Var "z" Bₜ))) > ∷ [] ]∷
--                          []
-- typerhs ∧-map-comp-sdec = [ ∧-map-dec , < Aₜ > ∷ < A'ₜ > ∷ < Bₜ > ∷ < B'ₜ > ∷ < fₜA→∙A' > ∷ < gₜB→∙B' > ∷ [] ]∷
--                          [ ∧-map-dec , < A'ₜ > ∷ < A''ₜ > ∷ < B'ₜ > ∷ < B''ₜ > ∷ < f'ₜA'→∙A'' > ∷ < g'ₜB'→∙B'' > ∷ [] ]∷
--                          []
-- def ∧-map-comp-sdec = Lam "a" Aₜ (Lam "b" Bₜ (Idp (Error "TODO")))

-- ∧-map-comp-dec = fill-declaration ∧-map-comp-sdec

{- α is a right inverse to α⁻¹ -}
α-rinv-sdec : SparseDeclaration
name α-rinv-sdec = "α-rinv"
params α-rinv-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype α-rinv-sdec = [A∧B]∧C
type α-rinv-sdec = Id (App (Dec αinv-dec (Aₜ ∷ Bₜ ∷ Cₜ ∷ []))
                          (App (Dec α-dec (Aₜ ∷ Bₜ ∷ Cₜ ∷ []))
                               (Var "x" (argtype-to-type [A∧B]∧C))))
                     (Var "x" (argtype-to-type [A∧B]∧C))
def α-rinv-sdec = Idp (Proj (Proj aₜA bₜB) cₜC)

α-rinv-dec = fill-declaration α-rinv-sdec

{- α is a left inverse to α⁻¹ -}
α-linv-sdec : SparseDeclaration
name α-linv-sdec = "α-linv"
params α-linv-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype α-linv-sdec = A∧[B∧C]
type α-linv-sdec = Id (App (Dec α-dec (Aₜ ∷ Bₜ ∷ Cₜ ∷ []))
                          (App (Dec αinv-dec (Aₜ ∷ Bₜ ∷ Cₜ ∷ []))
                               (Var "x" (argtype-to-type A∧[B∧C]))))
                     (Var "x" (argtype-to-type A∧[B∧C]))
def α-linv-sdec = Idp (Proj aₜA (Proj bₜB cₜC))

α-linv-dec = fill-declaration α-linv-sdec

{- Hexagon -}
hexagon-sdec : SparseDeclaration
name hexagon-sdec = "hexagon"
params hexagon-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype hexagon-sdec = [A∧B]∧C
type hexagon-sdec = Id (App (Dec ∧-map-dec (Bₜ ∷ Bₜ ∷ Smash Aₜ Cₜ ∷ Smash Cₜ Aₜ ∷ Lam "y" Bₜ (Var "y" Bₜ) ∷ Dec σ-dec (Aₜ ∷ Cₜ ∷ []) ∷ []))
                            (App (Dec α-dec (Bₜ ∷ Aₜ ∷ Cₜ ∷ []))
                                 (App (Dec ∧-map-dec (Smash Aₜ Bₜ ∷ Smash Bₜ Aₜ ∷ Cₜ ∷ Cₜ ∷ Dec σ-dec (Aₜ ∷ Bₜ ∷ []) ∷ Lam "z" Cₜ (Var "z" Cₜ) ∷ []))
                                      (Var "x" (argtype-to-type [A∧B]∧C)))))
                       (App (Dec α-dec (Bₜ ∷ Cₜ ∷ Aₜ ∷ []))
                            (App (Dec σ-dec (Aₜ ∷ Smash Bₜ Cₜ ∷ []))
                                 (App (Dec α-dec (Aₜ ∷ Bₜ ∷ Cₜ ∷ []))
                                      (Var "x" (argtype-to-type [A∧B]∧C)))))
def hexagon-sdec = Idp (Proj bₜB (Proj cₜC aₜA))

hexagon-dec = fill-declaration hexagon-sdec

{- MacLane’s pentagon -}
pentagon-sdec : SparseDeclaration
name pentagon-sdec = "pentagon"
params pentagon-sdec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ ("D", Ptd) ∷ []
argtype pentagon-sdec = [[A∧B]∧C]∧D
type pentagon-sdec = Id (App (Dec ∧-map-dec (Aₜ ∷ Aₜ ∷ Smash (Smash Bₜ Cₜ) Dₜ ∷ Smash Bₜ (Smash Cₜ Dₜ) ∷ Lam "x" Aₜ (Var "x" Aₜ) ∷ Dec α-dec (Bₜ ∷ Cₜ ∷ Dₜ ∷ []) ∷ []))
                            (App (Dec α-dec (Aₜ ∷ Smash Bₜ Cₜ ∷ Dₜ ∷ []))
                                 (App (Dec ∧-map-dec (Smash (Smash Aₜ Bₜ) Cₜ ∷ Smash Aₜ (Smash Bₜ Cₜ) ∷ Dₜ ∷ Dₜ ∷ Dec α-dec (Aₜ ∷ Bₜ ∷ Cₜ ∷ []) ∷ Lam "y" Dₜ (Var "y" Dₜ) ∷ []))
                                      (Var "x" (argtype-to-type [[A∧B]∧C]∧D)))))
                       (App (Dec α-dec (Aₜ ∷ Bₜ ∷ Smash Cₜ Dₜ ∷ []))
                            (App (Dec α-dec (Smash Aₜ Bₜ ∷ Cₜ ∷ Dₜ ∷ []))
                                 (Var "x" (argtype-to-type [[A∧B]∧C]∧D))))
def pentagon-sdec = Idp (Proj aₜA (Proj bₜB (Proj cₜC dₜD)))

pentagon-dec = fill-declaration pentagon-sdec

main : IO ⊤
main =
  putStr ("{-# OPTIONS --without-K --rewriting #-}

open import PathInduction
open import SmashDefs

module dump {i : ULevel} where
\n" ++
    -- generate-body id-dec ++ "\n\n" ++
    generate-body σ-dec ++ "\n\n" ++
    generate-body ∧-map-dec ++ "\n\n" ++

    generate-body ∧-map-id-dec ++ "\n\n" ++
    generate-body σ-triangle-dec ++ "\n\n" ++
    generate-body σ-2triangle-dec ++ "\n\n" ++

    generate-body α-dec ++ "\n\n" ++
    generate-body αinv-dec ++ "\n\n" ++

    -- generate-body β-dec ++ "\n\n" ++
    -- generate-body γ-dec ++ "\n\n" ++

    -- generate-body σ-nat-dec ++ "\n\n" ++

    generate-body α-rinv-dec ++ "\n\n" ++
    generate-body α-linv-dec ++ "\n\n" ++
    generate-body hexagon-dec ++ "\n\n" ++

    -- generate-body pentagon-dec ++ "\n\n" ++
    "")