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
{-# COMPILE GHC trace = \ _ s x -> Trace.trace (Text.unpack s) x #-}

postulate
  putStr : String → IO ⊤
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

{- The datatype of terms (and types).
   It is designed in such a way that it is always possible to figure out the
   type of a term, without needing to refer to an environment. In particular,
   all variables are tagged with their type.
-}
data Term : Set where
  -- Variable and its type
  Var : (s : String) (t : Term) → Term
  -- Declaration and its parameters (note that it is in a η-contracted form)
  Dec : (dec : Declaration) (args : List Term) → Term
  -- Application which may be explicit or implicit
  AppEI : (f : Term) (arg : Arg Term) → Term
  -- The smash product and its constructors
  Smash : (A B : Term) → Term
  Proj : (a b : Term) → Term
  BaseL : (A B : Term) → Term
  BaseR : (A B : Term) → Term
  GlueL : (A B a : Term) → Term
  GlueR : (A B b : Term) → Term
  -- Identity type and constant path
  Id : (a b : Term) → Term
  Idp : (a : Term) → Term
  -- Square type and constant square
  Square : (p q r s : Term) → Term
  Ids : (a : Term) → Term
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
  Error : String → Term

{- Type of contractible systems
   We support the following contractible systems:
   - ⟨*A⟩     for A a pointed type
   - ⟨*f⟩     for f a pointed function between pointed types
   - two pointed functions (not working at the moment)
   - cA ∧ cB  for cA and cB two contractible systems
-}
data ContractibleSystem : Set where
  PtdCS : Term → ContractibleSystem
  PtdMapCS : Term → ContractibleSystem
  DoublePtdMapCS : Term → Term → ContractibleSystem
  SmashCS : ContractibleSystem → ContractibleSystem → ContractibleSystem

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
   CS-codomain : The contractible system to use on the codomain
-}
record Declaration where
  inductive
  constructor declaration
  field
    name : String
    params : List (String × Term)
    argtype : ArgType
    type : Term
    def : Term
    CS-codomain : ContractibleSystem
open Declaration public

{- A top-level definition, with its name, type, and the definition as a string -}
record Definition : Set where
  constructor definition
  field
    name : String
    type : Term
    def : String
open Definition

pattern App f arg = AppEI f (Exp arg)
pattern AppI f arg = AppEI f (Imp arg)
pattern Pi x A B = PiEI (Exp x) A B
pattern PiI x A B = PiEI (Imp x) A B


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
a'ₜA = Var "a'" Aₜ
bₜB  = Var "b" Bₜ
b'ₜB = Var "b'" Bₜ
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

{- Parenthesize the argument in the argument is true -}
par : Bool → String → String
par false s = s
par true s = "(" ++ s ++ ")"

is-Pi : Term → Bool
is-Pi (PiEI _ _ _) = true
is-Pi _ = false

{- Print the term
   - parenthesizing it if the first argument is true (unless it’s clearly not needed)
   - with all implicit arguments if the second argument is true -}
print-term-p : Bool → Bool → Term → String

print-term-h : Bool → Term → String
print-term-h = print-term-p false

print-term-hP : Bool → Term → String
print-term-hP = print-term-p true

print-term-P : Term → String
print-term-P = print-term-p true false

{- Print a list of pairs of terms (used only for debugging) -}
print-list-term-p : Bool → List Term → String
print-list-term-p k [] = par k ""
print-list-term-p k (t ∷ []) = par k (print-term-P t)
print-list-term-p k (t ∷ ts) = par k (print-term-P t ++ " " ++ print-list-term-p false ts)

print-term-p k false (Var s t) = s
print-term-p k true (Var s t) = s ++ " {" ++ "-" ++ print-term-h true t ++ "-" ++ "}"
print-term-p k h (Dec dec params) = par k (name dec ++ " " ++ print-list-term-p false params)
print-term-p k h (App t arg) = par k (print-term-h h t ++ " " ++ print-term-hP h arg)
print-term-p k false (AppI t arg) = print-term-p k false t
print-term-p k true (AppI t arg) = par k (print-term-h true t ++ " {" ++ print-term-h true arg ++ "}")
print-term-p k h (Proj a b) = par k ("proj " ++ print-term-hP h a ++ " " ++ print-term-hP h b)
print-term-p k h (BaseL _ _) = "basel"
print-term-p k h (BaseR _ _) = "baser"
print-term-p k h (GlueL _ _ a) = par k ("gluel " ++ print-term-hP h a)
print-term-p k h (GlueR _ _ b) = par k ("gluer " ++ print-term-hP h b)
print-term-p k h (Id a b) = par k (print-term-h h a ++ " == " ++ print-term-h h b)
print-term-p k h (Idp _) = "idp"
print-term-p k h (Square p q r s) = par k ("Square " ++ print-term-h h p ++ " " ++ print-term-h h q ++ " " ++ print-term-h h r ++ " " ++ print-term-h h s)
print-term-p k h (Ids _) = "ids"
print-term-p k h (Pt A) = "pt" -- {" ++ "-" ++ print-term-h A ++ "-" ++ "}" -- Usually that should be enough
print-term-p k h (Ptf f A B) = par k ("ptf " ++ f)
print-term-p k h (Lam x A u) = par k ("λ " ++ x {- ++ " {" ++ "- " ++ print-term-h A ++ " -" ++ "}" -} ++ " → " ++ print-term-h h u)
-- print-term-p k h (Pi "_" A B) = 
print-term-p k h (Pi s A B) = if s ==ₛ "_" then par k (print-term-h h A ++ " → " ++ print-term-h h B) else par k ("(" ++ s ++ " : " ++ print-term-h h A ++ (if is-Pi B then ") " else ") → ") ++ print-term-h h B)
print-term-p k h (PiI s A B) = par k ("{" ++ s ++ " : " ++ print-term-h h A ++ (if is-Pi B then "} " else "} → ") ++ print-term-h h B)
print-term-p k h Ptd = par k "Type i"
print-term-p k h Type = par k "Type i"
print-term-p k h (PtdMap A B) = par k (print-term-hP h A ++ " → " ++ print-term-hP h B)
print-term-p k h (Smash A B) = par k (print-term-hP h A ++ " ∧ " ++ print-term-hP h B)
print-term-p k h (Error s) = "{" ++ "!ERROR (" ++ s ++ ")!" ++ "}"

print-term : Term → String
print-term = print-term-h false

data AllImplicit : Set where
  allImplicit : Term → AllImplicit

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

-- {- Print a list of pairs of terms (used only for debugging) -}
-- print-list-term-term : List (Term × Term) → String
-- print-list-term-term [] = ""
-- print-list-term-term ((t , u) ∷ []) = print-term t ++ " " ++ print-term u
-- print-list-term-term ((t , u) ∷ ts) = print-term t ++ " " ++ print-term u ++ " / " ++ print-list-term-term ts

print-definition : Definition → String
print-definition d = name d ++ " : " ++ print-term (type d) ++ "\n" ++ def d

print-argtype : ArgType → String
print-argtype (/ _ - A /) = print-term A
print-argtype (A [∧] B) = "[" ++ print-argtype A ++ "∧" ++ print-argtype B ++ "]"

{- Make all of these functions instances, so that we can simply use [print] and [sprintf] -}
instance
  Termₚ : Printable Term
  Termₚ = record { print-p = λ k → print-term-p k false }

  AllImplicitₚ : Printable AllImplicit
  AllImplicitₚ = record { print-p = λ k → λ { (allImplicit t) → print-term-p k true t} }

  ListTermₚ : Printable (List Term)
  ListTermₚ = record { print-p = print-list-term-p }

  -- ListTermTermₚ : Printable (List (Term × Term))
  -- ListTermTermₚ = record { print = print-list-term-term }

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
is-fresh-in s (Dec dec params) = is-fresh-inx s params
is-fresh-in s (App t arg) = is-fresh-in s t ∧ is-fresh-in s arg
is-fresh-in s (AppI t arg) = is-fresh-in s t ∧ is-fresh-in s arg
is-fresh-in s (Proj a b) = is-fresh-in s a ∧ is-fresh-in s b
is-fresh-in s (BaseL A B) = is-fresh-in s A ∧ is-fresh-in s B
is-fresh-in s (BaseR A B) = is-fresh-in s A ∧ is-fresh-in s B
is-fresh-in s (GlueL A B a) = is-fresh-in s A ∧ is-fresh-in s B ∧ is-fresh-in s a
is-fresh-in s (GlueR A B b) = is-fresh-in s A ∧ is-fresh-in s B ∧ is-fresh-in s b
is-fresh-in s (Id a b) = is-fresh-in s a ∧ is-fresh-in s b
is-fresh-in s (Idp a) = is-fresh-in s a
is-fresh-in s (Square p q r ss) = is-fresh-in s p ∧ is-fresh-in s q ∧ is-fresh-in s r ∧ is-fresh-in s ss
is-fresh-in s (Ids a) = is-fresh-in s a
is-fresh-in s (Pt A) = not (s ==ₛ A)
is-fresh-in s (Ptf f A B) = not (s ==ₛ f) ∧ is-fresh-in s A ∧ is-fresh-in s B
is-fresh-in s (Lam s' A t) = is-fresh-in s A ∧ ((s ==ₛ s') ∨ (not (s ==ₛ s') ∧ is-fresh-in s t))
is-fresh-in s (PiEI s' A B)  = is-fresh-in s A ∧ ((s ==ₛ unArg s') ∨ (not (s ==ₛ unArg s') ∧ is-fresh-in s B))
is-fresh-in s Ptd = true
is-fresh-in s Type = true
is-fresh-in s (PtdMap A B) = is-fresh-in s A ∧ is-fresh-in s B
is-fresh-in s (Smash A B) = is-fresh-in s A ∧ is-fresh-in s B
is-fresh-in s (Error x) = true

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

{- More notations for terms -}
Xₜ = Var "X" Type
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

get-type : Term → Term

{- Return the dimension of the given type (how many nested Id’s it consists of) -}
{-# TERMINATING #-}
dimension : Term → ℕ
dimension (Id a _) = suc (dimension (get-type a))
dimension _ = 0

{- Returns the domain of the given function type -}
get-domain : Term → Term
get-domain (PtdMap A _) = A
get-domain (PiEI _ A _) = A
get-domain t = Error ("get-domain " ++ print t)

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
mhs t = Error ("mhs " ++ print t)

{- Returns the base point of a type -}
pt : Term → Term
pt (Smash A B) = Proj (pt A) (pt B)
pt (Var s Type) = Pt s
pt (Var s Ptd) = Pt s
pt t = Error ("pt (" ++ print-term-h true t ++ ")")

coh∙ₜ : Term
coh∙ₜ = Var "coh∙" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (PiI "c" Xₜ
                   (Pi "p" a=bₜ (Pi "q" b=cₜ
                   a=cₜ))))))

ap : Term → Term → Term

ptf : Term → Term
ptf (Var f (PtdMap A B)) = Ptf f A B
ptf (Lam s A (Var s' A')) = if (s ==ₛ s') then Idp (Var s A) else Error ("ptfVar " ++ print s ++ " " ++ print s')
ptf (Lam s A (App f@(Var _ (PtdMap Y Z)) (App g@(Var _ (PtdMap X Y')) (Var s' A')))) = if (s ==ₛ s') then
   App (App (AppI (AppI (AppI (AppI coh∙ₜ Z) (App f (App g (pt X)))) (App f (pt Y))) (pt Z)) (ap f (ptf g))) (ptf f)
  else
    Error ("ptfcomp " ++ print s ++ " " ++ print s')
ptf t = Error ("ptf " ++ print t)


find : String → List String → List Term → Maybe (Term × List String × List Term)
find s [] _ = nothing
find s (v ∷ vs) [] = nothing  -- should not happen
find s (v ∷ vs) (t ∷ ts) with s ==ₛ v | find s vs ts
... | true  | _ = just (t , vs , ts)
... | false | nothing = nothing
... | false | just (t' , vs' , ts') = just (t' , v ∷ vs' , t ∷ ts')

{- Substitution -}
_[_/_] : Term → Term → String → Term
{- Simultaneous substitution -}
_[_/[]_] : Term → List Term → List String → Term
{- General simultaneous substitution with specified App(I)Reduce -}
_[_/g[]_]⟨_/_⟩ : Term → List Term → List String → (Term → Term → Term) → (Term → Term → Term) → Term
_[_/g_]⟨_/_⟩ : Term → Term → String → (Term → Term → Term) → (Term → Term → Term) → Term
{- Apply the first term to the second term, performing β-reduction if needed -}
AppReduce : Term → Term → Term
{- Same for implicit application -}
AppIReduce : Term → Term → Term

u [ t / s ] = u [ [ t ] /[] [ s ] ]
u [ t /[] s ] = u [ t /g[] s ]⟨ AppReduce / AppIReduce ⟩
u [ t /g s ]⟨ X / XI ⟩ = u [ [ t ] /g[] [ s ] ]⟨ X / XI ⟩

{- Note: in [Lam s A u], [s] should *not* occur in [A], because [Var s A]
         probably occurs in [u] and the [s] will get captured there.
-}
{-# TERMINATING #-}
u [ [] /g[] [] ]⟨ X / XI ⟩ = u
(Var s' u) [ t /g[] s ]⟨ X / XI ⟩ with find s' s t
... | nothing = Var s' (u [ t /g[] s ]⟨ X / XI ⟩)
... | just (k , _ , _) = k
(Dec dec params) [ t /g[] s ]⟨ X / XI ⟩ = Dec dec (map (_[ t /g[] s ]⟨ X / XI ⟩) params)
(App u arg) [ t /g[] s ]⟨ X / XI ⟩ = X (u [ t /g[] s ]⟨ X / XI ⟩) (arg [ t /g[] s ]⟨ X / XI ⟩)
(AppI u arg) [ t /g[] s ]⟨ X / XI ⟩ = XI (u [ t /g[] s ]⟨ X / XI ⟩) (arg [ t /g[] s ]⟨ X / XI ⟩)
(Proj a b) [ t /g[] s ]⟨ X / XI ⟩ = Proj (a [ t /g[] s ]⟨ X / XI ⟩) (b [ t /g[] s ]⟨ X / XI ⟩)
(BaseL A B) [ t /g[] s ]⟨ X / XI ⟩ = BaseL (A [ t /g[] s ]⟨ X / XI ⟩) (B [ t /g[] s ]⟨ X / XI ⟩)
(BaseR A B) [ t /g[] s ]⟨ X / XI ⟩ = BaseR (A [ t /g[] s ]⟨ X / XI ⟩) (B [ t /g[] s ]⟨ X / XI ⟩)
(GlueL A B a) [ t /g[] s ]⟨ X / XI ⟩ = GlueL (A [ t /g[] s ]⟨ X / XI ⟩) (B [ t /g[] s ]⟨ X / XI ⟩) (a [ t /g[] s ]⟨ X / XI ⟩)
(GlueR A B b) [ t /g[] s ]⟨ X / XI ⟩ = GlueR (A [ t /g[] s ]⟨ X / XI ⟩) (B [ t /g[] s ]⟨ X / XI ⟩) (b [ t /g[] s ]⟨ X / XI ⟩)
(Id a b) [ t /g[] s ]⟨ X / XI ⟩ = Id (a [ t /g[] s ]⟨ X / XI ⟩) (b [ t /g[] s ]⟨ X / XI ⟩)
(Idp a) [ t /g[] s ]⟨ X / XI ⟩ = Idp (a [ t /g[] s ]⟨ X / XI ⟩)
(Square p q r ss) [ t /g[] s ]⟨ X / XI ⟩ = Square (p [ t /g[] s ]⟨ X / XI ⟩) (q [ t /g[] s ]⟨ X / XI ⟩) (r [ t /g[] s ]⟨ X / XI ⟩) (ss [ t /g[] s ]⟨ X / XI ⟩)
(Ids a) [ t /g[] s ]⟨ X / XI ⟩ = Ids (a [ t /g[] s ]⟨ X / XI ⟩)
(Pt s') [ t /g[] s ]⟨ X / XI ⟩ with find s' s t
... | nothing = Pt s'
... | just (k , _ , _) = pt k
(Ptf s' A B) [ t /g[] s ]⟨ X / XI ⟩ with find s' s t
... | nothing = Ptf s' (A [ t /g[] s ]⟨ X / XI ⟩) (B [ t /g[] s ]⟨ X / XI ⟩)
... | just (k , _ , _) = ptf k
(Lam s' A u) [ t /g[] s ]⟨ X / XI ⟩ with find s' s t
... | nothing = let s'' = fresh (A ∷ (t ++ₗ map (λ k → Var k Type) s)) s' in
                Lam s'' (A [ t /g[] s ]⟨ X / XI ⟩) (u [ Var s'' A /g s' ]⟨ X / XI ⟩ [ t /g[] s ]⟨ X / XI ⟩)
... | just (k , vs , ts) =
                let s'' = fresh (A ∷ (ts ++ₗ map (λ k → Var k Type) vs)) s' in
                Lam s'' (A [ ts /g[] vs ]⟨ X / XI ⟩) (u [ Var s'' A /g s' ]⟨ X / XI ⟩ [ ts /g[] vs ]⟨ X / XI ⟩)
(PiEI s' A B) [ t /g[] s ]⟨ X / XI ⟩ with find (unArg s') s t
... | nothing = let s'' = fresh (A ∷ (t ++ₗ map (λ k → Var k Type) s)) (unArg s') in
                PiEI (hiding-app s' s'') (A [ t /g[] s ]⟨ X / XI ⟩) (B [ Var s'' A /g unArg s' ]⟨ X / XI ⟩ [ t /g[] s ]⟨ X / XI ⟩)
... | just (k , vs , ts) =
                let s'' = fresh (A ∷ (ts ++ₗ map (λ k → Var k Type) vs)) (unArg s') in
                PiEI (hiding-app s' s'') (A [ ts /g[] vs ]⟨ X / XI ⟩) (B [ Var s'' A /g unArg s' ]⟨ X / XI ⟩ [ ts /g[] vs ]⟨ X / XI ⟩)
Ptd [ t /g[] s ]⟨ X / XI ⟩ = Ptd
Type [ t /g[] s ]⟨ X / XI ⟩ = Type
(PtdMap A B) [ t /g[] s ]⟨ X / XI ⟩ = PtdMap (A [ t /g[] s ]⟨ X / XI ⟩) (B [ t /g[] s ]⟨ X / XI ⟩)
(Smash A B) [ t /g[] s ]⟨ X / XI ⟩ = Smash (A [ t /g[] s ]⟨ X / XI ⟩) (B [ t /g[] s ]⟨ X / XI ⟩)
(Error x) [ t /g[] s ]⟨ X / XI ⟩ = Error ("subst " ++ x)

{- β-reduction -}
AppReduce (Lam s A t) u = t [ u / s ]
{- ap f idp = idp -}
AppReduce (AppI (AppI (App (AppI (AppI (Var "ap" _) A) B) f) a) b) (Idp u) = Idp (AppReduce f u)
AppReduce t u = App t u

AppIReduce (Lam s A t) u = t [ u / s ]
AppIReduce t u = AppI t u

AppEIReduce : Term → Arg Term → Term
AppEIReduce t (Exp u) = AppReduce t u
AppEIReduce t (Imp u) = AppIReduce t u

_[_/[]CS_] : ContractibleSystem → List Term → List String → ContractibleSystem
PtdCS u [ t /[]CS s ] = PtdCS (u [ t /[] s ])
PtdMapCS u [ t /[]CS s ] = PtdMapCS (u [ t /[] s ])
DoublePtdMapCS u v [ t /[]CS s ] = DoublePtdMapCS (u [ t /[] s ]) (v [ t /[] s ])
SmashCS cA cB [ t /[]CS s ] = SmashCS (cA [ t /[]CS s ]) (cB [ t /[]CS s ])

Pi[] : List (Arg String × Term) → Term → Term
Pi[] [] u = u
Pi[] ((s , t) ∷ ts) u = PiEI s t (Pi[] ts u)

PiE[] : List (String × Term) → Term → Term
PiE[] [] u = u
PiE[] ((s , t) ∷ ts) u = Pi s t (PiE[] ts u)

get-type-declaration : Declaration → List Term → Term
get-type-declaration dec p =
  (PiE[] [ get-arg dec ] (type dec)) [ p /[] map proj₁ (params dec) ]

{- The first argument is a function type, the second an argument, return the return type -}
app-type : Term → Term → Term
app-type (PiEI x A B) t = if is-fresh-in (unArg x) t then
                            B [ t / unArg x ]
                          else
                            let x' = fresh (A ∷ B ∷ t ∷ []) (unArg x) in
                            B [ Var x' A / (unArg x) ] [ t / x' ]
app-type (PtdMap A B) t = B
app-type t u = Error ("app-type " ++ print t ++ " to " ++ print u)

{- Get the type of a term -}
get-type (Var s t) = t
get-type (Dec dec params) = get-type-declaration dec params
get-type (AppEI t arg) = app-type (get-type t) (unArg arg)
get-type (Proj a b) = Smash (get-type a) (get-type b)
get-type (BaseL A B) = Smash A B
get-type (BaseR A B) = Smash A B
get-type (GlueL A B a) = Id (Proj a (pt B)) (BaseL A B)
get-type (GlueR A B b) = Id (Proj (pt A) b) (BaseR A B)
get-type (Id a b) = Type
get-type (Idp a) = Id a a
get-type (Square p q r s) = Type
get-type (Ids a) = Square (Idp a) (Idp a) (Idp a) (Idp a)
get-type (Pt s) = Var s Type
get-type (Ptf f A B) = Id (App (Var f (PtdMap A B)) (pt A)) (pt B)
get-type Ptd = Type
get-type Type = Type
get-type (PtdMap A B) = Type
get-type (Smash A B) = Type
get-type (Lam s A u) = Pi s A (get-type u)
get-type (Error s) = Error ("get-type " ++ s)
get-type (PiEI _ _ _) = Type

{- The [ap] term -}
kₜA→B = Var "k" (Pi "_" Aₜ Bₜ)
apₜ = Var "ap" (PiI "A" Type (PiI "B" Type (Pi "k" (Pi "_" Aₜ Bₜ) (PiI "a" Aₜ (PiI "a'" Aₜ (Pi "p" (Id aₜA a'ₜA) (Id (App kₜA→B aₜA) (App kₜA→B a'ₜA))))))))

{- Returns the term corresponding to [ap f p]
   We can do that easily because we can figure out the complete type of [f] and [p]
-}
ap f p =
  let A = get-domain (get-type f) in
  let B = get-codomain (get-type f) in
  let T = get-type p in
  let a = lhs T in
  let b = rhs T in
  AppReduce (AppI (AppI (App (AppI (AppI apₜ A) B) f) a) b) p


{- α-equivalence -}
{-# TERMINATING #-}
_==ₜ_ : Term → Term → Bool
Var s t ==ₜ Var s' t' = (s ==ₛ s') ∧ (t ==ₜ t')
Dec dec params ==ₜ Dec dec' params' = (name dec ==ₛ name dec') ∧ (and (zipWith (_==ₜ_) params params'))
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
Pt s ==ₜ Pt s' = s ==ₛ s'
Ptf f A B ==ₜ Ptf f' A' B' = (f ==ₛ f') ∧ (A ==ₜ A') ∧ (B ==ₜ B')
Lam s A t ==ₜ Lam s' A' t' =
  if s ==ₛ s' then (A ==ₜ A') ∧ (t ==ₜ t')
  else let s'' = fresh (Var s A ∷ Var s' A' ∷ t ∷ t' ∷ []) s in
       (A ==ₜ A') ∧ (t [ Var s'' A / s ]) ==ₜ (t' [ Var s'' A / s' ])
-- TODO: implicit Pi and explicit Pi are considered equal
PiEI s A B ==ₜ PiEI s' A' B' = 
  if unArg s ==ₛ unArg s' then (A ==ₜ A') ∧ (B ==ₜ B')
  else let s'' = fresh (Var (unArg s) A ∷ Var (unArg s') A' ∷ B ∷ B' ∷ []) (unArg s) in
       (A ==ₜ A') ∧ (B [ Var s'' A / unArg s ]) ==ₜ (B' [ Var s'' A / unArg s' ])
Ptd ==ₜ Ptd = true
Ptd ==ₜ Type = true
Type ==ₜ Ptd = true
Type ==ₜ Type = true
PtdMap A B ==ₜ PtdMap A' B' = A ==ₜ A' ∧ B ==ₜ B'
PtdMap A B ==ₜ Pi _ A' B' = A ==ₜ A' ∧ B ==ₜ B'
Pi _ A B ==ₜ PtdMap A' B' = A ==ₜ A' ∧ B ==ₜ B'
Smash A B ==ₜ Smash A' B' = A ==ₜ A' ∧ B ==ₜ B'
_ ==ₜ _ = false





{- The declarations we want to generate -}

{- Commutativity of the smash product -}
σ-dec : Declaration
name σ-dec = "σ"
params σ-dec = ("A" , Ptd) ∷ ("B", Ptd) ∷ []
argtype σ-dec = A∧B
type σ-dec = Smash Bₜ Aₜ
def σ-dec = Proj bₜB aₜA
CS-codomain σ-dec = SmashCS (PtdCS Bₜ) (PtdCS Aₜ)

{- The identity function defined by induction -}
id-dec : Declaration
name id-dec = "idsmash"
params id-dec = ("A" , Ptd) ∷ ("B", Ptd) ∷ []
argtype id-dec = A∧B
type id-dec = Smash Aₜ Bₜ
def id-dec = Proj aₜA bₜB
CS-codomain id-dec = SmashCS (PtdCS Aₜ) (PtdCS Bₜ)

{- Functoriality of the smash product -}
∧-map-dec : Declaration
name ∧-map-dec = "∧-map"
params ∧-map-dec = ("A", Ptd) ∷ ("A'", Ptd) ∷ ("B", Ptd) ∷ ("B'", Ptd) ∷ ("f", PtdMap Aₜ A'ₜ) ∷ ("g" , PtdMap Bₜ B'ₜ) ∷ []
argtype ∧-map-dec = A∧B
type ∧-map-dec = Smash A'ₜ B'ₜ
def ∧-map-dec = Proj (App fₜA→∙A' aₜA) (App gₜB→∙B' bₜB)
CS-codomain ∧-map-dec = SmashCS (PtdMapCS fₜA→∙A') (PtdMapCS gₜB→∙B')

{- Associativity of the smash product -}
α-dec : Declaration
name α-dec = "α"
params α-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype α-dec = [A∧B]∧C
type α-dec = Smash Aₜ (Smash Bₜ Cₜ)
def α-dec = Proj aₜA (Proj bₜB cₜC)
CS-codomain α-dec = SmashCS (PtdCS Aₜ) (SmashCS (PtdCS Bₜ) (PtdCS Cₜ))

{- Inverse associator -}
αinv-dec : Declaration
name αinv-dec = "α⁻¹"
params αinv-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype αinv-dec = A∧[B∧C]
type αinv-dec = Smash (Smash Aₜ Bₜ) Cₜ
def αinv-dec = Proj (Proj aₜA bₜB) cₜC
CS-codomain αinv-dec = SmashCS (SmashCS (PtdCS Aₜ) (PtdCS Bₜ)) (PtdCS Cₜ)

{- Some random coherence -}
β-dec : Declaration
name β-dec = "β"
params β-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype β-dec = [A∧B]∧C
type β-dec = Smash (Smash Cₜ Bₜ) Aₜ
def β-dec = Proj (Proj cₜC bₜB) aₜA
CS-codomain β-dec = SmashCS (SmashCS (PtdCS Cₜ) (PtdCS Bₜ)) (PtdCS Aₜ)

{- Some random complicated coherence -}
γ-dec : Declaration
name γ-dec = "γ"
params γ-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype γ-dec = [A∧B]∧C
type γ-dec = Smash Aₜ (Smash (Smash Cₜ Bₜ) (Smash Aₜ Cₜ))
def γ-dec = Proj aₜA (Proj (Proj cₜC bₜB) (Proj aₜA cₜC))
CS-codomain γ-dec = SmashCS (PtdCS Aₜ) (SmashCS (SmashCS (PtdCS Cₜ) (PtdCS Bₜ)) (SmashCS (PtdCS Aₜ) (PtdCS Cₜ)))


{- MacLane’s pentagon -}
pentagon-dec : Declaration
name pentagon-dec = "pentagon"
params pentagon-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ ("D", Ptd) ∷ []
argtype pentagon-dec = [[A∧B]∧C]∧D
type pentagon-dec = Id (App (Dec ∧-map-dec (Aₜ ∷ Aₜ ∷ Smash (Smash Bₜ Cₜ) Dₜ ∷ Smash Bₜ (Smash Cₜ Dₜ) ∷ Lam "x" Aₜ (Var "x" Aₜ) ∷ Dec α-dec (Bₜ ∷ Cₜ ∷ Dₜ ∷ [])∷ []))
                            (App (Dec α-dec (Aₜ ∷ Smash Bₜ Cₜ ∷ Dₜ ∷ []))
                                 (App (Dec ∧-map-dec (Smash (Smash Aₜ Bₜ) Cₜ ∷ Smash Aₜ (Smash Bₜ Cₜ) ∷ Dₜ ∷ Dₜ ∷ Dec α-dec (Aₜ ∷ Bₜ ∷ Cₜ ∷ []) ∷ Lam "y" Dₜ (Var "y" Dₜ) ∷ []))
                                      (Var "x" (argtype-to-type [[A∧B]∧C]∧D)))))
                       (App (Dec α-dec (Aₜ ∷ Bₜ ∷ Smash Cₜ Dₜ ∷ []))
                            (App (Dec α-dec (Smash Aₜ Bₜ ∷ Cₜ ∷ Dₜ ∷ []))
                                 (Var "x" (argtype-to-type [[A∧B]∧C]∧D))))
def pentagon-dec = Idp (Proj aₜA (Proj bₜB (Proj cₜC dₜD)))
CS-codomain pentagon-dec = SmashCS (SmashCS (SmashCS (PtdCS Aₜ) (PtdCS Bₜ)) (PtdCS Cₜ)) (PtdCS Dₜ)

{- Functoriality preserves identities -}
∧-map-id-dec : Declaration
name ∧-map-id-dec = "∧-map-id"
params ∧-map-id-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ []
argtype ∧-map-id-dec = A∧B
type ∧-map-id-dec = Id (App (Dec ∧-map-dec (Aₜ ∷ Aₜ ∷ Bₜ ∷ Bₜ ∷ Lam "y" Aₜ (Var "y" Aₜ) ∷ Lam "z" Bₜ (Var "z" Bₜ) ∷ []))
                            (Var "x" (argtype-to-type A∧B)))
                       (Var "x" (argtype-to-type A∧B))
def ∧-map-id-dec = Idp (Proj aₜA bₜB)
CS-codomain ∧-map-id-dec = SmashCS (PtdCS Aₜ) (PtdCS Bₜ)

{- Symmetry -}
σ-triangle-dec : Declaration
name σ-triangle-dec = "σ-triangle"
params σ-triangle-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ []
argtype σ-triangle-dec = A∧B
type σ-triangle-dec = Id (App (Dec σ-dec (Bₜ ∷ Aₜ ∷ []))
                              (App (Dec σ-dec (Aₜ ∷ Bₜ ∷ []))
                                   (Var "x" (argtype-to-type A∧B))))
                         (Var "x" (argtype-to-type A∧B))
def σ-triangle-dec = Idp (Proj aₜA bₜB)
CS-codomain σ-triangle-dec = SmashCS (PtdCS Aₜ) (PtdCS Bₜ)

{- Double symmetry! -}
σ-2triangle-dec : Declaration
name σ-2triangle-dec = "σ-2triangle"
params σ-2triangle-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ []
argtype σ-2triangle-dec = A∧B
type σ-2triangle-dec = Id (App (Dec σ-dec (Bₜ ∷ Aₜ ∷ []))
                               (App (Dec σ-dec (Aₜ ∷ Bₜ ∷ []))
                                    (App (Dec σ-dec (Bₜ ∷ Aₜ ∷ []))
                                         (App (Dec σ-dec (Aₜ ∷ Bₜ ∷ []))
                                              (Var "x" (argtype-to-type A∧B))))))
                          (Var "x" (argtype-to-type A∧B))
def σ-2triangle-dec = Idp (Proj aₜA bₜB)
CS-codomain σ-2triangle-dec = SmashCS (PtdCS Aₜ) (PtdCS Bₜ)

{- Naturality of σ -}
σ-nat-dec : Declaration
name σ-nat-dec = "σ-nat"
params σ-nat-dec = ("A", Ptd) ∷ ("A'", Ptd) ∷ ("B", Ptd) ∷ ("B'", Ptd) ∷ ("f", PtdMap Aₜ A'ₜ) ∷ ("g" , PtdMap Bₜ B'ₜ) ∷ []
argtype σ-nat-dec = A∧B
type σ-nat-dec = Id (App (Dec σ-dec (A'ₜ ∷ B'ₜ ∷ []))
                         (App (Dec ∧-map-dec (Aₜ ∷ A'ₜ ∷ Bₜ ∷ B'ₜ ∷ fₜA→∙A' ∷ gₜB→∙B' ∷ []))
                              (Var "x" (argtype-to-type A∧B))))
                    (App (Dec ∧-map-dec (Bₜ ∷ B'ₜ ∷ Aₜ ∷ A'ₜ ∷ gₜB→∙B' ∷ fₜA→∙A' ∷ []))
                         (App (Dec σ-dec (Aₜ ∷ Bₜ ∷ []))
                              (Var "x" (argtype-to-type A∧B))))
def σ-nat-dec = Idp (Proj (App gₜB→∙B' bₜB) (App fₜA→∙A' aₜA))
CS-codomain σ-nat-dec = SmashCS (PtdMapCS gₜB→∙B') (PtdMapCS fₜA→∙A')

-- {- Functoriality of smash commutes with composition -}
-- ∧-map-comp-dec : Declaration₁
-- name ∧-map-comp-dec = "∧-map-comp"
-- params ∧-map-comp-dec = ("A", Ptd) ∷ ("A'", Ptd) ∷ ("A''", Ptd) ∷ ("B", Ptd) ∷ ("B'", Ptd) ∷ ("B''", Ptd) ∷ ("f", PtdMap Aₜ A'ₜ) ∷ ("f'", PtdMap A'ₜ A''ₜ) ∷ ("g" , PtdMap Bₜ B'ₜ) ∷ ("g'" , PtdMap B'ₜ B''ₜ) ∷ []
-- argtype ∧-map-comp-dec = A∧B
-- typelhs ∧-map-comp-dec = [ ∧-map-dec , < Aₜ > ∷ < A''ₜ > ∷ < Bₜ > ∷ < B''ₜ > ∷ < Lam "z" Aₜ (App f'ₜA'→∙A'' (App fₜA→∙A' (Var "z" Aₜ))) > ∷ < Lam "z" Bₜ (App g'ₜB'→∙B'' (App gₜB→∙B' (Var "z" Bₜ))) > ∷ [] ]∷
--                          []
-- typerhs ∧-map-comp-dec = [ ∧-map-dec , < Aₜ > ∷ < A'ₜ > ∷ < Bₜ > ∷ < B'ₜ > ∷ < fₜA→∙A' > ∷ < gₜB→∙B' > ∷ [] ]∷
--                          [ ∧-map-dec , < A'ₜ > ∷ < A''ₜ > ∷ < B'ₜ > ∷ < B''ₜ > ∷ < f'ₜA'→∙A'' > ∷ < g'ₜB'→∙B'' > ∷ [] ]∷
--                          []
-- def ∧-map-comp-dec = Lam "a" Aₜ (Lam "b" Bₜ (Idp (Error "TODO")))
-- CS-codomain ∧-map-comp-dec = SmashCS (DoublePtdMapCS fₜA→∙A' f'ₜA'→∙A'') (DoublePtdMapCS gₜB→∙B' g'ₜB'→∙B'')

{- α is a right inverse to α⁻¹ -}
α-rinv-dec : Declaration
name α-rinv-dec = "α-rinv"
params α-rinv-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
argtype α-rinv-dec = [A∧B]∧C
type α-rinv-dec = Id (App (Dec αinv-dec (Aₜ ∷ Bₜ ∷ Cₜ ∷ []))
                          (App (Dec α-dec (Aₜ ∷ Bₜ ∷ Cₜ ∷ []))
                               (Var "x" (argtype-to-type [A∧B]∧C))))
                     (Var "x" (argtype-to-type [A∧B]∧C))
def α-rinv-dec = Idp (Proj (Proj aₜA bₜB) cₜC)
CS-codomain α-rinv-dec = SmashCS (SmashCS (PtdCS Aₜ) (PtdCS Bₜ)) (PtdCS Cₜ)

-- {- α is a left inverse to α⁻¹ -}
-- α-linv-dec : Declaration₁
-- name α-linv-dec = "α-linv"
-- params α-linv-dec = ("A", Ptd) ∷ ("B", Ptd) ∷ ("C", Ptd) ∷ []
-- argtype α-linv-dec = A∧[B∧C]
-- typelhs α-linv-dec = [ αinv-dec , < Aₜ > ∷ < Bₜ > ∷ < Cₜ > ∷ [] ]∷
--                      [ α-dec , < Aₜ > ∷ < Bₜ > ∷ < Cₜ > ∷ [] ]∷
--                      []
-- typerhs α-linv-dec = idFun (Smash Aₜ (Smash Bₜ Cₜ))
-- def α-linv-dec = Lam "a" Aₜ (Lam "b" Bₜ (Lam "c" Cₜ (Idp (Proj aₜA (Proj bₜB cₜC)))))
-- CS-codomain α-linv-dec = SmashCS (PtdCS Aₜ) (SmashCS (PtdCS Bₜ) (PtdCS Cₜ))

data Uncoh : Set where
  <_> : Term → Uncoh
  Coh : String → Term → List (Arg Term) → Uncoh

print-uncoh : Uncoh → String
print-uncoh < t > = print t
print-uncoh (Coh s t args) = "Coh " ++ s ++ print-term-P t ++ " " ++ print (map unArg args)

instance
  Uncohₚ : Printable Uncoh
  Uncohₚ = record { print-p = λ _ → print-uncoh }

uncoh : Term → Uncoh
uncoh t = uncoh-aux t []  where

  uncoh-aux : Term → List (Arg Term) → Uncoh
  uncoh-aux (Var s t) l = Coh s t l
  uncoh-aux (AppEI f arg) l = uncoh-aux f (arg ∷ l)
  uncoh-aux _ l = < t >

App[] : Term → List (Arg Term) → Term
App[] t [] = t
App[] t (u ∷ us) = App[] (AppEIReduce t u) us

AppE[] : Term → List Term → Term
AppE[] t [] = t
AppE[] t (u ∷ us) = AppE[] (AppReduce t u) us

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

{- Figure out the type of a contractible system -}
get-type-of-CS : ContractibleSystem → Term
get-type-of-CS (PtdCS A) = A
get-type-of-CS (PtdMapCS f) = get-codomain (get-type f)
get-type-of-CS (DoublePtdMapCS f g) = get-codomain (get-type g)
get-type-of-CS (SmashCS cA cB) = Smash (get-type-of-CS cA) (get-type-of-CS cB)

{- Returns [true] if the argument is a point (of dimension 0) in the contractible system -}
is-in-CS : ContractibleSystem → Term → Bool
is-in-CS (PtdCS A) u = u ==ₜ pt A

is-in-CS (PtdMapCS f) u =
  let T = get-type f in
  let A = get-domain T in
  let B = get-codomain T in
  (u ==ₜ pt B) ∨ (u ==ₜ App f (pt A))

is-in-CS (DoublePtdMapCS f g) u =
  let T = get-type f in
  let A = get-domain T in
  let B = get-codomain T in
  let T' = get-type g in
  let C = get-codomain T' in
  (u ==ₜ pt C) ∨ (u ==ₜ App g (pt B)) ∨ (u ==ₜ App g (App f (pt A)))

is-in-CS (SmashCS cA cB) (Proj a b) = (is-in-CS cA a) ∨ (is-in-CS cB b)
is-in-CS (SmashCS cA cB) (BaseL _ _) = true
is-in-CS (SmashCS cA cB) (BaseR _ _) = true
is-in-CS (SmashCS cA cB) _ = false

{- Returns true if the term is an error (not sure if that’s really used/needed) -}
is-error : Term → Bool
is-error (Error s) = true
is-error _ = false

{-# TERMINATING #-}
get-root-type : Term → Term
get-root-type (Id a b) = get-root-type (get-type a)
get-root-type (Square p q r s) = get-root-type (get-type p)
get-root-type t = t

{- Given a function [f] and an element [u] in one of the iterated identity
   types of the domain of [f], returns the iterated ap of [f] applied to [u].
-}
{-# NON_TERMINATING #-}
ap* : Term → Term → Term
ap* f u =
  let A = get-domain (get-type f) in
  let T = get-type u in
  if u ==ₜ A then -- Special case, so that we can simply map ap* on the arguments of a coherence
    get-codomain (get-type f)
  else if not (get-root-type T ==ₜ A) then
    Error ("ap* " ++ print (get-root-type T) ++ " different from " ++ print A ++ "[" ++ print f ++ " / " ++ print u ++ "]")
  else if T ==ₜ A then
    AppReduce f u
  else
    let z = fresh (f ∷ u ∷ []) "z" in
    ap (Lam z (mhs T) (ap* f (Var z (mhs T)))) u

ap*Arg : Term → Arg Term → Arg Term
ap*Arg f (Exp u) = Exp (ap* f u)
ap*Arg f (Imp u) = Imp (ap* f u)

{- Various coherence terms needed later -}

coh∙!ₜ : Term
coh∙!ₜ = Var "coh∙!" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (PiI "c" Xₜ
                     (Pi "p" a=bₜ (Pi "q" c=bₜ
                     a=cₜ))))))

coh!∙ₜ : Term
coh!∙ₜ = Var "coh!∙" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (PiI "c" Xₜ
                     (Pi "p" b=aₜ (Pi "q" b=cₜ
                     a=cₜ))))))

coh∙∙!ₜ : Term
coh∙∙!ₜ = Var "coh∙∙!" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (PiI "c" Xₜ (PiI "d" Xₜ
                       (Pi "p" a=bₜ (Pi "q" b=cₜ (Pi "r" d=cₜ
                       a=dₜ))))))))

coh!∙∙ₜ : Term
coh!∙∙ₜ = Var "coh!∙∙" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (PiI "c" Xₜ (PiI "d" Xₜ
                       (Pi "p" b=aₜ (Pi "q" b=cₜ (Pi "r" c=dₜ
                       a=dₜ))))))))

{- And the corresponding helper functions -}

coh∙! : Term → Term → Term
coh∙! p q =
  let T = get-type p in
  let a = lhs T in
  let b = rhs T in
  let X = mhs T in
  let T' = get-type q in
  let c = lhs T' in
  App (App (AppI (AppI (AppI (AppI coh∙!ₜ X) a) b) c) p) q

coh∙ : Term → Term → Term
coh∙ p q =
  let T = get-type p in
  let a = lhs T in
  let b = rhs T in
  let X = mhs T in
  let T' = get-type q in
  let c = rhs T' in
  App (App (AppI (AppI (AppI (AppI coh∙ₜ X) a) b) c) p) q

coh!∙ : Term → Term → Term
coh!∙ p q =
  let T = get-type p in
  let a = rhs T in
  let b = lhs T in
  let X = mhs T in
  let T' = get-type q in
  let c = rhs T' in
  App (App (AppI (AppI (AppI (AppI coh!∙ₜ X) a) b) c) p) q

coh∙∙! : Term → Term → Term → Term
coh∙∙! p q r =
  let T = get-type p in
  let a = lhs T in
  let b = rhs T in
  let X = mhs T in
  let T' = get-type r in
  let c = rhs T' in
  let d = lhs T' in
  App (App (App (AppI (AppI (AppI (AppI (AppI coh∙∙!ₜ X) a) b) c) d) p) q) r

coh!∙∙ : Term → Term → Term → Term
coh!∙∙ p q r =
  let T = get-type p in
  let a = rhs T in
  let b = lhs T in
  let X = mhs T in
  let T' = get-type r in
  let c = lhs T' in
  let d = rhs T' in
  App (App (App (AppI (AppI (AppI (AppI (AppI coh!∙∙ₜ X) a) b) c) d) p) q) r


Yₜ = Var "Y" Type
fₜX→Y = Var "f" (Pi "_" Xₜ Yₜ)

vars : List (Arg String × Term) → List (Arg Term)
vars = map (λ {(s , t) → hiding-app s (Var (unArg s) t)})

apcohtype : String → Term → Term
apcohtype coh t =
  let (Δ , T) = unPi t in

  Pi[] ((Imp "X", Type) ∷ (Imp "Y", Type) ∷ (Exp "f", Pi "_" Xₜ Yₜ) ∷ tail Δ)
       (Id (ap* fₜX→Y (App[] (Var coh t) (vars Δ)))
           (App[] (Var coh t) (map (ap*Arg fₜX→Y) (vars Δ))))

{- Remove all duplicates (with respect to _==ₜ_), not necessarily adjacent
   We always keep the first one, and we keep the order
-}
{-# TERMINATING #-}
uniq : List Term → List Term
uniq [] = []
uniq (t ∷ ts) = t ∷ uniq (kill-all t ts) where
  kill-all : Term → List Term → List Term
  kill-all _ [] = []
  kill-all t (u ∷ ts) = if t ==ₜ u then kill-all t ts else u ∷ (kill-all t ts)

{- Takes a contractible system and a list of points in it, and returns the
   corresponding list of terms which should corresponds to a contractible context.
   The contractible context (pt, x0, p0, x1, p1, x2, p2) will be represented as
   (x2 , p2) ∷ (x1 , p1) ∷ (x0 , p0) ∷ []

   It only works with a list of points as argument (not an arbitrary list of
   cells), but so far we don’t need more than that anyway.
-}
get-args-from-CS : ContractibleSystem → List Term → List (Term × Term)
get-args-from-CS (PtdCS A) _ = []
get-args-from-CS (PtdMapCS f) _ =
  let T = get-type f in
  let A = get-domain T in
  (App f (pt A) , ptf f) ∷ []
get-args-from-CS (DoublePtdMapCS f g) _ =
  let T = get-type f in
  let A = get-domain T in
  let B = get-codomain T in
  (App g (App f (pt A)), ap g (ptf f)) ∷ (App g (pt B), ptf g) ∷ []
get-args-from-CS (SmashCS cA cB) ts =
  let (lA' , lB' , lcA' , lcB') = extract ts [] [] [] [] in
  let lcA = get-args-from-CS cA lcA' in
  let lcB = get-args-from-CS cB lcB' in
  {- In order for things to be well-ordered, we require that lA/lB
     - start with the base point
     - continue with the elements of lcA/lcB
     - then continue with the rest
     Note that lA/lB are in the reverse direction compared to lcA/lcB -}
  let lA = uniq (pt A ∷ reverse (points-of lcA) ++ₗ lA') in
  let lB = uniq (pt B ∷ reverse (points-of lcB) ++ₗ lB') in
  let init = (BaseL A B , GlueL A B (pt A))
           ∷ (BaseR A B , GlueR A B (pt B))
           ∷ [] in

  add-cA-b-things lcA lcB lB (add-a-cB-things lA lcB init)

  where
    A = get-type-of-CS cA
    B = get-type-of-CS cB

    {- Returns all points (dimension 0) in the argument. TODO: remove -}
    points-of : List (Term × Term) → List Term
    points-of [] = []
    points-of ((t , _) ∷ ts) = if dimension t == 0 then t ∷ points-of ts else points-of ts

    {- Returns a raw list of all the terms that should be taken into
       consideration when building [lA], [lB], [lcA], [lcB]
    -}
    extract : List Term → List Term → List Term → List Term → List Term → (List Term × List Term × List Term × List Term)
    extract [] lA lB lcA lcB = (lA , lB , lcA , lcB)
    extract (Proj a b ∷ ts) lA lB lcA lcB = 
      let lA' = a ∷ lA in
      let lB' = b ∷ lB in
      let lcA' = if is-in-CS cA a then (a ∷ lcA) else lcA in
      let lcB' = if is-in-CS cB b then (b ∷ lcB) else lcB in
      extract ts lA' lB' lcA' lcB'
    extract (BaseL _ _ ∷ ts) lA lB lcA lcB = extract ts lA lB lcA lcB
    extract (BaseR _ _ ∷ ts) lA lB lcA lcB = extract ts lA lB lcA lcB
    extract _ _ _ _ _ = (Error "extract" ∷ [] , Error "extract" ∷ []
                       , Error "extract" ∷ [] , Error "extract" ∷ [])

    other-side : Term × Term → Term
    other-side (x , p) =
      let T = get-type p in
      let a = lhs T in
      let b = rhs T in
      if x ==ₜ a then b
      else if x ==ₜ b then a
      else Error "other-side"

    add-a-cB-things : List Term → List (Term × Term) → List (Term × Term) → List (Term × Term)
    add-a-cB-things [] _ l = l
    add-a-cB-things (a ∷ as) lcB l = add-a-cB-things as lcB (add-a-cB-single a lcB l)

      where
        add-a-cB-single : Term → List (Term × Term) → List (Term × Term) → List (Term × Term)
        add-a-cB-single a lcB l =
          let l' = if (a ==ₜ pt A) then l else (Proj a (pt B) , GlueL A B a) ∷ l in
          concat (map g lcB) ++ₗ l'

          where
            y = fresh (A ∷ B ∷ a ∷ []) "y"
            ap*proja = ap* (Lam y B (Proj a (Var y B)))

            k : Term → Term → Term → Uncoh → List (Term × Term)
            k b q _ < t > = [ (ap*proja b , ap*proja q) ]
            k b q u (Coh s t l) =
              (ap*proja b , ap*proja q) ∷
              (ap*proja u , recoh ("ap" ++ s) (apcohtype s t) (Imp B ∷ Imp (Smash A B) ∷ Exp (Lam y B (Proj a (Var y B))) ∷ tail l)) ∷ []

            g : Term × Term → List (Term × Term)
            g (b , q) =
              let u = other-side (b , q) in
              k b q u (uncoh u)

    add-cA-b-things : List (Term × Term) → List (Term × Term) → List Term → List (Term × Term) → List (Term × Term)
    add-cA-b-things _ _ [] l = l
    add-cA-b-things lcA lcB (b ∷ bs) l = add-cA-b-things lcA lcB bs (add-cA-b-single lcA lcB b l)

      where
        get-direction-and-path : List (Term × Term) → Term → (Bool × Term)
        get-direction-and-path [] t = (true , Error ("get-direction-and-path " ++ print t))
        get-direction-and-path ((a , p) ∷ l) b =
          if lhs (get-type p) ==ₜ b then (true , p)
          else if rhs (get-type p) ==ₜ b then (false , p)
          else get-direction-and-path l b

        xₜA = Var "x" Aₜ
        xₜB = Var "x" Bₜ
        pₜ = Var "p" (Id aₜA a'ₜA)
        qₜ = Var "q" (Id bₜB b'ₜB)

        -- purple-rₜ : Term
        -- purple-rₜ = Var "purple-r" (PiI "A" Type (PiI "B" Type (PiI "b" Bₜ (PiI "b'" Bₜ (Pi "q" (Id Bₜ bₜB b'ₜB)
        --                 (Id (Id (Smash Aₜ Bₜ) (Proj (pt Aₜ) b'ₜB) (BaseR Aₜ Bₜ))
        --                     (GlueR Aₜ Bₜ b'ₜB)
        --                     (coh!∙ (ap (Lam "x" Bₜ (Proj (pt Aₜ) xₜB)) qₜ)
        --                            (GlueR Aₜ Bₜ bₜB))))))))

        -- purple-l-to-rₜ : Term
        -- purple-l-to-rₜ = Var "purple-l-to-r" (PiI "A" Type (PiI "B" Type (PiI "b" Bₜ (PiI "b'" Bₜ (Pi "q" (Id Bₜ bₜB b'ₜB)
        --                      (Id (get-type (App (AppI (AppI (AppI (AppI purple-lₜ Aₜ) Bₜ) bₜB) b'ₜB) qₜ))
        --                          (App (AppI (AppI (AppI (AppI purple-lₜ Aₜ) Bₜ) bₜB) b'ₜB) qₜ)
        --                          (App (App (Var "coh-purple-l-to-r" (Error "niy")) (ap (Lam "x" Bₜ (Proj (pt Aₜ) xₜB)) qₜ))
        --                               (App (AppI (AppI (AppI (AppI purple-rₜ Aₜ) Bₜ) bₜB) b'ₜB) qₜ))))))))

        -- purple-r-to-lₜ : Term
        -- purple-r-to-lₜ = Var "purple-r-to-l" (PiI "A" Type (PiI "B" Type (PiI "b" Bₜ (PiI "b'" Bₜ (Pi "q" (Id Bₜ bₜB b'ₜB)
        --                      (Id (get-type (App (AppI (AppI (AppI (AppI purple-rₜ Aₜ) Bₜ) bₜB) b'ₜB) qₜ))
        --                          (App (AppI (AppI (AppI (AppI purple-rₜ Aₜ) Bₜ) bₜB) b'ₜB) qₜ)
        --                          (App (App (Var "coh-purple-r-to-l" (Error "niy")) (ap (Lam "x" Bₜ (Proj (pt Aₜ) xₜB)) qₜ))
        --                               (App (AppI (AppI (AppI (AppI purple-lₜ Aₜ) Bₜ) bₜB) b'ₜB) qₜ))))))))

        -- coh-purple : {A : Type} {a b c : A} {p : b == c} (q : a == b) {r : a == c} → r == coh∙ q p → p == coh!∙ q r

        purpleₜ : Term
        purpleₜ = Var "purple" (PiI "A" Type (PiI "B" Type (PiI "b" Bₜ (PiI "b'" Bₜ (Pi "q" (Id bₜB b'ₜB)
                        (Id (GlueR Aₜ Bₜ bₜB)
                            (coh∙ (ap (Lam "x" Bₜ (Proj (pt Aₜ) xₜB)) qₜ)
                                  (GlueR Aₜ Bₜ b'ₜB))))))))

        coh-purpleₜ : Term
        coh-purpleₜ = Var "coh-purple" (PiI "X" Type (PiI "a" Xₜ (PiI "b" Xₜ (PiI "c" Xₜ (PiI "p" (Id bₜX cₜX)
                                       (Pi "q" (Id aₜX bₜX) (PiI "r" (Id aₜX cₜX)
                                       (Pi "_" (Id (Var "r" (Id aₜX cₜX)) (coh∙ (Var "q" (Id aₜX bₜX)) (Var "p" (Id bₜX cₜX))))
                                       (Id (Var "p" (Id bₜX cₜX)) (coh!∙ (Var "q" (Id aₜX bₜX)) (Var "r" (Id aₜX cₜX))))))))))))

        purple : List (Term × Term) → Term → Term
        purple lcB b₀ =
          let (d , q) = get-direction-and-path (reverse lcB) b₀ in
          -- let purpleₜ = if d then purple-lₜ else purple-rₜ in
          -- let purple'ₜ = if d then purple-rₜ else purple-lₜ in
          -- let eqₜ = if d then purple-r-to-lₜ else purple-l-to-rₜ in
          let T = get-type q in
          let b = lhs T in
          let b' = rhs T in
          let purple-applied = App (AppI (AppI (AppI (AppI purpleₜ A) B) b) b') q in
          if d then
            purple-applied
          else
            let x = fresh (A ∷ B ∷ q ∷ []) "x" in
            App (AppI (App (AppI (AppI (AppI (AppI (AppI coh-purpleₜ (Smash A B)) (Proj (pt A) b)) (Proj (pt A) b')) (BaseR A B)) (GlueR A B b')) (ap (Lam x B (Proj (pt A) (Var x B))) q)) (GlueR A B b)) purple-applied


 -- (ap (proj pt) q) (purple-lₜ q)

          -- (App (AppI (AppI (AppI (AppI purpleₜ A) B) b) b') q ,
          --  App (AppI (AppI (AppI (AppI purple'ₜ A) B) b) b') q ,
          --  App (AppI (AppI (AppI (AppI eqₜ A) B) b) b') q)

        greenₜ : Term
        greenₜ = Var "green" (PiI "A" Type (PiI "B" Type (PiI "a" Aₜ (PiI "a'" Aₜ (Pi "p" (Id aₜA a'ₜA)
                   (Id (ap (Lam "x" Aₜ (Proj xₜA (pt Bₜ))) pₜ)
                       (coh∙! (GlueL Aₜ Bₜ aₜA) (GlueL Aₜ Bₜ a'ₜA))))))))

        green : Term → Term
        green p =
          let T = get-type p in
          let a = lhs T in
          let a' = rhs T in
          App (AppI (AppI (AppI (AppI greenₜ A) B) a) a') p

        pink-lₜ : Term
        pink-lₜ = Var "pink-l"
                    (PiI "A" Type (PiI "B" Type (PiI "a" Aₜ (PiI "a'" Aₜ (PiI "b" Bₜ (PiI "b'" Bₜ
                      (Pi "p" (Id aₜA a'ₜA) (Pi "q" (Id bₜB b'ₜB)
                    (Id (ap (Lam "x" Aₜ (Proj xₜA bₜB)) pₜ)
                        (coh∙∙! (ap (Lam "x" Bₜ (Proj aₜA xₜB)) qₜ)
                                (ap (Lam "x" Aₜ (Proj xₜA b'ₜB)) pₜ)
                                (ap (Lam "x" Bₜ (Proj a'ₜA xₜB)) qₜ)))))))))))

        pink-rₜ : Term
        pink-rₜ = Var "pink-r"
                    (PiI "A" Type (PiI "B" Type (PiI "a" Aₜ (PiI "a'" Aₜ (PiI "b" Bₜ (PiI "b'" Bₜ
                      (Pi "p" (Id aₜA a'ₜA) (Pi "q" (Id bₜB b'ₜB)
                    (Id (ap (Lam "x" Aₜ (Proj xₜA b'ₜB)) pₜ)
                        (coh!∙∙ (ap (Lam "x" Bₜ (Proj aₜA xₜB)) qₜ)
                                (ap (Lam "x" Aₜ (Proj xₜA bₜB)) pₜ)
                                (ap (Lam "x" Bₜ (Proj a'ₜA xₜB)) qₜ)))))))))))
                               

        pink : List (Term × Term) → Term → Term → Term
        pink lcB p b =
          let (d , q) = get-direction-and-path (reverse lcB) b in
          let pinkₜ = if d then pink-lₜ else pink-rₜ in
          let a = lhs (get-type p) in
          let a' = rhs (get-type p) in
          let b = lhs (get-type q) in
          let b' = rhs (get-type q) in
          App (App (AppI (AppI (AppI (AppI (AppI (AppI pinkₜ A) B) a) a') b) b') p) q

        add-cA-b-single : List (Term × Term) → List (Term × Term) → Term → List (Term × Term) → List (Term × Term)
        add-cA-b-single lcA lcB b l =
          let l' = if (b ==ₜ pt B) then
                     l
                   else if is-in-CS cB b then
                     (GlueR A B b , purple lcB b) ∷ l  -- purple triangle (BROKEN, TODO)
                   else
                     (Proj (pt A) b , GlueR A B b) ∷ l
          in
          concat (map g lcA) ++ₗ l' where

            x = fresh (A ∷ B ∷ b ∷ []) "x"
            ap*proj-b = ap* (Lam x A (Proj (Var x A) b))

            k : Term → Term → Term → Uncoh → List (Term × Term)
            k a p _ < t > = [ (ap*proj-b a , ap*proj-b p) ]
            k a p u (Coh s t l) =
              (ap*proj-b a , ap*proj-b p) ∷
              (ap*proj-b u , recoh ("ap" ++ s) (apcohtype s t) (l ++ₗ (Imp (Smash A B) ∷ Exp (Lam x A (Proj (Var x A) b)) ∷ []))) ∷ []

            g : Term × Term → List (Term × Term)
            g (a , p) =
              if (b ==ₜ pt B) ∧ (dimension (get-type a) == 0) then
                [ (ap*proj-b p , green p) ]  -- green triangle
              else if is-in-CS cB b ∧ (dimension (get-type a) == 0) then
                [ (ap*proj-b p , pink lcB p b) ]  -- pink square (BROKEN, TODO)
              else
                let u = other-side (a , p) in
                k a p u (uncoh u)


get-cells : Term → List Term
get-cells-app : Term → Term → List Term → List Term

get-cells (Id a b) = get-cells a ++ₗ get-cells b
get-cells (Idp a) = get-cells a
get-cells (Square p q r s) = get-cells p ++ₗ get-cells q ++ₗ get-cells r ++ₗ get-cells s
get-cells (Ids a) = get-cells a
get-cells (Proj a b) = Proj a b ∷ []
get-cells (BaseL A B) = []
get-cells (BaseR A B) = []
get-cells (GlueL A B a) = Proj a (pt B) ∷ []
get-cells (GlueR A B b) = Proj (pt A) b ∷ []
get-cells (App f arg) = get-cells-app f arg []
get-cells (AppI f arg) = get-cells-app f arg []
get-cells _ = []

get-cells-app (Var "ap" _) _ _ = []
get-cells-app (Var _ _) t l = get-cells t ++ₗ l
get-cells-app (App f arg) t l = get-cells-app f arg (get-cells t ++ₗ l)
get-cells-app (AppI f arg) t l = get-cells-app f arg (get-cells t ++ₗ l)
get-cells-app _ _ _ = Error "get-cells-app" ∷ []

-- [is-in l t] checks if [t] is the second element of an element of [l], and
-- in that case it returns the corresponding string.
is-in : List (String × Term × Term) → Term → Maybe String
is-in ((s , u , _) ∷ xs) t = if u ==ₜ t then just s else is-in xs t 
is-in [] t = nothing

-- Auxiliary function
asubst : List (String × Term × Term) → Term → Term

antisubst : List (String × Term × Term) → Term → Term
antisubst l t with is-in l t
... | just s = Var s (get-type t)
... | nothing = asubst l t

asubst l (Var s' u) = Var s' u
asubst l (App u arg) = AppReduce (antisubst l u) (antisubst l arg)
asubst l (AppI u arg) = AppIReduce (antisubst l u) (antisubst l arg)
asubst l (Id a b) = Id (antisubst l a) (antisubst l b)
asubst l (Idp a) = Idp (antisubst l a)
asubst l (Square p q r s) = Square (antisubst l p) (antisubst l q) (antisubst l r) (antisubst l s)
asubst l (Ids a) = Ids (antisubst l a)
asubst l t = Error ("asubst " ++ print t)

contractibilify-once : String → List (String × Term × Term) → Term → List (String × Term × Term)
contractibilify-once s l t = trace ("ping " ++ s ++ " / " ++ print t) ((s , t , antisubst l (get-type t)) ∷ l)  where

-- (s, t, t') in the results represents a variable named [s], corresponding to [t] in the real world
-- and whose type in the coherence is [t']
contractibilify : Term → List (Term × Term) → List (String × Term × Term)
contractibilify A [] = ("a" , pt A , Xₜ) ∷ ("X" , A , Type) ∷ []
contractibilify A ((t , t') ∷ ts) = contractibilify-once ("p" ++ showℕ (length ts))
                                      (contractibilify-once ("x" ++ showℕ (length ts))
                                        (contractibilify A ts) t) t'

get-params : List (String × Term × Term) → List (Arg String × Term)
get-params l = map (λ {(a , b , c) → (Exp a , c)}) l

get-args : List (String × Term × Term) → List Term
get-args l = map (λ {(a , b , c) → b}) l

patternify : {A : Set} → List A → String
patternify (_ ∷ _ ∷ a ∷ b ∷ t) = patternify (a ∷ b ∷ t) ++ " _ idp"
patternify _ = "X a"

-- TODO: Use the other things instead of [to-pi-type] and [to-app] ?

to-pi-type : List (String × Term) → Term → Term
to-pi-type [] t = t
to-pi-type ((s , u) ∷ xs) t = Pi s u (to-pi-type xs t)

-- You need to reverse the list first!
to-app : Term → List Term → Term
to-app f [] = f
to-app f (a ∷ as) = to-app (AppReduce f a) as

{-# TERMINATING #-}
occurs : String → Term → Bool
occurs s (Var s' t) = (s ==ₛ s') ∨ occurs s t
occurs s (Dec dec params) = or (map (occurs s) params)
occurs s (App t arg) = occurs s t ∨ occurs s arg
occurs s (AppI t arg) = occurs s t ∨ occurs s arg
occurs s (Proj a b) = occurs s a ∨ occurs s b
occurs s (BaseL A B) = occurs s A ∨ occurs s B
occurs s (BaseR A B) = occurs s A ∨ occurs s B
occurs s (GlueL A B a) = occurs s A ∨ occurs s B ∨ occurs s a
occurs s (GlueR A B b) = occurs s A ∨ occurs s B ∨ occurs s b
occurs s (Id a b) = occurs s a ∨ occurs s b
occurs s (Idp a) = occurs s a
occurs s (Square p q r ss) = occurs s p ∨ occurs s q ∨ occurs s r ∨ occurs s ss
occurs s (Ids a) = occurs s a
occurs s (Pt A) = s ==ₛ A
occurs s (Ptf f A B) = (s ==ₛ f) ∨ occurs s A ∨ occurs s B
occurs s (Lam s' A t) = not (s ==ₛ s') ∧ (occurs s A ∨ occurs s t)
occurs s (PiEI s' A B) = not (s ==ₛ unArg s') ∧ (occurs s A ∨ occurs s B)
occurs s Ptd = false
occurs s Type = false
occurs s (PtdMap A B) = occurs s A ∨ occurs s B
occurs s (Smash A B) = occurs s A ∨ occurs s B
occurs s (Error x) = false

occursx : String → List (String × Term × Term) → Bool
occursx s [] = false
occursx s ((s' , t , u) ∷ l) = occurs s u ∨ occursx s l

simplify : List (String × Term × Term) → Term → List (String × Term × Term) → List (String × Term × Term)
simplify [] t acc = acc
simplify ((ps , pa , pt) ∷ (xs , xa , xt) ∷ l) t acc =
  if occurs ps t ∨ occursx ps acc ∨ occurs xs t ∨ occursx xs acc
  then simplify l t ((xs , xa , xt) ∷ (ps , pa , pt) ∷ acc)
  else simplify l t acc
simplify _ _ _ = []

generate-coh : String → ContractibleSystem → Term → Definition × Term
generate-coh s c t =
  let cells = boolFilter (λ t → get-type t ==ₜ get-type-of-CS c) (get-cells t) in
  let args = get-args-from-CS c cells in
  let root = get-root-type t in
  let ct-big = contractibilify root args in
  let type = antisubst ct-big t in
--  let ct = reverse ct-big in
  let ct = simplify ct-big type [] in
  let cohtype = Pi[] (get-params ct) type in
  let appterm = to-app (Var s cohtype) (get-args ct) in
                   
  (definition s cohtype (sprintf "%k %k = idp" (s ∷ patternify ct ∷ [])),
   appterm)

generate-apcoh : Definition → Definition
generate-apcoh (definition name type _) =
  let newname = "ap" ++ name in
  let (args , t) = unPi type in
  let newargs = (Imp "X", Type) ∷ (Imp "Y", Type) ∷ (Imp "f", Pi "_" (Var "X" Type) (Var "Y" Type))
                ∷ concat (map modify (tail args)) in
  let coh = Var name type in
  let newtype = Id (ap ff (App[] coh (vars args)))
                (AppE[] coh (map appf (vars args))) in
  let newdef = newname ++ patternify-apcoh (reverse newargs) ++ "= idp" in
  definition newname (Pi[] newargs newtype) newdef
    where
      ff = Var "f" (Pi "_" (Var "X" Type) (Var "Y" Type))

      modify : Arg String × Term → List (Arg String × Term)
      modify (s , t) =
        let thing = Var (unArg s) t in
        if dimension t == 1 then
          (Imp (unArg s) , t) ∷ (Imp ("f" ++ unArg s) , get-type (ap ff thing)) ∷ (Exp ("f" ++ unArg s ++ "=") , Id (ap ff thing) (Var ("f" ++ unArg s) (get-type (ap ff thing)))) ∷ []
        else
          [ Imp (unArg s) , t ]

      appf : Arg Term → Term
      appf (Exp (Var "X" _)) = Var "Y" Type
      appf (Exp (Var s t)) = if dimension t == 0 then App ff (Var s t) else Var ("f" ++ s) (get-type (ap ff (Var s t)))
      appf _ = Error "appf"

      patternify-apcoh : List (Arg String × Term) → String
      patternify-apcoh (_ ∷ _ ∷ _ ∷ _ ∷ []) = " "
      patternify-apcoh ((Imp p , _) ∷ (Imp _ , _) ∷ l) = patternify-apcoh l ++ "{" ++ p ++ " = idp} "
      patternify-apcoh ((Exp p , _) ∷ (Imp _ , _) ∷ l) = patternify-apcoh l ++ "idp "
      patternify-apcoh _ = "Error"


{-# TERMINATING #-}
newsubst : Term → Term → String → Term
NewAppReduce : Term → Term → Term
NewAppIReduce : Term → Term → Term
apply-path : Term → Term → (String × Term)

NewAppE[] : Term → List Term → Term
NewAppE[] t [] = t
NewAppE[] t (u ∷ us) = NewAppE[] (NewAppReduce t u) us

all-pt-subst : ArgType → Term → Term
all-pt-subst / a - A / u = u [ pt A / a ]
all-pt-subst (A [∧] B) u = all-pt-subst A (all-pt-subst B u)

all-proj : ArgType → Term
all-proj / a - A / = Var a A
all-proj (A [∧] B) = Proj (all-proj A) (all-proj B)

-- get-aux-gluel-0 : Declaration → Term → Term → Term → ?
-- get-aux-gluel-0 =
--   generate-coh (name dec ++ "-coh1") (CS-codomain dec)
--                (Id (NewAppE[]

get-coh1-0-A∧B : Declaration → Term → Term → String → Definition × Term
get-coh1-0-A∧B dec A B b =
  generate-coh (name dec ++ "-coh1") (CS-codomain dec)
               (Id (def dec [ pt B / b ]) (pt (type dec)))

get-coh2-0-A∧B : Declaration → Term → Term → String → Definition × Term
get-coh2-0-A∧B dec A B a =
  generate-coh (name dec ++ "-coh2") (CS-codomain dec)
               (Id (def dec [ pt A / a ]) (pt (type dec)))

get-coh-basel : Declaration → Term → Term → Definition × Term
get-coh-basel dec A B =
  generate-coh (name dec ++ "-coh1") (CS-codomain dec)
               (newsubst (type dec) (BaseL A B) "x")

get-coh-baser : Declaration → Term → Term → Definition × Term
get-coh-baser dec A B =
  generate-coh (name dec ++ "-coh2") (CS-codomain dec)
               (newsubst (type dec) (BaseR A B) "x")

get-coh3-1-A∧B : Declaration → Term → Term → String → String → Term → Definition × Term × String × String
get-coh3-1-A∧B dec A B a b coh1app =
  let (gluel-βlhs , gluel-pathlhs) = apply-path (lhs (type dec)) (GlueL A B (Var a A)) in
  let (gluel-βrhs , gluel-pathrhs) = apply-path (rhs (type dec)) (GlueL A B (Var a A)) in
  let (coh , cohapp) = generate-coh (name dec ++ "-coh3") (CS-codomain dec)
                                    (Square (def dec [ pt B / b ]) gluel-pathlhs gluel-pathrhs coh1app) in
  (coh , cohapp , gluel-βlhs , gluel-βrhs)

get-coh4-1-A∧B : Declaration → Term → Term → String → String → Term → Definition × Term × String × String
get-coh4-1-A∧B dec A B a b coh2app =
  let (gluer-βlhs , gluer-pathlhs) = apply-path (lhs (type dec)) (GlueR A B (Var b B)) in
  let (gluer-βrhs , gluer-pathrhs) = apply-path (rhs (type dec)) (GlueR A B (Var b B)) in
  let (coh , cohapp) = generate-coh (name dec ++ "-coh4") (CS-codomain dec)
                                    (Square (def dec [ pt A / a ]) gluer-pathlhs gluer-pathrhs coh2app) in
  (coh , cohapp , gluer-βlhs , gluer-βrhs)

get-coh1-0-X∧C : Declaration → Term → String → Definition × Term
get-coh1-0-X∧C dec C c = 
  generate-coh (name dec ++ "-coh1") (CS-codomain dec)
               (Id (def dec [ pt C / c ]) (pt (type dec)))

get-aux-0-X∧C : Declaration → ArgType → Term → String → Declaration
get-aux-0-X∧C dec X C c =
  declaration (name dec ++ "-aux")
              (params dec ++ₗ [ c , C ])
              X
              (type dec)
              (def dec)
              (CS-codomain dec)

get-auxcoh-0-X∧C : Declaration → Declaration → ArgType → Term → Term → Declaration
get-auxcoh-0-X∧C dec dec-aux X C coh1app =
  declaration (name dec ++ "-auxcoh")
              (params dec)
              X
              (Id (App (Dec dec-aux (map (λ {(s , t) → Var s t}) (params dec) ++ₗ [ pt C ]))
                       (Var "x" (argtype-to-type X)))
                  (pt (type dec)))
              coh1app
              (CS-codomain dec)

get-coh2-0-X∧C : Declaration → ArgType → Term → String → Definition × Term
get-coh2-0-X∧C dec X C c =
  generate-coh (name dec ++ "-coh2") (CS-codomain dec)
               (Id (all-pt-subst X (def dec)) (pt (type dec)))

get-aux-0-A∧X : Declaration → Term → ArgType → String → Declaration
get-aux-0-A∧X dec A X a =
  declaration (name dec ++ "-aux")
              (params dec ++ₗ [ a , A ])
              X
              (type dec)
              (def dec)
              (CS-codomain dec)

get-coh1-0-A∧X : Declaration → Term → String → Definition × Term
get-coh1-0-A∧X dec A a =
  generate-coh (name dec ++ "-coh1") (CS-codomain dec)
               (Id (def dec [ pt A / a ]) (pt (type dec)))

get-auxcoh-0-A∧X : Declaration → Declaration → Term → ArgType → Term → Declaration
get-auxcoh-0-A∧X dec dec-aux A X coh1app =
  declaration (name dec ++ "-auxcoh")
              (params dec)
              X
              (Id (App (Dec dec-aux (map (λ {(s , t) → Var s t}) (params dec) ++ₗ [ pt A ]))
                       (Var "x" (argtype-to-type X)))
                  (pt (type dec)))
              coh1app
              (CS-codomain dec)

get-coh2-0-A∧X : Declaration → ArgType → Term → String → Definition × Term
get-coh2-0-A∧X dec X A a =
  generate-coh (name dec ++ "-coh2") (CS-codomain dec)
               (Id (all-pt-subst X (def dec)) (pt (type dec)))

get-aux-1-X∧C : Declaration → ArgType → Term → String → Declaration
get-aux-1-X∧C dec X C c =
  declaration (name dec ++ "-aux")
              (params dec ++ₗ [ c , C ])
              X
              (newsubst (type dec) (Proj (Var "x" (argtype-to-type X)) (Var c C)) "x")
              (def dec)
              (CS-codomain dec)

get-coh1-1-X∧C : Declaration → Term → Term → Definition × Term
get-coh1-1-X∧C dec X C =
  generate-coh (name dec ++ "-coh1") (CS-codomain dec)
               (newsubst (type dec) (BaseL X C) "x")

get-coh2-1-X∧C : Declaration → Term → Term → Definition × Term
get-coh2-1-X∧C dec X C =
  generate-coh (name dec ++ "-coh2") (CS-codomain dec)
               (newsubst (type dec) (BaseR X C) "x")

get-auxcoh-1-X∧C : Declaration → Declaration → ArgType → Term → String → Term → Definition × Declaration × String × String
get-auxcoh-1-X∧C dec dec-aux X C c coh1app =
  let (gluel-βlhs , gluel-pathlhs) = apply-path (lhs (type dec)) (GlueL (argtype-to-type X) C (Var "x" (argtype-to-type X))) in
  let (gluel-βrhs , gluel-pathrhs) = apply-path (rhs (type dec)) (GlueL (argtype-to-type X) C (Var "x" (argtype-to-type X))) in
  let type = Id (coh∙ (App (Dec dec-aux (map (λ {(s , t) → Var s t}) (params dec) ++ₗ [ pt C ])) (Var "x" (argtype-to-type X))) gluel-pathrhs)
                (coh∙ gluel-pathlhs coh1app) in
  let (cohdef , cohdefapp) = generate-coh (name dec ++ "-cohdef")
                                          (CS-codomain dec)
                                          (newsubst type (all-proj X) "x") in
  let auxcoh = declaration (name dec ++ "-auxcoh")
                           (params dec)
                           X
                           type
                           cohdefapp
                           (CS-codomain dec) in
  (cohdef , auxcoh , gluel-βlhs , gluel-βrhs)


newsubst t u s = t [ u /g s ]⟨ NewAppReduce / NewAppIReduce ⟩

NewAppReduce (Lam s A t) u = newsubst t u s
NewAppReduce (Dec dec args) (BaseL _ _) with dimension (type dec)
... | 0 = pt (type dec [ args /[] map proj₁ (params dec) ])
... | 1 = Error "TODO1"
... | _ = Error "Not implemented"
NewAppReduce (Dec dec args) (BaseR _ _) with dimension (type dec)
... | 0 = pt (type dec [ args /[] map proj₁ (params dec) ])
... | 1 = Error "TODO2"
... | _ = Error "Not implemented"
NewAppReduce (Dec dec args) (Proj u v) with dimension (type dec) | argtype dec
... | _ | / a - A / [∧] / b - B / = def dec [ args /[] map proj₁ (params dec) ] [ u ∷ v ∷ [] /[] a ∷ b ∷ [] ]
... | 0 | X [∧] / c - C / = NewAppReduce (Dec (get-aux-0-X∧C dec X C c) (args ++ₗ [ v ])) u
... | 0 | / a - A / [∧] X = NewAppReduce (Dec (get-aux-0-A∧X dec A X a) (args ++ₗ [ u ])) v
... | _ | _ = Error ("TODO4(" ++ showℕ (dimension (type dec)) ++ ")")
NewAppReduce (AppI (AppI (App (AppI (AppI (Var "ap" _) A) B) f) a) b) (Idp u) = Idp (NewAppReduce f u)
NewAppReduce t u = AppReduce t u

NewAppIReduce (Lam s A t) u = newsubst t u s
NewAppIReduce t u = AppI t u

{- [split t] returns the first thing applied to "x", and then the rest. We return nothing if it’s constant. -}
split : Term → Maybe (Term × Term)
split (Var "x" X) = just (Error "splitidf", Error "splitidf")
split (App f (Var "x" T)) = just (f , Var "x" T)
split (App f arg) with split arg
... | just (a , b) = just (a , NewAppReduce f b)
... | nothing = nothing
split (Proj (Var "x" X) b) = just (Lam "x" X (Proj (Var "x" X) b) , Var "x" X)
split (Proj a (Var "x" X)) = just (Lam "x" X (Proj a (Var "x" X)) , Var "x" X)
split (Proj a b) with split a | split b
... | nothing | nothing = nothing
... | just (f , a') | nothing = just (f , Proj a' b)
... | nothing | just (g , b') = just (g , Proj a b')
... | just _ | just _ = just (Error "splitboth", Error "splitboth")
split t = nothing

is-Type : Term → Bool
is-Type Type = true
is-Type Ptd = true
is-Type _ = false

apply-path-single : Declaration → List Term → Term → (String × Term)
apply-path-single dec args t with argtype dec | t
... | / a - A / [∧] / b - B / | GlueL _ _ u =
  let (coh , cohapp) = get-coh1-0-A∧B dec A B b in
  ("gluel-β' " ++ print-P u , cohapp [ args /[] map proj₁ (params dec) ] [ u / a ])
... | / a - A / [∧] / b - B / | GlueR _ _ v =
  let (coh , cohapp) = get-coh2-0-A∧B dec A B a in
  ("gluer-β' " ++ print-P v , cohapp [ args /[] map proj₁ (params dec) ] [ v / b ])
... | / a - A / [∧] X | GlueL _ _ u =
  let (coh , cohapp) = get-coh2-0-A∧X dec X A a in
  ("gluel-β' " ++ print-P u , cohapp [ args /[] map proj₁ (params dec) ] [ u / a ])
... | / a - A / [∧] X | GlueR _ _ x =
  let dec-aux = get-aux-0-A∧X dec A X a in
  let (coh1 , coh1app) = get-coh1-0-A∧X dec A a in
  let dec-auxcoh = get-auxcoh-0-A∧X dec dec-aux A X coh1app in
  let u = NewAppReduce (Dec dec-auxcoh args) x in
  ("gluer-β' " ++ print-P x , u)
... | X [∧] / c - C / | GlueR _ _ w =
  let (coh , cohapp) = get-coh2-0-X∧C dec X C c in
  ("gluer-β' " ++ print-P w , cohapp [ args /[] map proj₁ (params dec) ] [ w / c ])
... | X [∧] / c - C / | GlueL _ _ x =
  let dec-aux = get-aux-0-X∧C dec X C c in
  let (coh1 , coh1app) = get-coh1-0-X∧C dec C c in
  let dec-auxcoh = get-auxcoh-0-X∧C dec dec-aux X C coh1app in
  let u = NewAppReduce (Dec dec-auxcoh args) x in
  ("gluel-β' " ++ print-P x , u)
... | _ | _ = ("idp" , ap (Dec dec args) t)
-- ("(apply-path-single (" ++ print t ++ " / " ++ print (name dec) ++ "))", Error ("aps(" ++ print t ++ " / " ++ print (argtype dec) ++ ")"))

unjust : Maybe (Term × Term) → Term
unjust (just (a , _)) = a
unjust nothing = Error "nothing"
 
{- [apply-path] takes a term [f] with free variable "x" and a term [p] and returns
   - the fully reduced version of [ap (λ x → f) p]
   - the string showing the equality of the actual [ap] with the fully reduced one
-}
apply-path (Var "x" _) u = ("ap-idf", u)
apply-path fun u with uncoh u
... | Coh "ap" _ (Imp A ∷ Imp B ∷ Exp (Lam x X (Proj v w)) ∷ Imp a ∷ Imp b ∷ Exp p ∷ []) =
    (let (s , t) = apply-path ((newsubst fun (Proj v w) "x") [ Var "x" X / x ]) p
      in (sprintf "∘-ap-eq (%k) (%k) (%k)" (Lam "x" (Error "aaa") fun ∷ Lam x X (Proj v w) ∷ s ∷ []), t))
... | Coh "ap" _ (Imp A ∷ Imp B ∷ Exp f ∷ Imp a ∷ Imp b ∷ Exp p ∷ []) =
  let z = fresh (A ∷ B ∷ f ∷ a ∷ b ∷ p ∷ []) "z" in
  (sprintf "∘-ap (%k) (%k)" (Lam "x" (Error "aaa") fun ∷ f ∷ []) , ap (Lam z A (newsubst fun (NewAppReduce f (Var z A)) "x")) p)
... | Coh s t arg =
  let str = "ap" ++ s in
  f arg str (Var s t)
    where
    f : List (Arg Term) → String → Term → String × Term
    f [] sacc tacc = (sacc , tacc)
    f (t ∷ ts) sacc tacc =
      if is-Type (get-type (unArg t)) then
        f ts sacc (AppEI tacc (hiding-app t (get-type fun)))
      else if dimension (get-type (unArg t)) == 1 then
        (let (s' , u) = apply-path fun (unArg t) in f ts (sacc ++ " (" ++ s' ++ ")") (AppEI tacc (hiding-app t u)))
      else f ts sacc (AppEI tacc (hiding-app t (newsubst fun (unArg t) "x")))
... | < t > with split fun
...   | just (Dec dec args , Var "x" _) = apply-path-single dec args t
...   | just (Dec dec args , rest) =
  let (str1 , u) = apply-path-single dec args t in
  let (str2 , v) = apply-path rest u in
  let str = sprintf "ap-∘ (%k) (%k) (%k) (%k)" (Lam "x" (Error "aaa") rest ∷ Dec dec args ∷ str1 ∷ str2 ∷ []) in
  (str , v)
...   | just (ff@(Lam _ _ (Proj a b)) , rest) = ("idp", ap ff u)
-- ...   | just (ff@(Lam _ _ (Proj a b)) , rest) = ("idp", ap ff u)
...   | nothing = ("ap-cst", Idp fun) -- We assume it’s constant
...   | _ = ("(NIY1 (" ++ print (unjust (split fun)) ++ " / " ++ print (allImplicit fun) ++ " / " ++ print u ++ "))", Error "NIY1")

{-# TERMINATING #-}
generate-body : Declaration → String

generate-body dec with dimension (type dec) | argtype dec
generate-body dec | 0 | / a - A / [∧] / b - B / =

  let (coh1 , coh1app) = get-coh1-0-A∧B dec A B b in
  let apcoh1 = generate-apcoh coh1 in 
  let (coh2 , coh2app) = get-coh2-0-A∧B dec A B a in
  let apcoh2 = generate-apcoh coh2 in 

  sprintf "%k\n\n%k\n\n%k\n\n%k

%k : %k %k → %k
%k %k =
  Smash-rec (λ %k %k → %k)
            pt
            (λ %k → %k)
            pt
            (λ %k → %k)
" (coh1 ∷ coh2 ∷ apcoh1 ∷ apcoh2
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec)
  ∷ a ∷ b ∷ def dec
  ∷ a ∷ coh1app
  ∷ b ∷ coh2app ∷ [])

generate-body dec | 1 | / a - A / [∧] / b - B / =

  let (coh1 , coh1app) = get-coh-basel dec A B in
  let (coh2 , coh2app) = get-coh-baser dec A B in
  let (coh3 , coh3app , gluel-βlhs , gluel-βrhs) = get-coh3-1-A∧B dec A B a b coh1app in
  let (coh4 , coh4app , gluer-βlhs , gluer-βrhs) = get-coh4-1-A∧B dec A B a b coh2app in

  sprintf "%k\n\n%k\n\n%k\n\n%k

%k : %k %k → %k
%k %k =
  Smash-elim (λ %k %k → %k)
             (%k)
             (λ %k → ↓-=-in-eq (%k) (%k) (%k))
             (%k)
             (λ %k → ↓-=-in-eq (%k) (%k) (%k))
" (coh1 ∷ coh2 ∷ coh3 ∷ coh4
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec)
  ∷ a ∷ b ∷ def dec
  ∷ coh1app
  ∷ a ∷ gluel-βrhs ∷ gluel-βlhs ∷ coh3app
  ∷ coh2app
  ∷ b ∷ gluer-βrhs ∷ gluer-βlhs ∷ coh4app ∷ [])

generate-body dec | 2 | / a - A / [∧] / b - B / =

  let (coh1 , coh1app) = get-coh-basel dec A B in
  let (coh2 , coh2app) = get-coh-baser dec A B in
  -- let (coh3 , coh3app , gluel-βlhs , gluel-βrhs) = get-coh3-1-A∧B dec A B a b coh1app in
  -- let (coh4 , coh4app , gluer-βlhs , gluer-βrhs) = get-coh4-1-A∧B dec A B a b coh2app in

  sprintf "%k\n\n%k

%k : %k %k → %k
%k %k =
  Smash-elim (λ %k %k → %k)
             (%k)
             ?
             (%k)
             ?
" (coh1 ∷ coh2
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec)
  ∷ a ∷ b ∷ def dec
  ∷ coh1app
  ∷ coh2app ∷ [])

generate-body dec | 0 | X [∧] / c - C / =

  let dec-aux = get-aux-0-X∧C dec X C c in
  let aux = generate-body dec-aux in
  let (coh1 , coh1app) = get-coh1-0-X∧C dec C c in
  let dec-auxcoh = get-auxcoh-0-X∧C dec dec-aux X C coh1app in
  let auxcoh = generate-body dec-auxcoh in
  let (coh2 , coh2app) = get-coh2-0-X∧C dec X C c in

  sprintf "%k\n%k\n\n%k\n%k

%k : %k %k → %k
%k %k =
  Smash-rec (λ x %k → %k %k x)
            pt
            (%k %k)
            pt
            (λ %k → %k)
" (aux ∷ coh1 ∷ auxcoh ∷ coh2
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec)
  ∷ c ∷ name dec-aux ∷ onlyNames (params dec-aux)
  ∷ name dec-auxcoh ∷ onlyNames (params dec-auxcoh)
  ∷ c ∷ coh2app ∷ [])

generate-body dec | 0 | / a - A / [∧] X =

  let dec-aux = get-aux-0-A∧X dec A X a in
  let aux = generate-body dec-aux in
  let (coh1 , coh1app) = get-coh1-0-A∧X dec A a in
  let dec-auxcoh = get-auxcoh-0-A∧X dec dec-aux A X coh1app in
  let auxcoh = generate-body dec-auxcoh in
  let (coh2 , coh2app) = get-coh2-0-A∧X dec X A a in

  sprintf "%k\n%k\n\n%k\n%k

%k : %k %k → %k
%k %k =
  Smash-rec (%k %k)
            pt
            (λ %k → %k)
            pt
            (%k %k)
" (aux ∷ coh1 ∷ auxcoh ∷ coh2
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec)
  ∷ name dec-aux ∷ onlyNames (params dec)
  ∷ a ∷ coh2app
  ∷ name dec-auxcoh ∷ onlyNames (params dec-auxcoh)
  ∷ [])

generate-body dec | 1 | X [∧] / c - C / =

  let dec-aux = get-aux-1-X∧C dec X C c in
  let aux = generate-body dec-aux in
  let (coh1 , coh1app) = get-coh-basel dec (argtype-to-type X) C in
  let (coh2 , coh2app) = get-coh-baser dec (argtype-to-type X) C in

  let (cohdef , dec-auxcoh , gluel-βlhs , gluel-βrhs) = get-auxcoh-1-X∧C dec dec-aux X C c coh1app in
  let auxcoh = generate-body dec-auxcoh in

  sprintf "%k\n%k\n\n%k\n\n%k\n%k

%k : %k %k → %k
%k %k =
  Smash-elim (λ x %k → %k %k x)
             (%k)
             (λ x → ↓-=-in-eq (%k) (%k) (%k %k x))
             (%k)
             (λ %k → ↓-=-in-eq (%k) (%k) (%k))
" (aux ∷ coh1 ∷ cohdef ∷ auxcoh ∷ coh2
  ∷ name dec ∷ params dec ∷ get-arg dec ∷ type dec
  ∷ name dec ∷ onlyNames (params dec)
  ∷ c ∷ name dec-aux ∷ onlyNames (params dec-aux)
  ∷ coh1app
  ∷ gluel-βrhs ∷ gluel-βlhs ∷ name dec-auxcoh ∷ onlyNames (params dec-auxcoh)
  ∷ coh2app
  ∷ c ∷ "{!gluer-βrhs!}" ∷ "{!gluer-βlhs!}" ∷ "{!coh3app!}" ∷ [])

generate-body dec | 2 | _ = "Two-dimensional!!!"

generate-body dec | _ | _ = "Not implemented yet"


main : IO ⊤
main =
  putStr ("\n" ++
    -- generate-body id-dec ++ "\n\n" ++
    -- generate-body σ-dec ++ "\n\n" ++
    -- generate-body ∧-map-dec ++ "\n\n" ++
    -- generate-body α-dec ++ "\n\n" ++
    -- generate-body αinv-dec ++ "\n\n" ++
    -- generate-body β-dec ++ "\n\n" ++
    -- generate-body γ-dec ++ "\n\n" ++
    -- generate-body ∧-map-id-dec ++ "\n\n" ++
    -- generate-body σ-triangle-dec ++ "\n\n" ++
    -- generate-body σ-2triangle-dec ++ "\n\n" ++
    -- generate-body σ-nat-dec ++ "\n\n" ++
    -- generate-body₁ pentagon-dec ++ "\n\n" ++
    -- generate-body α-rinv-dec ++ "\n\n" ++
    "")

