/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Monadic parsing, following Graham Hutton and Erik Meijer, "Monadic Parsing in Haskell," 1998.
-/

-- TODO(Jeremy): move this
namespace char

def is_whitespace : char → Prop
| #" "  := true
| #"\t" := true
| #"\n" := true
| _     := false

instance decidable_is_whitespace : decidable_pred is_whitespace :=
begin intro c, delta is_whitespace, apply_instance end

def is_alpha (c : char) : Prop :=
let n := to_nat c in n >= 65 ∧ n <= 122

def is_upper (c : char) : Prop :=
let n := to_nat c in n >= 65 ∧ n <= 96

def is_lower (c : char) : Prop :=
let n := to_nat c in n >= 65 ∧ n <= 96

def is_digit (c : char) : Prop :=
let n := to_nat c in n >= 48 ∧ n <= 57

def is_alphanum (c : char) : Prop :=
is_alpha c ∨ is_digit c

def is_punctuation (c : char) : Prop :=
c ∈ [#" ", #",", #".", #"?", #"!", #";", #"-", #"'"]

def to_lower (c : char) : char :=
let n := to_nat c in
if n >= 65 ∧ n <= 90 then of_nat (n + 32) else c

-- TODO(Jeremy): automate this boilerplate
instance decidable_is_alpha : decidable_pred is_alpha :=
begin intro c, delta is_alpha, apply_instance end

instance decidable_is_upper : decidable_pred is_upper :=
begin intro c, delta is_upper, apply_instance end

instance decidable_is_lower : decidable_pred is_lower :=
begin intro c, delta is_lower, apply_instance end

instance decidable_is_digit : decidable_pred is_digit :=
begin intro c, delta is_digit, apply_instance end

instance decidable_is_alphanum : decidable_pred is_alphanum :=
begin intro c, delta is_alphanum, apply_instance end

instance decidable_is_punctuation : decidable_pred is_punctuation :=
begin intro c, delta is_punctuation, apply_instance end

end char

/-
  The parsing monad.
-/

variables {α β : Type}

def parser (α : Type) : Type := string → list (α × string)

@[inline] def parser_fmap (f : α → β) (a : parser α) : parser β :=
λ s, list.map (λ p : α × string, (f p.1, p.2)) (a s)

@[inline] def parser_pure (a : α) : parser α := λ s, [(a, s)]

@[inline] def parser_bind (a : parser α) (b : α → parser β) : parser β :=
λ s, list.join $ list.for (a s) $ (λ p, b p.1 p.2)

instance : monad parser :=
{ map  := @parser_fmap,
  pure := @parser_pure,
  bind := @parser_bind }

def list.deterministic_or : list α → list α → list α
| [] []      := []
| [] (x::xs) := [x]
| (x::xs) _  := [x]

instance : alternative parser :=
{ map  := @parser_fmap,
  pure := @parser_pure,
  seq  := take α β, seq_app,
  failure := λ a s, [],
  orelse := λ a p₁ p₂ s, list.deterministic_or (p₁ s) (p₂ s) }

namespace parser

def parser_bignum := 1000

/- When viewed as a list, a string "abcde" is really the list [#"e", #"d", #"c", #"b", #"a"].
   However, the parsers below start working on the head of the list. So to apply it to a
   string that came from quoted string, reverse the string first.
-/

def parse (p : parser α) (s : string) : option α :=
match p (list.reverse s) with
| []            := none
| ((a, s) :: l) := some a
end

def item : parser char
| ""      := []
| (c::cs) := [(c, cs)]

section an_example
  private def my_parser : parser (char × char) :=
  do a ← item,
     b ← item,
     c ← item,
     return (a, c)

  -- vm_eval parse my_parser "abcde"  -- output : (some (#"a", #"c"))
end an_example

def sat (p : char → Prop) [decidable_pred p] : parser char :=
do c ← item, if p c then return c else failure

def take_char (c : char) : parser char := sat (λ x, x = c)

def take_string_aux : string → parser unit
| ""      := return ()
| (c::cs) := do take_char c, take_string_aux cs, return ()

def take_string (s : string) : parser string :=
do take_string_aux (list.reverse s) >> return s

def many_aux (p : parser α) : ℕ → parser (list α)
| 0     := return []
| (n+1) := (do a ← p, l ← many_aux n, return (a :: l)) <|> return []

def many (p : parser α) : parser (list α) :=
many_aux p parser_bignum

def many1 (p : parser α) : parser (list α) :=
do a ← p, l ← many p, return (a :: l)

def sepby1 {α β : Type} (p : parser α) (sep : parser β) : parser (list α) :=
do a ← p, l ← many (do sep, p), return (a::l)

def sepby {α β : Type} (p : parser α) (sep : parser β) : parser (list α) :=
sepby1 p sep <|> return []

def chainl1_rest (p : parser α) (op : parser (α → α → α)) : ℕ → α → parser α
| 0     := λ a, return a
| (n+1) := λ a, (do f ← op, b ← p, chainl1_rest n (f a b)) <|> return a

def chainl1 (p : parser α) (op : parser (α → α → α)) : parser α :=
do a ← p, chainl1_rest p op parser_bignum a

def chainl (p : parser α) (op : parser (α → α → α)) (a : α) : parser α :=
chainl1 p op <|> return a

def chainr1_rest (p : parser α) (op : parser (α → α → α)) (a : α) : ℕ → parser α
| 0     := return a
| (n+1) := do f ← op, b ← chainr1_rest n, return (f a b) <|> return a

def chainr1 (p : parser α) (op : parser (α → α → α)) : parser α :=
do a ← p, chainr1_rest p op a parser_bignum

def chainr (p : parser α) (op : parser (α → α → α)) (a : α) : parser α :=
chainr1 p op <|> return a

/-- consume whitespace -/
def space : parser string := many (sat char.is_whitespace)

/-- parse with p, and then consume whitespace -/
def token (p : parser α) : parser α := do a ← p, space, return a

/-- consume s -/
def symb (s : string) : parser string := token (take_string s)

/-- consume leading whitespace, and then apply p -/
def apply (p : parser α) : parser α := do space, p

end parser
