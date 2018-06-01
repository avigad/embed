import .prop data.buffer.parser

open parser

namespace prop

namespace parser

class has_vars (α : Type) :=
(var : string → α)

instance : has_vars symb :=
⟨symb.atom⟩

variables {α : Type} [is_symb α] [has_vars α]

-- whitespace
def Ws : parser unit :=
many' $ one_of' " \t\x0d\n".to_list

-- token
def tok (s : string) := str s >> Ws

/-
-- a variable: a, ..., z, A, ..., Z
def Var : parser nat := do 
c ← sat (λ x, _root_.true), 
Ws,
let n := c.to_nat in
if 65 ≤ n ∧ n ≤ 122 then 
  return n 
else 
  parser.fail "not a letter"
-/


def is_letter (c : char) :=
let n := c.to_nat in 65 ≤ n ∧ n ≤ 122

instance : decidable_pred is_letter := by { delta is_letter, apply_instance }

-- a variable: a, ..., z, A, ..., Z
def Var : parser (exp α) := do 
c ← sat is_letter, 
Ws,
return (@exp.cst _ $ has_vars.var _ c.to_string)

-- an atom
def Atom : parser (exp α) := 
(tok "⊤" >> Ws >> return prop.true) <|>
(tok "⊥" >> Ws >> return prop.false) <|>
Var
--(do n ← Var, pure (exp.fvr α n))

section formula
parameters {β : Type} [is_symb β] [has_vars β] (Form : parser (exp β))

def ParenForm : parser (exp β) :=
tok "(" *> Form <* tok ")" <* Ws
    
def Form0 : parser (exp β) :=
(fix $ λ F, Atom <|> ParenForm <|> (do tok "¬", f ← F, pure (prop.not f))) <* Ws

def Form1 : parser (exp β) :=
fix $ λ F, do
  l ← Form0,
  (do tok "∧",
      r ← F, 
      pure (prop.and l r)) <|>
    pure l

def Form2 : parser (exp β) :=
fix $ λ F, do
  l ← Form1,
  (do tok "∨",
      r ← F, 
      pure (prop.or l r)) <|>
    pure l

def Form3 : parser (exp β) :=
fix $ λ F, do
  l ← Form2,
  (do tok "→",
      r ← F, 
      pure (prop.imp l r)) <|>
    pure l

end formula

def Form : parser (exp α) := do
fix $ λ F, Form3 F

def Sequent : parser (seq  α) := do
l ← sep_by (tok ",") Form,
tok "⊢",
r ← sep_by (tok ",") Form,
return (l, r)

/-
def parse_prop_to_str (s : string) : string :=
match parser.run (Form : parser (exp symb)) s.to_char_buffer with
| (sum.inl error)  := error
| (sum.inr result) := fml2str result
end

def ex := parser.run (Form : parser (exp symb)) "(p ∧ ¬ q) → r ∨ s".to_char_buffer

#eval ex

def ex' := parse_prop_to_str "(p ∧ ¬ q) → r ∨ s"

#eval ex'
-/

section
open lean
open lean.parser
open interactive

/-
meta def mk_thm (s: string) : tactic unit :=
let S := (Sequent : parser (seq symb) in
match parser.run S s.to_char_buffer with
| (sum.inl error)  := do exact `(_root_.false)
| (sum.inr sq) := do  exact `(thm sq)
end

def thm_type (s : string) := Prop

meta def mk_thm' : tactic unit :=
do `(thm_type %%s) ← target | failed,
   ss ← eval_expr string s,
   mk_thm ss 
   
notation `!seq` s := (by mk_thm' : thm_type s)

-/

-- I don't know whether this is any better than the other method.
reserve prefix `!seq `:100
@[user_notation]
meta def sequent_macro (_ : parse $ tk "!seq") (s : string) : lean.parser pexpr :=
let S := (Sequent : _root_.parser (seq symb)) in
match parser.run S s.to_char_buffer with
| (sum.inl error)  := do pure ``(_root_.false)
| (sum.inr sq) := do let sq' := `(sq) in pure ``(thm %%sq')
end

end

/-
example : !seq "p, q ⊢ p" :=
begin
  apply thm.id
end

example : !seq "⊢ (p → q → r) → (p → q) → p → r" :=
begin
  showgoal,
  apply thm.impr,
  apply thm.impr,
  apply thm.impr,
  apply thm.rl 2, 
  apply thm.impl,
  apply thm.rl 1, 
  apply thm.id,
  apply thm.impl,
  apply thm.impl,
  apply thm.id,
  apply thm.id,
  apply thm.id,
  showgoal
end

example : !seq "p ∧ (q → ¬ p) ⊢ ¬ q" :=
begin
  apply thm.andl,
  showgoal
  sorry
end

theorem foo : !seq "p ∧ q ⊢ q ∧ p" :=
begin
  apply thm.andl,
  apply thm.andr,
  apply thm.rl 1,
  apply thm.id,
  apply thm.id, 
  showgoal
end

-/

end parser


def pp_thm {l r : list (exp symb)} (p : thm (l, r)) : string :=
sqt2str fml2str l r 

end prop