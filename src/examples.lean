import .interactive

example : !seq "⊢ p → q → p ∧ q" :=
begin [gentzen]
  impr, impr, andr, rl 1, id, id
end

example : !seq "⊢ p ∧ q ∨ p ∧ r → p" :=
begin [gentzen]
  impr, orl, andl, id, andl, id
end

example : !seq "p ∧ q, q → r ⊢  p ∧ r" :=
begin [gentzen]
  andl, rl 2, impl, id, andr, rl 2, id, id 
end

example : !seq "p ∧ (p → q) ⊢ q" :=
begin [gentzen]
  andl, rl 1, impl, id, id
end

example : !seq "p → q → r, p → q ⊢ p → r" :=
begin [gentzen]
  impr, rl 1, impl, rl 1, id, impl, impl, id, id, id 
end

theorem foo : !seq "⊢ q ∨ s → s ∨ q" :=
begin [gentzen]
  impr, orl, orr, rr 1, id, orr, id
end

#check foo
#eval prop.pp_thm foo
#print foo
