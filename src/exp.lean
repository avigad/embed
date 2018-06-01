import .list .misc

variable {α : Type }

@[derive has_reflect]
inductive exp (α : Type) : Type 
| bvr : nat → exp 
| fvr : nat → exp 
| cst : α → exp 
| lam : exp → exp 
| app : exp → exp → exp 

notation `#` n := exp.bvr _ n 
notation `&` n := exp.fvr _ n 

def seq (α : Type) : Type := (list (exp α)) × (list (exp α))

def proves (Γ Δ : list (exp α)) : seq α := ⟨Γ,Δ⟩

notation Γ `==>` Δ := proves Γ Δ

def fvrs : exp α → list nat
| (exp.lam e) := fvrs e
| (exp.app e1 e2) := fvrs e1 ++ fvrs e2 
| (exp.fvr α k) := [k]
| _ := []

def fvrs_list : list (exp α) → list nat 
| [] := []
| (e::es) := fvrs e ++ fvrs_list es

def inst_rec : nat → exp α → exp α → exp α 
| n t (exp.bvr α m) := 
  if n = m then t else (exp.bvr α m) 
| n t (exp.lam e) := 
  exp.lam (inst_rec (n+1) t e)
| n t (exp.app e1 e2) := 
  exp.app (inst_rec n t e1) (inst_rec n t e2)
| _ _ e := e

def inst (t e : exp α) : exp α := inst_rec 0 t e

instance [decidable_eq α] : decidable_eq (exp α) :=
by tactic.mk_dec_eq_instance