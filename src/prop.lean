import .exp .print

namespace prop

variable {α : Type}

class is_symb (α : Type) :=
(true : α) (false : α) (not : α)
(and : α) (or : α) (imp : α)

def true [is_symb α] := @exp.cst α (is_symb.true α)
notation  `⊤'` := true

def false [is_symb α] := @exp.cst α (is_symb.false α)
notation  `⊥'` := false

def not [is_symb α] (p : exp α) := exp.app (exp.cst (is_symb.not α)) p
notation  `¬'` p := not p

def and [is_symb α] (p q : exp α) := exp.app (exp.app (exp.cst (is_symb.and α)) p) q
notation  p `∧'` q := and p q

def or [is_symb α] (p q : exp α) := exp.app (exp.app (exp.cst (is_symb.or α)) p) q
notation  p `∨'` q := or p q

def imp [is_symb α] (p q : exp α) := exp.app (exp.app (exp.cst (is_symb.imp α)) p) q
notation  p `→'` q := imp p q

@[derive has_reflect]
inductive symb : Type 
| atom : string → symb 
| true : symb
| false : symb
| not : symb
| and : symb
| or  : symb
| imp : symb

instance : decidable_eq symb :=
by tactic.mk_dec_eq_instance

instance : is_symb symb := 
{ true  := symb.true,
  false := symb.false,
  not   := symb.not,
  and   := symb.and,
  or    := symb.or,
  imp   := symb.imp }

def A' (s : string) := @exp.cst symb (symb.atom s)

inductive inf [is_symb α] : list (seq α) → seq α → Prop
| id : ∀ Γ Δ p, inf [] (p::Γ ==> p::Δ)
| truer : ∀ Γ Δ, inf [] (Γ ==> ⊤'::Δ) 
| falsel : ∀ Γ Δ, inf [] (⊥'::Γ ==> Δ) 
| andl : ∀ Γ Δ p q, inf [p::q::Γ ==> Δ] ((p ∧' q)::Γ ==> Δ)
| andr : ∀ Γ Δ p q, inf [Γ ==> p::Δ, Γ ==> q::Δ] (Γ ==> (p ∧' q)::Δ)
| orl : ∀ Γ Δ p q, inf [p::Γ ==> Δ, q::Γ ==> Δ] ((p ∨' q)::Γ ==> Δ) 
| orr : ∀ Γ Δ p q, inf [Γ ==> p::q::Δ] (Γ ==> (p ∨' q)::Δ)
| impl : ∀ Γ Δ p q, inf [Γ ==> p::Δ, q::Γ ==> Δ] ((p →' q)::Γ ==> Δ) 
| impr : ∀ Γ Δ p q, inf [p::Γ ==> q::Δ] (Γ ==> (p →' q)::Δ) 
| wl : ∀ Γ Δ p, inf [Γ ==> Δ] (p::Γ ==> Δ) 
| wr : ∀ Γ Δ p, inf [Γ ==> Δ] (Γ ==> p::Δ) 
| cl : ∀ Γ Δ p, inf [p::p::Γ ==> Δ] (p::Γ ==> Δ) 
| cr : ∀ Γ Δ p, inf [Γ ==> p::p::Δ] (Γ ==> p::Δ)
| pl : ∀ Γ Γ' Δ, Γ ~ Γ' → inf [Γ ==> Δ] (Γ' ==> Δ) 
| pr : ∀ Γ Δ Δ', Δ ~ Δ' → inf [Γ ==> Δ] (Γ ==> Δ') 

inductive thm [is_symb α] : (seq α) → Prop  
| inf : ∀ {s S}, inf S s → (∀ s' ∈ S, thm s') → thm s 


/- Derived rules -/

open list

lemma thm.id [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, thm (p::Γ ==> p::Δ) :=
begin
  intros Γ Δ p, apply thm.inf,
  apply inf.id, apply forall_mem_nil 
end
 
lemma thm.truer [is_symb α] : 
  ∀ (Γ Δ : list (exp α)), thm (Γ ==> ⊤'::Δ) :=
begin
  intros Γ Δ, apply thm.inf,
  apply inf.truer, apply forall_mem_nil
end

lemma thm.falsel [is_symb α] : 
  ∀ (Γ Δ : list (exp α)), thm (⊥'::Γ ==> Δ) :=
begin
  intros Γ Δ, apply thm.inf,
  apply inf.falsel, apply forall_mem_nil
end

lemma thm.andl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q,
  thm (p::q::Γ ==> Δ) → thm ((p ∧' q)::Γ ==> Δ) :=
begin
  intros Γ Δ p q h, apply thm.inf, apply inf.andl, 
  rewrite forall_mem_singleton, apply h 
end

lemma thm.andr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q, 
  thm (Γ ==> p::Δ) → thm (Γ ==> q::Δ) 
  → thm (Γ ==> (p ∧' q)::Δ) :=
begin
  intros Γ Δ p q h1 h2, 
  apply thm.inf, apply inf.andr, intros s hs,
  rewrite mem_cons_iff at hs, cases hs with hs hs,
  rewrite hs, apply h1, rewrite mem_singleton at hs,
  rewrite hs, apply h2
end

lemma thm.orl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q,
  thm (p::Γ ==> Δ) → thm (q::Γ ==> Δ)
  → thm ((p ∨' q)::Γ ==> Δ) :=
begin
  intros Γ Δ p q h1 h2, 
  apply thm.inf, apply inf.orl, intros s hs,
  rewrite mem_cons_iff at hs, cases hs with hs hs,
  rewrite hs, apply h1, rewrite mem_singleton at hs,
  rewrite hs, apply h2
end

lemma thm.orr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q, 
  thm (Γ ==> p::q::Δ) → thm (Γ ==> (p ∨' q)::Δ) := 
begin
  intros Γ Δ p q h, apply thm.inf, apply inf.orr, 
  rewrite forall_mem_singleton, apply h 
end

lemma thm.impl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q, 
  thm (Γ ==> p::Δ) → thm (q::Γ ==> Δ) 
  → thm ((p →' q)::Γ ==> Δ) :=
begin
  intros Γ Δ p q h1 h2, apply thm.inf, apply inf.impl, 
  intros s hs, rewrite mem_cons_iff at hs, 
  cases hs with hs hs, rewrite hs, apply h1, 
  rewrite mem_singleton at hs, rewrite hs, apply h2
end

lemma thm.impr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q, 
  thm (p::Γ ==> q::Δ) → thm (Γ ==> (p →' q)::Δ) :=
begin
  intros Γ Δ p q h, apply thm.inf, apply inf.impr, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.wl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, 
  thm (Γ ==> Δ) → thm (p::Γ ==> Δ) :=  
begin
  intros Γ Δ p h, apply thm.inf, apply inf.wl, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.wr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, 
  thm (Γ ==> Δ) → thm (Γ ==> p::Δ) :=
begin
  intros Γ Δ p h, apply thm.inf, apply inf.wr, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.cl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, 
  thm (p::p::Γ ==> Δ) → thm (p::Γ ==> Δ) := 
begin
  intros Γ Δ p h, apply thm.inf, apply inf.cl, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.cr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, 
  thm (Γ ==> p::p::Δ) → thm (Γ ==> p::Δ) := 
begin
  intros Γ Δ p h, apply thm.inf, apply inf.cr, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.rl [is_symb α] : 
  ∀ n (Γ Δ : list (exp α)), thm (rotate n Γ ==> Δ) → thm (Γ ==> Δ) :=
begin
  intros n Γ Δ h, apply thm.inf,
  apply inf.pl (rotate n Γ), 
  apply perm_rotate, intros s' hs', 
  rewrite list.mem_singleton at hs', 
  rewrite hs', apply h
end
 
lemma thm.rr [is_symb α] : 
  ∀ n (Γ Δ : list (exp α)), thm (Γ ==> rotate n Δ) → thm (Γ ==> Δ) :=
begin
  intros n Γ Δ h, apply thm.inf,
  apply inf.pr _ (rotate n Δ), 
  apply perm_rotate, intros s' hs', 
  rewrite list.mem_singleton at hs', 
  rewrite hs', apply h
end



/- Printing -/

open expr tactic

meta def getsqt : tactic (list (exp symb) × list (exp symb)) :=
do `(thm (%%Γe ==> %%Δe)) ← tactic.target,
    Γ ← eval_expr (list (exp symb)) Γe, 
    Δ ← eval_expr (list (exp symb)) Δe, 
    return (Γ,Δ)

def fml2str : exp symb → string 
| (exp.app (exp.cst s) p) := 
  if s = (is_symb.not symb)
  then "¬" ++ fml2str p
  else "ERROR"
| (exp.app (exp.app (exp.cst s) p) q) := 
  if s = (is_symb.and symb)
  then "(" ++ fml2str p ++ " ∧ " ++ fml2str q ++ ")" else 
  if s = (is_symb.or symb)
  then "(" ++ fml2str p ++ " ∨ " ++ fml2str q ++ ")" else 
  if s = (is_symb.imp symb)
  then "(" ++ fml2str p ++ " → " ++ fml2str q ++ ")" else "ERROR"
| (exp.cst s) := 
  if s = is_symb.true symb
  then "⊤" else
  if s = is_symb.false symb
  then "⊥" else
  match s with 
  | (symb.atom str) := str 
  | _ := "ERROR"
  end
| _ := "ERROR"

meta def showgoal : tactic unit :=
(do (Γ,Δ) ← getsqt, trace (sqt2str fml2str Γ Δ)) <|> trace "No Goals"


/- Examples (Hilbert System Axioms) -/

example : thm ([] ==> [A' "φ" →' A' "φ"]) :=
begin
  showgoal,
  apply thm.impr,
  apply thm.id,
  showgoal
end

example : thm ([] ==> [A' "φ" →' (A' "ψ" →' A' "φ")]) :=
begin
  showgoal,
  apply thm.impr,
  apply thm.impr,
  apply thm.rl 1, 
  apply thm.id,
  showgoal
end

example : thm ([] ==> [(A' "φ" →' (A' "ψ" →' A' "χ")) →' ((A' "φ" →' A' "ψ") →' (A' "φ" →' A' "χ"))]) :=
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

end prop