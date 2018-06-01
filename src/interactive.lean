-- adapted from tests/interactive/my_tactic_class.lean

import .prop .print .parser
open prop

-- keep the extra state around just in case
meta def gentzen :=
state_t nat tactic

section
local attribute [reducible] gentzen
meta instance : monad gentzen := by apply_instance
meta instance : monad_state nat gentzen := by apply_instance
meta instance : has_monad_lift tactic gentzen := by apply_instance
end

meta instance (α : Type) : has_coe (tactic α) (gentzen α) :=
⟨monad_lift⟩

namespace gentzen

meta def show_goal (e : expr) : tactic format :=
do 
et ← tactic.infer_type e,
match et with
| `(prop.thm %%sq) := 
  do sq' ← tactic.eval_expr (seq symb) sq,
     pure $ sqt2str fml2str sq'.1 sq'.2
| _              := pure ("not a Gentzen sequent: " ++ et.to_string)
end

meta def show_goals_aux : list expr → tactic format 
| []     := pure ""
| (h::t) := do hd ← show_goal h,
               tl ← show_goals_aux t,
               pure (hd ++ format.line ++ tl)

meta def show_goals : tactic format :=
do g ← tactic.get_goals,
   if g = [] then pure "No goals!" else show_goals_aux g

meta def step {α : Type} (t : gentzen α) : gentzen unit :=
t >> return ()

-- TODO: not updated
meta def istep {α : Type} (line0 col0 line col : nat) (t : gentzen α) : gentzen unit :=
⟨λ v s, result.cases_on (@scope_trace _ line col (λ_, t.run v s))
  (λ ⟨a, v⟩ new_s, result.success ((), v) new_s)
  (λ opt_msg_thunk e new_s, match opt_msg_thunk with
    | some msg_thunk :=
      let msg := λ _ : unit, msg_thunk () ++ format.line ++ to_fmt "state:" ++ format.line ++
        match show_goals new_s with
        | (result.success fmt _) := fmt
        | _ := new_s^.to_format
        end in
          interaction_monad.result.exception (some msg) (some ⟨line, col⟩) new_s
    | none := interaction_monad.silent_fail new_s
    end)⟩

meta def execute (tac : gentzen unit) : tactic unit :=
tac.run 0 >> return ()

meta def save_info (p : pos) : gentzen unit :=
do v ← get,
   s ← tactic.read,
   fmt ← show_goals,
   tactic.save_info_thunk p
     (λ _, fmt)      

namespace interactive
/-
meta def intros : gentzen unit :=
tactic.intros >> return ()

meta def constructor : gentzen unit :=
tactic.constructor >> return ()

meta def trace (s : string) : gentzen unit :=
tactic.trace s

meta def assumption : gentzen unit :=
tactic.assumption

meta def inc : gentzen punit :=
modify (+1)
-/

meta def id : tactic unit :=
do tactic.applyc ``thm.id <|> tactic.fail "id tactic doesn't apply"

meta def truer : gentzen unit :=
do tactic.applyc ``thm.truer

meta def falsel : gentzen unit :=
do tactic.applyc ``thm.falsel

meta def andl : gentzen unit :=
do tactic.applyc ``thm.andl

meta def andr : gentzen unit :=
do tactic.applyc ``thm.andr

meta def orl : gentzen unit :=
do tactic.applyc ``thm.orl

meta def orr : gentzen unit :=
do tactic.applyc ``thm.orr

meta def impl : gentzen unit :=
do tactic.applyc ``thm.impl

meta def impr : gentzen unit :=
do tactic.applyc ``thm.impr

meta def rl (n : nat) : gentzen unit :=
do tactic.apply `(@thm.rl symb _ n).to_expr, tactic.skip

meta def rr (n : nat) : gentzen unit :=
do tactic.apply `(@thm.rr symb _ n).to_expr, tactic.skip

end interactive
end gentzen
