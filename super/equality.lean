import .clause .prover_state .utils
open tactic monad expr list

namespace super

meta def try_unify_eq_l (c : clause) (i : nat) : tactic clause := do
guard $ clause.literal.is_neg (clause.get_lit c i),
qf ← clause.open_metan c c↣num_quants,
match is_eq (qf↣1↣get_lit i)↣formula with
| none := failed
| some (lhs, rhs) := do
unify lhs rhs,
ty ← infer_type lhs,
univ ← infer_univ ty,
refl ← return $ app_of_list (const ``eq.refl [univ]) [ty, lhs],
opened ← clause.open_constn qf↣1 i,
clause.meta_closure qf↣2 $ clause.close_constn (opened↣1↣inst refl) opened↣2
end

meta def unify_eq_inf : inference := take given, sequence' $ do
i ← given↣selected,
[(do u ← ↑(try_unify_eq_l given↣c i), add_inferred u [given]) <|> return ()]

meta def has_refl_r (c : clause) : bool :=
list.bor $ do
literal ← c↣get_lits,
guard literal↣is_pos,
match is_eq literal↣formula with
| some (lhs, rhs) := [decidable.to_bool (lhs = rhs)]
| none := []
end

meta def refl_r_pre : resolution_prover unit :=
preprocessing_rule $ take new, return (filter (λc, ¬has_refl_r c) new)

end super
