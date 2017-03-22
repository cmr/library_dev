import .basic

open lattice

run_cmd tactic.mk_simp_attr `lattice_simp

section

variable {α : Type}
variable [lattice α]
variables (p q s : α)

@[lattice_simp]
private lemma la1 : p ≤ p := weak_order.le_refl p
@[lattice_simp]
private lemma la2 : p ≤ s → q ≤ s → p ⊔ q ≤ s := semilattice_sup.sup_le p q s
@[lattice_simp]
private lemma la3 : p ≤ s ∨ q ≤ s → p ⊓ q ≤ s := begin intro h, cases h,
    exact inf_le_left_of_le a,
    exact inf_le_right_of_le a
end

@[lattice_simp]
private lemma la4 : s ≤ p → s ≤ q → s ≤ p ⊓ q := le_inf

@[lattice_simp]
private lemma la5 : s ≤ p ∨ s ≤ q → s ≤ p ⊔ q := begin intro h, cases h,
    exact le_sup_left_of_le a,
    exact le_sup_right_of_le a,
end

@[lattice_simp]
private lemma la6 : p ≤ s → s ≤ q → p ≤ q := take h1 h2, weak_order.le_trans p s q h1 h2
@[lattice_simp]
private lemma la7 : p = q → p ≤ q ∧ q ≤ p := take h1, begin split,
    rw h1,
    rw -h1,
end

end

namespace tactic.interactive
open tactic

meta def lattice : tactic unit := --simp [] [`lattice_simp, `simp] [] []
    do lemmas ← get_user_simp_lemmas `lattice_simp,
       S ← simp_lemmas.mk_default,
       simplify_goal (S^.join lemmas) >> try triv

end tactic.interactive


--set_option pp.all true
