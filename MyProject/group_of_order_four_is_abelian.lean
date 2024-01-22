import algebra.group_theory -- hypothetical import, does not exist in Lean 4

variables {G : Type*} [group G] [fintype G]

-- hypothetical definition: a group is abelian if its operation is commutative
class abelian (G : Type*) [group G] : Prop :=
(comm : ∀ a b : G, a * b = b * a)

theorem group_of_order_four_is_abelian (hG : fintype.card G = 4) : abelian G :=
begin
  -- strategy: show that for all a and b in G, a * b = b * a
  apply abelian.mk,
  intros a b,
  -- this is where we would use the fact that G has order 4 to show that a * b = b * a
  -- however, without a library for group theory, we cannot complete this proof in Lean 4
  sorry
end