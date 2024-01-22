import Mathlib
import Duper
import LeanCopilot
variable {G : Type*} [Group G] [Fintype G]

-- hypothetical definition: a group is abelian if its operation is commutative
class abelian (G : Type*) [Group G] : Prop :=
(comm : ∀ a b : G, a * b = b * a)

theorem group_of_order_four_is_abelian (hG : Fintype.card G = 4) : abelian G := by
  apply abelian.mk
  intro a b
  let A := Subgroup.closure {a} -- this is a subgroup of G
  haveI : Fintype A := .ofFinite _
  have hq:= Subgroup.card_subgroup_dvd_card A
  rw [hG] at hq
  by_cases Fintype.card A = 4
  have hA : A = G := by
    apply ext z
    intro x
    split
    intro hx
    exact Subgroup.mem_top x
    intro hx
    exact hx
  have hA : A = {1, a, a * a, a * a * a} := by
    sorry
  by_cases Fintype.card A = 2
  have hA : A = {1, a} := by
    apply ext z
    intro x
    split
    intro hx
    have h1 : x = 1 ∨ x = a := by
      apply Subgroup.mem_closure_singleton.mp
      exact hx
    cases h1
    rw [h1]
    exact Subgroup.mem_insert 1 {a}
    rw [h1]
    exact Subgroup.mem_insert_of_mem 1 (Subgroup.mem_singleton a)
    intro hx
    cases hx
    rw [hx]
    exact Subgroup.one_mem A
    rw [hx]
    exact Subgroup.mem_closure_singleton.mpr (Or.inr rfl)
  have hA : a * a = 1 := by
    have h1 : a * a ∈ A := by
      rw [hA]
      exact Subgroup.mem_insert_of_mem 1 (Subgroup.mem_insert_of_mem a (Subgroup.mem_singleton a))
    have h2 : a * a = 1 ∨ a * a = a := by
      apply Subgroup.mem_closure_singleton.mp
      exact h1
    cases h2
    exact h2
    have h3 : a * a = a * a * a := by
      rw [←h2]
      rw [←mul_assoc]
      rw [mul_one]
    exact h3
    by_cases b = 1
    exact h
    by_cases b = a
    exact h
    have hA A = {1, a, a * b, b} := by
    sorry
    have hA : a * b = b * a := by
    sorry
    by_cases Fintype.card A = 1
    have hA : A = {1} := by
    sorry
    have hA : a * b = b * a := by
    sorry

  --if Fintype.card A = 4
  --then have hA : A = G
  --A isabelian
  --G is abelian
  --if Fintype.card A = 2
  --then have hA : A = {1, a}
  --have hA : a * a = 1
  --if b = e, true
  --if b = a, true
  --if b = a * a, true
  --else b≠b*b
  --G = {1, a, a*b, b}
  --a*b = b*a
