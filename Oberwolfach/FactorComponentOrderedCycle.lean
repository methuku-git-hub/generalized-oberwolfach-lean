module

public import Oberwolfach.FactorComponentCycle

@[expose] public section
/-! Enumerate a two-factor component in cyclic walk order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem two_factor_component_ordered_cycle (F : SimpleGraph V)
    (hF : F.IsRegularOfDegree 2) (v : V) :
    ∃ p : F.Walk v v, p.IsCycle ∧ p.support.dropLast.Nodup ∧
      3 ≤ p.support.dropLast.length ∧
      p.support.dropLast ++ [v] = p.support ∧
      ∀ x, x ∈ p.support.dropLast ↔ x ∈ (F.connectedComponentMk v).supp := by
  obtain ⟨p,hp,hcomp⟩:=two_factor_component_cycle F hF v
  have hlen : p.support.dropLast.length = p.length := by
    simp [List.length_dropLast, p.length_support]
  have hlen3 : 3 ≤ p.support.dropLast.length := by
    rw [hlen]
    exact hp.isCircuit.three_le_length
  have hdrop : p.support.dropLast ≠ [] := by
    apply List.ne_nil_of_length_pos
    omega
  have hv : v ∈ p.support.dropLast := by
    have hh := List.head_mem hdrop
    simpa [List.head_dropLast, p.head_support] using hh
  have hclosed : p.support.dropLast ++ [v] = p.support := by
    simpa using List.dropLast_append_getLast p.support_ne_nil
  refine ⟨p,hp,hp.nodup_dropLast_support,hlen3,hclosed,?_⟩
  intro x
  have hmem : (x∈p.support.dropLast ∨ x=v) ↔ x∈p.support := by
    simpa only [List.mem_append,List.mem_singleton] using
      Iff.of_eq (congrArg (fun xs : List V => x∈xs) hclosed)
  rw [←hcomp, p.mem_verts_toSubgraph, ←hmem]
  constructor
  · exact Or.inl
  · rintro (hx|rfl)
    · exact hx
    · exact hv
end Oberwolfach
