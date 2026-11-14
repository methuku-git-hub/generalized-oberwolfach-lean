module

public import Oberwolfach.MarkedHubFactorLift

@[expose] public section
/-! Vertex-disjoint cycles at a hub give the rim separation and terminal
avoidance needed to concatenate their physical paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor_interval_separation
    {V U E K I:Type*} [Fintype V] [DecidableEq V]
    (tail head:E→V) (ktail khead:K→V) (m b:ℕ) (π:Equiv.Perm V)
    (H₀ Hₖ:V→U→Prop) (u:U)
    (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (hM:∀C∈M,∀D∈M,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D))
    (select:I↪HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u)
    (hselect:∀i,select i∈M) (S:Finset V)
    (hS:∀C∈M,hubMarkedCycleVertices u C⊆S) (z:V) (hz:z∉S):
    (∀i j:I,i≠j→∀a b:Fin (m+1),(select i).val a≠(select j).val b) ∧
    (∀i:I,∀a:Fin (m+1),z≠(select i).val a) := by
  constructor
  · intro i j hij a b heq
    have hne:select i≠select j:=fun h=>hij (select.injective h)
    have hdis:=hM (select i) (hselect i) (select j) (hselect j) hne
    apply Finset.disjoint_left.mp hdis
      (show (select i).val a∈hubMarkedCycleVertices u (select i) from Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
    exact heq ▸ (show (select j).val b∈hubMarkedCycleVertices u (select j) from Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩)
  · intro i a heq
    apply hz
    apply hS (select i) (hselect i)
    rw [heq]
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
end Oberwolfach
