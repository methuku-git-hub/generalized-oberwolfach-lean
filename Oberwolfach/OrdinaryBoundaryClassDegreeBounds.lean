module

public import Oberwolfach.OrdinaryBoundaryRootSets
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! Every surviving boundary class and every class-membership count is
    bounded by the physical degree of the same actual host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_class_degree_bounds
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (Dmax:ℕ)
    (hdeg:∀w:V⊕U,(ordinaryPhysicalGraph Q H).degree w≤Dmax):
    (∀i,(ordinaryBoundaryRowSet H X Z i).card≤Dmax) ∧
    (∀j,(ordinaryBoundaryHubSet H Z X j).card≤Dmax) ∧
    (∀v,(Finset.univ.filter (fun i=>v∈ordinaryBoundaryRimSet Q X i)).card≤Dmax) ∧
    (∀z,(Finset.univ.filter (fun i=>z∈ordinaryBoundaryRowSet H X Z i)).card≤Dmax):=by
  have hrow (v:V):(Finset.univ.filter (H v)).card≤Dmax:=by
    have hh:=hdeg (Sum.inl v)
    rw [ordinary_physical_degree_row] at hh
    omega
  have hrim (v:V):Q.degree v≤Dmax:=by
    have hh:=hdeg (Sum.inl v)
    rw [ordinary_physical_degree_row] at hh
    omega
  have hcol (z:U):(Finset.univ.filter (fun v=>H v z)).card≤Dmax:=by
    have hh:=hdeg (Sum.inr z)
    rw [ordinary_physical_degree_column] at hh
    exact hh
  constructor
  · intro i
    exact (Finset.card_le_card (by intro z hz;simpa [ordinaryBoundaryRowSet] using (Finset.mem_filter.mp hz).2)).trans (hrow i.val)
  constructor
  · intro j
    exact (Finset.card_le_card (by intro v hv;simpa [ordinaryBoundaryHubSet] using (Finset.mem_filter.mp hv).2)).trans (hcol j.val)
  constructor
  · intro v
    let C:Finset {x:V // x∉X}:=Finset.univ.filter (fun i=>v∈ordinaryBoundaryRimSet Q X i)
    have hsub:C.image Subtype.val⊆Q.neighborFinset v:=by
      intro w hw
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hw
      have hv:Q.Adj i.val v:=by
        have hx: v∈Q.neighborFinset i.val∩X:=(Finset.mem_filter.mp hi).2
        exact (Q.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hx).1
      exact (Q.mem_neighborFinset _ _).mpr hv.symm
    have hh:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective,SimpleGraph.card_neighborFinset_eq_degree] at hh
    exact hh.trans (hrim v)
  · intro z
    let C:Finset {x:V // x∉X}:=Finset.univ.filter (fun i=>z∈ordinaryBoundaryRowSet H X Z i)
    have hsub:C.image Subtype.val⊆Finset.univ.filter (fun v=>H v z):=by
      intro w hw
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hw
      have hz:z∈Z.filter (H i.val):=(Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩
    have hh:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
    exact hh.trans (hcol z)
end Oberwolfach
