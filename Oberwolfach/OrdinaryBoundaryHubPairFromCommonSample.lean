module

public import Oberwolfach.OrdinaryBoundaryHubPairStability
public import Oberwolfach.RawOrdinaryDomainIndexEvent

@[expose] public section
/-! The original common-hub sample supplies eligible hubs for every actual
outside rim edge after the bounded spoke-row edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_parent_hub_pairs_from_common_sample
    (Q Q' F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (Z:Finset U)
    (pH t L β:ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hQsub:Q'≤Q) (hQF:Disjoint Q F)
    (hcols:RawOrdinaryDomainIndices F π d 3 Z pH j t σ)
    (hrow:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v))
      (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hmargin:β*Fintype.card (V⊕U)+t+2*L≤pH^2*Z.card):
    ∀a c,Q'.Adj a c→β*Fintype.card (V⊕U)≤((Z.filter (fun u=>H a u∧H c u)).card:ℝ):=by
  intro a c hac
  have hne:a≠c:=hac.ne
  have hF:¬F.Adj a c:=by
    intro hf
    exact (disjoint_iff_inf_le.mp hQF) (v:=a) (w:=c) ⟨hQsub hac,hf⟩
  have hfree:∀v∈({a,c}:Finset V),∀w∈({a,c}:Finset V),¬F.Adj v w:=by
    intro v hv w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
    rcases hv with rfl|rfl <;> rcases hw with rfl|rfl
    · exact fun h=>F.irrefl h
    · exact hF
    · exact fun h=>hF h.symm
    · exact fun h=>F.irrefl h
  have hh:=hcols {a,c} (by simp [hne]) hfree
  have he:common Z ({a,c}:Finset V) (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))=
      Z.filter (fun u=>rawWheelSpokes π d σ j a u∧rawWheelSpokes π d σ j c u):=by
    ext u
    simp [mem_common_iff]
  rw [he,Finset.card_pair hne] at hh
  have hst:=ordinary_boundary_hub_pair_count_stability (rawWheelSpokes π d σ j) H Z a c L (hrow a) (hrow c)
  have hraw:=(abs_lt.mp hh).1
  have hdiff:=(abs_le.mp hst).2
  linarith only [hraw,hdiff,hmargin]
end Oberwolfach
