module

public import Oberwolfach.MarkedRestrictedDegreePhysicalOnRoots

@[expose] public section
/-! A single bound on actual changed-edge degrees outside the protected set
controls the first-inner and deeper restricted degrees simultaneously. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_two_restricted_degrees_outside
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A T:Finset V)
    (hπ:∀v,π v∈A↔v∈A)
    (σ τ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V) (δ:ℝ)
    (hchange:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈D.edgeFinset)
    (hD:∀v,v∉A→(D.degree v:ℝ)≤δ):
    ∀mark incoming v,v∉A→
      |(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v A:ℝ)-
        (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v A:ℝ)|≤δ ∧
      |(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v T:ℝ)-
        (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v T:ℝ)|≤δ :=by
  let Roots:=Finset.univ\A
  have hRoots:∀v,v∈Roots→π v∈Roots:=by
    intro v hv
    have hvA:v∉A:=(Finset.mem_sdiff.mp hv).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h=>hvA ((hπ v).mp h)⟩
  have hD':∀v∈Roots,(D.degree v:ℝ)≤δ:=by
    intro v hv
    exact hD v (Finset.mem_sdiff.mp hv).2
  intro mark incoming v hv
  have hv':v∈Roots:=Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩
  exact ⟨marked_restricted_degree_after_physical_changes_on_roots P π d A σ τ D δ hchange Roots hRoots hD' mark incoming v hv',
    marked_restricted_degree_after_physical_changes_on_roots P π d T σ τ D δ hchange Roots hRoots hD' mark incoming v hv'⟩
end Oberwolfach
