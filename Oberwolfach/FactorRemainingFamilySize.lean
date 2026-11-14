module

public import Oberwolfach.FactorPrunedFamilyRemoval

@[expose] public section
/-! After the small classes are removed, the number of remaining prescribed
factors is exactly half the residual regular degree. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_remaining_family_size {W:Type} [Fintype W] (D:ℕ) (hEven:Even D)
    (hsize:Fintype.card W=D/2) (removed:Finset W)
    (hbound:2*removed.card≤D):
    Fintype.card {w:W // w∉removed}=(D-2*removed.card)/2 ∧
    Even (D-2*removed.card):=by
  have hcard:removed.card≤D/2:=by omega
  have hrem:Fintype.card {w:W // w∉removed}=Fintype.card W-removed.card:=by
    simp
  constructor
  · rw [hrem,hsize]
    omega
  · obtain ⟨k,hk⟩:=hEven
    refine ⟨k-removed.card,?_⟩
    omega
end Oberwolfach
