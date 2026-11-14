module

public import Oberwolfach.ActualResidualAnchorProtection

@[expose] public section
/-! Set inclusions used to exclude reserved spoke labels from the old image
and from the newly required inner labels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_spoke_label_set_exclusions {I V:Type} [DecidableEq V] {X:I→Type} [∀i,DecidableEq (X i)]
    (Old:∀i,Finset (X i)) (ψ:∀i,X i→V) (Outer Forbidden Required Reserve:I→Finset V)
    (Inner:Finset V)
    (hOld:∀i,Disjoint ((Old i).image (ψ i)) (Outer i))
    (hForbidden:∀i,Forbidden i⊆Outer i)
    (hRequired:∀i,Required i⊆Inner\Reserve i)
    (hReserve:∀i,Forbidden i∩Inner⊆Reserve i):
    (∀i x,x∈Old i→ψ i x∉Forbidden i) ∧
    (∀i,Disjoint (Required i) (Forbidden i)) :=by
  constructor
  · intro i x hx hforbid
    have him:ψ i x∈(Old i).image (ψ i):=Finset.mem_image.mpr ⟨x,hx,rfl⟩
    exact (Finset.disjoint_left.mp (hOld i)) him (hForbidden i hforbid)
  · intro i
    apply Finset.disjoint_left.mpr
    intro v hv hforbid
    have hin: v∈Inner ∧ v∉Reserve i:=Finset.mem_sdiff.mp (hRequired i hv)
    exact hin.2 (hReserve i (Finset.mem_inter.mpr ⟨hforbid,hin.1⟩))
end Oberwolfach
