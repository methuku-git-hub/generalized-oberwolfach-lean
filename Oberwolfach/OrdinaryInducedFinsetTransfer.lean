module

public import Oberwolfach.OrdinaryInducedCommonCard

@[expose] public section
/-! Exact set and cardinality transfer for subsets of an induced domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def ordinaryInducedFinset (T Y:Finset V):Finset {v:V // v∈T}:=
  Finset.univ.filter (fun v=>v.val∈Y)

theorem ordinary_induced_finset_image (T Y:Finset V) (hYT:Y⊆T):
    (ordinaryInducedFinset T Y).image Subtype.val=Y:=by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hx).2
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v,hYT hv⟩,by simp [ordinaryInducedFinset,hv],rfl⟩

theorem ordinary_induced_finset_card (T Y:Finset V) (hYT:Y⊆T):
    (ordinaryInducedFinset T Y).card=Y.card:=by
  have hh:=Finset.card_image_of_injective (ordinaryInducedFinset T Y)
    (Subtype.val_injective : Function.Injective (Subtype.val : {v:V // v∈T}→V))
  rw [ordinary_induced_finset_image T Y hYT] at hh
  exact hh.symm

theorem ordinary_induced_finset_sdiff (T Y Z:Finset V):
    ordinaryInducedFinset T (Y\Z)=ordinaryInducedFinset T Y\ordinaryInducedFinset T Z:=by
  ext v
  simp [ordinaryInducedFinset]
end Oberwolfach
