module

public import Oberwolfach.VortexExtended
public import Oberwolfach.OrdinaryInducedTargetNeighbourCount

@[expose] public section
/-! Consecutive vortex levels inherit the target minimum-degree bound from
the original regular host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_vortex_consecutive_target_degree (P:SimpleGraph V) (D m:ℕ) (β ε density:ℝ)
    (Q:Vortex U P D β ε m) (i:ℕ) (hi:i+1≤Q.length)
    (hdegree:density+β/2≤(D:ℝ)/Fintype.card V):
    ∀v∈Q.vertices i,density*(Q.vertices (i+1)).card≤
      (((Q.vertices (i+1))∩P.neighborFinset v).card:ℝ):=by
  intro v hv
  have hsub:Q.vertices i⊆Q.vertices ((i+1)-2):=
    finset_chain_subset Q.vertices Q.length Q.nested (by omega) (by omega)
  have hh:=Q.degrees (i+1) hi (by omega) v (hsub hv)
  have hh':|((P.neighborFinset v∩Q.vertices (i+1)).card:ℝ)-
      ((D:ℝ)/Fintype.card V)*(Q.vertices (i+1)).card|≤(β/2)*(Q.vertices (i+1)).card:=by
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hnonneg:0≤((Q.vertices (i+1)).card:ℝ):=by positivity
  have hscale:=mul_le_mul_of_nonneg_right hdegree hnonneg
  have hl:=(abs_le.mp hh').1
  have ht:density*(Q.vertices (i+1)).card≤((P.neighborFinset v∩Q.vertices (i+1)).card:ℝ):=by
    nlinarith only [hscale,hl]
  simpa only [Finset.inter_comm] using ht

def ordinaryContainedTarget (X Y:Finset V):Finset ↥X:=
  Finset.univ.filter (fun v=>v.val∈Y)

theorem ordinary_contained_target_image (X Y:Finset V) (hYX:Y⊆X):
    (ordinaryContainedTarget X Y).image (Subtype.val:↥X→V)=Y:=by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hx).2
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v,hYX hv⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
end Oberwolfach
