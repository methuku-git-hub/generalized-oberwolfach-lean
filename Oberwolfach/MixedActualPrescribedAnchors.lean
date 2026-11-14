module

public import Oberwolfach.ActualPrescribedAnchorEmbedding
public import Oberwolfach.RetainedAndRawIntervalGeometry

@[expose] public section
/-! Construct the actual prescribed anchor injection from the original
retained-final and raw-approximate intervals in the same mixed outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_actual_prescribed_anchor_embedding
    {X V K J U Γ Color:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [Fintype K] [DecidableEq K] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (π:Equiv.Perm V) (hnoshort:∀x l,0<l→l<2*data.d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀ g₁:Γ) (hclasses:g₀≠g₁) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π data.d σ g₀) t) (w:U)
    (index:K ≃ retainedAndRawIntervalIndex π data.d σ g₀ g₁ t Jret w)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (hsrc:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))):
    let root:=fun i=>retainedAndRawIntervalRoot π data.d σ g₀ g₁ t Jret w (index i)
    ∃g:{x // x∈data.prescribed}↪V,
      ∀i (j:Fin (data.d+1)) (hj:bufferedMarker data.c data.d (ext i) j∈data.prescribed),
        g ⟨bufferedMarker data.c data.d (ext i) j,hj⟩=(π^j.val) (root i):=by
  classical
  intro root
  have hgeom:=retained_and_raw_interval_geometry π data.d data.hd hnoshort σ g₀ g₁ hclasses t Jret w
  apply actual_prescribed_anchor_embedding data ext hsupp hsrc π root
  · intro i
    exact hgeom.1 (index i)
  · intro i j hij
    exact hgeom.2 (index i) (index j) (fun h=>hij (index.injective h))
end Oberwolfach
