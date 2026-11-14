module

public import Oberwolfach.OrdinaryApproximateLabelsOccupiedFromMarkers
public import Oberwolfach.OrdinaryMatchedResidualHubPackage

@[expose] public section

/-! The retained marker witness puts every approximate-start label in the
same package's old image, for arbitrary source vertex types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_package_approximate_occupied
    {n:ℕ} {U X J W:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [Fintype J] [DecidableEq J]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (u:U)
    (t:ℕ) (R:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (G:SimpleGraph X) (Arc:Fin n→Fin n→Prop) (Avail Reserve:Finset (Fin n))
    (Good:W→Prop) (Pack:W→Finset (Finset (Fin n)))
    (Pos:W→{a:Fin n // rawIntervalColouredStart π d (fun e=>σ (u,e)) a true}→Finset ℕ) (len:J→ℕ)
    (pk:OrdinaryMatchedResidualHubPackage G m d π (retainedAndRawIntervalRoot π d σ false true t R u)
      Arc Avail Reserve Good Pack Pos len)
    (hmarkers:∀i∈pk.data.s₂,∀j:Fin (d+1),
      ∃x∈pk.data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) pk.inner,
        pk.ψ x=(π^j.val) (retainedAndRawIntervalRoot π d σ false true t R u i)):
    ∀x,rawIntervalFamilyState π d σ (x,u)=some (Sum.inl true)→
      x∈(pk.data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) pk.inner).image pk.ψ :=by
  exact ordinary_approximate_labels_occupied_from_markers π d σ u pk.data pk.hs₂
    (bufferedPathStrictInterior (fun _=>(m+1)*d) pk.inner) pk.ψ
    (retainedAndRawIntervalRoot π d σ false true t R u) (by intro b; rfl) hmarkers
end Oberwolfach
