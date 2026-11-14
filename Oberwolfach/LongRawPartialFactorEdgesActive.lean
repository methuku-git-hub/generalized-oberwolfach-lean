module

public import Oberwolfach.LongRawSelectedOrdinaryActive

@[expose] public section
/-! A partial factor whose source edges map into selected ordinary rims has
all of those image edges in the original raw approximate rim layer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_partial_factor_edges_active
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    ∀x y, (∃a:LongRawSelectedOrdinary π d m ℓ e M,
      longRawSelectedRimRelation π d m ℓ e M a x y) →
      rawMarkedPairRims P π d raw (Sum.inl (x,y)) ∨
      rawMarkedPairRims P π d raw (Sum.inl (y,x)) :=by
  intro state e R M x y h
  obtain ⟨a,ha⟩:=h
  exact long_raw_selected_ordinary_rim_active P π d m ℓ raw g j M a x y ha
end Oberwolfach
