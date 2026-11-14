module

public import Oberwolfach.MixedFreshPairingParentInsideRoots
public import Oberwolfach.OrdinaryGeneralHubConditionsFromCleanup
public import Oberwolfach.OrdinaryMixedHubWeightsGeneral
public import Oberwolfach.OrdinaryEndpointPairingGeometryFromCleanup
public import Oberwolfach.OrdinaryEndpointSizesFromCleanup

@[expose] public section
/-! The actual cleanup profile and adaptive general-length hub weights
    furnish the whole fresh pairing parent on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinary_pairing_parent_from_cleanup
    (m b₀:ℕ) (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ κ b Bweight p₀ a ε η pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH L βe βh s j σ)
    (hA:A.Nonempty) (hpH:p₀≤pH) (hpH1:pH≤1)
    (hγscale:γ*Fintype.card V≤βe*Fintype.card (V⊕U))
    (hκscale:κ*Fintype.card V≤βe*Fintype.card (V⊕U))
    (hF:∀v,(F.degree v:ℝ)≤ε*Fintype.card V)
    (hFphys:∀w:V⊕U,(ordinaryPhysicalGraph F (fun _ _=>False)).degree w≤b₀)
    (hRbudget:a*Fintype.card (V⊕U)+tR+L≤pR*density*A.card)
    (hHbudget:a*Fintype.card (V⊕U)+tH+L≤pH*Z.card)
    (hrow:∀x,(tH+2*L)+pH*(tH+L)≤η*(Z.filter (H x)).card)
    (hcol:∀x,(tR+2*L)+pH*(tR+L)≤η*(A∩Q.neighborFinset x).card)
    (hcodeg:∀x,(tH+3*L)+pH^2*(tH+L)≤η*(Z.filter (H x)).card)
    (hw:OrdinaryMixedHubWeightsOfLength m b Bweight η Q F H A Z):
    MixedFreshPairingParentInsideRoots m b₀ γ κ b Bweight p₀ a ε η
      (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A)
      (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr)
      (fun _=>pH):=by
  have hhub:=ordinary_general_hub_conditions_from_cleanup P Q F H A Z π d j s γ κ pR pH density tR tH L βe βh σ
    profile hA hγscale hκscale
  have hsize:=ordinary_endpoint_sizes_from_cleanup P Q F H A Z π d j s pR pH density tR tH L βe βh a σ
    profile hRbudget hHbudget
  have hgeom:=ordinary_endpoint_pairing_geometry_from_cleanup P Q F H A Z π d j s pR pH density tR tH L βe βh a η σ
    profile hsize.1 hsize.2 hrow hcol hcodeg
  refine
    { mapped_host := ?_
      endpoint_disjoint := hgeom.1
      hub_size := hhub.1
      endpoint_size := hgeom.2.1
      endpoint_probability := fun _=>⟨hpH,hpH1⟩
      rim_conflict := hF
      physical_conflict := hFphys
      hub_neighborhoods := hhub.2
      endpoint_row := hgeom.2.2.1
      endpoint_column := hgeom.2.2.2.1
      endpoint_codegree := hgeom.2.2.2.2
      hub_weight := hw.weight
      hub_weight_bounds := hw.bounds
      hub_weight_load := hw.loads }
  rw [graph_map_inl_physical]
  intro x y hxy
  cases x <;> cases y <;> simpa [ordinaryPhysicalGraph] using hxy
end Oberwolfach
