module

public import Oberwolfach.OrdinaryVortexLocalSizeInputs
public import Oberwolfach.OrdinaryVortexCleanupErrorRates

@[expose] public section
/-! Geometry and edit errors required by the local pairing theorem are
simultaneous consequences of one sufficiently large fixed vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D mv:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε mv)

theorem ordinary_vortex_pairing_input_geometry
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (i:ℕ) (hi:i<Q.length)
    (Ncert N:ℕ) (hN:Ncert≤N) (hsize:2/ε≤N) (hterminal:(N:ℝ)≤ε*mv/2)
    (δend εR εH rateParent Ledit:ℝ) (hδ:0≤δend)
    (hR:εR≤δend/4) (hH:εH≤δend/4) (hRate:rateParent≤δend*ε/8)
    (hEdit:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)):
    let A:=markedVortexInnerVertices Q i;let Z:=markedVortexInnerHubs Q i;
    A.Nonempty ∧ Ncert≤A.card ∧ (ρ₀/8)*(A.card:ℝ)≤Z.card ∧ Z.card≤A.card ∧
    Fintype.card {u:markedVortexHubType Q i // u∉Z}≤A.card^2 ∧
    Fintype.card {v:markedVortexVertexType Q i // v∉A}≤(ordinaryPhysicalInnerDomain A Z).card^2 ∧
    εR*A.card+Ledit≤δend*A.card ∧ εH*Z.card+Ledit≤δend*A.card:=by
  intro A Z
  obtain ⟨hA,hNcert,hZA,hZ,hJ,hI⟩:=ordinary_vortex_local_size_inputs Q hreg hn hD hρ hρlo hρhi
    hβ hβ1 hε hm i hi Ncert N hN hsize hterminal
  have herr:=ordinary_vortex_cleanup_error_rates Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
    δend εR εH rateParent Ledit hδ hR hH hRate hEdit hZ
  exact ⟨hA,hNcert,hZA,hZ,hJ,hI,herr.1,herr.2⟩
end Oberwolfach
