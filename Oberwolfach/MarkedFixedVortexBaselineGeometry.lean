module

public import Oberwolfach.MarkedFixedVortexEventInputs
public import Oberwolfach.MarkedFixedVortexMinimumDomains
public import Oberwolfach.MarkedFixedVortexScaleInputs
public import Oberwolfach.MarkedFixedVortexParentHubDensity

@[expose] public section
/-! The actual pre-exposure vortex supplies the geometric, finite-domain,
scale and permutation inputs of the baseline marked reference event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_baseline_geometry
    (β ε ρ₀:ℝ) (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (he1:ε<1/4)
    (hr:0<ρ₀) (M:ℕ):
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D ≤ 1→
      m₀≤m→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (L:ℕ),L<Q.length→
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let ρ:=markedVortexPermutation Q π hpres
    let I:=markedVortexInnerVertices Q
    let T:=markedVortexDeeperVertices Q
    let J:=markedVortexInnerHubs Q
    let Wrem:=markedVortexDeeperHubs Q
    (∀ i x,f i (ρ i x)=π (f i x)) ∧
    (∀ i≤L,
      M≤(I i).card ∧ M≤(J i).card ∧ M≤Fintype.card (W i) ∧ M≤Fintype.card (Z i) ∧
      (ρ₀/8)*(Fintype.card (W i):ℝ)≤Fintype.card (Z i) ∧ Fintype.card (Z i)≤Fintype.card (W i) ∧
      (I i).card≤Fintype.card (W i) ∧ (J i).card≤Fintype.card (W i) ∧
      (Fintype.card (W (i+1)):ℝ)≤ε*Fintype.card (W i) ∧
      T i⊆I i ∧ Wrem i⊆J i ∧
      (((T i).card:ℝ)≤ε*(I i).card) ∧ (((Wrem i).card:ℝ)≤ε*(J i).card) ∧
      (((I (i+1)).card:ℝ)≤ε*(I i).card) ∧ (((J (i+1)).card:ℝ)≤ε*(J i).card) ∧
      (∀ x,ρ i x∈I i↔x∈I i) ∧ (∀ x,ρ i x∈T i↔x∈T i)):=by
  obtain ⟨m₀,hm₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hb hb1 he he1 hr M
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hrlo hrhi hm Q π hpres L hL W Z f ρ I T J Wrem
  have hmpos:0<m:=by omega
  constructor
  · exact fun i=>(marked_vortex_permutation_compatibility Q π hpres i).1
  · intro i hi
    have hi':i<Q.length:=by omega
    have hs:=hsize V U G D m hreg hn hD hrlo hrhi hm Q i hi'
    have hmin:=marked_vortex_event_minimum_domains Q M i he.le hs.2.1 hs.2.2.1
    have hhub:=marked_vortex_fixed_parent_hub_density Q hreg hn hD hr hrlo hb hb1 i hi'.le
    have hscale:=marked_vortex_reference_scale_inputs Q hreg hn hD hr hrlo hrhi hb hb1 he hmpos i hi'
    have hgeom:=marked_vortex_fixed_active_geometry Q he.le i
    have hπ:=marked_vortex_permutation_compatibility Q π hpres i
    exact ⟨hmin.1,hmin.2.1,hmin.2.2.1,hmin.2.2.2,hhub,hscale.2.2.1,hscale.1,hscale.2.1,hscale.2.2.2,
      hgeom.1,hgeom.2.1,hgeom.2.2.1,hgeom.2.2.2.1,hgeom.2.2.2.2.1,hgeom.2.2.2.2.2,hπ.2.1,hπ.2.2⟩
end Oberwolfach
