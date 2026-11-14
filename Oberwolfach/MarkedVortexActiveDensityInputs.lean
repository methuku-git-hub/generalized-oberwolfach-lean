module

public import Oberwolfach.MarkedActiveHubDensityArithmetic
public import Oberwolfach.MarkedVortexNonDeeperInnerHubs
public import Oberwolfach.MarkedVortexNonDeeperGeometry
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! Active vertex and hub density fields for the actual vortex levels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_active_density_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (hehalf:ε≤1/2) (hm:0<m)
    (ω:ℝ) (hω:0≤ω) (hωv:ω≤ε/8) (hωu:ω≤ρ₀*ε/64)
    (L:ℕ) (hL:L<Q.length):
    ∀ i≤L,
      let VP:=markedVortexVertexType Q i
      let Ukeep:=markedVortexNonDeeperHubType Q i
      let Vkeep:=markedVortexNonDeeperVertexType Q i
      let W:=↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
        Finset (markedVortexVertexType Q (i+1)))
      let Zinner:=markedVortexInnerNonDeeperHubs Q i
      ω*Fintype.card (Vkeep⊕Ukeep)≤(Fintype.card W:ℝ) ∧
      ω*Fintype.card (Vkeep⊕Ukeep)≤(Zinner.card:ℝ):=by
  intro i hi VP Ukeep Vkeep W Zinner
  let I:=markedVortexInnerVertices Q i
  let J:=markedVortexInnerHubs Q i
  let T:=markedVortexDeeperVertices Q i
  let R:=markedVortexDeeperHubs Q i
  have hsize:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ hρlo hρhi hb hb1 he hm i (by omega)
  have hgeom:=marked_vortex_fixed_active_geometry Q he.le i
  have hA:Fintype.card W=(I\T).card:=by
    have hh:=marked_vortex_next_active_parent_image Q i
    rw [←hh,Finset.card_image_of_injective _ (by
      intro x y hxy
      exact (markedVortexNextActiveInNonDeeper Q i).injective
        ((markedVortexNonDeeperVertexEmbedding Q i).injective hxy))]
    simp only [Finset.card_univ]
    rfl
  have hB:Zinner.card=(J\R).card:=by
    have hh:=marked_vortex_inner_nondeeper_hubs_image Q i
    rw [←hh,Finset.card_image_of_injective _ (markedVortexNonDeeperHubToParent Q i).injective]
  have hAr:(Fintype.card W:ℝ)=(I.card:ℝ)-T.card:=by
    rw [hA,Finset.card_sdiff,Finset.inter_eq_left.mpr hgeom.1,Nat.cast_sub (Finset.card_le_card hgeom.1)]
  have hBr:(Zinner.card:ℝ)=(J.card:ℝ)-R.card:=by
    rw [hB,Finset.card_sdiff,Finset.inter_eq_left.mpr hgeom.2.1,Nat.cast_sub (Finset.card_le_card hgeom.2.1)]
  have hV:(Fintype.card Vkeep:ℝ)≤Fintype.card VP:=by
    change (Fintype.card ↥((Finset.univ\T):Finset VP):ℝ)≤Fintype.card VP
    rw [Fintype.card_coe]
    exact_mod_cast (Finset.card_le_univ (Finset.univ\T))
  have hU:(Fintype.card Ukeep:ℝ)≤Fintype.card VP:=by
    have hh:Fintype.card Ukeep≤Fintype.card (markedVortexHubType Q i):=by
      change Fintype.card ↥((Finset.univ\R):Finset (markedVortexHubType Q i))≤_
      rw [Fintype.card_coe]
      exact Finset.card_le_univ (Finset.univ\R)
    exact_mod_cast hh.trans hsize.2.2
  have hres:=marked_active_hub_density_arithmetic (Fintype.card VP) (Fintype.card Vkeep) (Fintype.card Ukeep)
    I.card J.card T.card R.card (Fintype.card W) Zinner.card ε ρ₀ ω
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    he hehalf hρ hω hV hU hsize.1 hsize.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hAr hBr hωv hωu
  simpa only [Fintype.card_sum,Nat.cast_add] using hres
end Oberwolfach
