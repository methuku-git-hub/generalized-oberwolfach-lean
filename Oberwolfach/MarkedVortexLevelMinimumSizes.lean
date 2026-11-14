module

public import Oberwolfach.MarkedNestedVortexActiveGeometry
public import Oberwolfach.MarkedActiveSizeThreshold
public import Oberwolfach.MarkedVortexNonDeeperGeometry

@[expose] public section
/-! The size thresholds in the level record are reached uniformly over the
fixed vortex levels once its terminal scale is sufficiently large. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_level_minimum_sizes (ρ₀ ε:ℝ) (hρ:0<ρ₀) (he:0<ε) (he1:ε≤1/4) (N NI:ℕ):
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
      G.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→m₀≤m→
      ∀ L:ℕ,L<Q.length→∀ i≤L,
      let VP:=markedVortexVertexType Q i
      let I:=markedVortexInnerVertices Q i
      let W:=↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
        Finset (markedVortexVertexType Q (i+1)))
      N≤Fintype.card VP ∧ N≤Fintype.card W ∧ NI≤I.card:=by
  obtain ⟨m₀,hm₀,hsize⟩:=marked_active_size_threshold ρ₀ ε hρ he (max N NI) N
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hD hrlo hrhi hb hb1 hm L hL i hi VP I W
  have hg:=marked_nested_vortex_active_geometry Q ρ₀ hρ hreg hn hD hrlo hrhi hb hb1 he.le he1 (i+1) (by omega)
  have hN:(N:ℝ)≤Fintype.card W:=by
    have hh:=(hsize m hm).1
    change (N:ℝ)≤Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1)))
    rw [Fintype.card_coe]
    exact hh.trans hg.2.2.2.1
  have hNI:(NI:ℝ)≤Fintype.card W:=by
    have hh:=(hsize m hm).2.1
    have hmax:(NI:ℝ)≤(max N NI:ℕ):=by exact_mod_cast (le_max_right N NI)
    change (NI:ℝ)≤Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1)))
    rw [Fintype.card_coe]
    exact hmax.trans (hh.trans hg.2.2.2.1)
  have hA:Fintype.card W≤I.card:=by
    have hh:=marked_vortex_next_active_parent_image Q i
    have hc:=congrArg Finset.card hh
    rw [Finset.card_image_of_injective _ (by
      intro x y hxy
      exact (markedVortexNextActiveInNonDeeper Q i).injective
        ((markedVortexNonDeeperVertexEmbedding Q i).injective hxy)),Finset.card_univ] at hc
    exact hc ▸ Finset.card_le_card (by intro x hx;exact (Finset.mem_sdiff.mp hx).1)
  have hI:I.card≤Fintype.card VP:=Finset.card_le_univ I
  have hNnat:N≤Fintype.card W:=by exact_mod_cast hN
  have hNInat:NI≤Fintype.card W:=by exact_mod_cast hNI
  exact ⟨hNnat.trans (hA.trans hI),hNnat,hNInat.trans hA⟩
end Oberwolfach
