module

public import Oberwolfach.MarkedLevelSmallRemainderBounds
public import Oberwolfach.MarkedFixedVortexParentDegrees

@[expose] public section
/-! Size fields for the actual fixed vortex, including the non-deeper
vertex complement and the independently rounded hub sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_small_remainder_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (hehalf:ε≤1/2)
    (κ hcut ξ:ℝ) (hek:ε≤κ) (hec:ε≤hcut) (hex:ε≤ξ)
    (L:ℕ) (hL:L<Q.length):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let I:=markedVortexInnerVertices Q i
      let T:=markedVortexDeeperVertices Q i
      let J:=markedVortexInnerHubs Q i
      let R:=markedVortexDeeperHubs Q i
      (T.card:ℝ)≤κ*Fintype.card W ∧ (R.card:ℝ)≤κ*Fintype.card W ∧
      (T.card:ℝ)≤hcut*I.card ∧ (R.card:ℝ)≤hcut*J.card ∧
      (T.card:ℝ)≤ξ*Fintype.card W ∧ (R.card:ℝ)≤ξ*Fintype.card W ∧
      (Fintype.card W:ℝ)/2≤(Fintype.card ↥((Finset.univ\T):Finset W):ℝ):=by
  intro i hi W I T J R
  have hcard: Fintype.card (markedVortexHubType Q i)≤Fintype.card W:=by
    have hh:=Q.index_size_upper hreg hn hD he hρhi (i:=i) (by omega)
    change Fintype.card ↥(Q.extendedIndices i)≤Fintype.card ↥(Q.extendedVertices i)
    simp only [Fintype.card_coe]
    rw [Q.extendedIndices_eq (by omega:i≤Q.length),Q.extendedVertices_eq (by omega:i≤Q.length)]
    omega
  have hJ:(J.card:ℝ)≤Fintype.card W:=by
    exact_mod_cast (le_trans (Finset.card_le_univ J) hcard)
  obtain ⟨_,_,hT,hR,_,_⟩:=marked_vortex_fixed_active_geometry Q he i
  exact marked_level_small_remainder_bounds I T J R ε κ hcut ξ he hehalf hek hec hex hT hR hJ
end Oberwolfach
