module

public import Oberwolfach.MarkedVortexInnerUpperSizeInputs
public import Oberwolfach.MarkedVortexSmallRemainderInputs

@[expose] public section
/-! The deeper sets are two vortex steps below the parent, giving an
ε²-scale parent bound while retaining the ε-scale bound inside the inner set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_two_step_remainder_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (hehalf:ε≤1/2)
    (κ hcut ξ:ℝ) (hek:ε^2≤κ) (hec:ε≤hcut) (hex:ε^2≤ξ)
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
  have hupper:=marked_vortex_inner_upper_size_inputs Q hreg hn hD hρhi he ε le_rfl L hL i hi
  have hgeom:=marked_vortex_fixed_active_geometry Q he i
  have hT:(T.card:ℝ)≤ε^2*Fintype.card W:=by
    have hh:=mul_le_mul_of_nonneg_left hupper.1 he
    nlinarith only [hgeom.2.2.1,hh]
  have hR:(R.card:ℝ)≤ε^2*Fintype.card W:=by
    have hh:=mul_le_mul_of_nonneg_left hupper.2 he
    nlinarith only [hgeom.2.2.2.1,hh]
  have hW:(0:ℝ)≤Fintype.card W:=Nat.cast_nonneg _
  have hI:(0:ℝ)≤I.card:=Nat.cast_nonneg _
  have hJ:(0:ℝ)≤J.card:=Nat.cast_nonneg _
  have hbase:=marked_vortex_small_remainder_inputs Q hreg hn hD hρhi he hehalf ε ε ε le_rfl le_rfl le_rfl L hL i hi
  refine ⟨hT.trans (mul_le_mul_of_nonneg_right hek hW),hR.trans (mul_le_mul_of_nonneg_right hek hW),
    hgeom.2.2.1.trans (mul_le_mul_of_nonneg_right hec hI),
    hgeom.2.2.2.1.trans (mul_le_mul_of_nonneg_right hec hJ),
    hT.trans (mul_le_mul_of_nonneg_right hex hW),hR.trans (mul_le_mul_of_nonneg_right hex hW),hbase.2.2.2.2.2.2⟩
end Oberwolfach
