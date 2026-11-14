module

public import Oberwolfach.OrdinaryVortexTriangleInnerEditBudget
public import Oberwolfach.OrdinaryTriangleInnerNumericInputsFromScales
public import Oberwolfach.OrdinaryVortexLocalSizeInputs

@[expose] public section
/-! The original vortex size bounds and a bounded parent edit yield the
inner triangle numeric inputs at every nonterminal level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D mv:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε mv)

theorem ordinary_vortex_triangle_inner_numeric_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (i:ℕ) (hi:i<Q.length)
    (p εfactor ηend εrows δ εcount t lam:ℝ)
    (num:OrdinaryTriangleInnerNumericParameters p (ρ₀/8) εfactor ηend εrows δ εcount t lam)
    (hp:0<p) (M b₀:ℕ) (hM:32≤M) (hMε:4/ε≤(M:ℝ))
    (hMb:(b₀:ℝ)≤lam*M) (hterminal:(M:ℝ)≤ε*mv/2)
    (L Ledit tR tH tP δactual rateParent:ℝ)
    (hL:0≤L) (hLb:L≤b₀) (hE:0≤Ledit) (hrate:rateParent≤lam*ε/4)
    (hEdit:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)):
    let A:=markedVortexInnerVertices Q i;let Z:=markedVortexInnerHubs Q i;
    tR≤εcount*A.card/2→tH≤εcount*Z.card/2→tP≤t→δactual≤δ→
    A.Nonempty ∧ M≤A.card ∧ (ρ₀/8)*(A.card:ℝ)≤Z.card ∧ Z.card≤A.card ∧
    Fintype.card {v:markedVortexVertexType Q i // v∉A}≤A.card^2 ∧
    Fintype.card {u:markedVortexHubType Q i // u∉Z}≤A.card^2 ∧
    tR+4*Ledit≤εcount*A.card ∧ tH+3*Ledit≤εcount*Z.card ∧
    tR+4*Ledit≤εrows*A.card ∧ tH+3*Ledit≤εrows*Z.card ∧
    L≤(A.card:ℝ)/24 ∧ L≤εfactor*A.card ∧
    δactual+(2*40+(1+2*40)/(2*(ρ₀/8)*p))*L/A.card+
      (tP+10*(40/((ρ₀/8)*p^5))*Ledit/A.card)≤ηend:=by
  intro A Z hR hH hP hδ
  have h2ε:2/ε≤(M:ℝ):=by
    have hh:0≤(1/ε:ℝ):=by positivity
    have htwo:2/ε=2*(1/ε):=by ring
    have hfour:4/ε=4*(1/ε):=by ring
    linarith only [hMε,hh,htwo,hfour]
  obtain ⟨hA,hAs,hZA,hZ,_hJ,_hI⟩:=ordinary_vortex_local_size_inputs Q hreg hn hD hρ hρlo hρhi
    hβ hβ1 hε hm i hi M M (le_refl _) h2ε hterminal
  have hApos:0<(A.card:ℝ):=by exact_mod_cast Finset.card_pos.mpr hA
  have hAM:(M:ℝ)≤A.card:=by exact_mod_cast hAs
  have hLsmall:L≤lam*A.card:=by
    exact hLb.trans (hMb.trans (mul_le_mul_of_nonneg_left hAM num.lambda_pos.le))
  have hEsmall:Ledit≤lam*A.card:=ordinary_vortex_triangle_inner_edit_budget Q hreg hn hD hρ hρlo hρhi
    hβ hβ1 hε hm i hi lam rateParent Ledit num.lambda_pos.le hrate hEdit
  have hlarge:(4/ε:ℝ)≤A.card:=hMε.trans hAM
  have hidx:=(ordinary_vortex_triangle_inner_size_and_indices Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi).2 hlarge
  have hκ:0<ρ₀/8:=by positivity
  have hs:=ordinary_triangle_inner_numeric_inputs_from_scales p (ρ₀/8) εfactor ηend εrows δ εcount t lam
    A.card Z.card L Ledit tR tH tP δactual num hp hκ hApos hZA hL hLsmall hE hEsmall hR hH hP hδ
  have hrow:tR+4*Ledit≤εrows*A.card:=hs.1.trans
    (mul_le_mul_of_nonneg_right num.count_rows (Nat.cast_nonneg _))
  have hindex:tH+3*Ledit≤εrows*Z.card:=hs.2.1.trans
    (mul_le_mul_of_nonneg_right num.count_rows (Nat.cast_nonneg _))
  exact ⟨hA,hAs,hZA,hZ,hidx.1,hidx.2,hs.1,hs.2.1,hrow,hindex,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2⟩
end Oberwolfach
