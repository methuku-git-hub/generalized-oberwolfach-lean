module

public import Oberwolfach.OrdinaryNonrootRootRestrictionGeometry
public import Oberwolfach.MarkedFixedVortexSizes
public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! The original regular-host vortex yields the restricted root geometry
at every nonterminal parent, under the preselected numerical smallness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_root_restriction_geometry
    (P:SimpleGraph V) (D vsize:ℕ) (β ε ρ₀ lam ξ:ℝ)
    (Q:Vortex U P D β ε vsize) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ₀:0<ρ₀)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hv:0<vsize)
    (hξ:0≤ξ) (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2)
    (hεξ:ε≤ξ/2) (hερ:ε≤ξ*(ρ₀/8)/2) (hεroot:2*ε^2≤lam)
    (i:ℕ) (hi:i<Q.length):
    let X:=markedVortexInnerVertices Q i;let T:=markedVortexDeeperVertices Q i;
    let Z:=markedVortexInnerHubs Q i;let W:=markedVortexDeeperHubs Q i;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X)
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q i) ∧
    0<Fintype.card A ∧ 0<Fintype.card C ∧
    ((ρ₀/8)/2)*Fintype.card A≤Fintype.card C ∧ Fintype.card C≤Fintype.card A ∧
    (Xf.card:ℝ)≤ξ*Fintype.card A ∧ (Zf.card:ℝ)≤ξ*Fintype.card A ∧
    (Zf.card:ℝ)≤ξ*Fintype.card C :=by
  intro X T Z W A C Xf Zf
  let W₀:=markedVortexVertexType Q i
  let Z₀:=markedVortexHubType Q i
  have hWcard:Fintype.card W₀=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq hi.le]
  have hZcard:Fintype.card Z₀=(Q.indices i).card:=by
    change Fintype.card (Q.extendedIndices i)=(Q.indices i).card
    rw [Fintype.card_coe,Q.extendedIndices_eq hi.le]
  have hDpos:0<D:=by
    have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (show (0:ℝ)<D by linarith)
  have hWpos:0<Fintype.card W₀:=by
    rw [hWcard]
    have hh:=Q.vertices_lower (i:=i) hi.le
    have hvR:(0:ℝ)<vsize:=by exact_mod_cast hv
    exact_mod_cast (show (0:ℝ)<(Q.vertices i).card by nlinarith)
  have hlow:(ρ₀/8)*Fintype.card W₀≤(Fintype.card Z₀:ℝ):=by
    rw [hWcard,hZcard]
    exact Q.index_size_lower hreg hn hD hρ₀ hρlo hβ hβ1 hi.le
  have hupp:2*Fintype.card Z₀≤Fintype.card W₀:=by
    rw [hWcard,hZcard]
    exact Q.index_size_upper hreg hn hDpos hε.le hρhi hi.le
  have hinner:=(marked_vortex_inner_cardinalities Q i)
  have hstep:=Q.extended_successor_size_bounds hε.le i
  have hX:(X.card:ℝ)≤ε*Fintype.card W₀:=by
    have hh:=hstep.1
    simpa only [X,hinner.1,W₀,markedVortexVertexType,Fintype.card_coe] using hh
  have hZ:(Z.card:ℝ)≤ε*Fintype.card W₀:=by
    have hh:=hstep.2
    have hzu:(Fintype.card Z₀:ℝ)≤Fintype.card W₀:=by exact_mod_cast (show Fintype.card Z₀≤Fintype.card W₀ by omega)
    have hh':=mul_le_mul_of_nonneg_left hzu hε.le
    have hz:(Z.card:ℝ)≤ε*Fintype.card Z₀:=by
      simpa only [Z,hinner.2.2.1,Z₀,markedVortexHubType,Fintype.card_coe] using hh
    exact hz.trans hh'
  have hdeep:=marked_vortex_fixed_active_geometry Q hε.le i
  have hT:(T.card:ℝ)≤ε^2*Fintype.card W₀:=by
    have hh:=mul_le_mul_of_nonneg_left hX hε.le
    have hh':=hdeep.2.2.1
    nlinarith only [hh,hh']
  have hWd:(W.card:ℝ)≤ε^2*Fintype.card W₀:=by
    have hh:=mul_le_mul_of_nonneg_left hZ hε.le
    have hh':=hdeep.2.2.2.1
    nlinarith only [hh,hh']
  have hroot:(T.card:ℝ)+W.card≤lam*Fintype.card W₀:=by
    have hh:=mul_le_mul_of_nonneg_right hεroot (show (0:ℝ)≤Fintype.card W₀ by positivity)
    nlinarith only [hh,hT,hWd]
  exact ⟨hroot,ordinary_nonroot_root_restriction_geometry W₀ Z₀ T X W Z (ρ₀/8) lam ε ξ
    (by positivity) hξ hlam hlam1 hlamρ hε.le hεξ hερ hWpos hlow hupp hroot hX hZ⟩
end Oberwolfach
