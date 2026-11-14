module

public import Oberwolfach.OrdinaryVortexAsymmetricMatchingScales
public import Oberwolfach.OrdinaryVortexTriangleInnerSizeAndIndices
public import Oberwolfach.OrdinaryVortexLocalSizeInputs
public import Oberwolfach.OrdinaryVortexCleanupErrorRates

@[expose] public section
/-! The original vortex supplies the size, cleanup-error and linear matching
scale inputs of the general (not triangle-specific) sharp certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D mv:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε mv)

theorem ordinary_vortex_general_certificate_inner_bounds
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (i:ℕ) (hi:i<Q.length)
    (M:ℕ) (hM:4/ε≤(M:ℝ)) (hterminal:(M:ℝ)≤ε*mv/2)
    (δend εR εH rateParent Ledit:ℝ) (hδ:0≤δend)
    (hR:εR≤δend/4) (hH:εH≤δend/4) (hRate:rateParent≤δend*ε/8)
    (hEdit:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i))
    (ζh ζe γ eParent cMatch:ℝ) (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ)
    (he:γ≤eParent) (hc:0<cMatch)
    (hcBound:cMatch≤min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2):
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let n:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i);
    let κh:=γ*(1/4:ℝ)*ε;let κinner:=(1/4:ℝ)*ε;let θmatch:=cMatch*ε;
    I.Nonempty ∧ M≤I.card ∧ (ρ₀/8)*(I.card:ℝ)≤B.card ∧ B.card≤I.card ∧
    Fintype.card {u:markedVortexHubType Q i // u∉B}≤I.card^2 ∧
    Fintype.card {v:markedVortexVertexType Q i // v∉I}≤(ordinaryPhysicalInnerDomain I B).card^2 ∧
    εR*I.card+Ledit≤δend*I.card ∧ εH*B.card+Ledit≤δend*I.card ∧
    0<κh ∧ 0<κinner ∧ 0<θmatch ∧
    κh*n≤γ*I.card ∧ κinner*n≤(ordinaryPhysicalInnerDomain I B).card ∧
    θmatch≤ζh*κh ∧ θmatch≤ζe*κinner ∧ γ*I.card≤(eParent*ε)*n :=by
  intro I B n κh κinner θmatch
  have h2ε:2/ε≤(M:ℝ):=by
    have hh:0≤(1/ε:ℝ):=by positivity
    have htwo:2/ε=2*(1/ε):=by ring
    have hfour:4/ε=4*(1/ε):=by ring
    linarith only [hM,hh,htwo,hfour]
  obtain ⟨hI,hIM,hκ,hBI,_hJ,_hV⟩:=ordinary_vortex_local_size_inputs Q hreg hn hD hρ hρlo hρhi
    hβ hβ1 hε hm i hi M M (le_refl _) h2ε hterminal
  have hlarge:(4/ε:ℝ)≤I.card:=hM.trans (by exact_mod_cast hIM)
  have hindex:=(ordinary_vortex_triangle_inner_size_and_indices Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi).2 hlarge
  have hphysical:I.card≤(ordinaryPhysicalInnerDomain I B).card:=by
    rw [ordinary_physical_inner_domain_card]
    omega
  have hvIndex:Fintype.card {v:markedVortexVertexType Q i // v∉I}≤(ordinaryPhysicalInnerDomain I B).card^2:=by
    exact hindex.1.trans (Nat.pow_le_pow_left hphysical 2)
  have herr:=ordinary_vortex_cleanup_error_rates Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
    δend εR εH rateParent Ledit hδ hR hH hRate hEdit hBI
  have hs:=ordinary_vortex_asymmetric_matching_scales Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
    ζh ζe γ eParent hζh hζe hγ he
  have hθ:θmatch≤(min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2)*ε:=
    mul_le_mul_of_nonneg_right hcBound hε.le
  refine ⟨hI,hIM,hκ,hBI,hindex.2,hvIndex,herr.1,herr.2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [κh];positivity
  · dsimp [κinner];positivity
  · dsimp [θmatch];positivity
  · exact hs.2.2.2.2.1
  · exact hs.2.2.2.2.2.1
  · exact hθ.trans hs.2.2.2.2.2.2.1
  · exact hθ.trans hs.2.2.2.2.2.2.2.1
  · exact hs.2.2.2.2.2.2.2.2
end Oberwolfach
