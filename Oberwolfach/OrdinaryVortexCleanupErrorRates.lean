module

public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! Explicit rate conditions imply both local endpoint error inequalities
at each level of the fixed vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem ordinary_vortex_cleanup_error_rates
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<m) (i:ℕ) (hi:i<Q.length)
    (δend εR εH rateParent Ledit:ℝ) (hδ:0≤δend)
    (hR:εR≤δend/4) (hH:εH≤δend/4)
    (hRate:rateParent≤δend*ε/8)
    (hEdit:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i))
    (hZ:(markedVortexInnerHubs Q i).card≤(markedVortexInnerVertices Q i).card):
    εR*(markedVortexInnerVertices Q i).card+Ledit≤δend*(markedVortexInnerVertices Q i).card ∧
    εH*(markedVortexInnerHubs Q i).card+Ledit≤δend*(markedVortexInnerVertices Q i).card:=by
  have hf:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
  let A:ℝ:=(markedVortexInnerVertices Q i).card
  let Z:ℝ:=(markedVortexInnerHubs Q i).card
  let n:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)
  have hA:0≤A:=by dsimp [A];positivity
  have hZ0:0≤Z:=by dsimp [Z];positivity
  have hn0:0≤n:=by dsimp [n];positivity
  have hZA:Z≤A:=by dsimp [A,Z];exact_mod_cast hZ
  have hUV:(Fintype.card (markedVortexHubType Q i):ℝ)≤Fintype.card (markedVortexVertexType Q i):=by exact_mod_cast hf.2.2
  have hnEq:n=(Fintype.card (markedVortexVertexType Q i):ℝ)+Fintype.card (markedVortexHubType Q i):=by dsimp [n];simp
  have hεn:ε*n≤4*A:=by
    rw [hnEq]
    have hu:=mul_le_mul_of_nonneg_left hUV hε.le
    dsimp [A] at *
    nlinarith only [hf.1,hu]
  have hδn:=mul_le_mul_of_nonneg_left hεn hδ
  have hEdit':Ledit≤(δend*ε/8)*n:=hEdit.trans (mul_le_mul_of_nonneg_right hRate hn0)
  have hR':εR*A≤(δend/4)*A:=mul_le_mul_of_nonneg_right hR hA
  have hH':εH*Z≤(δend/4)*Z:=mul_le_mul_of_nonneg_right hH hZ0
  have hZ':(δend/4)*Z≤(δend/4)*A:=mul_le_mul_of_nonneg_left hZA (by positivity)
  have hδA:0≤δend*A:=mul_nonneg hδ hA
  change εR*A+Ledit≤δend*A ∧ εH*Z+Ledit≤δend*A
  constructor <;> nlinarith only [hδn,hEdit',hR',hH',hZ',hδA]
end Oberwolfach
