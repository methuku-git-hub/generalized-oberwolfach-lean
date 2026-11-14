module

public import Oberwolfach.OrdinaryVortexAsymmetricMatchingScales
public import Oberwolfach.OrdinaryBoundaryIndexCountFromInnerSizeBoth

@[expose] public section
/-! Actual vortex sizes supply the linear inner-domain margin and the two
quadratic index bounds required by the inner triangle factor events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem ordinary_vortex_triangle_inner_size_and_indices
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<m) (i:ℕ) (hi:i<Q.length):
    let A:=markedVortexInnerVertices Q i;
    let Z:=markedVortexInnerHubs Q i;
    let n:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i);
    (ε/4)*n≤A.card ∧
    ((4/ε:ℝ)≤A.card→
      Fintype.card {v:markedVortexVertexType Q i // v∉A}≤A.card^2 ∧
      Fintype.card {u:markedVortexHubType Q i // u∉Z}≤A.card^2):=by
  intro A Z n
  have hs:=ordinary_vortex_asymmetric_matching_scales Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
    1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_,_,_,_,hlo,_,_,_,_⟩:=hs
  have hsize:(ε/4)*n≤(A.card:ℝ):=by convert hlo using 1 <;> ring
  refine ⟨hsize,?_⟩
  intro hlarge
  have hn0:0≤n:=by dsimp [n];positivity
  have hAn:0≤(A.card:ℝ):=by positivity
  have hInv:0<(4/ε:ℝ):=by positivity
  have hN:n≤(4/ε)*A.card:=by
    have hh:=mul_le_mul_of_nonneg_left hsize (le_of_lt hInv)
    have heq:(4/ε)*(ε/4)=1:=by field_simp
    have hmul:(4/ε)*(ε/4*n)=n:=by rw [←mul_assoc,heq,one_mul]
    rw [hmul] at hh
    exact hh
  have hf:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
  have hV:(Fintype.card (markedVortexVertexType Q i):ℝ)≤n:=by
    dsimp [n]
    simp only [Fintype.card_sum,Nat.cast_add]
    have hh:(0:ℝ)≤Fintype.card (markedVortexHubType Q i):=by positivity
    linarith
  have hU:(Fintype.card (markedVortexHubType Q i):ℝ)≤n:=by
    dsimp [n]
    simp only [Fintype.card_sum,Nat.cast_add]
    have hh:(0:ℝ)≤Fintype.card (markedVortexVertexType Q i):=by positivity
    linarith
  have hboth:=ordinary_boundary_index_count_from_inner_size_both A Z (4/ε) hlarge (hV.trans hN) (hU.trans hN)
  exact ⟨hboth.2,hboth.1⟩
end Oberwolfach
