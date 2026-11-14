module

public import Oberwolfach.OrdinaryTriangleFixedDomainsCommon
public import Oberwolfach.OrdinaryFixedVortexDeepCoverInputs
public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! Robust deep cover holds simultaneously on every fixed vortex level of
one raw sample. All local host means, degrees and conflict bounds come from
the original regular host and vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_triangle_cover_common
    (α ρ₀ p:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hp:0<p) (hp1:p≤1):
    ∃κ:ℝ,0<κ ∧ ∀(ε χ:ℝ),0<ε→ε<1/4→ε≤κ→ε≤ρ₀/16→0<χ→
    ∀(β:ℝ),0≤β→β≤1/4→β≤α/8→β≤κ→
    ∀d:ℕ,∀hd:2≤d,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold 3≤θhost→
      (θhost+α)*Fintype.card V≤D→
    ∀(pR pH:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH→pH≤1→pR=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    let hpR0:0≤pR:=hp.le.trans hpR;
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀i,i<Q.length→OrdinaryTriangleFiniteCoverOuterDegreeEvent κ
        (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)):=by
  obtain ⟨κ,hκ,hcommon⟩:=ordinary_triangle_cover_fixed_domains_common (α/2) p (ρ₀/16)
    (by positivity) hp hp1 (by positivity)
  refine ⟨κ,hκ,?_⟩
  intro ε χ hε hε1 hεa hεsmall hχ β hβ hβ1 hβα hβε d hd
  obtain ⟨M,hM,hcommon⟩:=hcommon ε χ hε (by linarith) hχ (2*(3*d)) d hd
  obtain ⟨v₀,hv₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    pR pH hpR hpR1 hpH hpH1 hpEq q hq hQ s hs hS j hj hpR0
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) (show (0:ℝ)≤Fintype.card V by positivity)
    nlinarith only [hh,hdegree]
  let L:=Q.length-1
  have hL:L<Q.length:=by have :=Q.length_pos;dsimp [L];omega
  let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
  let g:=fun i=>markedVortexHubEmbedding Q i
  let ρi:=markedVortexPermutation Q π hπ
  let A:=markedVortexInnerVertices Q
  let B:=markedVortexInnerHubs Q
  have hmin:∀i≤L,M≤(A i).card:=by
    intro i hi
    have hh:=hsize V U P D vsize hreg hn hDhalf hρlo hρhi hv Q i (by omega)
    have he:0≤ε*((A i).card:ℝ):=by positivity
    have hs:=hh.2.1
    exact_mod_cast (show (M:ℝ)≤(A i).card by nlinarith only [hs,he])
  have hstep:∀i<L,((A (i+1)).card:ℝ)≤ε*(A i).card:=by
    intro i hi
    exact (marked_vortex_fixed_active_geometry Q hε.le i).2.2.2.2.1
  have hinputs:∀i≤L,OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d (α/2) p (ρ₀/16) κ κ
      (P.comap (f i)) ((permutationConflictGraph π (3*d)).comap (f i)) (ρi i) (B i) pR pH
      (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D) β:=by
    intro i hi
    have hh:=ordinary_fixed_vortex_deep_cover_inputs 2 d P D vsize β ε θhost α (α/2) ρ₀ p (ρ₀/16) κ κ pR pH
      Q π hπ hreg hn hθ hthreshold hα (by linarith) hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hβε
      hε hεa (by linarith) (by omega) hnoshort hpR hpR1 hpH hpH1 hpEq i (by omega)
    exact hh
  have hgood:=hcommon V U Γ Color (markedVortexVertexType Q) (markedVortexHubType Q)
    P (permutationConflictGraph π (3*d)) f g ρi A B L hmin hstep pR pH hpR0 hpR1
    (fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D) (fun _=>β)
    (by intro i hi; convert hinputs i hi using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) q hq hQ s hs hS j hj
  apply hgood.trans
  apply finiteLaw_probability_mono
  intro σ hh i hi
  have hlocal:=hh i (by have :=Q.length_pos;dsimp [L];omega)
  convert hlocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
