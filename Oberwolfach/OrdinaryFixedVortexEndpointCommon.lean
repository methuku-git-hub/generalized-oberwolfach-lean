module

public import Oberwolfach.OrdinaryEndpointFixedDomainsCommon
public import Oberwolfach.OrdinaryFixedVortexCleanupDomainGeometry
public import Oberwolfach.OrdinaryVortexLevelParentDensityBalance
public import Oberwolfach.OrdinaryFixedVortexConflict
public import Oberwolfach.OddSharpThreshold

@[expose] public section
/-! The original vortex geometry chooses endpoint parent weights on every
level before sampling, with all endpoint tests on one raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_endpoint_common
    (β ε ρ₀ α pmin t χ:ℝ) (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (ht:0<t) (hχ:0<χ)
    (d:ℕ) (hd:2≤d):
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀θhost:ℝ,cycleThreshold 3≤θhost→(θhost+α)*Fintype.card V≤D→
    ∃weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ,
      (∀i,i<Q.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (weight i)) ∧
    ∀(pR pH:ℝ) (hpR:pmin≤pR) (hpR1:pR≤1),pmin≤pH→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),(∀u,s u j=pH)→
    let hpR0:0≤pR:=hpmin.le.trans hpR;
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀i,i<Q.length→EndpointPhysicalPotentialEvent
        (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
        (markedVortexPermutation Q π hπ i) d j (weight i) pR pH t
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)):=by
  let K:ℝ:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  have hK:1≤K:=by
    dsimp [K]
    have h1:0≤1/(ε/2):=by positivity
    have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    linarith
  obtain ⟨M,hM,hcommon⟩:=ordinary_endpoint_fixed_domains_common K (ρ₀/8) pmin t ε χ hK (by positivity) hpmin ht hε (by linarith) hχ d hd
  obtain ⟨v₀,hv₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  obtain ⟨v₁,hv₁,hgeom⟩:=ordinary_fixed_vortex_cleanup_domain_geometry β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨max v₀ v₁,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ hnoshort θhost hthreshold hdegree
  let L:=Q.length-1
  let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
  let g:=fun i=>markedVortexHubEmbedding Q i
  let ρ:=markedVortexPermutation Q π hπ
  let A:=markedVortexInnerVertices Q
  let B:=markedVortexInnerHubs Q
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hmin:∀i≤L,M≤(A i).card:=by
    intro i hi
    have hh:=hgeom V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i (by have :=Q.length_pos;dsimp [L] at *;omega)
    exact hh.2.2.1
  have hstep:∀i<L,((A (i+1)).card:ℝ)≤ε*(A i).card:=by
    intro i hi
    exact (marked_vortex_fixed_active_geometry Q hε.le i).2.2.2.2.1
  have hsize':∀i≤L,
      (Fintype.card (markedVortexVertexType Q i):ℝ)≤K*(A i).card ∧
      (Fintype.card (markedVortexHubType Q i):ℝ)≤K*(A i).card:=by
    intro i hi
    have hh:=hsize V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i (by have :=Q.length_pos;dsimp [L] at *;omega)
    exact ⟨hh.2.2.2.1,hh.2.2.2.2.1⟩
  have hB:∀i≤L,(ρ₀/8)*(A i).card≤(B i).card:=by
    intro i hi
    exact (hgeom V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i (by have :=Q.length_pos;dsimp [L] at *;omega)).2.2.2.2.1
  have hparent:∀i≤L,∀v,
      (3/4:ℝ)*(A i).card≤(((A i)∩(P.comap (f i)).neighborFinset v).card:ℝ):=by
    intro i hi v
    have hh:=ordinary_vortex_level_parent_density_balance P D vsize β ε θhost α (initialIndexDensity U D) 0
      Q hn hreg rfl hρ hβ (by norm_num) hdegree i (by have :=Q.length_pos;dsimp [L] at *;omega)
    have hcoef:(3/4:ℝ)≤θhost+α-β/2:=by have ht3:=cycleThreshold_triangle_lower;linarith
    exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans (hh.1 v)
  have hconf':∀i≤L,permutationConflictGraph (ρ i) (3*d)≤(permutationConflictGraph π (3*d)).comap (f i):=by
    intro i hi
    have hh:=ordinary_fixed_vortex_conflict_restriction P D vsize β ε Q π hπ i (3*d)
    convert hh.ge using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hshort:∀i≤L,∀x k,0<k→k<2*d+1→((ρ i)^k) x≠x:=by
    intro i hi x k hk hk' heq
    have hcomm:∀x,f i (ρ i x)=π (f i x):=(marked_vortex_permutation_compatibility Q π hπ i).1
    have hh:=congrArg (f i) heq
    rw [permutation_embedding_power (f i) π (ρ i) hcomm k x] at hh
    exact hnoshort (f i x) k hk hk' hh
  obtain ⟨weight,hweight,hprob⟩:=hcommon V U Γ Color (markedVortexVertexType Q) (markedVortexHubType Q)
    P (permutationConflictGraph π (3*d)) f g ρ A B L hmin hstep (fun i hi=>(hsize' i hi).1)
    (fun i hi=>(hsize' i hi).2) hB
    (by intro i hi x hx v hv;convert hparent i hi v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hconf' hshort
  refine ⟨weight,?_,?_⟩
  · intro i hi
    convert hweight i (by have :=Q.length_pos;dsimp [L];omega) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro pR pH hpR hpR1 hpH q hq hQ s hs hS j hj hpR0
    have hh:=hprob pR pH hpR hpR1 hpH q hq hQ s hs hS j hj
    apply hh.trans
    apply finiteLaw_probability_mono
    intro σ hh i hi
    convert hh i (by have :=Q.length_pos;dsimp [L];omega) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
