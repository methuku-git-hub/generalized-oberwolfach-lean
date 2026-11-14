module

public import Oberwolfach.OrdinaryRowsIndicesVortexCommon
public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! The original vortex geometry supplies the size hypotheses for all
ordinary row and hub tests on a single pre-exposure sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_rows_indices_event
    (h d:ℕ) (hd:2≤d) (εR εH β ε ρ₀ χ:ℝ)
    (hεR:0<εR) (hεH:0<εH) (hβ:0≤β) (hβ1:β≤1/4)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hχ:0<χ):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P F:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→permutationConflictGraph π (3*d)≤F→
    ∀(p:ℝ) (hp:0≤p) (hp1:p≤1)
      (q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑a,q u a)) (j:Color) (pH:ℝ) (hj:∀u,s u j=pH),
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀i,i<Q.length→
        RawOrdinaryRows (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d h
          (markedVortexInnerVertices Q i) p (fun z=>s (markedVortexHubEmbedding Q i z)) j
          (εR*(markedVortexInnerVertices Q i).card)
          (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) ∧
        RawOrdinaryDomainIndices (F.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d h
          (markedVortexInnerHubs Q i) pH j (εH*(markedVortexInnerHubs Q i).card)
          (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)):=by
  let K:ℝ:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  have hK:1≤K:=by
    dsimp [K]
    have h1:0≤1/(ε/2):=by positivity
    have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    linarith
  obtain ⟨M,hM,hcommon⟩:=ordinary_rows_indices_vortex_common h d hd εR εH K ε χ hεR hεH hK hε (by linarith) hχ
  obtain ⟨m₀,hm₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F D m hreg hn hD hρlo hρhi hm Q π hπ hnoshort hF
    p hp hp1 q hq hQ s hs hS j pH hj
  let L:=Q.length-1
  have hL:L<Q.length:=by have :=Q.length_pos;dsimp [L];omega
  have hsize':∀i≤L,
      (M:ℝ)≤(1-ε)*((markedVortexInnerVertices Q i).card:ℝ) ∧
      (M:ℝ)≤(1-ε)*((markedVortexInnerHubs Q i).card:ℝ) ∧
      (Fintype.card (markedVortexVertexType Q i):ℝ)≤K*(markedVortexInnerVertices Q i).card ∧
      (Fintype.card (markedVortexHubType Q i):ℝ)≤K*(markedVortexInnerVertices Q i).card ∧
      (Fintype.card (markedVortexVertexType Q i):ℝ)≤K*(markedVortexInnerHubs Q i).card:=by
    intro i hi
    have hh:=hsize V U P D m hreg hn hD hρlo hρhi hm Q i (by omega)
    exact hh.2
  let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
  let g:=fun i=>markedVortexHubEmbedding Q i
  let ρ:=markedVortexPermutation Q π hπ
  let A:=markedVortexInnerVertices Q
  let B:=markedVortexInnerHubs Q
  have hnA:∀i≤L,M≤(A i).card:=by
    intro i hi
    have hh:=(hsize' i hi).1
    have hn:(0:ℝ)≤(A i).card:=by positivity
    have he:ε*(A i).card≥0:=by positivity
    exact_mod_cast (show (M:ℝ)≤(A i).card by nlinarith only [hh,he])
  have hnB:∀i≤L,M≤(B i).card:=by
    intro i hi
    have hh:=(hsize' i hi).2.1
    have he:ε*(B i).card≥0:=by positivity
    exact_mod_cast (show (M:ℝ)≤(B i).card by nlinarith only [hh,he])
  have hstepA:∀i<L,((A (i+1)).card:ℝ)≤ε*(A i).card:=by
    intro i hi
    exact (marked_vortex_fixed_active_geometry Q hε.le i).2.2.2.2.1
  have hstepB:∀i<L,((B (i+1)).card:ℝ)≤ε*(B i).card:=by
    intro i hi
    exact (marked_vortex_fixed_active_geometry Q hε.le i).2.2.2.2.2
  have hWA:∀i≤L,(Fintype.card (markedVortexVertexType Q i):ℝ)≤K*(A i).card:=fun i hi=>(hsize' i hi).2.2.1
  have hZA:∀i≤L,(Fintype.card (markedVortexHubType Q i):ℝ)≤K*(A i).card:=fun i hi=>(hsize' i hi).2.2.2.1
  have hWB:∀i≤L,(Fintype.card (markedVortexVertexType Q i):ℝ)≤K*(B i).card:=fun i hi=>(hsize' i hi).2.2.2.2
  have hh:=hcommon V U Γ Color (markedVortexVertexType Q) (markedVortexHubType Q) P F π hnoshort hF
    f g ρ (fun i x=>(marked_vortex_permutation_compatibility Q π hπ i).1 x) A B L hnA hnB hstepA hstepB hWA hZA hWB
    p hp hp1 q hq hQ s hs hS j pH hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hgood i hi
  have hidx:i≤L:=by have hp:=Q.length_pos;dsimp [L];omega
  convert hgood i hidx using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
