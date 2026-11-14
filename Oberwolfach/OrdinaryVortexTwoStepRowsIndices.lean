module

public import Oberwolfach.OrdinaryRowsIndicesVortexCommon
public import Oberwolfach.OrdinaryVortexTwoStepEventSizes

@[expose] public section
/-! Row and index tests on the pair two levels down hold together over all
eligible vortex parents on the original raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_two_step_rows_indices_event
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
      (fun σ=>∀i,i+2≤Q.length→
        RawOrdinaryRows (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d h
          (ordinaryVortexBufferedVertices Q i 2) p (fun z=>s (markedVortexHubEmbedding Q i z)) j
          (εR*(ordinaryVortexBufferedVertices Q i 2).card)
          (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) ∧
        RawOrdinaryDomainIndices (F.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d h
          (ordinaryVortexBufferedHubs Q i 2) pH j (εH*(ordinaryVortexBufferedHubs Q i 2).card)
          (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)):=by
  let K:ℝ:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  have hK:1≤K:=by
    dsimp [K]
    have h1:0≤1/(ε/2):=by positivity
    have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    linarith
  have hK2:1≤K^2:=by nlinarith
  obtain ⟨M,hM,hcommon⟩:=ordinary_rows_indices_vortex_common h d hd εR εH (K^2) ε χ hεR hεH hK2 hε (by linarith) hχ
  obtain ⟨m₀,hm₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F D m hreg hn hD hρlo hρhi hm Q π hπ hnoshort hF
    p hp hp1 q hq hQ s hs hS j pH hj
  by_cases hlen:2≤Q.length
  · let L:=Q.length-2
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=fun i=>markedVortexHubEmbedding Q i
    let ρ:=markedVortexPermutation Q π hπ
    let A:=fun i=>ordinaryVortexBufferedVertices Q i 2
    let B:=fun i=>ordinaryVortexBufferedHubs Q i 2
    have hAcard:∀i,(A i).card=(Q.extendedVertices (i+2)).card:=by
      intro i
      have hh:=congrArg Finset.card (ordinary_vortex_buffered_images Q i 2).1
      rwa [Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective] at hh
    have hBcard:∀i,(B i).card=(Q.extendedIndices (i+2)).card:=by
      intro i
      have hh:=congrArg Finset.card (ordinary_vortex_buffered_images Q i 2).2
      rwa [Finset.card_image_of_injective _ (markedVortexHubEmbedding Q i).injective] at hh
    have hgeom:∀i≤L,M≤(A i).card ∧ M≤(B i).card ∧
        (Fintype.card (markedVortexVertexType Q i):ℝ)≤K^2*(A i).card ∧
        (Fintype.card (markedVortexHubType Q i):ℝ)≤K^2*(A i).card ∧
        (Fintype.card (markedVortexVertexType Q i):ℝ)≤K^2*(B i).card:=by
      intro i hi
      have hi0:i<Q.length:=by dsimp [L] at hi;omega
      have hi1:i+1<Q.length:=by dsimp [L] at hi;omega
      have h0:=hsize V U P D m hreg hn hD hρlo hρhi hm Q i hi0
      have h1:=hsize V U P D m hreg hn hD hρlo hρhi hm Q (i+1) hi1
      exact ordinary_vortex_two_step_event_sizes P D m β ε K Q i M hK hε.le
        ⟨h0.2.2.2.1,h0.2.2.2.2.1⟩ ⟨h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2.2⟩
    have hstepA:∀i<L,((A (i+1)).card:ℝ)≤ε*(A i).card:=by
      intro i hi
      rw [hAcard,hAcard]
      simpa only [show i+1+2=i+2+1 by omega] using (Q.extended_successor_size_bounds hε.le (i+2)).1
    have hstepB:∀i<L,((B (i+1)).card:ℝ)≤ε*(B i).card:=by
      intro i hi
      rw [hBcard,hBcard]
      simpa only [show i+1+2=i+2+1 by omega] using (Q.extended_successor_size_bounds hε.le (i+2)).2
    have hh:=hcommon V U Γ Color (markedVortexVertexType Q) (markedVortexHubType Q) P F π hnoshort hF
      f g ρ (fun i x=>(marked_vortex_permutation_compatibility Q π hπ i).1 x) A B L
      (fun i hi=>(hgeom i hi).1) (fun i hi=>(hgeom i hi).2.1) hstepA hstepB
      (fun i hi=>(hgeom i hi).2.2.1) (fun i hi=>(hgeom i hi).2.2.2.1) (fun i hi=>(hgeom i hi).2.2.2.2)
      p hp hp1 q hq hQ s hs hS j pH hj
    apply hh.trans
    apply finiteLaw_probability_mono
    intro σ hgood i hi
    have hidx:i≤L:=by dsimp [L];omega
    convert hgood i hidx using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · have heq:(fun σ:RawWheelOutcome V U Γ Color=>∀i,i+2≤Q.length→
        RawOrdinaryRows (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d h
          (ordinaryVortexBufferedVertices Q i 2) p (fun z=>s (markedVortexHubEmbedding Q i z)) j
          (εR*(ordinaryVortexBufferedVertices Q i 2).card)
          (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) ∧
        RawOrdinaryDomainIndices (F.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d h
          (ordinaryVortexBufferedHubs Q i 2) pH j (εH*(ordinaryVortexBufferedHubs Q i 2).card)
          (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ))=(fun _=>True):=by
      funext σ
      apply propext
      constructor
      · intro _;trivial
      · intro _ i hi;omega
    rw [heq,finiteLaw_probability_true]
    linarith
end Oberwolfach
