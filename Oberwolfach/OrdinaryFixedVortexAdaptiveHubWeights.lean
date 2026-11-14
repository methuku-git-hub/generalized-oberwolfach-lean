module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsFixedDomains
public import Oberwolfach.OrdinaryHubPotentialUniformEditBudget
public import Oberwolfach.OrdinaryFixedVortexConflict
public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! Once the fixed cycle weights and their setups are chosen, one raw sample
supplies the adaptive hub weights at every fixed vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_adaptive_hub_weights
    (m d:ℕ) (hm:2≤m) (hd:2≤d)
    (β ε ρ₀ pmin ξ Lconf cLo cHi b Bweight ηHub Kdom χ:ℝ)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hpmin:0<pmin) (hξ:0<ξ) (hcHi:0<cHi) (hχ:0<χ)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom):
    ∃t ζ:ℝ,0<t ∧ 0<ζ ∧ ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(pR pH:ℝ) (hpR:0≤pR) (hpR1:pR≤1)
      (Dlevel Ledit density tR tH βe βh:ℕ→ℝ)
      (weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ),
      (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (weight i) pmin pR pH (Dlevel i) β ξ Lconf cLo cHi b Bweight ηHub Kdom)→
      (∀i,i<Q.length→0≤Ledit i ∧ Ledit i≤ζ*(markedVortexInnerVertices Q i).card)→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hpR) (fun _=>hpR1)
      d hd q hq hQ s hs hS)).probability (fun σ=>∀i,i<Q.length→
      OrdinaryAdaptiveHubWeightsLevelEvent m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
        pR pH (density i) (tR i) (tH i) (Ledit i) (βe i) (βh i) b Bweight ηHub
        (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)):=by
  obtain ⟨t,ζ,ht,hζ,hbudget⟩:=ordinary_hub_potential_uniform_edit_budget m pmin cHi ξ hpmin hcHi hξ
  let K₀:ℝ:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  have hK₀:0≤K₀:=by
    dsimp [K₀]
    have h1:0≤1/(ε/2):=by positivity
    have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    linarith
  have hK:0≤Kdom:=hK₀.trans hKdom
  obtain ⟨M₀,hM₀,hcommon⟩:=ordinary_adaptive_hub_weights_fixed_domains m d hm hd
    pmin β ξ Lconf cLo cHi b Bweight ηHub Kdom t Kdom ε χ hpmin hcHi ht hK hε (by linarith) hχ
  obtain ⟨v₀,hv₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M₀
  refine ⟨t,ζ,ht,hζ,v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ hnoshort
    pR pH hpR hpR1 Dlevel Ledit density tR tH βe βh weight hsetup hedit q hq hQ s hs hS j
  let L:=Q.length-1
  let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
  let g:=fun i=>markedVortexHubEmbedding Q i
  let ρi:=markedVortexPermutation Q π hπ
  let A:=markedVortexInnerVertices Q
  let B:=markedVortexInnerHubs Q
  have hmin:∀i≤L,M₀≤(A i).card:=by
    intro i hi
    have hh:=hsize V U P D vsize hreg hn hD hρlo hρhi hv Q i (by have :=Q.length_pos;dsimp [L] at *;omega)
    have he:0≤ε*((A i).card:ℝ):=by positivity
    have hs:=hh.2.1
    exact_mod_cast (show (M₀:ℝ)≤(A i).card by nlinarith only [hs,he])
  have hstep:∀i<L,((A (i+1)).card:ℝ)≤ε*(A i).card:=by
    intro i hi
    exact (marked_vortex_fixed_active_geometry Q hε.le i).2.2.2.2.1
  have hZ:∀i≤L,(Fintype.card (markedVortexHubType Q i):ℝ)≤Kdom*(A i).card:=by
    intro i hi
    have hh:=hsize V U P D vsize hreg hn hD hρlo hρhi hv Q i (by have :=Q.length_pos;dsimp [L] at *;omega)
    have hk:=mul_le_mul_of_nonneg_right hKdom (show (0:ℝ)≤(A i).card by positivity)
    exact hh.2.2.2.2.1.trans hk
  have hconf:∀i≤L,permutationConflictGraph (ρi i) (3*d)≤(permutationConflictGraph π (3*d)).comap (f i):=by
    intro i hi
    have hh:=ordinary_fixed_vortex_conflict_restriction P D vsize β ε Q π hπ i (3*d)
    change (permutationConflictGraph π (3*d)).comap (f i)=permutationConflictGraph (ρi i) (3*d) at hh
    exact hh.symm.le
  have hshort:∀i≤L,∀x l,0<l→l<2*d+1→((ρi i)^l) x≠x:=by
    intro i hi x l hl hl' heq
    have hcomm:∀x,f i (ρi i x)=π (f i x):=(marked_vortex_permutation_compatibility Q π hπ i).1
    have hh:=congrArg (f i) heq
    rw [permutation_embedding_power (f i) π (ρi i) hcomm l x] at hh
    exact hnoshort (f i x) l hl hl' hh
  have hsetup':∀i≤L,OrdinaryInnerHubWeightSetupGeneral m (P.comap (f i))
      ((permutationConflictGraph π (3*d)).comap (f i)) (A i) (weight i)
      pmin pR pH (Dlevel i) β ξ Lconf cLo cHi b Bweight ηHub Kdom:=by
    intro i hi
    exact hsetup i (by have :=Q.length_pos;dsimp [L] at *;omega)
  have hmargin:∀i≤L,t+((m+1:ℕ):ℝ)^2*(4*cHi/pmin^(3*m+1))*Ledit i/(A i).card+
      2*(3*((m+1:ℕ):ℝ)^4*(4*cHi/pmin^(3*m+1))*Ledit i/(A i).card)≤ξ:=by
    intro i hi
    have hp:(0:ℝ)<(A i).card:=by exact_mod_cast (show 0<(A i).card by have hh:=hmin i hi;omega)
    have he:=hedit i (by have :=Q.length_pos;dsimp [L] at *;omega)
    exact hbudget (A i).card (Ledit i) hp he.1 he.2
  have hgood:=hcommon V U Γ Color (markedVortexVertexType Q) (markedVortexHubType Q)
    P (permutationConflictGraph π (3*d)) f g ρi A B L hmin hstep hZ hconf hshort pR pH hpR hpR1
    Dlevel Ledit density tR tH βe βh weight
    (by intro i hi; convert hsetup' i hi using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hmargin q hq hQ s hs hS j
  apply hgood.trans
  apply finiteLaw_probability_mono
  intro σ hh i hi
  have hlocal:=hh i (by have :=Q.length_pos;dsimp [L];omega)
  convert hlocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
