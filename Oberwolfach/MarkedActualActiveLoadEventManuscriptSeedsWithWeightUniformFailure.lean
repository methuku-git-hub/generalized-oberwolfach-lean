module

public import Oberwolfach.MarkedActualActiveLoadEventSeededWithWeightUniformFailure
public import Oberwolfach.MarkedActualActiveLoadEventSeededWithWeight
public import Oberwolfach.MarkedActualActiveLoadEventSeeded
public import Oberwolfach.MarkedSeedDensities
public import Oberwolfach.MarkedActiveSeedMass
public import Oberwolfach.MarkedActiveSizeThreshold
public import Oberwolfach.MarkedNestedVortexActiveGeometry
public import Oberwolfach.MarkedRetainedLocalLoadVortex
public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
/-! Retained local spoke loads on the actual fixed active vortex sets. The
weights are chosen before the profile and the two exposures. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_active_local_load_event_manuscript_seeds_with_weight_uniform_failure
    (k c:ℕ) (hlen:c+1=(k+2)*2) (hc:3≤c)
    (α τ ρ₀ sstar tol Qexp tstar ζ:ℝ)
    (hα:0<α) (hτ:0<τ) (hρ₀:0<ρ₀) (hsstar:0<sstar)
    (htol:0<tol) (htstar:0<tstar) (hζ:0<ζ)
    (hmargin:successorCycleRatio k+α/4≤1/2+α/2):
    ∃ βmax:ℝ,0<βmax ∧ ∀ χ:ℝ,0<χ→∀ (d:ℕ) (hd:2≤d), ∃ N₀:ℕ,1≤N₀ ∧
    ∀ ε:ℝ,0<ε→ε≤1/4→∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),N₀≤Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    0≤β→β≤βmax→m₀≤m→
    ∀ (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L≤Q.length→
    letI : Nonempty V:=Fintype.card_pos_iff.mp hn
    let W:=fun i=>markedVortexVertexType Q i
    let Z:=fun i=>markedVortexHubType Q i
    let A:∀ i,Finset (W i):=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let B:∀ i,Finset (Z i):=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let X:=fun i=>↥(A i)
    let Y:=fun i=>↥(B i)
    let f:=fun i=>markedVortexActiveVertexEmbedding Q i
    let g:=fun i=>markedVortexActiveHubEmbedding Q i
    let ρ:=fun i=>markedVortexActivePermutation Q π hπ i
    let Dactive:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D;
    ∃ weight:∀ i,(Fin (c+1)→X i)→ℝ,
    (∀ i≤L,SuccessorSequenceWeightConditions (G.comap (f i)) (ρ i) (3*d)
      (Dactive i) τ (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (weight i)) ∧
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color] (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let pstar:=ρ₀*sstar/(2*(c:ℝ))
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds c (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
    let p:=dens*s₀/2
    let kval:=p/(c:ℝ);
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/c)→(∀ u,s u j=s₀)→tstar≤s₀/c→
    ∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (err:ℝ),
    1-err≤(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability E→
    1-χ-(Fintype.card V:ℝ)^(-Qexp)-err≤
      (rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
        (fun z=>(∀ i≤L,MarkedLocalSpokeLoadsWithSpokes (G.comap (f i)) (ρ i) d c (Dactive i) p kval s₀ (weight i)
          (τ+tol+5*((c:ℝ)+1)^4*(2*successorWeightUpper k (α/4)/pstar^(2*c+1))*ζ)
          (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ E z) :=by
  let pstar:=ρ₀*sstar/(2*(c:ℝ))
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  obtain ⟨βmax,hβmax,hbase⟩:=
    marked_actual_active_local_load_event_seeded_with_weight_uniform_failure k c hlen hc α τ ρ₀ pstar tol Qexp tstar ζ
      hα hτ hρ₀ hpstar htol htstar hζ hmargin
  refine ⟨βmax,hβmax,?_⟩
  intro χ hχ d hd
  have hbase:=hbase χ hχ
  obtain ⟨N₀,hN,hbase⟩:=hbase d hd
  refine ⟨N₀,hN,?_⟩
  intro ε he he1
  obtain ⟨m₀,hm₀,hbase⟩:=hbase ε he he1
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hn0 hD hρlo hρhi hb hbmax hm π hπ hshort L hL W Z A B X Y f g ρ Dactive
  obtain ⟨weight,hw,hweight⟩:=hbase V U G D m β Q hreg hn hn0 hD hρlo hρhi hb hbmax hm π hπ hshort L hL
  refine ⟨weight,hw,?_⟩
  intro Γ Color _ _ s₀ hslo hshi pstar' dens densities p kval q hq hQ s hs hS a j hq0 hsprofile htlo E err hExtra
  have hp:0<p:=densities.1.trans_le densities.2.1
  have hk:0<kval:=densities.1.trans_le densities.2.2.1
  have hphys:2*p+2*kval≤1:=densities.2.2.2.2.2.2.2.2
  exact hweight Γ Color p kval s₀ hp hk hphys densities.2.1 densities.2.2.1 densities.2.2.2.1
    densities.2.2.2.2.1 densities.2.2.2.2.2.1 densities.2.2.2.2.2.2.1
    q hq hQ s hs hS a j hq0 hsprofile htlo E err hExtra
end Oberwolfach
