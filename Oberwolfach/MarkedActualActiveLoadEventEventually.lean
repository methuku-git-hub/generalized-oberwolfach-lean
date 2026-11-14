module

public import Oberwolfach.MarkedActualActiveLoadEvent
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

theorem marked_actual_active_local_load_event_eventually
    (k c:ℕ) (hlen:c+1=(k+2)*2) (hc:3≤c)
    (α τ ρ₀ pstar tol χ Qexp pret ζ:ℝ)
    (hα:0<α) (hτ:0<τ) (hρ₀:0<ρ₀) (hpstar:0<pstar)
    (htol:0<tol) (hχ:0<χ) (hpret:0<pret) (hζ:0<ζ)
    (hmargin:successorCycleRatio k+α/4≤1/2+α/2):
    ∃ βmax:ℝ,0<βmax ∧ ∀ (d:ℕ) (hd:2≤d), ∃ N₀:ℕ,1≤N₀ ∧
    ∀ ε:ℝ,0<ε→ε≤1/4→∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),N₀≤Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→
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
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color]
      (p kval s₀:ℝ) (hp:0<p) (hk:0<kval) (hphys:2*p+2*kval≤1),
      pstar≤p→pstar≤kval→pstar≤s₀→p≤1→kval≤1→s₀≤1→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/c)→(∀ u,s u j=s₀)→pret*Fintype.card V≤(s₀/c)*Fintype.card U→
    ∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (err:ℝ),
    1-err≤(rawMarkedRetentionLaw π d hd a p kval hp.le hk.le hphys q hq hQ s hs hS).probability E→
    1-χ-(Fintype.card V:ℝ)^(-Qexp)-err≤
      (rawMarkedRetentionLaw π d hd a p kval hp.le hk.le hphys q hq hQ s hs hS).probability
        (fun z=>(∀ i≤L,MarkedLocalSpokeLoadsWithSpokes (G.comap (f i)) (ρ i) d c (Dactive i) p kval s₀ (weight i)
          (τ+tol+5*((c:ℝ)+1)^4*(2*successorWeightUpper k (α/4)/pstar^(2*c+1))*ζ)
          (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ E z) :=by
  obtain ⟨βmax,hβmax,hbase⟩:=
    marked_actual_active_local_load_event k c hlen hc α τ ρ₀ pstar tol χ Qexp pret ζ
      hα hτ hρ₀ hpstar htol hχ hpret hζ hmargin
  refine ⟨βmax,hβmax,?_⟩
  intro d hd
  obtain ⟨M₀,N₀,Nweight,hM,hN,hW,hbase⟩:=hbase d hd
  refine ⟨N₀,hN,?_⟩
  intro ε he he1
  obtain ⟨m₀,hm₀,hsize⟩:=marked_active_size_threshold ρ₀ ε hρ₀ he M₀ Nweight
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hn0 hD hρlo hρhi hb hbmax hm π hπ hshort L hL
  obtain ⟨hsizeW,hsizeA,hsizeB⟩:=hsize m hm
  exact hbase V U G D m β ε Q hreg hn hn0 hD hρlo hρhi hb hbmax he he1 hsizeW hsizeA hsizeB π hπ hshort L hL
end Oberwolfach
