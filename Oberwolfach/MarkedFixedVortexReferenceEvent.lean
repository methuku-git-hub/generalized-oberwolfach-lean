module

public import Oberwolfach.MarkedReferenceAdaptiveVortexEvent
public import Oberwolfach.MarkedFixedVortexBaselineGeometry
public import Oberwolfach.MarkedFixedVortexParentDegrees

@[expose] public section
/-! The reference-statistics, cut and configuration event on the actual
pre-exposure vortex. Its later physical deletions remain quantified after
the single sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_reference_event
    (r:ℕ) (hr:1≤r) (α ρ₀ sstar tstar kstar:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀)
    (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar):
    ∃ βconfig:ℝ,0<βconfig ∧ ∀ εref δref χ β ε:ℝ,
    0<εref→0<δref→0<χ→0≤β→β≤α/8→β≤1/4→β≤εref/4→0<ε→ε<1/4→
    ∀ d:ℕ,∀ hd:2≤d,∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤(D:ℝ)→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D ≤ 1→
      m₀≤m→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let g:=markedVortexHubEmbedding Q
    let ρ:=markedVortexPermutation Q π hpres
    let Dload:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D;
    ∀ (p k:ℝ) (hp:0≤p) (hk:0≤k) (hsum:2*p+2*k≤1),kstar≤p→kstar≤k→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a:Γ) (j:Color) (s₀ t₀:ℝ),(∀ u,q u a=t₀)→(∀ u,s u j=s₀)→sstar≤s₀→tstar≤t₀→
    1-χ≤(rawMarkedRetentionLaw π d hd a p k hp hk hsum q hq hQ s hs hS).probability
      (fun z=>∀ i≤L,
        MarkedReferenceConfigurations r (G.comap (f i)) (ρ i) d a j βconfig
          (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) ∧
        ∀ ζ:ℝ,0≤ζ→2*ζ≤(3/4)*(α/2)*p^2→ζ≤(α/2)*min p k/8→
        ∀ DR:SimpleGraph (W i),(∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card (W i))→
        MarkedReferenceStatistics (G.comap (f i)) (ρ i) d a j (Dload i) (εref+ζ) δref ((α/2)/2) p k s₀ t₀
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) DR.edgeFinset) ∧
        MarkedReferenceCutFamilies (G.comap (f i)) (ρ i) d a j ((α/2)/2) p k tstar
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) DR.edgeFinset)):=by
  obtain ⟨βconfig,hβconfig,hbase⟩:=marked_reference_adaptive_vortex_event r hr (α/2) sstar tstar kstar (ρ₀/8)
    (by positivity) (by linarith) hsstar htstar htstar1 horder hkstar (by positivity)
  refine ⟨βconfig,hβconfig,?_⟩
  intro εref δref χ β ε hεref hδref hχ hb hbα hb1 hbε he he1 d hd
  obtain ⟨M,hM,hbase⟩:=hbase εref δref ε χ hεref hδref he (by linarith) hχ d hd
  obtain ⟨m₀,hm₀,hgeo⟩:=marked_fixed_vortex_baseline_geometry β ε ρ₀ hb hb1 he he1 hρ₀ M
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ G D m hreg hn hD hρlo hρhi hm Q π hpres hnoshort L hL W Z f g ρ Dload
  have hmpos:0<m:=by omega
  have hρ:0 < initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
    nlinarith only [hD, mul_nonneg hα.le hn0]
  have hgeom:=hgeo V U G D m hreg hn hhalf hρlo hρhi hm Q π hpres L hL
  have hcomm:∀ i x,f i (ρ i x)=π (f i x):=hgeom.1
  have hfield (i:ℕ) (hi:i≤L):=marked_vortex_fixed_parent_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hmpos i (by omega)
  have hmin (i:ℕ) (hi:i≤L):M≤Fintype.card (W i):=(hgeom.2 i hi).2.2.1
  have hscale (i:ℕ) (hi:i<L):(Fintype.card (W (i+1)):ℝ)≤ε*Fintype.card (W i):=(hgeom.2 i (by omega)).2.2.2.2.2.2.2.2.1
  have hhublo (i:ℕ) (hi:i≤L):(ρ₀/8)*(Fintype.card (W i):ℝ)≤Fintype.card (Z i):=(hgeom.2 i hi).2.2.2.2.1
  have hhubhi (i:ℕ) (hi:i≤L):Fintype.card (Z i)≤Fintype.card (W i):=(hgeom.2 i hi).2.2.2.2.2.1
  intro p k hp hk hsum hpmin hkmin q hq hQ s hs hS a j s₀ t₀ hq₀ hs₀ hslo htlo
  have hh:=hbase V U Γ Color W Z G π hnoshort f g ρ hcomm L hmin hscale hhublo hhubhi
    p k hp hk hsum hpmin hkmin Dload β hb hbε
    (fun i hi x=>(hfield i hi).2.1 x) (fun i hi x=>(hfield i hi).1 x)
    q hq hQ s hs hS a j s₀ t₀ hq₀ hs₀ hslo htlo
  convert hh using 1 <;> congr! <;> try ring
end Oberwolfach
