module

public import Oberwolfach.MarkedCutVortexTargetUniform
public import Oberwolfach.MarkedFixedVortexBaselineGeometry
public import Oberwolfach.MarkedFixedVortexParentDegrees
public import Oberwolfach.RawMarkedRetention

@[expose] public section
/-! Parent reference cut families at the supplied density t₀, with the
vortex and sample sizes chosen uniformly from the fixed lower density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_parent_cuts_target_event
    (α ρ₀ tstar kstar χ:ℝ) (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀)
    (htstar:0<tstar) (htstar1:tstar≤1) (hkstar:0<kstar) (hχ:0<χ)
    (β ε:ℝ) (hb:0≤β) (hbα:β≤α/8) (hb1:β≤1/4) (he:0<ε) (he1:ε<1/4)
    (d:ℕ) (hd:2≤d):
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤(D:ℝ)→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
      m₀≤m→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let g:=markedVortexHubEmbedding Q
    let ρ:=markedVortexPermutation Q π hpres;
    ∀ (p k:ℝ) (hp:0≤p) (hk:0≤k) (hsum:2*p+2*k≤1),kstar≤p→kstar≤k→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a:Γ) (j:Color) (s₀ t₀:ℝ),(∀ u,q u a=t₀)→(∀ u,s u j=s₀)→
      tstar≤s₀→tstar≤t₀→t₀≤1→t₀≤s₀→
    ∀ (Extra:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (err:ℝ),
    1-err≤(rawMarkedRetentionLaw π d hd a p k hp hk hsum q hq hQ s hs hS).probability Extra→
    1-χ-err≤(rawMarkedRetentionLaw π d hd a p k hp hk hsum q hq hQ s hs hS).probability
      (fun z=>(∀ i≤L,MarkedReferenceCutFamilies (G.comap (f i)) (ρ i) d a j (α/8) p k t₀
        (rawMarkedRestrictPair (f i) (g i) z.1)) ∧ Extra z):=by
  obtain ⟨M,hM,hcuts⟩:=marked_cut_vortex_target_uniform_event (α/8) kstar tstar (ρ₀/8) ε χ
    (by positivity) (by linarith) hkstar htstar htstar1 (by positivity) he (by linarith) hχ d hd
  obtain ⟨m₀,hm₀,hgeo⟩:=marked_fixed_vortex_baseline_geometry β ε ρ₀ hb hb1 he he1 hρ₀ M
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ G D m hreg hn hD hρlo hρhi hm Q π hpres hshort L hL W Z f g ρ
  have hmpos:0<m:=by omega
  have hρ:0 < initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
    nlinarith [mul_nonneg hα.le hn0]
  have hgeom:=hgeo V U G D m hreg hn hhalf hρlo hρhi hm Q π hpres L hL
  have hfield (i:ℕ) (hi:i≤L):=marked_vortex_fixed_parent_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hmpos i (by omega)
  have hmin (i:ℕ) (hi:i≤L):M≤Fintype.card (W i):=(hgeom.2 i hi).2.2.1
  have hscale (i:ℕ) (hi:i<L):(Fintype.card (W (i+1)):ℝ)≤ε*Fintype.card (W i):=(hgeom.2 i (by omega)).2.2.2.2.2.2.2.2.1
  have hhublo (i:ℕ) (hi:i≤L):(ρ₀/8)*(Fintype.card (W i):ℝ)≤Fintype.card (Z i):=(hgeom.2 i hi).2.2.2.2.1
  have hhubhi (i:ℕ) (hi:i≤L):Fintype.card (Z i)≤Fintype.card (W i):=(hgeom.2 i hi).2.2.2.2.2.1
  have hparent (i:ℕ) (hi:i≤L) (v:W i):(1/2+α/8)*Fintype.card (W i)≤((G.comap (f i)).degree v:ℝ):=by
    have hc:=mul_le_mul_of_nonneg_right (show (1/2+α/8:ℝ)≤1/2+α/2 by linarith) (Nat.cast_nonneg (Fintype.card (W i)))
    exact hc.trans ((hfield i hi).1 v)
  intro p k hp hk hsum hpmin hkmin q hq hQ s hs hS a j s₀ t₀ hq0 hs0 hslo htlo htone hts Extra err hExtra
  let E:=fun σ:RawMarkedOutcome V U Γ Color=>∀ i≤L,MarkedReferenceCutFamilies (G.comap (f i)) (ρ i) d a j (α/8) p k t₀
    (rawMarkedRestrictPair (f i) (g i) σ)
  have hraw:=hcuts V U Γ Color W Z G π hshort f g ρ hgeom.1 L hmin hscale hhublo hhubhi hparent
    p k hp hk hsum hpmin hkmin q hq hQ s hs hS a j s₀ t₀ hq0 hs0 hslo htlo t₀ htlo htone hts le_rfl
  let μ:=rawMarkedRetentionLaw π d hd a p k hp hk hsum q hq hQ s hs hS
  have hE:1-χ≤μ.probability (fun z=>E z.1):=by
    rw [rawMarkedRetentionLaw_raw_projection]
    exact hraw
  have hj:=finiteLaw_good_intersection μ (fun z=>E z.1) Extra err hExtra
  change 1-χ-err≤μ.probability (fun z=>E z.1 ∧ Extra z)
  linarith only [hE,hj]
end Oberwolfach
