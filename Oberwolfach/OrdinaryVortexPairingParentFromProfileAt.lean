module

public import Oberwolfach.OrdinaryVortexPairingGeometry
public import Oberwolfach.OrdinaryPairingParentFromProfile
public import Oberwolfach.OrdinaryAdaptiveHubWeightsLevelEvent

@[expose] public section
/-! At any fixed vortex level, including the initial one, the local profile
and same-sample adaptive hub event supply the fresh-pairing parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_pairing_parent_from_profile_at
    (ε ρ₀ pmin Kdom ηf εf γ κ a lam b Bweight βe βh:ℝ)
    (d mWheel:ℕ) (β:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hηf:0<ηf) (hεf:0<εf)
    (hγ:0≤γ) (hκ:0≤κ) (ha:0<a) (hlam:0<lam)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom)
    (hRrate:a*(2*Kdom)+2*lam≤pmin/2) (hHrate:a*(2*Kdom)+2*lam≤pmin*(ρ₀/8))
    (herr:6*lam≤ηf*a) (hγβ:γ≤βe) (hκβ:κ≤βe) (hβ:0≤β) (hβ1:β≤1/4):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P G:SimpleGraph V) (Hs:V→U→Prop) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (i:ℕ),i<Q.length→
    ∀(s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (pR pH density εR εH Ledit:ℝ),pmin≤pR→pmin≤pH→pH≤1→
      0≤εR→εR≤lam→0≤εH→εH≤lam→0≤Ledit→G≤P→
    let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let ρ:=markedVortexPermutation Q π hπ i;let F:=permutationConflictGraph π (3*d);
    Ledit≤lam*I.card→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
      ρ d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ)→
    OrdinaryAdaptiveHubWeightsLevelEvent mWheel (P.comap f) (F.comap f) I B ρ d
      pR pH density (εR*I.card) (εH*B.card) Ledit βe βh b Bweight ηf (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ)→
    Nonempty (MixedFreshPairingParentInsideRoots mWheel (2*(3*d)) γ κ b Bweight pmin a εf ηf
      (spanningRestriction (G.comap f) I) (F.comap f)
      (ordinaryPhysicalGraph (spanningRestriction (G.comap f) I) (fun v u=>Hs (f v) (g u)∧v∈I∧u∈B))
      (ordinaryPhysicalGraph (F.comap f) (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q i↪_)
      (ordinaryBoundaryHubSet (fun v u=>Hs (f v) (g u)) B I)
      (fun k=>(ordinaryBoundaryRimSet (G.comap f) I k).image Sum.inl)
      (fun k=>(ordinaryBoundaryRowSet (fun v u=>Hs (f v) (g u)) I B k).image Sum.inr) (fun _=>pH)) :=by
  obtain ⟨v₀,hv₀,hgeom⟩:=ordinary_vortex_pairing_geometry β ε ρ₀ Kdom εf d hβ hβ1 hε hε1 hρ₀ hεf hKdom
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P G Hs D m hreg hn hD hρlo hρhi hm Q π hπ i hi s j σ
    pR pH density εR εH Ledit hpR hpH hpH1 hεR hεRlam hεH hεHlam hL0 hGP f g I B ρ F hL hprofile hevent
  have hlocal:(G.comap f)≤(P.comap f):=by intro v w hvw;exact hGP hvw
  have hHub:=hevent (G.comap f) (fun v u=>Hs (f v) (g u)) (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hlocal
  have hg:=hgeom V U P D m hreg hn hD hρlo hρhi hm Q π hπ i hi
  obtain ⟨hI,hsize,hZ,hBI,hF,hFsmall⟩:=hg
  have hR:εR*I.card≤lam*I.card:=mul_le_mul_of_nonneg_right hεRlam (by positivity)
  have hH:εH*B.card≤lam*I.card:=by
    have hh:=mul_le_mul_of_nonneg_left (show (B.card:ℝ)≤I.card by exact_mod_cast hBI) hεH
    have hh':=mul_le_mul_of_nonneg_right hεHlam (show (0:ℝ)≤I.card by positivity)
    linarith only [hh,hh']
  exact ordinary_pairing_parent_from_profile mWheel (2*(3*d)) (P.comap f) (G.comap f) (F.comap f)
    (fun v u=>Hs (f v) (g u)) I B ρ d j (fun u=>s (g u)) γ κ b Bweight pmin a εf ηf pR pH
    density (εR*I.card) (εH*B.card) Ledit βe βh (ρ₀/8) (2*Kdom) lam (ordinaryRawRestrictPair f g σ)
    hprofile hI hpmin (by positivity) hηf ha hlam hRrate hHrate herr hsize hZ hpR hpH hpH1
    (by positivity) hR (by positivity) hH hL0 hL hγ hκ hγβ hκβ hF hFsmall (by convert hHub using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
end Oberwolfach
