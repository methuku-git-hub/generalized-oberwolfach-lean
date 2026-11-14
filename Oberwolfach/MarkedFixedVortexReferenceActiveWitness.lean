module

public import Oberwolfach.MarkedFixedVortexReferenceActiveEvent
public import Oberwolfach.MarkedReferenceExplicitFailureBudget

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

theorem marked_fixed_vortex_reference_and_active_witness
    (r h:ℕ) (hr:1≤r) (α ρ₀ sstar tstar kstar tol pstar ζActive:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀)
    (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (htol:0<tol) (hpstar:0<pstar) (hpstarBound:pstar≤ρ₀*tstar/4) (hζActive:0<ζActive):
    ∃ βconfig:ℝ,0<βconfig ∧ ∀ εref δref β ε:ℝ,
    0<εref→0<δref→0≤β→β≤α/8→β≤1/4→β≤εref/4→0<ε→ε<1/4→
    ∀ d:ℕ,∀ hd:2≤d,∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤(D:ℝ)→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D ≤ 1→
      m₀≤m→m≤Fintype.card V→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let g:=markedVortexHubEmbedding Q
    let ρ:=markedVortexPermutation Q π hpres
    let Dload:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D
    let I:=markedVortexInnerVertices Q
    let T:=markedVortexDeeperVertices Q
    let J:=markedVortexInnerHubs Q
    let Wrem:=markedVortexDeeperHubs Q;
    ∀ (p k:ℝ) (hp:0≤p) (hk:0≤k) (hsum:2*p+2*k≤1),kstar≤p→kstar≤k→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a:Γ) (j:Color) (s₀ t₀:ℝ),(∀ u,q u a=t₀)→(∀ u,s u j=s₀)→sstar≤s₀→tstar≤t₀→
    ∃ z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a, ((∀ i≤L,
        MarkedReferenceConfigurations r (G.comap (f i)) (ρ i) d a j βconfig
          (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) ∧
        ∀ ζ:ℝ,0≤ζ→2*ζ≤(3/4)*(α/2)*p^2→ζ≤(α/2)*min p k/8→
        ∀ DR:SimpleGraph (W i),(∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card (W i))→
        MarkedReferenceStatistics (G.comap (f i)) (ρ i) d a j (Dload i) (εref+ζ) δref ((α/2)/2) p k s₀ t₀
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) DR.edgeFinset) ∧
        MarkedReferenceCutFamilies (G.comap (f i)) (ρ i) d a j ((α/2)/2) p k tstar
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) DR.edgeFinset)) ∧ (∀ i≤L,
          let ω := rawMarkedRestrictPair (f i) (g i) z.1
          let H := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u);
          ∀ deltaR deltaV deltaU : ℝ,0≤deltaR→0≤deltaV→0≤deltaU→
          ∀ (DR : SimpleGraph (W i)) (DS : SimpleGraph (W i⊕Z i)),
            (∀ x,((DR.neighborFinset x∩(I i\T i)).card:ℝ)≤deltaR)→
            (∀ x,((((J i\Wrem i)).filter (fun u=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaV)→
            (∀ u,((((I i\T i)).filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaU)→
          MarkedRowsWithSpokes (G.comap (f i)) (ρ i) d h ((I i\T i)) p k
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((tol+h*ζActive)*((I i\T i)).card+h*(deltaR+deltaU))
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS) ∧
          MarkedIndicesWithSpokes (ρ i) d h ((J i\Wrem i))
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((tol+h*ζActive)*((J i\Wrem i)).card+h*deltaV)
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS))) ∧ 0<(rawMarkedRetentionLaw π d hd a p k hp hk hsum q hq hQ s hs hS).mass z:=by
  obtain ⟨βconfig,hβconfig,hbase⟩:=marked_fixed_vortex_reference_and_active_event r h hr α ρ₀ sstar tstar kstar
    tol (1/100) 1 pstar ζActive hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar htol (by norm_num) hpstar hpstarBound hζActive
  refine ⟨βconfig,hβconfig,?_⟩
  intro εref δref β ε hεref hδref hb hbα hb1 hbε he he1 d hd
  obtain ⟨m₀,hm₀,hbase⟩:=hbase εref δref (1/100) β ε hεref hδref (by norm_num) hb hbα hb1 hbε he he1 d hd
  refine ⟨max m₀ 16,le_trans hm₀ (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ G D m hreg hn hD hrlo hrhi hm hmn Q π hpres hnoshort L hL W Z f g ρ Dload I T J Wrem
  intro p k hp hk hsum hpmin hkmin q hq hQ s hs hS a j s₀ t₀ hq₀ hs₀ hslo htlo
  have hh:=hbase V U Γ Color G D m hreg hn hD hrlo hrhi ((le_max_left _ _).trans hm) hmn Q π hpres hnoshort L hL
    p k hp hk hsum hpmin hkmin q hq hQ s hs hS a j s₀ t₀ hq₀ hs₀ hslo htlo
  have hn16:16≤Fintype.card V:=(le_max_right _ _).trans (hm.trans hmn)
  apply marked_reference_explicit_positive_mass (rawMarkedRetentionLaw π d hd a p k hp hk hsum q hq hQ s hs hS) _ (Fintype.card V) hn16
  have hpw:0≤(Fintype.card V:ℝ)^(-(1:ℝ)):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcompare:1-(1/10:ℝ)-5*(Fintype.card V:ℝ)^(-(1:ℝ))-9*(Fintype.card V:ℝ)^(-(1:ℝ))≤
      1-(1/100:ℝ)-2*(1/100:ℝ)-2*(Fintype.card V:ℝ)^(-(1:ℝ)):=by nlinarith
  apply hcompare.trans
  convert hh using 1 <;> congr!
end Oberwolfach
