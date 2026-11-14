module

public import Oberwolfach.MarkedFixedVortexReferenceActiveEvent
public import Oberwolfach.MarkedRegularHostRobustAbsorberJointEvent

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

theorem marked_fixed_vortex_reference_active_absorber_event_separate_thresholds
    (r h k₀ Qpow:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2) (α ρ₀ sstar tstar kstar tol χActive Qexp pstar ζActive:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀)
    (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+α/2≤1/2+α)
    (htol:0<tol) (hχActive:0<χActive) (hpstar:0<pstar) (hpstarBound:pstar≤ρ₀*tstar/4) (hζActive:0<ζActive):
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig:ℝ,0<βconfig ∧ ∀ εref δref χ β ε:ℝ,
    0<εref→0<δref→0<χ→0≤β→β≤α/8→β≤1/4→β≤εref/4→0<ε→ε<1/4→
    ∀ d:ℕ,∀ hd:2≤d,∃ m₀:ℕ,1≤m₀ ∧
    ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f₀:ℕ,∃ n₀:ℕ,1≤n₀ ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hrlo:ρ₀ ≤ initialIndexDensity U D) (hrhi:initialIndexDensity U D ≤ 1),
      m₀≤m→n₀≤Fintype.card V→m≤Fintype.card V→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
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
    ∀ (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds (r+4) (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hrlo hrhi hslo hshi
    let p:=dens*s₀/2
    let k:=p/((r+4:ℕ):ℝ)
    kstar≤p→kstar≤k→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a:Γ) (j:Color),(∀ u,q u a=s₀/((r+4:ℕ):ℝ))→(∀ u,s u j=s₀)→tstar≤s₀/((r+4:ℕ):ℝ)→
    1-χ-2*χActive-2*(Fintype.card V:ℝ)^(-Qexp)-2/(Fintype.card V:ℝ)^Qpow≤
      (rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>((∀ i≤L,
        MarkedReferenceConfigurations r (G.comap (f i)) (ρ i) d a j βconfig
          (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) ∧
        ∀ ζ:ℝ,0≤ζ→2*ζ≤(3/4)*(α/2)*p^2→ζ≤(α/2)*min p k/8→
        ∀ DR:SimpleGraph (W i),(∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card (W i))→
        MarkedReferenceStatistics (G.comap (f i)) (ρ i) d a j (Dload i) (εref+ζ) δref ((α/2)/2) p k s₀ (s₀/((r+4:ℕ):ℝ))
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
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS))) ∧ (let Habs:Bool→V→U→Prop:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
          ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
            (∀ x,(DR.degree x:ℝ)≤ζAbs*Fintype.card V)→
            (∀ x,(DS.degree x:ℝ)≤ζAbs*Fintype.card V)→
          let σ':=rawMarkedDeleteRims z.1 DR.edgeFinset
          let H':=markedDeletePhysicalSpokes Habs DS
          MarkedReservedTerminalAbsorberProperty
            (fun e:MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
            (fun e:MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
            (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs)):=by
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,habs⟩:=marked_regular_host_robust_absorber_with_existing_event
    k₀ r Qpow hr hlen α ρ₀ sstar hα hρ₀ hsstar hmargin
  obtain ⟨βconfig,hβconfig,href⟩:=marked_fixed_vortex_reference_and_active_event r h (by omega) α ρ₀ sstar tstar kstar
    tol χActive Qexp pstar ζActive hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar htol hχActive hpstar hpstarBound hζActive
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,?_⟩
  intro εref δref χ β ε hεref hδref hχ hb hbα hb1 hbε he he1 d hd
  obtain ⟨mRef,hmRef,href⟩:=href εref δref χ β ε hεref hδref hχ hb hbα hb1 hbε he he1 d hd
  refine ⟨mRef,hmRef,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,habs⟩:=habs size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀
  obtain ⟨nAbs,hnAbs,habs⟩:=habs f₀ d hd
  refine ⟨nAbs,hnAbs,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ G D m hreg hn hD hrlo hrhi hm hnAbs hmn Q π hpres hnoshort L hL W Z f g ρ Dload I T J Wrem
  intro s₀ hslo hshi dens densities p k hpmin hkmin q hq hQ s hs hS a j hq₀ hs₀ htlo
  let hp:0≤p:=(densities.1.trans_le densities.2.1).le
  let hk:0≤k:=(densities.1.trans_le densities.2.2.1).le
  let hsum:2*p+2*k≤1:=densities.2.2.2.2.2.2.2.2
  have hRef:=href V U Γ Color G D m hreg hn hD hrlo hrhi hm hmn
    Q π hpres hnoshort L hL p k hp hk hsum hpmin hkmin q hq hQ s hs hS a j s₀ (s₀/((r+4:ℕ):ℝ))
    hq₀ hs₀ hslo htlo
  have hE:=hRef
  rw [show 1-χ-2*χActive-2*(Fintype.card V:ℝ)^(-Qexp)=
    1-(χ+2*χActive+2*(Fintype.card V:ℝ)^(-Qexp)) by ring] at hE
  have hAbs:=habs V U Γ Color hnAbs hn G D hreg hD hrlo hrhi π hnoshort
    s₀ hslo hshi q hq hQ s hs hS a j hq₀ hs₀ _ (χ+2*χActive+2*(Fintype.card V:ℝ)^(-Qexp)) hE
  rw [show 1-(χ+2*χActive+2*(Fintype.card V:ℝ)^(-Qexp))-2/(Fintype.card V:ℝ)^Qpow=
    1-χ-2*χActive-2*(Fintype.card V:ℝ)^(-Qexp)-2/(Fintype.card V:ℝ)^Qpow by ring] at hAbs
  apply hAbs.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact hz
end Oberwolfach
