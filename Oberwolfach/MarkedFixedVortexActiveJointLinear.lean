module

public import Oberwolfach.MarkedFixedVortexActiveJointEvent
public import Oberwolfach.MarkedFixedVortexLevelCount

@[expose] public section
/-! The active-domain event specialized to the actual pre-exposure paired
vortex. All domain choices and embeddings precede the random outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_active_event_linear_level_count
    (h d:ℕ) (hd:2≤d) (β ε ρ₀ tol χ Qexp pstar ζ:ℝ)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (he1:ε<1/4) (hr:0<ρ₀)
    (htol:0<tol) (hχ:0<χ) (hpstar:0<pstar) (hζ:0<ζ):
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀ (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D ≤ 1→
      m₀≤m→m≤Fintype.card V→
    ∀ (vtx:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈vtx.extendedVertices i↔x∈vtx.extendedVertices i),
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀ L:ℕ,L<vtx.length→
    let W:=markedVortexVertexType vtx
    let Z:=markedVortexHubType vtx
    let f:=markedVortexVertexEmbedding vtx
    let g:=markedVortexHubEmbedding vtx
    let ρi:=markedVortexPermutation vtx π hpres
    let I:=markedVortexInnerVertices vtx
    let T:=markedVortexDeeperVertices vtx
    let J:=markedVortexInnerHubs vtx
    let Wrem:=markedVortexDeeperHubs vtx;
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
      (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a : Γ) (j : Color)
      (t₀ : ℝ),(∀ u,q u a=t₀) → pstar*Fintype.card V≤t₀*Fintype.card U →
    ∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (err:ℝ),
    1-err≤(rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability E →
    1-err-2*χ-2*(Fintype.card V:ℝ)^(-Qexp)≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>E z ∧ ∀ i≤L,
          let ω := rawMarkedRestrictPair (f i) (g i) z.1
          let H := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u);
          ∀ deltaR deltaV deltaU : ℝ,0≤deltaR→0≤deltaV→0≤deltaU→
          ∀ (DR : SimpleGraph (W i)) (DS : SimpleGraph (W i⊕Z i)),
            (∀ x,((DR.neighborFinset x∩(I i\T i)).card:ℝ)≤deltaR)→
            (∀ x,((((J i\Wrem i)).filter (fun u=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaV)→
            (∀ u,((((I i\T i)).filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaU)→
          MarkedRowsWithSpokes (G.comap (f i)) (ρi i) d h ((I i\T i)) p k
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((tol+h*ζ)*((I i\T i)).card+h*(deltaR+deltaU))
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS) ∧
          MarkedIndicesWithSpokes (ρi i) d h ((J i\Wrem i))
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((tol+h*ζ)*((J i\Wrem i)).card+h*deltaV)
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS)) := by
  obtain ⟨m₀,hm₀,hbase⟩:=marked_fixed_vortex_active_neighbourhood_with_existing_event
    h d hd β ε ρ₀ tol χ 1 Qexp pstar ζ hb hb1 he he1 hr htol hχ hpstar hζ
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ G D m hreg hn hD hrlo hrhi hm hmn vtx π hpres hπ L hL W Z f g ρi I T J Wrem
  have hmpos:0<m:=by omega
  have hLpoly:=marked_fixed_vortex_level_count vtx he (by linarith) hmpos L hL
  intro p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass E err hE
  have hh:=hbase V U Γ Color G D m hreg hn hD hrlo hrhi hm hmn vtx π hpres hπ L hL hLpoly
    p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass E err hE
  convert hh using 1 <;> congr!
end Oberwolfach
