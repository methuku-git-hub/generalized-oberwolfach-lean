module

public import Oberwolfach.MarkedFixedVortexActiveJointLinear
public import Oberwolfach.MarkedReferenceJointFailureBudget

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

theorem marked_fixed_vortex_active_joint_positive_witness
    (h d:ℕ) (hd:2≤d) (β ε ρ₀ tol χActive Qreal pstar ζ χ χCommon χBal χNbr χLoad χLocal χConfig:ℝ) (Qnat:ℕ)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (he1:ε<1/4) (hr:0<ρ₀)
    (htol:0<tol) (hχ:0<χActive) (hpstar:0<pstar) (hζ:0<ζ)
    (hQnat:0<Qnat) (hQr:0<Qreal)
    (herr:markedReferenceFixedFailure χ χCommon χBal χNbr χLoad χLocal χConfig χActive<1):
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
    ∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop),
    1-χ-2/(Fintype.card V:ℝ)^Qnat-χCommon-(Fintype.card V:ℝ)^(-Qreal)-χBal-(Fintype.card V:ℝ)^(-Qreal)-
      2*χNbr-2*(Fintype.card V:ℝ)^(-Qreal)-χLoad-(Fintype.card V:ℝ)^(-Qreal)-χLocal-(Fintype.card V:ℝ)^(-Qreal)-
      χConfig-(Fintype.card V:ℝ)^(-Qreal)-2/(Fintype.card V:ℝ)^Qnat-1/(Fintype.card V:ℝ)^Qnat≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability E →
    ∃ z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a, (E z ∧ ∀ i≤L,
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
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS)) ∧ 0<(rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).mass z := by
  obtain ⟨m₁,hm₁,hbase⟩:=marked_fixed_vortex_active_event_linear_level_count
    h d hd β ε ρ₀ tol χActive Qreal pstar ζ hb hb1 he he1 hr htol hχ hpstar hζ
  obtain ⟨N,_,hwit⟩:=marked_reference_joint_failure_positive_witness Qnat hQnat Qreal
    χ χCommon χBal χNbr χLoad χLocal χConfig χActive hQr herr
  refine ⟨max m₁ N,le_trans hm₁ (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ G D m hreg hn hD hrlo hrhi hm hmn vtx π hpres hπ L hL W Z f g ρi I T J Wrem
  intro p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass E hE
  let base:ℝ:=1-χ-2/(Fintype.card V:ℝ)^Qnat-χCommon-(Fintype.card V:ℝ)^(-Qreal)-χBal-(Fintype.card V:ℝ)^(-Qreal)-
      2*χNbr-2*(Fintype.card V:ℝ)^(-Qreal)-χLoad-(Fintype.card V:ℝ)^(-Qreal)-χLocal-(Fintype.card V:ℝ)^(-Qreal)-
      χConfig-(Fintype.card V:ℝ)^(-Qreal)-2/(Fintype.card V:ℝ)^Qnat-1/(Fintype.card V:ℝ)^Qnat
  have hE':1-(1-base)≤(rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability E:=by
    dsimp [base]
    linarith
  have hcombined:=hbase V U Γ Color G D m hreg hn hD hrlo hrhi ((le_max_left _ _).trans hm) hmn
    vtx π hpres hπ L hL p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass E (1-base) hE'
  have hnN:N≤Fintype.card V:=(le_max_right _ _).trans (hm.trans hmn)
  apply hwit (Fintype.card V) hnN (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS)
  dsimp [base] at hcombined
  convert hcombined using 1 <;> try ring <;> congr!
end Oberwolfach
