module

public import Oberwolfach.MarkedVortexPreselectReservedProperty
public import Oberwolfach.MarkedVortexPreselectAdaptiveAgreement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

def MarkedVortexFixedSelection
    (r d size a₀ b₀ e₀ f₀:ℕ) (εAbs:ℝ) (G:SimpleGraph V) (π:Equiv.Perm V) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a) : Prop :=
    ∀ (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
      (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (L:ℕ), L+1=Q.length →
    G.IsRegularOfDegree D → 0<Fintype.card V → 0<D →
    initialIndexDensity U D≤1 → 0≤ε → ε≤εAbs → 2*m≤size →
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let E:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true;
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f₀→
    ∃ C:MarkedSupportedEdgeSet (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      C.edges.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅ ∧
      MarkedFixedTerminalAbsorber G π d (r+4) z.1 H C.edges
        (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1))

variable {W Z Hdom:ℕ→Type}
  [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)]
  [∀ i,Fintype (Hdom i)] [∀ i,DecidableEq (Hdom i)]
variable (r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ)
variable (β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal Kbal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ:ℝ)
variable (P:SimpleGraph V) (π:Equiv.Perm V)
variable (f:∀ i,W i↪oV) (g:∀ i,Z i↪U) (ρi:∀ i,Equiv.Perm (W i))
variable (A:∀ i,Finset (W i)) (Bset:∀ i,Finset (Z i))
variable (Scale:ℕ→ℕ) (D Dbal Dload:ℕ→ℝ) (b:∀ i,Hdom i↪Z i)
variable (weight:∀ i,(Fin ((r+4)+1)→W i)→ℝ)
variable (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)



theorem marked_adaptive_agreement_vortex_fixed_selection
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hEvent:MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π f g ρi A Bset Scale D Dload b weight q s a j z):
    MarkedVortexFixedSelection r d size a₀ b₀ e₀ f₀ εAbs P π a j z := by
  have hprop:=marked_adaptive_agreement_reserved_absorber r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π f g ρi A Bset Scale D Dload b weight q s a j z hEvent
  intro Dnat m βQ εQ Q hpres LQ hL hreg hn hD hρhi he heAbs hsize H E K F₀ hF
  exact marked_vortex_preselect_absorber_from_reserved_property r d εAbs size a₀ b₀ e₀ f₀ P Dnat m βQ εQ Q π hpres LQ hL a j z hreg hn hD hρhi he heAbs hsize hprop F₀ hF
end Oberwolfach
