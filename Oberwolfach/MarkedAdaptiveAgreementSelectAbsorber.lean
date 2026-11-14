module

public import Oberwolfach.MarkedAdaptiveAgreementAbsorber
public import Oberwolfach.MarkedChooseReservedTerminalReservoir

@[expose] public section
/-! A named predicate for the full agreement-inclusive retained event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} {W Z Hdom:ℕ→Type}
  [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
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


theorem marked_adaptive_agreement_select_absorber
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hEvent:MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π f g ρi A Bset Scale D Dload b weight q s a j z):
    let H:Bool→V→U→Prop:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let E:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let H₀:=H false
    let HK:=H true
    ∀ (X:Finset V) (Zset:Finset U),X.card+Zset.card≤size→
    ∀ (Xbig:Finset V) (Zbig:Finset U),X⊆Xbig→Zset⊆Zbig→
      (Xbig.card:ℝ)≤εAbs*Fintype.card V+f₀→(Zbig.card:ℝ)≤εAbs*Fintype.card V+f₀→
    ∀ (F₀:Finset (Finset V⊕(V×U))),F₀.card≤f₀→
    let A₀:=Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)
    let S₀:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1∈X∧z.2∈Zset);
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π Xbig Zbig e) ∧
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (r+4) π (3*d) H₀ HK=>markedWheelPhysicalResources W) C.edges ∧
      ∀ A⊆A₀,∀ S⊆S₀,MarkedRemainderDivisible tail head ktail khead HK A S (r+4)→
        IsResourceAbsorber
          (fun W:MarkedWheel tail head ktail khead (r+4) π (3*d) H₀ HK=>markedWheelPhysicalResources W)
          (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) C.edges := by
  intro H E K tail head ktail khead H₀ HK X Zset hs Xbig Zbig hXX hZZ hXbig hZbig F₀ hF A₀ S₀
  have hAbs:=marked_adaptive_agreement_reserved_absorber r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π f g ρi A Bset Scale D Dload b weight q s a j z hEvent
  exact marked_choose_reserved_terminal_reservoir tail head ktail khead H₀ HK π (3*d) r size a₀ b₀ e₀ f₀ εAbs hAbs X Zset hs Xbig Zbig hXX hZZ hXbig hZbig F₀ hF
end Oberwolfach
