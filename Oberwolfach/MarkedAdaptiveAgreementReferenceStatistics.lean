module

public import Oberwolfach.MarkedEmptyPhysicalDeletion
public import Oberwolfach.MarkedAdaptiveAgreementProperty
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


theorem marked_adaptive_agreement_reference_statistics
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hEvent:MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π f g ρi A Bset Scale D Dload b weight q s a j z)
    (hγ:0≤γ) (hp:0≤p) (hk:0≤k):
    ∀i≤L,MarkedReferenceStatistics (P.comap (f i)) (ρi i) d a j (D i) εRef δRef (γ/2) p k s₀
      (s₀/((r+4:ℕ):ℝ)) (rawMarkedRestrictPair (f i) (g i) z.1):=by
  dsimp only [MarkedAdaptiveAgreementProperty] at hEvent
  have hsource:∀ i≤L,
        MarkedReferenceConfigurations r (P.comap (f i)) (ρi i) d a j β
          (rawMarkedRestrictPair (f i) (g i) z.1) ∧
        ∀ ζ:ℝ,0≤ζ → 2*ζ≤(3/4)*γ*p^2 → ζ≤γ*min p k/8 →
        ∀ DR:SimpleGraph (W i),(∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card (W i)) →
        MarkedReferenceStatistics (P.comap (f i)) (ρi i) d a j (D i) (εRef+ζ) δRef (γ/2) p k s₀
          (s₀/((r+4:ℕ):ℝ)) (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset) ∧
        MarkedReferenceCutFamilies (P.comap (f i)) (ρi i) d a j (γ/2) p k tstar
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset):=by
    first
      | exact hEvent.1
      | exact hEvent.1.1
      | exact hEvent.1.1.1
      | exact hEvent.1.1.1.1
      | exact hEvent.1.1.1.1.1
      | exact hEvent.1.1.1.1.1.1
      | exact hEvent.1.1.1.1.1.1.1
      | exact hEvent.1.1.1.1.1.1.1.1
      | exact hEvent.1.1.1.1.1.1.1.1.1
      | exact hEvent.1.1.1.1.1.1.1.1.1.1
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1
  intro i hi
  have hzero1:2*(0:ℝ)≤(3/4)*γ*p^2:=by
    have hz:0≤(3/4:ℝ)*γ*p^2:=by positivity
    linarith
  have hzero2:(0:ℝ)≤γ*min p k/8:=by positivity
  have hh:=(hsource i hi).2 0 (by norm_num) hzero1 hzero2 ⊥ (by intro x; simp)
  have hzero:@SimpleGraph.edgeFinset (W i) ⊥
      (@SimpleGraph.fintypeEdgeSet (W i) ⊥ (inferInstance) (fun x y=>Classical.propDecidable _))=∅:=by
    ext e
    simp
  rw [hzero] at hh
  simpa only [add_zero,rawMarkedDeleteRims_empty] using hh.1
end Oberwolfach
