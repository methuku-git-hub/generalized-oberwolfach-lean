module

public import Oberwolfach.OrdinaryTriangleFiniteCoverEvent
public import Oberwolfach.OrdinaryDeepCoverNamedEvent

@[expose] public section
/-! One finite-cover interface for all ordinary wheel lengths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

def OrdinaryFiniteCoverEvent (r:ℕ) (κ:ℝ) (P F:SimpleGraph V) (J:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color):Prop :=
  ∀ (Q:SimpleGraph V) (H:V→U→Prop) (L:ℝ),Q≤P\F → 0≤L → L≤κ*Fintype.card V →
    (∀v,(F.degree v:ℝ)≤L) →
    (∀v,((changed ((rawWheelGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
    (∀v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v)) (Finset.univ.filter (H v))).card:ℝ)≤L) →
    (∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L) →
    ∀I:Finset V,(I.card:ℝ)≤κ*Fintype.card V →
    ∀(E:Finset (Sym2 V⊕(V×U))) (D₀:ℕ),
      E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J) →
      (∀v w,Sum.inl s(v,w)∈E→¬F.Adj v w) →
      (∀t,(E.filter (ordinaryResourceIncident t)).card≤D₀) →
      (E.card:ℝ)≤κ^2*(Fintype.card V:ℝ)^2 → (D₀:ℝ)≤κ*Fintype.card V →
    ∀(T:Finset V) (W:Finset U),T⊆I → W⊆J →
      (T.card:ℝ)≤κ*Fintype.card V → (2*W.card:ℝ)≤L →
      (∀u∈W,r∣(Finset.univ.filter (fun v=>H v u)).card) →
      (∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card) →
      (∀v∈T,∀w∈I,Q.Adj v w→Sum.inl s(v,w)∈E) →
      (∀v∈T,∀u∈J,H v u→Sum.inr (v,u)∈E) →
      (∀u∈W,∀v∈I,H v u→Sum.inr (v,u)∈E) →
    ∃R:Finset (OrdinaryWheel Q F H r),
      (∀A∈R,∀B∈R,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
      R.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
        (fun v u=>H v u∧v∈I∧u∈J)=E ∧
      (∀v∈T,∀w,(ordinaryWheelRimGraph R).Adj v w↔Q.Adj v w) ∧
      (∀v∈T,∀u,ordinaryPackingSpokes R v u↔H v u) ∧
      (∀u∈W,∀v,ordinaryPackingSpokes R v u↔H v u)


theorem ordinary_triangle_finite_cover_general (κ:ℝ) (P F:SimpleGraph V) (J:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (h:OrdinaryTriangleFiniteCoverEvent κ P F J π d j σ):
    OrdinaryFiniteCoverEvent 3 κ P F J π d j σ:=by
  exact h

theorem ordinary_deep_finite_cover_general (m K:ℕ) (a ρ θ κ:ℝ)
    (P F:SimpleGraph V) (J:Finset U) (π:Equiv.Perm V) (d:ℕ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color) (hκ:0≤κ) (ha:κ≤a) (hρ:κ≤ρ) (hθ:κ≤θ)
    (hDeep:OrdinaryDeepCoverEvent m K a ρ θ P F J π d j σ):
    OrdinaryFiniteCoverEvent (m+1) κ P F J π d j σ:=by
  intro Q H L hQ hL hLκ hF hQR hHr hHc I hI E D₀ hE hFE hDE hEcard hD₀
    T W hTI hWJ hTcard hWcard hWdiv hTbal hErim hErow hEcol
  have hn:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have ha0:0≤a:=hκ.trans ha
  have hI':(I.card:ℝ)≤a*Fintype.card V:=hI.trans (mul_le_mul_of_nonneg_right ha hn)
  have hD₀':(D₀:ℝ)≤a*Fintype.card V:=hD₀.trans (mul_le_mul_of_nonneg_right ha hn)
  have hTcard':(T.card:ℝ)≤θ*Fintype.card V:=hTcard.trans (mul_le_mul_of_nonneg_right hθ hn)
  have hLρ:L≤ρ*Fintype.card V:=hLκ.trans (mul_le_mul_of_nonneg_right hρ hn)
  have hsq:κ^2≤a^2:=by nlinarith only [ha,hκ,ha0]
  have hEcard':(E.card:ℝ)≤a^2*(Fintype.card V:ℝ)^2:=
    hEcard.trans (mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
  have hFT:∀v∈T,∀w,Q.Adj v w→¬F.Adj v w:=by
    intro v hv w h
    exact (hQ h).2
  obtain ⟨PE,hPE,hPEE,hPEone,hPEr,hPEs,hPEc,M,hM,hMr,hMs,hMc,hMd,hMrow,hMcol,hMroot,hMavoidR,hMavoidS,hMavoidC,R,hR,hRE,hRr,hRs,hRc⟩:=
    hDeep Q H L (hQ.trans sdiff_le) hL hLρ hF hQR hHr hHc I hI' E D₀ hE hFE hDE hEcard' hD₀'
      T W hTI hWJ hTcard' hWcard hWdiv hFT hTbal hErim hErow hEcol
  exact ⟨R,hR,hRE,hRr,hRs,hRc⟩
end Oberwolfach
