module

public import Oberwolfach.MarkedProtectedCorrectionWithBounds
public import Oberwolfach.MarkedCanonicalSparseCorrectionState

@[expose] public section
/-! Retain the robust absorber and the exact corrected sample when forming
the initial valid deletion state from a bounded protected correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_protected_bounded_correction_reference_state
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ ξ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (T:Finset V) (W:Finset U)
    (γ σloss:ℝ) (hξ:0≤ξ)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξ*Fintype.card V)≤min γ σloss)
    (hCorr:MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζ ξ σ H T W):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∃ (DA:Finset (E⊕K)) (DS:Finset (V×U)) (D:MarkedReferenceDeletion P π d σ),
      D.arcs=DA ∧ D.spokes=DS ∧ D.Valid H (r+4) T W γ σloss ∧
      let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
      let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
      let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
      let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
      MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
        (H' true) Finset.univ (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) (r+4) ∧
      MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs := by
  intro E K
  dsimp only [MarkedProtectedAbsorbableCorrectionWithBounds] at hCorr
  obtain ⟨DA,DS,hsub,hArc,hRow,hCol,hcardA,hcardS,havoid,hRim,hSpoke,hdiv,habs⟩:=hCorr
  let B:ℝ:=8*((((r+4):ℕ):ℝ)+1)*ξ*Fintype.card V
  have hB:0≤B:=by dsimp [B];positivity
  have hRow':∀v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤B:=by
    intro v
    dsimp [B]
    have hh:=hRow v
    have hp:0≤4*((((r+4):ℕ):ℝ)+1)*ξ*Fintype.card V:=by positivity
    linarith
  have hCol':∀u,((DS.filter (fun z=>z.2=u)).card:ℝ)≤B:=by
    intro u;dsimp [B];have hh:=hCol u;have hh':((DS.filter (fun z=>z.2=u)).card:ℝ)≤4*((((r+4):ℕ):ℝ)+1)*ξ*Fintype.card V:=by simpa only [eq_comm] using hh
    have hp:0≤4*((((r+4):ℕ):ℝ)+1)*ξ*Fintype.card V:=by positivity
    linarith
  obtain ⟨D,hDA,hDS,hvalid⟩:=marked_canonical_sparse_correction_reference_state P π d (r+4) σ H T W γ σloss B hB hbudget
    DA DS hsub havoid hArc hRow' hCol' hdiv
  exact ⟨DA,DS,D,hDA,hDS,hvalid,hdiv,habs⟩
end Oberwolfach
