module

public import Oberwolfach.MarkedProtectedCorrectionWithBounds
public import Oberwolfach.MarkedUnchangedInnerSample

@[expose] public section
/-! The same protected correction supplies the bounded physical deletion
and its avoidance of every graph supported inside the protected vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_protected_correction_matching_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ ξ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (T:Finset V) (W:Finset U):
    MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζ ξ σ H T W →

    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∃(DA:Finset (E⊕K)) (DS:Finset (V×U)),DS⊆S ∧
      (∀v,((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
        8*(((r+4:ℕ):ℝ)+1)*ξ*Fintype.card V) ∧
      (∀v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξ*Fintype.card V) ∧
      (∀u,((DS.filter (fun z=>u=z.2)).card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξ*Fintype.card V) ∧
      (DA.card:ℝ)≤8*(((r+4:ℕ):ℝ)+1)*ξ*(Fintype.card V:ℝ)^2 ∧
      (DS.card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξ*(Fintype.card V:ℝ)^2 ∧
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource T W)=∅ ∧
      (∀v,((markedSampleArcSetGraph P π d σ DA).degree v:ℝ)≤ζ*Fintype.card V) ∧
      (∀z,((markedFiniteSpokeGraph DS).degree z:ℝ)≤ζ*Fintype.card V) ∧
      (∀x∈T,∀y∈T,¬(markedSampleArcSetGraph P π d σ DA).Adj x y) ∧
      (∀x∈T,∀u∈W,¬(markedFiniteSpokeGraph DS).Adj (Sum.inl x) (Sum.inr u)) ∧
      (∀Protected:SimpleGraph V,(∀x y,Protected.Adj x y→x∈T ∧ y∈T)→
        ∀x y,(markedSampleArcSetGraph P π d σ DA).Adj x y→¬Protected.Adj x y) ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) (r+4) ∧
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs := by
  intro hCorr
  obtain ⟨DA,DS,hSub,hArc,hRow,hCol,hCardA,hCardS,hEmpty,hDegA,hDegS,hDiv,hAbs⟩ := hCorr
  obtain ⟨hInnerA,hInnerS⟩ := marked_removed_resources_empty_inner P π d σ DA DS T W hEmpty
  refine ⟨DA,DS,hSub,hArc,hRow,hCol,hCardA,hCardS,hEmpty,hDegA,hDegS,hInnerA,hInnerS,?_,hDiv,hAbs⟩
  intro Protected hProtected x y hxy hxyProtected
  obtain ⟨hx,hy⟩ := hProtected x y hxyProtected
  exact hInnerA x hx y hy hxy
end Oberwolfach
