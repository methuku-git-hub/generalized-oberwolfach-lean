module

public import Oberwolfach.MarkedProtectedAbsorbableCorrection
public import Oberwolfach.MarkedActualInnerCorrectionInputs
public import Oberwolfach.MarkedProtectedCanonicalCorrectionAbsorber

@[expose] public section
/-! A protected correction with a divisible remaining sample and a robust
terminal absorber on that same physically deleted sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def MarkedProtectedAbsorbableCorrectionWithNestedBalance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (T:Finset V) (W:Finset U):Prop:=
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∃(DA:Finset (E⊕K)) (DS:Finset (V×U)),DS⊆S ∧
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource T W)=∅ ∧
      (∀v,((markedSampleArcSetGraph P π d σ DA).degree v:ℝ)≤ζ*Fintype.card V) ∧
      (∀z,((markedFiniteSpokeGraph DS).degree z:ℝ)≤ζ*Fintype.card V) ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) (r+4) ∧
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs ∧
    ∀(I:Finset V) (J:Finset U),I⊆T→J⊆W→(∀v,π v∈I↔v∈I)→
    ∀z,Sum.elim (fun v=>v∈I) (fun u=>u∈J) z→∀i,
      markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
        (Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2)) (r+4) I J z i=
      markedFiniteDomainBalance tail head ktail khead (H true) Finset.univ S (r+4) I J z i

theorem marked_absorbable_correction_preserves_nested_balance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (T:Finset V) (W:Finset U)
    :
    MarkedProtectedAbsorbableCorrection P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H T W→
    MarkedProtectedAbsorbableCorrectionWithNestedBalance P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H T W:=by
  intro hcor
  obtain ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs⟩:=hcor
  refine ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,?_⟩
  intro I J hIT hJW hI
  have hsmall:(markedFiniteResources (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1)
      (fun e=>e.val.2) (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1)
      (fun e=>e.val.2) π DA DS).filter (markedInnerResource I J)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx,hinner⟩:=Finset.mem_filter.mp hx
    have hlarge:x∈(markedFiniteResources (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1)
        (fun e=>e.val.2) (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1)
        (fun e=>e.val.2) π DA DS).filter (markedInnerResource T W):=by
      refine Finset.mem_filter.mpr ⟨hx,?_⟩
      cases x with
      | inl e=>exact fun y hy=>hIT (hinner hy)
      | inr z=>exact ⟨hIT hinner.1,hJW hinner.2⟩
    rw [havoid] at hlarge
    exact Finset.notMem_empty _ hlarge
  exact marked_actual_inner_balance_unchanged P π d (r+4) σ H I J hI DA DS hsub hsmall
end Oberwolfach
