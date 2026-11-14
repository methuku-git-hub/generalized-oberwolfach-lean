module

public import Oberwolfach.MarkedVortexAbsorbableCorrectionBalance
public import Oberwolfach.MarkedUnchangedInnerSample
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def MarkedVortexAbsorbableCorrectionWithRestrictions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m):Prop:=
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∃(DA:Finset (E⊕K)) (DS:Finset (V×U)),DS⊆S ∧
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅ ∧
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
    (∀ (i : ℕ), 1 ≤ i → ∀ z, Sum.elim (fun v => v ∈ Q.extendedVertices i) (fun u => u ∈ Q.extendedIndices i) z → ∀ j,
      markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
        (Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2)) (r+4)
        (Q.extendedVertices i) (Q.extendedIndices i) z j=
      markedFiniteDomainBalance tail head ktail khead (H true) Finset.univ S (r+4)
        (Q.extendedVertices i) (Q.extendedIndices i) z j) ∧
    ∀ (i : ℕ), 1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ' =
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ ∧
      (fun b x u => H' b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)) =
        (fun b x u => H b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u))

theorem marked_absorbable_correction_vortex_restrictions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m):
    MarkedVortexAbsorbableCorrectionWithBalance P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H D m β ε Q →
    MarkedVortexAbsorbableCorrectionWithRestrictions P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H D m β ε Q := by
  intro hcor
  obtain ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance⟩ := hcor
  refine ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance,?_⟩
  intro i hi
  exact marked_raw_pair_unchanged_on_inner P π d σ H DA DS
    (Q.extendedVertices 1) (Q.extendedIndices 1) havoid
    (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
    (fun x => Q.extendedVertices_subset hi x.property)
    (fun u => Q.extendedIndices_subset hi u.property)
end Oberwolfach
