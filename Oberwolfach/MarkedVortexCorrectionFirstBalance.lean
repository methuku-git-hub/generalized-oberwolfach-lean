module

public import Oberwolfach.MarkedVortexCorrectionLevelFacts
public import Oberwolfach.MarkedVortexInitialInnerBalance
public import Oberwolfach.MarkedCorrectionBalanceError
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

def MarkedVortexCorrectionWithFirstBalance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (L:ℕ)
    (C:∀i, RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color →
      (Bool → markedVortexVertexType Q i → markedVortexHubType Q i → Prop) → Prop) (err:ℝ):Prop:=
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
    (∀ (i : ℕ), 1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ' =
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ ∧
      (fun b x u => H' b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)) =
        (fun b x u => H b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u))) ∧
    (∀ i, 1 ≤ i → i ≤ L →
      C i (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ')
        (fun b x u => H' b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u))) ∧
    MarkedLevelFiniteBalanceBound P π d (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
      (err+((r+4)+2)*(4*(ζ*Fintype.card V))) σ' H'

theorem marked_vortex_correction_first_balance_from_event
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (L:ℕ)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (hζ:0≤ζ) (err:ℝ)
    (C:∀i,RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color →
      (Bool→markedVortexVertexType Q i→markedVortexHubType Q i→Prop)→Prop)
    (hbal:MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q 0))
      (markedVortexPermutation Q π hpres 0) d (r+4) (markedVortexInnerVertices Q 0) (markedVortexInnerHubs Q 0) err
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σ)
      (fun b x u=>H b (markedVortexVertexEmbedding Q 0 x) (markedVortexHubEmbedding Q 0 u)))
    (hcor:MarkedVortexAbsorbableCorrectionWithLevelFacts P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H D m β ε Q L C):
    MarkedVortexCorrectionWithFirstBalance P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H D m β ε Q L C err := by
  have hhost:=marked_vortex_initial_inner_balance_on_host P π D m β ε Q hpres d (r+4) err σ H hbal
  obtain ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance,hrestr,hfacts⟩:=hcor
  refine ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance,hrestr,hfacts,?_⟩
  simpa only [Nat.cast_add,Nat.cast_ofNat] using marked_correction_balance_from_physical_degrees P π d (r+4) σ H (Q.extendedVertices 1) (Q.extendedIndices 1)
    err (ζ*Fintype.card V) (by positivity) DA DS hsub hrim hspoke hhost
end Oberwolfach
