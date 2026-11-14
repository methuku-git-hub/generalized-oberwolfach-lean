module

public import Oberwolfach.MarkedCorrectionFirstDeeperBalance
public import Oberwolfach.MarkedVortexDeeperBalanceScale
public import Oberwolfach.MarkedVortexInitialDeeperBalance
public import Oberwolfach.MarkedVortexDeeperBoundsWithTerminal
public import Oberwolfach.MarkedCorrectionBalanceError
public import Oberwolfach.MarkedVortexFirstBalanceScale
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
  [LinearOrder V] [Nonempty V] [DecidableEq U]

def MarkedVortexCorrectionWithBothScaledBalances
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (L:ℕ)
    (C:∀i, RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color →
      (Bool → markedVortexVertexType Q i → markedVortexHubType Q i → Prop) → Prop) (η epsBal ζBal:ℝ):Prop:=
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
      (η*(Q.extendedVertices 1).card) σ' H' ∧
    MarkedLevelFiniteBalanceBound P π d (r+4) (Q.extendedVertices 2) (Q.extendedIndices 2)
      (η*(Q.extendedVertices 2).card) σ' H'

theorem marked_correction_first_deeper_balance_at_inner_scale
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (L:ℕ)
    (he:0<ε) (hm:0<m) (η epsBal ζBal:ℝ) (hη:0≤η)
    (hbase:epsBal+((r+4)+2:ℕ)*ζBal≤η/2)
    (hcor:((r+4)+2:ℕ)*(4*ζ)≤η*ε^2/8)
    (C:∀i,RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color →
      (Bool→markedVortexVertexType Q i→markedVortexHubType Q i→Prop)→Prop)
    (hstate:MarkedVortexCorrectionWithFirstAndDeepBalance P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H D m β ε Q L C η epsBal ζBal):
    MarkedVortexCorrectionWithBothScaledBalances P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H D m β ε Q L C η epsBal ζBal := by
  obtain ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance,hrestr,hfacts,hfirst,hdeep⟩:=hstate
  refine ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance,hrestr,hfacts,hfirst,?_⟩
  by_cases hLen:1<Q.length
  · exact marked_vortex_deeper_balance_from_ambient P π D m β ε Q he hm hLen r d η epsBal ζBal ζ hη hbase hcor _ _ hdeep
  · intro z j
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let S':=Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2)
    have hV:Q.extendedVertices 2=∅:=Q.extendedVertices_empty (by omega)
    have hU:Q.extendedIndices 2=∅:=Q.extendedIndices_empty (by omega)
    have hz:=markedFiniteDomainBalance_zero_of_avoids (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' (r+4)
      (Q.extendedVertices 2) (Q.extendedIndices 2) (by intro a ha;simp [hV])
      (by intro x hx;simp [hV,hU]) z j
    rw [hz,abs_zero]
    positivity
end Oberwolfach
