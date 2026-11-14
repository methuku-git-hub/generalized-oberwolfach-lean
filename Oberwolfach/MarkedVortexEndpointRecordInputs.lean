module

public import Oberwolfach.MarkedActiveEndpointRecordInputs
public import Oberwolfach.MarkedVortexNonDeeperInnerHubs
public import Oberwolfach.MarkedVortexNonDeeperGeometry

@[expose] public section
/-! Endpoint record fields on the actual nested vortex embeddings, taking
zero deletions in the same retained reference event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_endpoint_record_inputs
    (r h d:ℕ) (α βconfig εref δref tol ζActive ζAbs tstar εAbs:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε)
    (L:ℕ) (hL:L<Q.length) (s₀ p k x:ℝ) (he0:0≤tol+h*ζActive) (hex:tol+h*ζActive≤x/2)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hevent:MarkedReferenceActiveAbsorberProperty r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:=markedVortexNonDeeperHubToParent Q i
      let X:=Finset.univ.image f
      let Zinner:=markedVortexInnerNonDeeperHubs Q i
      let ω:=rawMarkedRestrictPair fP gP z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fP x) (gP u);
      ∃ errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card W ∧ errI≤(x/2)*Fintype.card W ∧
        MarkedRowsWithSpokes (G.comap fP) ρ d h (X.image fA) p k (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR ω H ∧
        MarkedIndicesWithSpokes ρ d h (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) a j errI ω H:=by
  intro i hi W Z fP gP ρ fA f gA X Zinner ω H
  have hUV:Fintype.card Z≤Fintype.card W:=by
    have hh:=Q.index_size_upper hreg hn hD he hρhi (i:=i) (by omega)
    change Fintype.card ↥(Q.extendedIndices i)≤Fintype.card ↥(Q.extendedVertices i)
    simp only [Fintype.card_coe]
    rw [Q.extendedIndices_eq (by omega:i≤Q.length),Q.extendedVertices_eq (by omega:i≤Q.length)]
    omega
  have hX:X.image fA=markedVortexInnerVertices Q i\markedVortexDeeperVertices Q i:=by
    dsimp [X,fA,f]
    rw [Finset.image_image]
    exact marked_vortex_next_active_parent_image Q i
  have hZ:Zinner.image gA=markedVortexInnerHubs Q i\markedVortexDeeperHubs Q i:=
    marked_vortex_inner_nondeeper_hubs_image Q i
  have hh:=marked_reference_active_endpoint_base r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z hevent i hi
  rw [hX,hZ]
  exact marked_active_endpoint_record_inputs (G.comap fP) ρ d h _ _ p k (fun u=>q (gP u)) (fun u=>s (gP u)) a j
    (tol+h*ζActive) x he0 hex hUV ω H hh.1 hh.2
end Oberwolfach
