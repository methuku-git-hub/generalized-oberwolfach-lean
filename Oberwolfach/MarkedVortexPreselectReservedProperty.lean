module

public import Oberwolfach.MarkedVortexReservedCapacityFields
public import Oberwolfach.MarkedVortexSampledOriginalAbsorber
public import Oberwolfach.MarkedSelectFixedTerminalAbsorber

@[expose] public section
/-! The joint sample already permits selection of one fixed terminal absorber
which avoids the entire first inner pair before cover-down begins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_preselect_absorber_from_reserved_property
    (r d:ℕ) (εAbs:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (hL:L+1=Q.length) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (heAbs:ε≤εAbs) (hsize:2*m≤size)
    (hprop:MarkedReservedTerminalAbsorberProperty
        (fun e:MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
        (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j false)
        (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j true)
        π (3*d) r size a₀ b₀ e₀ f₀ εAbs):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let E:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true;
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f₀→
    ∃ C:MarkedSupportedEdgeSet (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      C.edges.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅ ∧
      MarkedFixedTerminalAbsorber G π d (r+4) z.1 H C.edges
        (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) := by
  intro H E K F₀ hF
  have hcap:=marked_vortex_reserved_capacity_fields Q hreg hn hD hρhi he εAbs heAbs L hL
    (Function.Embedding.refl (markedVortexVertexType Q L)) (Function.Embedding.refl (markedVortexHubType Q L))
  obtain ⟨hI0,_,hJ0,_⟩:=marked_vortex_inner_cardinalities Q 0
  obtain ⟨hIL,_,hJL,_⟩:=marked_vortex_inner_cardinalities Q L
  have hcard0:Fintype.card (markedVortexVertexType Q 0)=Fintype.card V := by
    change Fintype.card ↥(Q.extendedVertices 0)=Fintype.card V
    rw [Fintype.card_coe,Q.extendedVertices_eq (Nat.zero_le _),Q.initial,Finset.card_univ]
  have hfirstV:((Q.extendedVertices 1).card:ℝ)≤εAbs*Fintype.card V+f₀ := by
    have hh:=hcap.1
    rw [hI0,hcard0] at hh
    have hf:(0:ℝ)≤f₀:=Nat.cast_nonneg _
    linarith
  have hfirstU:((Q.extendedIndices 1).card:ℝ)≤εAbs*Fintype.card V+f₀ := by
    have hh:=hcap.2.1
    rw [hJ0,hcard0] at hh
    have hf:(0:ℝ)≤f₀:=Nat.cast_nonneg _
    linarith
  have hterm:(Q.extendedVertices (L+1)).card+(Q.extendedIndices (L+1)).card≤size := by
    have hh:=hcap.2.2
    simp only [Function.Embedding.coe_refl,Finset.image_id] at hh
    rw [hIL,hJL] at hh
    exact hh.trans hsize
  exact marked_select_fixed_terminal_absorber G π d r size a₀ b₀ e₀ f₀ εAbs z.1 H hprop
    (Q.extendedVertices (L+1)) (Q.extendedVertices 1) (Q.extendedVertices 1)
    (Q.extendedIndices (L+1)) (Q.extendedIndices 1) (Q.extendedIndices 1)
    hterm (Q.extendedVertices_subset (by omega)) (Q.extendedIndices_subset (by omega))
    Finset.Subset.rfl Finset.Subset.rfl (hpres 1) hfirstV hfirstU F₀ hF
end Oberwolfach
