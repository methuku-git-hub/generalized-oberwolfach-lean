module

public import Oberwolfach.MarkedVortexFixedSelectionProperty

@[expose] public section
/-! Apply the uniform fixed-selection property at the terminal pair of the
actual vortex, before the matching and deletion are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_select_canonical_terminal
    (r d size a₀ b₀ e₀ f₀:ℕ) (εAbs:ℝ) (G:SimpleGraph V) (π:Equiv.Perm V) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hfixed:MarkedVortexFixedSelection r d size a₀ b₀ e₀ f₀ εAbs G π a j z)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρ:initialIndexDensity U D≤1) (he:0≤ε) (heAbs:ε≤εAbs) (hsize:2*m≤size):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let E:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f₀→
    ∃ C:MarkedSupportedEdgeSet (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      C.edges.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅ ∧
      MarkedFixedTerminalAbsorber G π d (r+4) z.1 H C.edges
        (Q.extendedVertices Q.length) (Q.extendedIndices Q.length) := by
  have hlast:Q.length-1+1=Q.length:=by have hh:=Q.length_pos;omega
  simpa only [hlast] using hfixed D m β ε Q hpres (Q.length-1) hlast hreg hn hD hρ he heAbs hsize
end Oberwolfach
