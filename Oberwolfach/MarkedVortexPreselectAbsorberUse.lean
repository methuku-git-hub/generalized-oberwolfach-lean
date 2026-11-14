module

public import Oberwolfach.MarkedVortexPreselectFromJointSample

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_preselect_absorber_and_apply
    (r h d:ℕ) (α βconfig εref δref tol ζActive ζAbs tstar εAbs:ℝ)
    (hζ:0≤ζAbs)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (hL:L+1=Q.length) (s₀ p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (heAbs:ε≤εAbs) (hsize:2*m≤size)
    (hevent:MarkedReferenceActiveAbsorberProperty r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let E:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true;
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f₀→
    ∀ Result:Finset (Finset V⊕(V×U))→Prop,
      (∀ Reserve,MarkedFixedTerminalAbsorber G π d (r+4) z.1 H Reserve
        (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1))→Result Reserve)→
    ∃ C:MarkedSupportedEdgeSet (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      C.edges.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅ ∧
      MarkedFixedTerminalAbsorber G π d (r+4) z.1 H C.edges
        (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧ Result C.edges := by
  intro H E K F₀ hF Result hResult
  obtain ⟨C,hdis,hcard,hrows,hhubs,hinner,hfixed⟩:=
    marked_vortex_preselect_absorber_from_joint_sample r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
      hζ size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L hL s₀ p k q s a j z
      hreg hn hD hρhi he heAbs hsize hevent F₀ hF
  exact ⟨C,hdis,hcard,hrows,hhubs,hinner,hfixed,hResult C.edges hfixed⟩
end Oberwolfach
