module

public import Oberwolfach.MarkedVortexPreselectFromJointSample
public import Oberwolfach.MarkedVortexFixedAbsorberCompleteFromSteps
public import Oberwolfach.RetainedMarkedSpokeGeometry

@[expose] public section
/-! A common sampled absorber event completes the original physical host
once the divisible initial state and every cover-down step are available. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_completion_from_joint_sample_and_steps
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
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z)
    (γ σloss:ℕ→ℝ):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let P:=fun i=>G.comap (markedVortexVertexEmbedding Q i)
    let ρ:=fun i=>markedVortexPermutation Q π hpres i
    let σi:=fun i=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1
    let Hi:=fun i b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val
    let State:=fun i=>MarkedReferenceDeletion (P i) (ρ i) d (σi i)
    let Good:=fun i (T:State i)=>T.Valid (Hi i) (r+4) (markedVortexInnerVertices Q i)
      (markedVortexInnerHubs Q i) (γ i) (σloss i)
    let F:=fun i=>markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)
    let B:=fun i (T:State i)=>(T.remaining (Hi i)).image (F i)
    let E₀:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K₀:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true
    let R₀:=fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
      (r+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources W
    let S₀:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let Full:=markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) π Finset.univ S₀;
    (∀ i,i<Q.length→∀ T:State i,Good i T→∃ Tnext:State (i+1),Good (i+1) Tnext ∧
      B (i+1) Tnext⊆B i T ∧ HasResourceDecomposition R₀ (B i T\B (i+1) Tnext))→
    MarkedRemainderDivisible (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S₀ (r+4)→
    (e₀:ℝ)≤γ 0 → (e₀:ℝ)≤σloss 0 → HasResourceDecomposition R₀ Full := by
  intro H P ρ σi Hi State Good F B E₀ K₀ R₀ S₀ Full hsteps hdiv hγ hσ
  obtain ⟨C,_,hCe,_,_,hEmpty,habs⟩:=marked_vortex_preselect_absorber_from_joint_sample
    r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs hζ size a₀ b₀ e₀ f₀
    G D m β ε Q π hpres L hL s₀ p k q s a j z hreg hn hD hρhi he heAbs hsize hevent ∅ (by simp)
  have hH:∀ v u,¬(H false v u∧H true v u):=by
    intro v u
    exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j v u
  have hγ':(C.edges.card:ℝ)≤γ 0:=(by exact_mod_cast hCe : (C.edges.card:ℝ)≤e₀).trans hγ
  have hσ':(C.edges.card:ℝ)≤σloss 0:=(by exact_mod_cast hCe : (C.edges.card:ℝ)≤e₀).trans hσ
  rw [hL] at habs
  exact marked_vortex_fixed_absorber_complete_from_steps Q π hpres d (r+4) Q.length z.1 H γ σloss
    hsteps C.edges habs hH hdiv hEmpty hγ' hσ'
end Oberwolfach
