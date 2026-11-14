module

public import Oberwolfach.MarkedVortexInitialSampleChangeData
public import Oberwolfach.MarkedModifiedPhysicalIncidence

@[expose] public section
/-! Transfer arbitrary initial-parent row and index test sets under the
same physical correction, retaining their separate error allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_boundary_rows_transfer
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d h:ℕ) (σglobal τglobal:RawMarkedOutcome V U Γ Color) (Hglobal Hglobal':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (ζ:ℝ) (hζ:0≤ζ)
    (hinterval:∀e,σglobal (Sum.inr e)=τglobal (Sum.inr e))
    (hR:∀a,¬(rawMarkedPairRims G π d σglobal a↔rawMarkedPairRims G π d τglobal a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(Hglobal b v u↔Hglobal' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V):
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hπ 0
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σglobal
    let τ:=rawMarkedRestrictPair f g τglobal
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let H':=fun b v u=>Hglobal' b (f v) (g u);
    ∀(A:Finset W) (B:Finset Z) (p k errR errI:ℝ) (q:Z→Γ→ℝ) (s:Z→Color→ℝ) (a:Γ) (j:Color),
    MarkedRowsWithSpokes P ρ d h A p k q s a j errR σ H→
    MarkedIndicesWithSpokes ρ d h B q s a j errI σ H→
    MarkedRowsWithSpokes P ρ d h A p k q s a j (errR+h*(2*ζ*Fintype.card W)) τ H' ∧
    MarkedIndicesWithSpokes ρ d h B q s a j (errI+h*(ζ*Fintype.card W)) τ H' := by
  intro W Z f g ρ P σ τ H H' A B p k errR errI q s a j hrows hindices
  have hchanges:=marked_vortex_initial_sample_change_data Q π hπ d σglobal τglobal Hglobal Hglobal' FR FS ζ hinterval hR hS hFR hFS
  have hδ:0≤ζ*Fintype.card W:=by positivity
  have hdec:(Subtype.instDecidableEq : DecidableEq W)=(fun x y=>Classical.propDecidable (x=y)):=Subsingleton.elim _ _
  try rw [hdec] at hrows
  try rw [hdec] at hindices
  try rw [hdec]
  have hh:=marked_neighbourhoods_after_physical_change P ρ d h A B p k q s a j errR errI
    (ζ*Fintype.card W) (ζ*Fintype.card W) (ζ*Fintype.card W) hδ hδ hδ σ τ H H' hrows hindices
    (FR.comap f) (FS.comap (Sum.map f g)) hchanges.2.1 hchanges.2.2.1 hchanges.2.2.2.1
    (fun v=>hchanges.2.2.2.2.1 (Sum.inl v)) (fun u=>hchanges.2.2.2.2.1 (Sum.inr u))
  convert hh using 1 <;> congr! 3 <;> ring
end Oberwolfach
