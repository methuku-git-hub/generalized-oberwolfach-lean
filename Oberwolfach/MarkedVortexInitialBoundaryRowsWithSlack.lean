module

public import Oberwolfach.MarkedVortexInitialBoundaryRowsTransfer
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

theorem marked_vortex_initial_boundary_rows_with_slack
    (h:ℕ) (x:ℝ) (hx:0<x):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d:ℕ) (σglobal τglobal:RawMarkedOutcome V U Γ Color) (Hglobal Hglobal':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hinterval:∀e,σglobal (Sum.inr e)=τglobal (Sum.inr e))
    (hR:∀a,¬(rawMarkedPairRims G π d σglobal a↔rawMarkedPairRims G π d τglobal a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(Hglobal b v u↔Hglobal' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V),
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
    0≤errR→0≤errI→errR≤(x/4)*Fintype.card W→errI≤(x/4)*Fintype.card W→
    MarkedRowsWithSpokes P ρ d h A p k q s a j errR σ H→
    MarkedIndicesWithSpokes ρ d h B q s a j errI σ H→
    ∃eR eI:ℝ,0≤eR ∧ 0≤eI ∧ eR≤(x/2)*Fintype.card W ∧ eI≤(x/2)*Fintype.card W ∧
      MarkedRowsWithSpokes P ρ d h A p k q s a j eR τ H' ∧
      MarkedIndicesWithSpokes ρ d h B q s a j eI τ H'  := by
  let cap:ℝ:=x/(8*((h:ℝ)+1))
  have hcap:0<cap:=by dsimp [cap];positivity
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ G D m β ε Q π hπ d σglobal τglobal Hglobal Hglobal' FR FS
    hinterval hR hS hFR hFS W Z f g ρ P σ τ H H' A B p k errR errI q s a j herrR herrI hboundR hboundI hrows hindices
  have hn:(0:ℝ)≤Fintype.card W:=Nat.cast_nonneg _
  have hζbound:ζ*(8*((h:ℝ)+1))≤x:=(le_div_iff₀ (by positivity)).mp hζcap
  have hcost:2*(h:ℝ)*ζ≤x/4:=by nlinarith [mul_nonneg (show (0:ℝ)≤h by positivity) hζ]
  have hcostn:=mul_le_mul_of_nonneg_right hcost hn
  let eR:=errR+(h:ℝ)*(2*ζ*Fintype.card W)
  let eI:=errI+(h:ℝ)*(ζ*Fintype.card W)
  have hRbound:eR≤(x/2)*Fintype.card W:=by dsimp [eR];nlinarith
  have hIbound:eI≤(x/2)*Fintype.card W:=by
    dsimp [eI]
    nlinarith [mul_nonneg (show (0:ℝ)≤h by positivity) (mul_nonneg hζ hn)]
  have hh:=marked_vortex_initial_boundary_rows_transfer V U Γ Color G D m β ε Q π hπ d h σglobal τglobal Hglobal Hglobal' FR FS ζ hζ hinterval hR hS hFR hFS
    A B p k errR errI q s a j hrows hindices
  refine ⟨eR,eI,?_,?_,hRbound,hIbound,hh.1,hh.2⟩ <;> dsimp [eR,eI] <;> positivity
end Oberwolfach
