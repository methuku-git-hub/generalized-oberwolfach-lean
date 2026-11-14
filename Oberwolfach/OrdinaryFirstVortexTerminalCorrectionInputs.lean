module

public import Oberwolfach.OrdinaryCorrectionAllLocalVortexThresholds
public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! The actual last vortex level fits the terminal budget before the sample,
and is contained in the first vortex level used by the correction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_first_vortex_terminal_correction_inputs
    {n q D mv:ℕ} {β ε εabs εv:ℝ} (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv)
    (hreg:P.IsRegularOfDegree D) (hn:0<n) (hD:0<D) (he:0≤ε)
    (hρ:initialIndexDensity (Fin q) D≤1)
    (hZabs:((Q.extendedVertices 1).card:ℝ)≤εabs*n)
    (hBabs:((Q.extendedIndices 1).card:ℝ)≤εabs*n)
    (hZv:((Q.extendedVertices 1).card:ℝ)≤εv*n)
    (hBv:((Q.extendedIndices 1).card:ℝ)≤εv*n):
    let Z:=Q.extendedVertices 1; let B:=Q.extendedIndices 1;
    let Wterm:=Q.extendedVertices Q.length; let Bterm:=Q.extendedIndices Q.length;
    Wterm.card+Bterm.card≤2*mv ∧ Wterm⊆Z ∧ Bterm⊆B ∧ Wterm.card≤mv ∧
    (Z.card:ℝ)≤εabs*n ∧ (B.card:ℝ)≤εabs*n+mv ∧
    (Z.card:ℝ)≤εv*n ∧ (B.card:ℝ)≤εv*n+mv :=by
  intro Z B Wterm Bterm
  have hlen:1≤Q.length:=by have h:=Q.length_pos; omega
  have hW:Wterm⊆Z:=Q.extendedVertices_subset hlen
  have hB:Bterm⊆B:=Q.extendedIndices_subset hlen
  have hterminal:Wterm.card<mv:=by
    dsimp only [Wterm]
    rw [Q.extendedVertices_eq (le_refl Q.length)]
    exact Q.terminal_upper
  have hupper:=Q.extended_index_size_upper hreg (by simpa using hn) hD he hρ Q.length
  change 2*Bterm.card≤Wterm.card at hupper
  have hpair:Wterm.card+Bterm.card≤2*mv:=by omega
  have hBabs':(B.card:ℝ)≤εabs*n+mv:=by
    have hm:(0:ℝ)≤mv:=by positivity
    dsimp only [B]
    linarith [hBabs]
  have hBv':(B.card:ℝ)≤εv*n+mv:=by
    have hm:(0:ℝ)≤mv:=by positivity
    dsimp only [B]
    linarith [hBv]
  exact ⟨hpair,hW,hB,by omega,hZabs,hBabs',hZv,hBv'⟩
end Oberwolfach
