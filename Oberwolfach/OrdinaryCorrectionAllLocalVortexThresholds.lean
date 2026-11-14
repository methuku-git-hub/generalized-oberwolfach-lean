module

public import Oberwolfach.OrdinaryVortexLocalEventGeometry

@[expose] public section
/-! One size threshold supplies all three local concentration tests and
the correction theorem on the original first vortex level. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_correction_all_local_vortex_thresholds
    (ε εabs εv:ℝ) (hε:0<ε) (habs:ε ≤ εabs) (hv:ε ≤ εv)
    (Nc Ng Nh Ncol:ℕ):
    ∃N:ℕ,1 ≤ N ∧ ∀{V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ) (β ρ₀:ℝ) (Q:Vortex U P D β ε mv),
      P.IsRegularOfDegree D → 0<Fintype.card V → 0<D → (Fintype.card V:ℝ)/2 ≤ D → 0<mv → 
      0<ρ₀ → ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D ≤ 1 → 
      0 ≤ β → β ≤ 1/4 → Fintype.card U ≤ Fintype.card V → N ≤ Fintype.card V → 
      let Z:=Q.extendedVertices 1;let Htest:=Q.extendedIndices 1;
      Ng ≤ Fintype.card V ∧ Nc ≤ Z.card ∧ Nh ≤ Z.card ∧ Ncol ≤ Z.card ∧
      0<Htest.card ∧ Htest.card ≤ Z.card ∧ (Htest.card:ℝ) ≤ (2/ε)*Z.card ∧
      (Z.card:ℝ) ≤ εabs*Fintype.card V ∧ (Htest.card:ℝ) ≤ εabs*Fintype.card V ∧
      (Z.card:ℝ) ≤ εv*Fintype.card V ∧ (Htest.card:ℝ) ≤ εv*Fintype.card V :=by
  let Nlocal:=max Nc (max Nh Ncol)
  obtain ⟨Ngeom,hNgeom,hgeometry⟩:=ordinary_vortex_local_event_geometry_eventually ε εabs εv hε habs hv Nlocal
  refine ⟨max Ngeom Ng,by omega,?_⟩
  intro V U _ _ _ _ P D mv β ρ₀ Q hreg hn hD hhalf hmv hρ hρlo hρhi hβ hβ1 hU hnN Z Htest
  obtain ⟨hlarge,hpositive,hHle,hratio,hZabs,hHabs,hZv,hHv⟩:=
    hgeometry P D mv β ρ₀ Q hreg hn hD hhalf hmv hρ hρlo hρhi hβ hβ1 hU (by omega)
  change Nlocal ≤ Z.card at hlarge
  have hNc:Nc ≤ Z.card:=by dsimp [Nlocal] at hlarge;omega
  have hNh:Nh ≤ Z.card:=by dsimp [Nlocal] at hlarge;omega
  have hNcol:Ncol ≤ Z.card:=by dsimp [Nlocal] at hlarge;omega
  exact ⟨by omega,hNc,hNh,hNcol,hpositive,hHle,hratio,hZabs,hHabs,hZv,hHv⟩
end Oberwolfach
