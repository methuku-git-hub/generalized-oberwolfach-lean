module

public import Oberwolfach.OrdinaryTrianglePreparationFromOriginal
public import Oberwolfach.OrdinaryProtectedPreparationStatement
public import Oberwolfach.ConditionalPreparationMain

@[expose] public section
/-! The triangle case is proved; ordinary preparation reduces to the
remaining component lengths at least four. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryNontriangleProtectedPreparation : Prop :=
  ∀(θ α₀ εmax ρstar β:ℝ),
    (1/2:ℝ)≤θ→θ<1→0<α₀→0<εmax→∀(hρstar:0<ρstar),ρstar≤1→0<β→β≤1→
  ∀rstar:ℕ,4≤rstar→
  ∃ξ:ℝ,0<ξ ∧ ∀χ:ℝ,0<χ→χ<1→∃B N:ℕ,1≤B ∧ 1≤N ∧
  ∀n≥N,∀(P:SimpleGraph (Fin n)) (D q:ℕ),
    P.IsRegularOfDegree D→Even D→(θ+α₀)*(n:ℝ)≤D→
  let ρ:ℝ:=2*(q:ℝ)/(D:ℝ);
  ∀(hρlo:ρstar≤ρ) (hρhi:ρ≤1),
  ∀F:Fin q→SimpleGraph (Fin n),
    (∀w,(F w).IsRegularOfDegree 2)→
    (∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)→
    (∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ))→
  ∃I:Finset (Fin n), (I.card:ℝ)≤εmax*n ∧
    1-χ-1/(n:ℝ)^10≤
      (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ
        (hρstar.le.trans hρlo) hρhi)).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F)

theorem ordinary_triangle_nontriangle_preparation_reduction
    (hNontriangle:OrdinaryNontriangleProtectedPreparation):OrdinaryProtectedPreparation :=by
  intro θ α₀ εmax ρstar β hθ hθ1 hα hε hρ hρ1 hβ hβ1 rstar hr
  by_cases h:rstar=3
  · subst rstar
    exact ordinary_triangle_preparation_from_original θ α₀ εmax ρstar β hθ hθ1 hα hε hρ hρ1 hβ hβ1
  · exact hNontriangle θ α₀ εmax ρstar β hθ hθ1 hα hε hρ hρ1 hβ hβ1 rstar (by omega)
theorem ordinary_nontriangle_and_long_imply_fixed_set
    (hNontriangle:OrdinaryNontriangleProtectedPreparation) (hLong:LongProtectedPreparation):FixedSetTheorem :=
  conditional_preparation_fixed_set (ordinary_triangle_nontriangle_preparation_reduction hNontriangle) hLong

theorem ordinary_nontriangle_and_long_imply_main
    (hNontriangle:OrdinaryNontriangleProtectedPreparation) (hLong:LongProtectedPreparation):MainTheorem :=
  conditional_preparation_main (ordinary_triangle_nontriangle_preparation_reduction hNontriangle) hLong
end Oberwolfach
