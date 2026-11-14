module

public import Oberwolfach.LongProtectedPreparationStatement
public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! Basic size and class hypotheses for long matching follow directly from
the original regular host and the original long-cycle assumption. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_original_basic_inputs
    {n D q K:ℕ} (hn:0<n) (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D)
    (θ α:ℝ) (hθ:1/2≤θ) (hα:0<α) (hdegree:(θ+α)*(n:ℝ)≤D)
    (hρhi:2*(q:ℝ)/(D:ℝ)≤1)
    (F:Fin q→SimpleGraph (Fin n))
    (hlong:∀u,(n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)):
    0<D ∧ 2*q≤D ∧ q≤n ∧ (∀u,factorPreparationClass (F u) K=none) :=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hDreal:0<(D:ℝ):=(mul_pos (by linarith : 0<θ+α) hnR).trans_le hdegree
  have hD:0<D:=by exact_mod_cast hDreal
  have h2qR:2*(q:ℝ)≤D:=(div_le_one hDreal).mp hρhi
  have h2q:2*q≤D:=by exact_mod_cast h2qR
  let v:Fin n:=⟨0,hn⟩
  have hDn:D≤n:=by
    have hh:=P.degree_lt_card_verts v
    rw [hP v] at hh
    simpa only [Fintype.card_fin] using hh.le
  refine ⟨hD,h2q,by omega,?_⟩
  intro u
  have hlong':(1/2:ℝ)≤((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n:=by
    apply (le_div_iff₀ hnR).2
    nlinarith [hlong u]
  simp only [factorPreparationClass,if_pos hlong']
end Oberwolfach
