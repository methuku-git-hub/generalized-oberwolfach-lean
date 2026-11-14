module

public import Oberwolfach.OrdinaryProtectedPreparationStatement
public import Oberwolfach.ProtectedPreparationDensityOneProbability

@[expose] public section
/-! Consequence of the ordinary proposition at density one. The ordinary
proposition itself remains an explicit hypothesis of this reduction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_preparation_density_one
    (hOrd:OrdinaryProtectedPreparation) (θ α β:ℝ)
    (hθ:(1/2:ℝ)≤θ) (hθ1:θ<1) (hα:0<α) (hβ:0<β) (hβ1:β≤1)
    (r:ℕ) (hr:3≤r):
    ∃ξ:ℝ,0<ξ ∧ ∃B N:ℕ,∀n≥N,∀(P F:SimpleGraph (Fin n)) (D:ℕ),
      P.IsRegularOfDegree D→Even D→(θ+α)*(n:ℝ)≤D→
      F.IsRegularOfDegree 2→
      (∀v,cycleThreshold (Fintype.card (F.connectedComponentMk v))≤θ)→
      β*n≤((Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=r)).card:ℝ)→
      ∃I:Finset (Fin n), 0<
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num))).probability
          (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B (fun _:Fin (D/2)=>F)) :=by
  obtain ⟨ξ,hξ,hχ⟩:=hOrd θ α 1 (1/2) β hθ hθ1 hα (by norm_num) (by norm_num) (by norm_num) hβ hβ1 r hr
  obtain ⟨B,N,hB,hN,hPrep⟩:=hχ (1/4) (by norm_num) (by norm_num)
  refine ⟨ξ,hξ,B,max N 4,?_⟩
  intro n hn P F D hP hEven hdegree hF hthreshold habund
  have hn4:4≤n:=by omega
  have hn0:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hdpos:0<(D:ℝ):=lt_of_lt_of_le (mul_pos (by linarith) hn0) hdegree
  have hdhalf:2*(D/2)=D:=by
    obtain ⟨k,hk⟩:=hEven
    omega
  have hρ:2*((D/2:ℕ):ℝ)/(D:ℝ)=1:=by
    have heq:2*((D/2:ℕ):ℝ)=(D:ℝ):=by exact_mod_cast hdhalf
    rw [heq,div_self (ne_of_gt hdpos)]
  have hρlo:(1/2:ℝ)≤2*((D/2:ℕ):ℝ)/(D:ℝ):=by rw [hρ]; norm_num
  have hρhi:2*((D/2:ℕ):ℝ)/(D:ℝ)≤1:=by rw [hρ]
  obtain ⟨I,hI,hProb⟩:=hPrep n (by omega) P D (D/2) hP hEven hdegree hρlo hρhi
    (fun _:Fin (D/2)=>F) (fun _=>hF) (fun _=>hthreshold) (fun _=>habund)
  have hnR:(4:ℝ)≤n:=by exact_mod_cast hn4
  have hpow1:1≤(n:ℝ)^9:=one_le_pow₀ (by linarith) 
  have hpow:4≤(n:ℝ)^10:=by
    have hmul:(n:ℝ)≤n*(n:ℝ)^9:=by nlinarith
    rw [pow_succ]
    nlinarith
  have hfrac:(1:ℝ)/(n:ℝ)^10≤1/4:=by
    exact one_div_le_one_div_of_le (by norm_num) hpow
  have hprobpos:0<1-(1/4:ℝ)-1/(n:ℝ)^10:=by linarith
  refine ⟨I,?_⟩
  apply lt_of_lt_of_le hprobpos
  simpa only [hρ] using hProb
end Oberwolfach
