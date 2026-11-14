module

public import Oberwolfach.OrdinaryPreparationDensityOne
public import Oberwolfach.FactorClassAssignment
public import Oberwolfach.PreparationWeightsFromAllowedThreshold

@[expose] public section
/-! A conditional reduction: ordinary preparation supplies the short-class
positive-probability input, uniformly over the finitely many short classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_short_class_preparation_reduction
    (hOrd:OrdinaryProtectedPreparation) (Allowed:Set ℕ)
    (hAllowed:Allowed.Nonempty) (hValid:∀s∈Allowed,3≤s)
    (α:ℝ) (hα:0<α) (K:ℕ) (hK:3≤K):
    ∃N:ℕ,∀n≥N,∀(P F:SimpleGraph (Fin n)) (D:ℕ),
      P.IsRegularOfDegree D→Even D→(allowedThreshold Allowed+α/2)*(n:ℝ)≤D→
      F.IsRegularOfDegree 2→AllowedCycleLengths F Allowed→factorPreparationClass F K≠none→
      ∃(I:Finset (Fin n)) (ξ:ℝ) (B:ℕ),0≤ξ ∧ 0<
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num))).probability
          (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B (fun _:Fin (D/2)=>F)) :=by
  let θ:=allowedThreshold Allowed
  have hθ:(1/2:ℝ)≤θ:=allowedThreshold_half_le hAllowed hValid
  by_cases hθ1:θ<1
  · let β:ℝ:=1/(2*(K:ℝ))
    have hβ:0<β:=by dsimp [β]; positivity
    have hβ1:β≤1:=by
      dsimp [β]
      have hKr:(3:ℝ)≤K:=by exact_mod_cast hK
      rw [div_le_one (by positivity)]
      linarith
    have hEach:∀i:Fin K,∃ξ:ℝ,0<ξ ∧ ∃B N:ℕ,∀n≥N,∀(P F:SimpleGraph (Fin n)) (D:ℕ),
      P.IsRegularOfDegree D→Even D→(θ+α/2)*(n:ℝ)≤D→F.IsRegularOfDegree 2→
      (∀v,cycleThreshold (Fintype.card (F.connectedComponentMk v))≤θ)→
      β*n≤((Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=max 3 (i.val+1))).card:ℝ)→
      ∃I:Finset (Fin n),0<(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num))).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B (fun _:Fin (D/2)=>F)):=by
      intro i
      exact ordinary_preparation_density_one hOrd θ (α/2) β hθ hθ1 (by positivity) hβ hβ1 _ (le_max_left _ _)
    choose ξ hξ B N hPrep using hEach
    refine ⟨max 1 (∑i:Fin K,N i),?_⟩
    intro n hn P F D hP hEven hdegree hF hFAllowed hshort
    have hn0:0<n:=by omega
    cases hc:factorPreparationClass F K with
    | none => exact False.elim (hshort hc)
    | some i =>
      have hclass:(3:ℕ)≤ i.val+1 ∧ i.val+1∈Allowed ∧ i∈factorShortCandidates F K ∧
          ∀j∈factorShortCandidates F K,i ≤ j:=
        (factor_preparation_class hn0 F hF Allowed hFAllowed K (by omega)).2 i hc
      have hlen:max 3 (i.val+1)=i.val+1:=max_eq_right hclass.1
      have hnN:N i≤n:=le_trans (Finset.single_le_sum (fun j _=>Nat.zero_le (N j)) (Finset.mem_univ i)) (by omega)
      have hbdd:BddAbove (cycleThreshold '' Allowed):=by
        refine ⟨1,?_⟩
        rintro x ⟨s,hs,rfl⟩
        exact cycleThreshold_le_one s
      have hthreshold:∀v,cycleThreshold (Fintype.card (F.connectedComponentMk v))≤θ:=by
        intro v
        exact le_csSup hbdd ⟨_,(AllowedCycleLengths_iff_component_orders F Allowed).1 hFAllowed _,rfl⟩
      have hfrac:β≤((Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=i.val+1)).card:ℝ)/n:=
        (Finset.mem_filter.mp hclass.2.2.1).2
      have habund:β*n≤((Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=max 3 (i.val+1))).card:ℝ):=by
        rw [hlen]
        exact (le_div_iff₀ (by exact_mod_cast hn0)).1 hfrac
      obtain ⟨I,hProb⟩:=hPrep i n hnN P F D hP hEven hdegree hF hthreshold habund
      exact ⟨I,ξ i,B i,(hξ i).le,hProb⟩
  · refine ⟨1,?_⟩
    intro n hn P F D hP hEven hdegree hF hFAllowed hshort
    have hn0:0<n:=by omega
    let v:Fin n:=⟨0,hn0⟩
    have hDn:D≤n:=by
      have hh:=Finset.card_le_univ (P.neighborFinset v)
      simpa only [SimpleGraph.card_neighborFinset_eq_degree,hP v,Fintype.card_fin] using hh
    have hnR:0<(n:ℝ):=by exact_mod_cast hn0
    have hdn:(D:ℝ)≤n:=by exact_mod_cast hDn
    have hθge:1≤θ:=le_of_not_gt hθ1
    have : (n:ℝ)<(θ+α/2)*n:=by nlinarith
    linarith
end Oberwolfach
