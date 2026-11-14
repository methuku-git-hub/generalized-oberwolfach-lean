module

public import Oberwolfach.FirstVortexFullPackingPreciseDegreeBudget

@[expose] public section
/-! Discharge both required-degree inputs for all-hub completion using the
same full matching packing and the actual class correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_all_hub_capacity_degree_inputs
    (ε θ lam ξ a δglobal:ℝ) (d:ℕ) (hε:0≤ε) (hθ:0<θ) (ha:0<a) (ha1:a≤1)
    (hεsmall:ε≤a/8192) (hsmall:lam+ξ≤a*θ/4096) (hglobal:10*θ≤δglobal):
    ∃N:ℕ,∀n:ℕ,N≤n→∀{U:Type} [Fintype U] [DecidableEq U]
      {P S₀ S Used Sel:SimpleGraph (Fin n)} {Dv m:ℕ} {β:ℝ}
      (Q:Vortex U P Dv β ε m) (π:Equiv.Perm (Fin n)) (D:Fin n→Fin n→Prop),
      S≤P→
      (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
      (∀v,((longRequiredPhysicalGraph P (S₀\Used) Sel π d (Q.extendedVertices 1) D
        (fun x y=>Used.Adj x y)).degree v:ℝ)≤2*θ*(Q.extendedVertices 1).card+
          (n:ℝ)^(3/4:ℝ)+lam*n+(6*d+2:ℕ))→
      ∀Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop,
      (∀Old Pack,Extra Old Pack→Pack=Used.edgeFinset)→
      let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y)
      let Kplus:=fun Pack=>longClassInnerRequiredRepair S Used Kbase (Q.extendedVertices 1) Pack;
      (∀Old Pack,Extra Old Pack→∀v,((Kplus Pack).degree v:ℝ)≤((a*θ/64)/16)*n) ∧
      (∀Old Pack,Extra Old Pack→∀v,((Kplus Pack).degree v:ℝ)≤δglobal*n/4) :=by
  obtain ⟨N,hN⟩:=first_vortex_full_packing_precise_degree_budget ε θ lam ξ a δglobal d hε hθ ha ha1 hεsmall hsmall hglobal
  refine ⟨N,?_⟩
  intro n hn U _ _ P S₀ S Used Sel Dv m β Q π D hSP hedit hbase Extra hPack Kbase Kplus
  constructor
  · intro Old Pack hExtra v
    exact (hN n hn Q π D hSP hedit hbase Pack (hPack Old Pack hExtra)).1 v
  · intro Old Pack hExtra v
    exact (hN n hn Q π D hSP hedit hbase Pack (hPack Old Pack hExtra)).2 v
end Oberwolfach
