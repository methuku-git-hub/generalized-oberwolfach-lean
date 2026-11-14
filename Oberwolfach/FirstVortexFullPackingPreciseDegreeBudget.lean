module

public import Oberwolfach.FirstVortexPreciseRequiredDegreeBudget
public import Oberwolfach.LongFullPackingDynamicBadRetarget

@[expose] public section
/-! Use the actual sampled and correction degrees for the full matching
packing. The auxiliary capacity parameter need not be the host margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_full_packing_precise_degree_budget
    (ε θ lam ξ a δglobal:ℝ) (d:ℕ) (hε:0≤ε) (hθ:0<θ) (ha:0<a) (ha1:a≤1)
    (hεsmall:ε≤a/8192) (hsmall:lam+ξ≤a*θ/4096) (hglobal:10*θ≤δglobal):
    ∃N:ℕ,∀n:ℕ,N≤n→∀{U:Type} [Fintype U] {P S₀ S Used Sel:SimpleGraph (Fin n)}
      {Dv m:ℕ} {β:ℝ} (Q:Vortex U P Dv β ε m) (π:Equiv.Perm (Fin n)) (D:Fin n→Fin n→Prop),
      S≤P→
      (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
      (∀v,((longRequiredPhysicalGraph P (S₀\Used) Sel π d (Q.extendedVertices 1) D
        (fun x y=>Used.Adj x y)).degree v:ℝ)≤2*θ*(Q.extendedVertices 1).card+
          (n:ℝ)^(3/4:ℝ)+lam*n+(6*d+2:ℕ))→
      ∀Pack:Finset (Sym2 (Fin n)),Pack=Used.edgeFinset→
      let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y)
      let Kplus:=longClassInnerRequiredRepair S Used Kbase (Q.extendedVertices 1) Pack;
      (∀v,(Kplus.degree v:ℝ)≤((a*θ/64)/16)*n) ∧
      (∀v,(Kplus.degree v:ℝ)≤δglobal*n/4) :=by
  obtain ⟨N,hN⟩:=first_vortex_precise_required_degree_budget ε θ lam ξ a d hε hθ ha hεsmall hsmall
  refine ⟨N,?_⟩
  intro n hn U _ P S₀ S Used Sel Dv m β Q π D hSP hedit hbase Pack hPack Kbase Kplus
  have hp:=class_required_precise_degree_from_edits P S₀ S Used Sel π d (Q.extendedVertices 1) D θ lam ξ ((n:ℝ)^(3/4:ℝ)) hSP hedit hbase
  have hk:=hN n hn Q hp
  have heq:Kplus=Kbase:=matching_exact_class_packing_repair_vanishes S Used Kbase (Q.extendedVertices 1) Pack hPack
  have hθa:a*θ≤θ:=by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hθ.le]
  have hscale:a*θ/1024≤δglobal/4:=by linarith
  constructor
  · intro v
    rw [heq]
    have hh:=hk v
    dsimp only [Kbase] at *
    convert hh using 1 <;> ring
  · intro v
    rw [heq]
    have hh:=hk v
    dsimp only [Kbase] at *
    have hm:=mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg n)
    nlinarith only [hh,hm]
end Oberwolfach
