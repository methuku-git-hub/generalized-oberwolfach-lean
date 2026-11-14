module

public import Oberwolfach.OrdinaryBoundaryReserveGeometry
public import Oberwolfach.OrdinaryOuterHostBalanceRefined
public import Oberwolfach.OrdinaryReserveImbalanceBound

@[expose] public section
/-! A retained boundary reserve preserves near balance when the original
inner and boundary profiles are near balanced and the reserve has the
corresponding degree deviations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_reserved_near_balance
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (τ b c e:ℝ) (hτ:0≤τ)
    (hQbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hInner:∀v,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)
    (hBoundary:let B:=ordinaryBoundaryGraph Q H I J;
      ∀v,|((B.comap Sum.inl).degree v:ℝ)-2*(Finset.univ.filter (fun u=>B.Adj (Sum.inl v) (Sum.inr u))).card|≤c)
    (hRetained:let B:=ordinaryBoundaryGraph Q H I J;let R:=retainedGraph B σ;
      ∀v,|(((R.comap Sum.inl).degree v:ℝ)-2*(Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card)-
        τ*((B.comap Sum.inl).degree v-2*(Finset.univ.filter (fun u=>B.Adj (Sum.inl v) (Sum.inr u))).card)|≤e):
    let R:=retainedGraph (ordinaryBoundaryGraph Q H I J) σ;
    ∀v,|((((Q\spanningRestriction Q I)\(R.comap Sum.inl)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u=>(H v u∧¬(v∈I∧u∈J))∧¬R.Adj (Sum.inl v) (Sum.inr u))).card|
        ≤b+τ*c+e:=by
  intro R v
  let B:=ordinaryBoundaryGraph Q H I J
  let Q₀:=Q\spanningRestriction Q I
  let H₀:=fun v u=>H v u∧¬(v∈I∧u∈J)
  have hfull:∀x,|(Q.degree x:ℝ)-2*(Finset.univ.filter (H x)).card|≤0:=by
    intro x
    have hh:(Q.degree x:ℝ)=2*(Finset.univ.filter (H x)).card:=by exact_mod_cast hQbal x
    rw [hh,sub_self,abs_zero]
  have houter0:=ordinary_outer_host_balance_refined Q H I J 0 b hfull hInner
  have houter:∀x,|(Q₀.degree x:ℝ)-2*(Finset.univ.filter (H₀ x)).card|≤b:=by
    intro x
    have hh:=houter0 x
    convert hh using 1 <;> simp <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hgeo:=ordinary_boundary_reserve_geometry Q H I J σ
  have hD:(R.comap Sum.inl)≤Q₀:=hgeo.1
  have hK:∀x u,R.Adj (Sum.inl x) (Sum.inr u)→H₀ x u:=hgeo.2
  have hReserve:∀x,|((R.comap Sum.inl).degree x:ℝ)-2*(Finset.univ.filter (fun u=>R.Adj (Sum.inl x) (Sum.inr u))).card|≤τ*c+e:=by
    intro x
    let A:ℝ:=((R.comap Sum.inl).degree x:ℝ)-2*(Finset.univ.filter (fun u=>R.Adj (Sum.inl x) (Sum.inr u))).card
    let D:ℝ:=((B.comap Sum.inl).degree x:ℝ)-2*(Finset.univ.filter (fun u=>B.Adj (Sum.inl x) (Sum.inr u))).card
    have hd:|D|≤c:=hBoundary x
    have he:|A-τ*D|≤e:=hRetained x
    exact ordinary_reserve_imbalance_bound A D τ c e hτ hd he
  have hout:=ordinary_deleted_host_balance_refined Q₀ (R.comap Sum.inl) H₀
    (fun x u=>R.Adj (Sum.inl x) (Sum.inr u)) b (τ*c+e) hD hK
    (by intro x;convert houter x using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro x;convert hReserve x using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) v
  have heq:b+(τ*c+e)=b+τ*c+e:=by ring
  rw [heq] at hout
  convert hout using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
