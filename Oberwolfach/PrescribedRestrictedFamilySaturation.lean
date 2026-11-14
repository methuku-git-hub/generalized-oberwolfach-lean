module

public import Oberwolfach.PrescribedRestrictedSaturationBudget

@[expose] public section
/-! The restricted free occurrences have total size at most the number of
selected hubs times the maximum size of a residual source. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem prescribed_restricted_family_saturation
    {I X V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]
    (H:Finset I) (QV:I→Finset X) (T:Finset (I×X)) (φ:I×X→V)
    (a n κ θ b:ℝ) (ha:0<a) (hκ:0<κ) (hn:0≤n) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤a) (hθbudget:θ≤κ*b)
    (hQ:∀i∈H,((QV i).card:ℝ)≤θ*n)
    (hT:∀p∈T,p.1∈H ∧ p.2∈QV p.1):
    ((Finset.univ.filter (fun v=>κ*a≤((T.filter (fun p=>φ p=v)).card:ℝ))).card:ℝ)≤b*n :=by
  let W:Finset (I×X):=H.biUnion (fun i=>({i}:Finset I).product (QV i))
  have hsub:T⊆W:=by
    intro p hp
    have hh:=hT p hp
    exact Finset.mem_biUnion.mpr ⟨p.1,hh.1,Finset.mem_product.mpr ⟨by simp,hh.2⟩⟩
  have hcard:T.card≤∑i∈H,(QV i).card:=by
    calc
      T.card≤W.card:=Finset.card_le_card hsub
      _≤∑i∈H,(({i}:Finset I).product (QV i)).card:=Finset.card_biUnion_le
      _=∑i∈H,(QV i).card:=by simp [Finset.card_product]
  have hsum:((∑i∈H,(QV i).card:ℕ):ℝ)≤(H.card:ℝ)*(θ*n):=by
    push_cast
    calc
      _ ≤ ∑i∈H,θ*n:=Finset.sum_le_sum (fun i hi=>hQ i hi)
      _ = _ :=by simp
  have htotal:(T.card:ℝ)≤θ*n*(H.card:ℝ):=by
    have hh:((T.card:ℝ)≤((∑i∈H,(QV i).card:ℕ):ℝ)):=by exact_mod_cast hcard
    nlinarith only [hh,hsum]
  exact prescribed_restricted_saturation_budget T φ a H.card n κ θ b ha hκ hn hθ (by positivity) hH hθbudget htotal
end Oberwolfach
