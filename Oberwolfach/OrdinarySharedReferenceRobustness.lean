module

public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion
public import Oberwolfach.OrdinaryNaturalPreparationCertificate

@[expose] public section
/-! A class perturbation deletes only a locally bounded number of reference
edges, and deletes no reference edge within the protected set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_shared_reference_robustness
    {n:ℕ} {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P S:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
    (hI:∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y)
    (hedit:∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y)
      ((longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))).card:ℝ)≤ξ*n):
    let R:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e));
    (∀x,((R\S).degree x:ℝ)≤ξ*n) ∧
    (∀x∈I,∀y∈I,R.Adj x y→S.Adj x y) :=by
  intro R
  have hsub:R≤longPhysicalStateGraph P σ {0,1,2,3,4}:=ordinary_shared_sample_reference_graph_le_class P σ
  constructor
  · intro x
    have hh:(R\S).neighborFinset x⊆Finset.univ.filter (fun y=>Xor (S.Adj x y)
        ((longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y)):=by
      intro y hy
      have hy':(R\S).Adj x y:=((R\S).mem_neighborFinset x y).mp hy
      have hz:=hsub hy'.1
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Xor]
      exact Or.inr ⟨hz,hy'.2⟩
    have hc:=Finset.card_le_card hh
    have hc':((R\S).degree x:ℝ)≤((Finset.univ.filter (fun y=>Xor (S.Adj x y)
        ((longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))).card:ℝ):=by exact_mod_cast hc
    exact hc'.trans (hedit x)
  · intro x hx y hy hxy
    exact (hI x hx y hy).2 (hsub hxy)
end Oberwolfach
