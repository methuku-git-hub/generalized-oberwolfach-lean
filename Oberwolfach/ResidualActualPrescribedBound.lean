module

public import Oberwolfach.ResidualActualPrescribedSet

@[expose] public section
/-! The prescribed vertices have the bound used in the residual embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem residual_actual_prescribed_set_bound (F Q:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) (hQ:Q≤F)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:3≤c) (hd:0<d) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d) (C:Finset V)
    (hC:∀i∈s₁∪s₂,Disjoint (P i).support.toFinset C):
    let R:=Finset.univ \ (C ∪ (s₁∪s₂).biUnion (pathFamilyLocalDeletion F s₁ u v P c d T hT))
    let A₀ := (s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})) ∪
      (R ∩ s₂.biUnion (fun i=>(Finset.range (d+1)).image (fun j=>(P i).getVert (2+c*j))))
    let missing:=∑i∈s₂,(d-(T i).card);
    A₀.card≤2*(s₁.card+s₂.card)+2*missing := by
  have hA:=residual_actual_prescribed_set F Q hF hQ s₁ s₂ hs u v P hp hP c d hc hd hlen T hT C hC
  have hr:=(maximal_run_family_counts s₂ d hd T (by intro i hi;exact hT i)).2.1
  dsimp only at hA hr ⊢
  omega
end Oberwolfach
