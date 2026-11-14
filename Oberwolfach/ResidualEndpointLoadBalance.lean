module

public import Oberwolfach.ResidualDirectedDegreeBalance

@[expose] public section
/-! Equal loads of path starts and finishes give equal missing-arc loads. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_missing_load_balance
    {V U:Type*} [DecidableEq V] [Fintype U]
    (Z B T:U→Finset V)
    (hZB:∀w,Disjoint (Z w) (B w))
    (hZT:∀w,Disjoint (Z w) (T w))
    (hBT:∀v,(Finset.univ.filter (fun w=>v∈B w)).card=
      (Finset.univ.filter (fun w=>v∈T w)).card):
    ∀v,(Finset.univ.filter (fun w=>v∉Z w∪T w)).card=
      (Finset.univ.filter (fun w=>v∉Z w∪B w)).card:=by
  classical
  intro v
  let A:Finset U:=Finset.univ.filter (fun w=>v∈Z w)
  let C:Finset U:=Finset.univ.filter (fun w=>v∈B w)
  let E:Finset U:=Finset.univ.filter (fun w=>v∈T w)
  have hAC:Disjoint A C:=by
    apply Finset.disjoint_left.mpr
    intro w hwA hwC
    exact Finset.disjoint_left.mp (hZB w) (Finset.mem_filter.mp hwA).2 (Finset.mem_filter.mp hwC).2
  have hAE:Disjoint A E:=by
    apply Finset.disjoint_left.mpr
    intro w hwA hwE
    exact Finset.disjoint_left.mp (hZT w) (Finset.mem_filter.mp hwA).2 (Finset.mem_filter.mp hwE).2
  have hC:C.card=E.card:=hBT v
  have hB:(Finset.univ.filter (fun w=>v∈Z w∪B w))=A∪C:=by
    ext w
    simp [A,C,Finset.mem_union]
  have hT:(Finset.univ.filter (fun w=>v∈Z w∪T w))=A∪E:=by
    ext w
    simp [A,E,Finset.mem_union]
  have hactive:(Finset.univ.filter (fun w=>v∈Z w∪B w)).card=
      (Finset.univ.filter (fun w=>v∈Z w∪T w)).card:=by
    rw [hB,hT,Finset.card_union_of_disjoint hAC,Finset.card_union_of_disjoint hAE,hC]
  have hb:=Finset.card_filter_add_card_filter_not (s:=(Finset.univ:Finset U)) (fun w=>v∈Z w∪B w)
  have ht:=Finset.card_filter_add_card_filter_not (s:=(Finset.univ:Finset U)) (fun w=>v∈Z w∪T w)
  omega
end Oberwolfach
