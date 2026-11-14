module

public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! Vertex counts used by the preparation propositions equal sums of the
sizes of the corresponding connected components. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem component_abundance_vertex_count {V:Type} [Fintype V] [DecidableEq V]
    (F:SimpleGraph V) (P:ℕ→Prop):
    letI : Fintype F.ConnectedComponent:=Fintype.ofFinite _
    ((Finset.univ.filter (fun v=>P (Fintype.card (F.connectedComponentMk v)))).card:ℕ)=
      ∑C ∈ (Finset.univ.filter (fun C:F.ConnectedComponent=>P (Fintype.card C))),Fintype.card C :=by
  classical
  letI : Fintype F.ConnectedComponent:=Fintype.ofFinite _
  let S:Finset V:=Finset.univ.filter (fun v=>P (Fintype.card (F.connectedComponentMk v)))
  let T:Finset F.ConnectedComponent:=Finset.univ.filter (fun C=>P (Fintype.card C))
  have hMaps:(S:Set V).MapsTo F.connectedComponentMk T:=by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩
  have hsum:=Finset.card_eq_sum_card_fiberwise hMaps
  have hfiber:∀C∈T,(S.filter (fun v=>F.connectedComponentMk v=C)).card=Fintype.card C:=by
    intro C hC
    have hc:P (Fintype.card C):=(Finset.mem_filter.mp hC).2
    have heq:S.filter (fun v=>F.connectedComponentMk v=C)=C.supp.toFinset:=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_toFinset,SimpleGraph.ConnectedComponent.mem_supp_iff,S]
      constructor
      · exact And.right
      · intro hv
        refine ⟨?_,hv⟩
        simpa only [hv] using hc
    rw [heq]
    calc
      C.supp.toFinset.card = Fintype.card C.supp := Set.toFinset_card C.supp
      _ = Fintype.card C := Fintype.card_congr (Equiv.refl _)
  change S.card=∑C∈T,Fintype.card C
  rw [hsum]
  exact Finset.sum_congr rfl hfiber

end Oberwolfach
