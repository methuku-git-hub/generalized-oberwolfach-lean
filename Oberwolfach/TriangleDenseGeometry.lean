module

public import Oberwolfach.DenseCommonNeighbourBounds
public import Oberwolfach.TriangleTransformerAvailableHubSets

@[expose] public section
/-! Four fixed graph roots and two fixed hubs have many common neighbours
under the triangle transformer's minimum-degree and near-completeness inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_four_graph_neighbours {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (β:ℝ)
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(G.degree v:ℝ)) (a b c d:V):
    4*β*(Fintype.card V:ℝ)≤
      (((Finset.univ:Finset V).filter (fun x=>G.Adj a x∧G.Adj b x∧G.Adj c x∧G.Adj d x)).card:ℝ):=by
  let N:Fin 4→Finset V:=fun i=>G.neighborFinset (![a,b,c,d] i)
  have hd:∀ i∈(Finset.univ:Finset (Fin 4)),(3/4+β)*((Finset.univ:Finset V).card:ℝ)≤
      (((Finset.univ:Finset V)∩N i).card:ℝ):=by
    intro i _
    simpa [N,SimpleGraph.card_neighborFinset_eq_degree] using hdeg (![a,b,c,d] i)
  have h:=common_neighbour_card_lower (Finset.univ:Finset V) (Finset.univ:Finset (Fin 4)) N (3/4+β) hd
  have he:common (Finset.univ:Finset V) (Finset.univ:Finset (Fin 4)) N=
      (Finset.univ:Finset V).filter (fun x=>G.Adj a x∧G.Adj b x∧G.Adj c x∧G.Adj d x):=by
    ext x
    simp only [common,Finset.mem_filter,Finset.mem_univ,true_and,N,SimpleGraph.mem_neighborFinset]
    constructor
    · intro h
      exact ⟨h 0 (by simp),h 1 (by simp),h 2 (by simp),h 3 (by simp)⟩
    · rintro ⟨ha,hb,hc,hd⟩ i _
      fin_cases i <;> simp_all
  rw [he] at h
  simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] at h
  nlinarith

theorem triangle_four_neighbours_two_hubs {V U:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    (G:SimpleGraph V) (H:V→U→Prop) (β ε:ℝ) (hε:ε≤β)
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(G.degree v:ℝ))
    (hnear:∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))
    (u u':U) (a b c d:V):
    2*β*(Fintype.card V:ℝ)≤
      (((Finset.univ:Finset V).filter (fun x=>H x u∧H x u'∧G.Adj a x∧G.Adj b x∧G.Adj c x∧G.Adj d x)).card:ℝ):=by
  let C:Finset V:=(Finset.univ:Finset V).filter (fun x=>G.Adj a x∧G.Adj b x∧G.Adj c x∧G.Adj d x)
  let W:Finset V:=((Finset.univ:Finset V).filter (fun x=>¬H x u))∪((Finset.univ:Finset V).filter (fun x=>¬H x u'))
  have he:C\W=(Finset.univ:Finset V).filter (fun x=>H x u∧H x u'∧G.Adj a x∧G.Adj b x∧G.Adj c x∧G.Adj d x):=by
    ext x
    simp only [C,W,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    tauto
  have hw:(W.card:ℝ)≤2*ε*(Fintype.card V:ℝ):=by
    have hc:(W.card:ℝ)≤(((Finset.univ:Finset V).filter (fun x=>¬H x u)).card:ℝ)+
      (((Finset.univ:Finset V).filter (fun x=>¬H x u')).card:ℝ):=by exact_mod_cast Finset.card_union_le _ _
    have h1:=hnear u
    have h2:=hnear u'
    linarith
  have hC:4*β*(Fintype.card V:ℝ)≤(C.card:ℝ):=triangle_four_graph_neighbours G β hdeg a b c d
  have hsplit:(C.card:ℝ)≤((C\W).card:ℝ)+(W.card:ℝ):=by exact_mod_cast Finset.card_le_card_sdiff_add_card (s:=C) (t:=W)
  have hn:0≤(Fintype.card V:ℝ):=by positivity
  rw [←he]
  nlinarith
theorem triangle_common_hub_neighbours {V U:Type} [Fintype U] [DecidableEq U] [DecidableEq V]
    (H:V→U→Prop) (ε:ℝ) (hε:0≤ε)
    (hnear:∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))
    (T:Finset V) (hT:T.card≤9):
    (1-9*ε)*(Fintype.card U:ℝ)≤
      ((common (Finset.univ:Finset U) T (fun v=>(Finset.univ:Finset U).filter (fun u=>H v u))).card:ℝ):=by
  let N:V→Finset U:=fun v=>(Finset.univ:Finset U).filter (fun u=>H v u)
  have hd:∀ v∈T,(1-ε)*((Finset.univ:Finset U).card:ℝ)≤(((Finset.univ:Finset U)∩N v).card:ℝ):=by
    intro v _
    have hc:((N v).card:ℝ)+(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)=Fintype.card U:=by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s:=(Finset.univ:Finset U)) (fun u=>H v u)
    have hh:=hnear v
    simpa only [Finset.univ_inter,Finset.card_univ] using (show (1-ε)*(Fintype.card U:ℝ)≤(N v).card by linarith)
  have hh:=common_neighbour_card_lower (Finset.univ:Finset U) T N (1-ε) hd
  simp only [Finset.card_univ] at hh
  have ht:(T.card:ℝ)≤9:=by exact_mod_cast hT
  have hn:0≤(Fintype.card U:ℝ):=by positivity
  have hprod:(T.card:ℝ)*ε≤9*ε:=mul_le_mul_of_nonneg_right ht hε
  have hprod':(T.card:ℝ)*ε*(Fintype.card U:ℝ)≤9*ε*(Fintype.card U:ℝ):=
    mul_le_mul_of_nonneg_right hprod hn
  dsimp [N] at hh
  nlinarith

end Oberwolfach
