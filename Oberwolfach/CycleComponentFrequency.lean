module

public import Oberwolfach.UniformFiberCounts
public import Oberwolfach.LongPreparationFactorFractions

@[expose] public section
/-! Convert a vertex frequency into the actual number of components of
the specified size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem component_size_vertex_count {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ):
    let T:=Finset.univ.filter (fun C:G.ConnectedComponent=>Fintype.card C=r)
    (Finset.univ.filter (fun v:V=>Fintype.card (G.connectedComponentMk v)=r)).card=r*T.card :=by
  intro T
  have hs:∀C∈T,(Finset.univ.filter (fun v:V=>G.connectedComponentMk v=C)).card=r:=by
    intro C hC
    have hCsize:Fintype.card C=r:=(Finset.mem_filter.mp hC).2
    have hset:Finset.univ.filter (fun v:V=>G.connectedComponentMk v=C)=C.supp.toFinset:=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_toFinset,
        SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [hset]
    rw [Set.toFinset_card]
    have heq:Fintype.card C.supp=Fintype.card C:=Fintype.card_congr (Equiv.refl _)
    exact heq.trans hCsize
  have h:=card_of_uniform_fibers G.connectedComponentMk T r hs
  apply Eq.trans ?_ h
  congr 1
  ext v
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,T]
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem component_fraction_times_order_div_size {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) (hr:0<r) (hV:0<Fintype.card V):
    let T:=Finset.univ.filter (fun C:G.ConnectedComponent=>Fintype.card C=r)
    (((Finset.univ.filter (fun v:V=>Fintype.card (G.connectedComponentMk v)=r)).card:ℝ)/
      (Fintype.card V:ℝ))*(Fintype.card V:ℝ)/(r:ℝ)=(T.card:ℝ) :=by
  intro T
  have hn:(Fintype.card V:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hV)
  have hrr:(r:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hr)
  have hc:=component_size_vertex_count G r
  dsimp only at hc
  rw [hc]
  push_cast
  field_simp
  rfl
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_fraction_component_count {n K:ℕ} (hn:0<n)
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (i:Fin K):
    let fraction:=((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i)).card:ℝ)/n
    let T:=Finset.univ.filter (fun C:F.ConnectedComponent=>Fintype.card C=i.val+1)
    fraction*n/((i.val+1:ℕ):ℝ)=(T.card:ℝ) :=by
  intro fraction T
  have hset:Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i)=
      Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=i.val+1):=by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (long_preparation_cycle_class F hF K v).2 i
  dsimp only [fraction]
  rw [hset]
  simpa only [Fintype.card_fin] using
    component_fraction_times_order_div_size F (i.val+1) (by omega) (by simpa only [Fintype.card_fin] using hn)
end Oberwolfach
