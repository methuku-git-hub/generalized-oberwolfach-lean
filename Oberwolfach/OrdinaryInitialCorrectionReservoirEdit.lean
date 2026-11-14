module

public import Oberwolfach.OrdinaryResourceRemovalEdit
public import Oberwolfach.OrdinaryPhysicalConflictDegree
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! The initial conflict deletion, sparse balance correction and selected
reservoir have an explicit total physical-edit bound on the same host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_initial_correction_reservoir_physical_edit
    (R F JQ:SimpleGraph V) (J JH:V→U→Prop) (K:Finset (Sym2 V⊕(V×U))) (Lconf Lcorr:ℝ)
    (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
    (hrow:∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤Lcorr)
    (hcol:∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤Lcorr)
    (hK:K⊆ordinaryHostResources ((R\F)\JQ) (fun v u=>J v u∧¬JH v u)):
    let Q:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let G:=Q\ordinaryResourceRim Q K;let Hs:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    ∀w:V⊕U,((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph G Hs).neighborFinset w)).card:ℝ)≤
      Lconf+Lcorr+(ordinaryResourceRows K).card+(ordinaryResourceHubs K).card:=by
  intro Q H G Hs
  let C:SimpleGraph (V⊕U):=ordinaryPhysicalGraph F (fun (_:V) (_:U)=>False)
  let D:=ordinaryPhysicalGraph JQ JH
  have hC:∀w:V⊕U,(C.degree w:ℝ)≤Lconf:=ordinary_physical_conflict_degree F Lconf hLconf hF
  have hD:∀w:V⊕U,(D.degree w:ℝ)≤Lcorr:=by
    intro w
    cases w with
    | inl v=>
      have hh:=ordinary_physical_degree_row JQ JH v
      rw [hh,Nat.cast_add]
      exact hrow v
    | inr u=>
      have hh:=ordinary_physical_degree_column JQ JH u
      rw [hh]
      exact hcol u
  have he1:ordinaryPhysicalGraph (R\F) J=ordinaryPhysicalGraph R J\C:=by
    ext x y
    cases x <;> cases y <;> simp [ordinaryPhysicalGraph,C]
  have he2:ordinaryPhysicalGraph Q H=ordinaryPhysicalGraph (R\F) J\D:=by
    convert ordinary_physical_graph_after_deletion (R\F) J D using 1 <;> rfl
  have hbase:∀w:V⊕U,((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤Lconf+Lcorr:=by
    intro w
    have h1:((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
        ((ordinaryPhysicalGraph (R\F) J).neighborFinset w)).card:ℝ)≤Lconf:=by
      rw [he1]
      have hh:=graph_changed_neighbors_after_deletion (ordinaryPhysicalGraph R J) C w
      have hh':((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
          ((ordinaryPhysicalGraph R J\C).neighborFinset w)).card:ℝ)≤C.degree w:=by exact_mod_cast hh
      convert hh'.trans (hC w) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have h2:((changed ((ordinaryPhysicalGraph (R\F) J).neighborFinset w)
        ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤Lcorr:=by
      rw [he2]
      have hh:=graph_changed_neighbors_after_deletion (ordinaryPhysicalGraph (R\F) J) D w
      have hh':((changed ((ordinaryPhysicalGraph (R\F) J).neighborFinset w)
          ((ordinaryPhysicalGraph (R\F) J\D).neighborFinset w)).card:ℝ)≤D.degree w:=by exact_mod_cast hh
      convert hh'.trans (hD w) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have ht:((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
        ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤
        ((changed ((ordinaryPhysicalGraph R J).neighborFinset w) ((ordinaryPhysicalGraph (R\F) J).neighborFinset w)).card:ℝ)+
        ((changed ((ordinaryPhysicalGraph (R\F) J).neighborFinset w) ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ):=by
      exact_mod_cast changed_card_triangle ((ordinaryPhysicalGraph R J).neighborFinset w)
        ((ordinaryPhysicalGraph (R\F) J).neighborFinset w) ((ordinaryPhysicalGraph Q H).neighborFinset w)
    linarith only [ht,h1,h2]
  exact ordinary_resource_removal_from_reference R Q J H K hK (Lconf+Lcorr) hbase
end Oberwolfach
