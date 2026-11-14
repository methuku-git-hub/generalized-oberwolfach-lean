module

public import Oberwolfach.IndexedMarkedRealizationRootPair
public import Oberwolfach.IndexedMarkedRealizationVertexMap

@[expose] public section

/-! An actual edge-preserving vertex map supplies a marked transformer
input. The image may identify vertices; its edge occurrences remain
injective, as required by the host realisation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V₁ U₁ V U E K A S:Type}
    [Fintype V₀] [Fintype U₀] [Fintype V₁] [Fintype U₁] [Fintype A] [Fintype S]
    [Fintype V] [Fintype U]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

theorem marked_mapped_realizations_root_pair
    (G:IndexedMarkedGraph V₀ U₀ A S) (G':IndexedMarkedGraph V₁ U₁ A S) (hG:G.IsBalanced m)
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (T:IndexedMarkedHostRealization G' tail head ktail khead H₀ HK π b)
    (f:V₀→V₁) (g:U₀→U₁) (he:G.map f g=G')
    (hRi:Function.Injective R.rows) (hHi:Function.Injective R.hubs)
    (B:Finset U) (hRB:R.hubSet⊆B) (hTB:T.hubSet⊆B)
    (hd:Disjoint R.rowSet T.rowSet) (hh:Disjoint R.hubSet T.hubSet)
    (hs:∀ v∈R.rowSet,∀ w∈T.rowSet,¬PermutationClose π b v w):
    ∃ P:MarkedRootPair tail head ktail khead H₀ HK π b m A S,
      P.source=R.resources∧P.image=T.resources∧P.R=R.rowSet∧P.R'=T.rowSet∧P.B=B:=by
  let T':=IndexedMarkedHostRealization.ofVertexMap G T f g he
  have hrow:∀ v,T'.rows v∈T.rowSet:=fun v=>T.row_mem (f v)
  have hhub:∀ u,T'.hubs u∈B:=fun u=>hTB (T.hub_mem (g u))
  have hdiff:∀ s,R.hubs (G.hub s)≠T'.hubs (G.hub s):=by
    intro s heq
    exact Finset.disjoint_left.mp hh (R.hub_mem (G.hub s)) (heq.symm ▸ T.hub_mem (g (G.hub s)))
  let P:=indexedMarkedRealizationRootPair G hG R T' hRi hHi R.rowSet T.rowSet B
    R.row_mem hrow (fun u=>hRB (R.hub_mem u)) hhub hd hs hdiff
  have hp:=indexedMarkedRealizationRootPair_endpoints G hG R T' hRi hHi R.rowSet T.rowSet B
    R.row_mem hrow (fun u=>hRB (R.hub_mem u)) hhub hd hs hdiff
  refine ⟨P,hp.1,?_,rfl,rfl,rfl⟩
  exact hp.2.trans (IndexedMarkedHostRealization.resources_ofVertexMap G T f g he)

end Oberwolfach
