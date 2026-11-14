module

public import Oberwolfach.OrdinaryInnerPhysicalComap
public import Oberwolfach.OrdinaryProtectedTraceWindowInnerEdit

@[expose] public section
/-! The same trace gives rim and spoke row/column edit bounds on the actual
induced host of the next level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_trace_induced_window_physical_edit
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (Jwin:Finset ℕ) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hJ:∀j∈Jwin,j < i+1)
    (hX:∀j < i+1,j∉Jwin→X i⊆T j) (hZ:∀j < i+1,j∉Jwin→Z i⊆W j)
    (hXnest:∀j∈Jwin,X i⊆X j) (hZnest:∀j∈Jwin,Z i⊆Z j):
    let V₁:=↥(X i);let U₁:=↥(Z i);
    let Q₁:=Q.induce ((X i):Set V);let G₁:=G.induce ((X i):Set V);
    let H₁:=fun (v:V₁) (u:U₁)=>H v.val u.val;
    let Hs₁:=fun (v:V₁) (u:U₁)=>Hs v.val u.val;
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤∑j∈Jwin,cost j:=by
  intro V₁ U₁ Q₁ G₁ H₁ Hs₁ a
  let K:=spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices (X i) (Z i))
  let K':=spanningRestriction (ordinaryPhysicalGraph G Hs) (ordinaryInnerVertices (X i) (Z i))
  let e:=ordinaryInnerEmbedding (X i) (Z i)
  have hn:(ordinaryPhysicalGraph Q₁ H₁).neighborFinset a=(K.comap e).neighborFinset a:=by
    ext b
    simp only [SimpleGraph.mem_neighborFinset]
    change (ordinaryPhysicalGraph (Q.induce ((X i):Set V)) (fun (v:V₁) (u:U₁)=>H v.val u.val)).Adj a b ↔
      ((spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices (X i) (Z i))).comap e).Adj a b
    rw [ordinary_induced_physical_comap,ordinary_inner_comap_spanning]
  have hn':(ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a=(K'.comap e).neighborFinset a:=by
    ext b
    simp only [SimpleGraph.mem_neighborFinset]
    change (ordinaryPhysicalGraph (G.induce ((X i):Set V)) (fun (v:V₁) (u:U₁)=>Hs v.val u.val)).Adj a b ↔
      ((spanningRestriction (ordinaryPhysicalGraph G Hs) (ordinaryInnerVertices (X i) (Z i))).comap e).Adj a b
    rw [ordinary_induced_physical_comap,ordinary_inner_comap_spanning]
  have hc:=graph_changed_comap_le K K' e a
  have hc':((changed ((K.comap e).neighborFinset a) ((K'.comap e).neighborFinset a)).card:ℝ)≤
      ((changed (K.neighborFinset (e a)) (K'.neighborFinset (e a))).card:ℝ):=by exact_mod_cast hc
  have ht:=ordinary_protected_trace_window_inner_edit Q H X T Z W cost deepCost i Jwin A G Hs htrace hstate hJ hX hZ hXnest hZnest (e a)
  have ht':((changed (K.neighborFinset (e a)) (K'.neighborFinset (e a))).card:ℝ)≤∑j∈Jwin,cost j:=by
    convert ht using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  rw [hn,hn']
  convert hc'.trans ht' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _

end Oberwolfach
