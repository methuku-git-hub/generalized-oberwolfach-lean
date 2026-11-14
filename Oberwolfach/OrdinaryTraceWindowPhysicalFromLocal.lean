module

public import Oberwolfach.OrdinaryProtectedTraceInducedWindowEdit
public import Oberwolfach.OrdinaryInducedPhysicalEditOfGlobal
public import Oberwolfach.HubToRowDeletion

@[expose] public section
/-! Local initial sample edits and the latest level edit add on each induced pair;
earlier protected levels incur no further cost there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_trace_induced_window_physical_from_local_reference
    (R Q:SimpleGraph V) (J H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (Jwin:Finset ℕ) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (L:ℝ) (hbase:∀a:↥(X i)⊕↥(Z i),
      ((changed ((ordinaryPhysicalGraph (R.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>J v.val u.val)).neighborFinset a)
        ((ordinaryPhysicalGraph (Q.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>H v.val u.val)).neighborFinset a)).card:ℝ)≤L)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hJ:∀j∈Jwin,j < i+1)
    (hX:∀j < i+1,j∉Jwin→X i⊆T j) (hZ:∀j < i+1,j∉Jwin→Z i⊆W j)
    (hXnest:∀j∈Jwin,X i⊆X j) (hZnest:∀j∈Jwin,Z i⊆Z j):
    let V₁:=↥(X i);let U₁:=↥(Z i);
    let R₁:=R.induce ((X i):Set V);let G₁:=G.induce ((X i):Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let Hs₁:=fun (v:V₁) (u:U₁)=>Hs v.val u.val;
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤L+∑j∈Jwin,cost j:=by
  intro V₁ U₁ R₁ G₁ J₁ Hs₁
  let Q₁:=Q.induce ((X i):Set V)
  let H₁:=fun (v:V₁) (u:U₁)=>H v.val u.val
  have hf:=hbase
  have hs:=ordinary_protected_trace_induced_window_physical_edit Q H X T Z W cost deepCost i Jwin A G Hs htrace hstate hJ hX hZ hXnest hZnest
  have hedit:∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤L+∑j∈Jwin,cost j:=by
    intro a
    have ht:((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
        ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤
      ((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a) ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a)).card:ℝ)+
      ((changed ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ):=by
      exact_mod_cast changed_card_triangle ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
        ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)
    have hf':((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a) ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a)).card:ℝ)≤L:=by
      convert hf a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hs':((changed ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤∑j∈Jwin,cost j:=by
      convert hs a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    linarith only [ht,hf',hs']
  exact hedit
end Oberwolfach
