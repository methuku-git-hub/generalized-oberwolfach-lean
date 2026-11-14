module

public import Oberwolfach.OrdinaryProtectedTraceInducedEdits
public import Oberwolfach.OrdinaryInducedPhysicalEditOfGlobal
public import Oberwolfach.HubToRowDeletion

@[expose] public section
/-! Initial sample edits and the latest level edit add on each induced pair;
earlier protected levels incur no further cost there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_trace_induced_edits_from_reference
    (R Q:SimpleGraph V) (J H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (L:ℝ) (hbase:∀w:V⊕U,((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤L)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hX:∀j < i,X i⊆T j) (hZ:∀j < i,Z i⊆W j):
    let V₁:=↥(X i);let U₁:=↥(Z i);
    let R₁:=R.induce ((X i):Set V);let G₁:=G.induce ((X i):Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let Hs₁:=fun (v:V₁) (u:U₁)=>Hs v.val u.val;
    (∀v:V₁,((changed (R₁.neighborFinset v) (G₁.neighborFinset v)).card:ℝ)≤L+cost i) ∧
    (∀v:V₁,((changed (Finset.univ.filter (J₁ v)) (Finset.univ.filter (Hs₁ v))).card:ℝ)≤L+cost i) ∧
    (∀u:U₁,((changed (Finset.univ.filter (fun v=>J₁ v u)) (Finset.univ.filter (fun v=>Hs₁ v u))).card:ℝ)≤L+cost i):=by
  intro V₁ U₁ R₁ G₁ J₁ Hs₁
  let Q₁:=Q.induce ((X i):Set V)
  let H₁:=fun (v:V₁) (u:U₁)=>H v.val u.val
  have hf:=ordinary_induced_physical_edit_of_global R Q J H (X i) (Z i) L hbase
  have hs:=ordinary_protected_trace_induced_physical_edit Q H X T Z W cost deepCost i A G Hs htrace hstate hX hZ
  have hedit:∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤L+cost i:=by
    intro a
    have ht:((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
        ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤
      ((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a) ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a)).card:ℝ)+
      ((changed ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ):=by
      exact_mod_cast changed_card_triangle ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
        ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)
    have hf':((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a) ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a)).card:ℝ)≤L:=by
      convert hf a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hs':((changed ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤cost i:=by
      convert hs a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    linarith only [ht,hf',hs']
  have hh:=ordinary_physical_edit_to_typed_changes R₁ G₁ J₁ Hs₁ (L+cost i) hedit
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
