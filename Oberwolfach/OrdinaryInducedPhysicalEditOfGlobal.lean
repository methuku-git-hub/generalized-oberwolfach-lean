module

public import Oberwolfach.OrdinaryInnerPhysicalComap

@[expose] public section
/-! Global physical edits restrict to induced vertex and hub types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_physical_edit_of_global
    (Q R:SimpleGraph V) (H J:V→U→Prop) (X:Finset V) (Z:Finset U) (L:ℝ)
    (hedit:∀w:V⊕U,((changed ((ordinaryPhysicalGraph Q H).neighborFinset w)
      ((ordinaryPhysicalGraph R J).neighborFinset w)).card:ℝ)≤L):
    let V₁:=↥X;let U₁:=↥Z;
    let Q₁:=Q.induce (X:Set V);let R₁:=R.induce (X:Set V);
    let H₁:=fun (v:V₁) (u:U₁)=>H v.val u.val;
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a)
      ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)).card:ℝ)≤L:=by
  intro V₁ U₁ Q₁ R₁ H₁ J₁ a
  let e:=ordinaryInnerEmbedding X Z
  have hn:(ordinaryPhysicalGraph Q₁ H₁).neighborFinset a=((ordinaryPhysicalGraph Q H).comap e).neighborFinset a:=by
    ext b
    simp only [SimpleGraph.mem_neighborFinset]
    exact Iff.of_eq (congrArg (fun G:SimpleGraph (V₁⊕U₁)=>G.Adj a b) (ordinary_induced_physical_comap Q H X Z))
  have hn':(ordinaryPhysicalGraph R₁ J₁).neighborFinset a=((ordinaryPhysicalGraph R J).comap e).neighborFinset a:=by
    ext b
    simp only [SimpleGraph.mem_neighborFinset]
    exact Iff.of_eq (congrArg (fun G:SimpleGraph (V₁⊕U₁)=>G.Adj a b) (ordinary_induced_physical_comap R J X Z))
  have hc:=graph_changed_comap_le (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph R J) e a
  have hc':((changed (((ordinaryPhysicalGraph Q H).comap e).neighborFinset a)
      (((ordinaryPhysicalGraph R J).comap e).neighborFinset a)).card:ℝ)≤
      ((changed ((ordinaryPhysicalGraph Q H).neighborFinset (e a)) ((ordinaryPhysicalGraph R J).neighborFinset (e a))).card:ℝ):=by exact_mod_cast hc
  rw [hn,hn']
  convert hc'.trans (hedit (e a)) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
