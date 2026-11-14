module

public import Oberwolfach.OrdinaryResourceRemovalEdit
public import Oberwolfach.OrdinaryInducedPhysicalEditOfGlobal

@[expose] public section
/-! Reserving a bounded set of resource rows and hubs adds only that absolute
cost to any already-local initial edit bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_resource_removal_from_local_reference
    (R Q:SimpleGraph V) (J H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (hK:K⊆ordinaryHostResources Q H) (X:Finset V) (Z:Finset U) (L:ℝ):
    let V₁:=↥X;let U₁:=↥Z;
    let R₁:=R.induce (X:Set V);let Q₁:=Q.induce (X:Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let H₁:=fun (v:V₁) (u:U₁)=>H v.val u.val;
    (∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a)).card:ℝ)≤L)→
    let G:=Q\ordinaryResourceRim Q K;
    let Hs:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let G₁:=G.induce (X:Set V);
    let Hs₁:=fun (v:V₁) (u:U₁)=>Hs v.val u.val;
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤
        L+((ordinaryResourceRows K).card:ℝ)+(ordinaryResourceHubs K).card:=by
  intro V₁ U₁ R₁ Q₁ J₁ H₁ hbase G Hs G₁ Hs₁ a
  have hr:=ordinary_resource_removal_physical_edit Q H K hK
  have hi:=ordinary_induced_physical_edit_of_global Q G H Hs X Z
    ((ordinaryResourceRows K).card+(ordinaryResourceHubs K).card) hr
  have ht:((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤
      ((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a) ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a)).card:ℝ)+
      ((changed ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ):=by
    exact_mod_cast changed_card_triangle ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)
  have hr':((changed ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤
      ((ordinaryResourceRows K).card:ℝ)+(ordinaryResourceHubs K).card:=by
    convert hi a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  linarith only [ht,hbase a,hr']
end Oberwolfach
