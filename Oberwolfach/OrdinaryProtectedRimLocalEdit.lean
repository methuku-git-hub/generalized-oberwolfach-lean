module

public import Oberwolfach.OrdinaryPhysicalEditOfEqualRims
public import Oberwolfach.OrdinaryProtectedReservoirLocalAgreement

@[expose] public section
/-! Protected rim agreement and local spoke row/column changes control the
actual initial edit on each smaller pair, with no reservoir loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_rim_local_edit
    (R Q:SimpleGraph V) (J H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (X Y:Finset V) (Z B:Finset U) (hXY:X⊆Y) (hZB:Z⊆B)
    (hr:∀v∈Y,∀w∈Y,R.Adj v w↔Q.Adj v w)
    (havoid:Disjoint K (ordinaryRootResources Y B)) (L:ℝ):
    let V₁:=↥X;let U₁:=↥Z;
    let R₁:=R.induce (X:Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let H₁:=fun (v:V₁) (u:U₁)=>H v.val u.val;
    (∀v:V₁,((changed (Finset.univ.filter (J₁ v)) (Finset.univ.filter (H₁ v))).card:ℝ)≤L)→
    (∀u:U₁,((changed (Finset.univ.filter (fun v=>J₁ v u)) (Finset.univ.filter (fun v=>H₁ v u))).card:ℝ)≤L)→
    let G₁:=(Q\ordinaryResourceRim Q K).induce (X:Set V);
    let Hs₁:=fun (v:V₁) (u:U₁)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K);
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤L:=by
  intro V₁ U₁ R₁ J₁ H₁ hrow hcol G₁ Hs₁ a
  have hR:(Q.induce (X:Set V))=R₁:=by
    ext v w
    exact (hr v.val (hXY v.property) w.val (hXY w.property)).symm
  obtain ⟨hQ,hH⟩:=ordinary_protected_reservoir_nested_pair Q H K X Y Z B hXY hZB havoid
  have hp:ordinaryPhysicalGraph G₁ Hs₁=ordinaryPhysicalGraph R₁ H₁:=by
    dsimp only [G₁,Hs₁,H₁]
    rw [hQ,hH,hR]
  have hn:(ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a=(ordinaryPhysicalGraph R₁ H₁).neighborFinset a:=by
    ext b
    simp only [SimpleGraph.mem_neighborFinset]
    rw [hp]
  have hh:=ordinary_physical_edit_of_equal_rims R₁ J₁ H₁ L hrow hcol a
  rw [hn]
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
