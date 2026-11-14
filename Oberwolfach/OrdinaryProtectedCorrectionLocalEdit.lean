module

public import Oberwolfach.OrdinaryProtectedRimLocalEdit

@[expose] public section
/-! Exact protected rim agreement and a locally bounded spoke correction
supply the initial physical edit budget after reserving an avoiding absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_correction_local_edit
    (R Q:SimpleGraph V) (J H D:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (X Y:Finset V) (Z B:Finset U) (hXY:X⊆Y) (hZB:Z⊆B)
    (hr:∀v∈Y,∀w∈Y,R.Adj v w↔Q.Adj v w)
    (hs:∀v∈Y,∀u∈B,¬D v u→(J v u↔H v u))
    (havoid:Disjoint K (ordinaryRootResources Y B)) (L:ℝ):
    let V₁:=↥X;let U₁:=↥Z;
    (∀v:V₁,((Finset.univ.filter (fun u:U₁=>D v.val u.val)).card:ℝ)≤L)→
    (∀u:U₁,((Finset.univ.filter (fun v:V₁=>D v.val u.val)).card:ℝ)≤L)→
    let R₁:=R.induce (X:Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let G₁:=(Q\ordinaryResourceRim Q K).induce (X:Set V);
    let Hs₁:=fun (v:V₁) (u:U₁)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K);
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤L:=by
  intro V₁ U₁ hrow hcol R₁ J₁ G₁ Hs₁
  have hrow':∀v:V₁,((changed (Finset.univ.filter (fun u:U₁=>J v.val u.val))
      (Finset.univ.filter (fun u:U₁=>H v.val u.val))).card:ℝ)≤L:=by
    intro v
    have hsub:changed (Finset.univ.filter (fun u:U₁=>J v.val u.val))
        (Finset.univ.filter (fun u:U₁=>H v.val u.val))⊆
        Finset.univ.filter (fun u:U₁=>D v.val u.val):=by
      intro u hu
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
      by_contra hn
      have hh:=hs v.val (hXY v.property) u.val (hZB u.property) hn
      tauto
    have hc:=Finset.card_le_card hsub
    have hc':((changed (Finset.univ.filter (fun u:U₁=>J v.val u.val))
        (Finset.univ.filter (fun u:U₁=>H v.val u.val))).card:ℝ)≤
        ((Finset.univ.filter (fun u:U₁=>D v.val u.val)).card:ℝ):=by exact_mod_cast hc
    exact hc'.trans (hrow v)
  have hcol':∀u:U₁,((changed (Finset.univ.filter (fun v:V₁=>J v.val u.val))
      (Finset.univ.filter (fun v:V₁=>H v.val u.val))).card:ℝ)≤L:=by
    intro u
    have hsub:changed (Finset.univ.filter (fun v:V₁=>J v.val u.val))
        (Finset.univ.filter (fun v:V₁=>H v.val u.val))⊆
        Finset.univ.filter (fun v:V₁=>D v.val u.val):=by
      intro v hv
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      by_contra hn
      have hh:=hs v.val (hXY v.property) u.val (hZB u.property) hn
      tauto
    have hc:=Finset.card_le_card hsub
    have hc':((changed (Finset.univ.filter (fun v:V₁=>J v.val u.val))
        (Finset.univ.filter (fun v:V₁=>H v.val u.val))).card:ℝ)≤
        ((Finset.univ.filter (fun v:V₁=>D v.val u.val)).card:ℝ):=by exact_mod_cast hc
    exact hc'.trans (hcol u)
  have hh:=ordinary_protected_rim_local_edit R Q J H K X Y Z B hXY hZB hr havoid L hrow' hcol'
  intro a
  convert hh a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
