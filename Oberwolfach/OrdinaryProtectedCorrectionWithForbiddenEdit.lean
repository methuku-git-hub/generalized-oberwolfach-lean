module

public import Oberwolfach.OrdinaryProtectedCorrectionLocalEdit
public import Oberwolfach.OrdinaryInducedPhysicalEditOfGlobal
public import Oberwolfach.OrdinaryProtectedBoundaryEdit
public import Oberwolfach.HubToRowDeletion

@[expose] public section
/-! Forbidden rim edges need not be absent from the sample: their maximum
degree is charged once, while a protected reservoir costs nothing locally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_forbidden_rim_edit
    (R F:SimpleGraph V) (J:V→U→Prop) (L:ℝ) (hL:0≤L)
    (hF:∀v,(F.degree v:ℝ)≤L):
    ∀a:V⊕U,((changed ((ordinaryPhysicalGraph R J).neighborFinset a)
      ((ordinaryPhysicalGraph (R\F) J).neighborFinset a)).card:ℝ)≤L:=by
  intro a
  cases a with
  | inl v=>
    have he:changed ((ordinaryPhysicalGraph R J).neighborFinset (Sum.inl v))
        ((ordinaryPhysicalGraph (R\F) J).neighborFinset (Sum.inl v))=
        (changed (R.neighborFinset v) ((R\F).neighborFinset v)).image Sum.inl:=by
      ext b
      cases b <;> simp [changed,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
    rw [he,Finset.card_image_of_injective _ Sum.inl_injective]
    have hh:=graph_changed_neighbors_after_deletion R F v
    have hh':((changed (R.neighborFinset v) ((R\F).neighborFinset v)).card:ℝ)≤F.degree v:=by exact_mod_cast hh
    exact hh'.trans (hF v)
  | inr u=>
    have he:((ordinaryPhysicalGraph R J).neighborFinset (Sum.inr u))=
        ((ordinaryPhysicalGraph (R\F) J).neighborFinset (Sum.inr u)):=by
      ext b
      cases b <;> simp [ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
    rw [←he]
    simpa [changed, Finset.sdiff_self] using hL

theorem ordinary_protected_correction_forbidden_local_edit
    (R F Q:SimpleGraph V) (J H D:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (X Y:Finset V) (Z B:Finset U) (hXY:X⊆Y) (hZB:Z⊆B)
    (hr:∀v∈Y,∀w∈Y,(R\F).Adj v w↔Q.Adj v w)
    (hs:∀v∈Y,∀u∈B,¬D v u→(J v u↔H v u))
    (havoid:Disjoint K (ordinaryRootResources Y B)) (LF LS:ℝ) (hLF:0≤LF)
    (hF:∀v,(F.degree v:ℝ)≤LF):
    let V₁:=↥X;let U₁:=↥Z;
    (∀v:V₁,((Finset.univ.filter (fun u:U₁=>D v.val u.val)).card:ℝ)≤LS)→
    (∀u:U₁,((Finset.univ.filter (fun v:V₁=>D v.val u.val)).card:ℝ)≤LS)→
    let R₁:=R.induce (X:Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let G₁:=(Q\ordinaryResourceRim Q K).induce (X:Set V);
    let Hs₁:=fun (v:V₁) (u:U₁)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K);
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤LF+LS:=by
  intro V₁ U₁ hrow hcol R₁ J₁ G₁ Hs₁ a
  let Rf:=(R\F).induce (X:Set V)
  have hfirst:=ordinary_induced_physical_edit_of_global R (R\F) J J X Z LF
    (ordinary_physical_forbidden_rim_edit R F J LF hLF hF) a
  have hsecond:=ordinary_protected_correction_local_edit (R\F) Q J H D K X Y Z B hXY hZB hr hs havoid LS hrow hcol a
  have htriangle:((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤
      ((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
        ((ordinaryPhysicalGraph Rf J₁).neighborFinset a)).card:ℝ)+
      ((changed ((ordinaryPhysicalGraph Rf J₁).neighborFinset a)
        ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ):=by
    exact_mod_cast changed_card_triangle ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph Rf J₁).neighborFinset a) ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)
  have hfirst':((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
        ((ordinaryPhysicalGraph Rf J₁).neighborFinset a)).card:ℝ)≤LF:=by
    convert hfirst using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hsecond':((changed ((ordinaryPhysicalGraph Rf J₁).neighborFinset a)
        ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤LS:=by
    convert hsecond using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  linarith only [htriangle,hfirst',hsecond']
end Oberwolfach
