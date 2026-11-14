module

public import Oberwolfach.OrdinaryPlacementCertificateCostBound
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness

@[expose] public section
/-! The exact edit cost used by the same-sample preparation theorem obeys
the preselected first-level certificate budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_preparation_edit_cost_bound
    (m d tAbs aAbs bAbs K N dNeed:ℕ)
    (η capEdit α lamList ζList δ θ κ b z matchErr σ κ' ζret lam a γ ξedit unused:ℝ)
    (hη:0<η) (hcap:capEdit≤η)
    (hstage:OrdinaryPlacementStage m dNeed α lamList ζList capEdit δ θ κ b z matchErr σ κ')
    (hafter:OrdinaryPlacementAfterSpacing m d N α δ θ κ b z matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lam a γ)
    (hξ:0≤ξedit) (hξσ:ξedit≤σ) (hunused0:0≤unused) (hunused:unused≤2*θ):
    ∃Ncost:ℕ,∀n:ℕ,Ncost≤n→∀rows hubs:ℝ,0≤rows→0≤hubs→
      rows+hubs≤((2^(tAbs*tAbs)*aAbs+2^(tAbs*tAbs)*bAbs:ℕ):ℝ)→
      let LF:ℝ:=2*((3*d:ℕ):ℝ);
      let edit:=ξedit*n;let t:ℝ:=(n:ℝ)^(3/5:ℝ);
      let newLoss:=5*Real.sqrt δ*n;
      let κref:ℝ:=(max a γ)*n+unused*n+3*t+((6*d+4:ℕ):ℝ)+edit+LF;
      let e:ℝ:=σ*n+2*(σ*n)+LF;
      let Lrim:=edit+κref+newLoss;
      let Lspoke:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+σ*n);
      0≤Lrim+Lspoke+rows+hubs ∧ Lrim+Lspoke+rows+hubs≤14*η*n :=by
  have hstage':=hstage
  obtain ⟨hδ,hδ1,hδbound,hsqrt,hθ,hθ1,hθδ,hκ,hb,hz,hmatch,hσ,hσcap,hblower,hzlower,
    hbζ,hbα,hbδ,hzb,hκ',hκ'κ,hdNeed,hRate,hrest⟩:=hstage'
  have hσb:σ≤b:=by
    have hh:=hRate 1 σ 0 0 0 (by norm_num) (by simp) (by simpa using hσ.le)
      (by simpa using hσ.le) (by simpa using hσ.le)
    simpa using hh
  obtain ⟨Ncost,hcost⟩:=ordinary_placement_certificate_cost_bound m d tAbs aAbs bAbs K N dNeed η capEdit α lamList ζList δ θ κ b z matchErr σ κ' ζret lam a γ hη hcap hstage hafter hmatching
  refine ⟨Ncost,?_⟩
  intro n hn rows hubs hrows0 hhubs0 hres LF edit tt newLoss κref e Lrim Lspoke
  have hn0:(0:ℝ)≤n:=by positivity
  have heditσ:edit≤σ*n:=by dsimp [edit];exact mul_le_mul_of_nonneg_right hξσ hn0
  have heditb:edit≤b*n:=by dsimp [edit];exact mul_le_mul_of_nonneg_right (hξσ.trans hσb) hn0
  have hbound:=hcost n hn unused edit rows hubs hunused heditσ hres
  let bref:ℝ:=(max a γ)*n+unused*n+3*(n:ℝ)^(3/5:ℝ)+((6*d+4:ℕ):ℝ)+b*n+LF
  let brim:ℝ:=edit+bref+newLoss
  let bspoke:ℝ:=max (2*newLoss+(brim+e)/2) (2*(δ*n)+σ*n)
  have hrim:Lrim≤brim:=by dsimp [Lrim,κref,brim,bref,tt];linarith
  have hspoke:Lspoke≤bspoke:=by
    dsimp [Lspoke,bspoke]
    apply max_le_max
    · linarith
    · rfl
  have ha:0<a:=hmatching.2.2.1
  have hγ:0<γ:=hmatching.2.2.2.1
  have hnonneg:0≤Lrim+Lspoke+rows+hubs:=by
    dsimp [Lrim,Lspoke,κref,edit,tt,newLoss,e,LF]
    positivity
  refine ⟨hnonneg,?_⟩
  have hbnd:brim+bspoke+rows+hubs≤14*η*n:=by
    convert hbound using 1 <;> dsimp [brim,bspoke,bref,LF,newLoss,e] <;> ring_nf
  linarith

theorem ordinary_corrected_reservoir_resource_sum_bound
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (r m t a b:ℕ) (ξ:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A Z Wterm:Finset V) (Bterm B:Finset U)
    (K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop)
    (hw:OrdinaryCorrectedProtectedReservoirWitness r m t a b ξ Q F H A Z Wterm Bterm B K JQ JH):
    ((ordinaryResourceRows K).card:ℝ)+(ordinaryResourceHubs K).card≤
      ((2^(t*t)*a+2^(t*t)*b:ℕ):ℝ) :=by
  exact_mod_cast Nat.add_le_add hw.2.2.1 hw.2.2.2.1
end Oberwolfach
