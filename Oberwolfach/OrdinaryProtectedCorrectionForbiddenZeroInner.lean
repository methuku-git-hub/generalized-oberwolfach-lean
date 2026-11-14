module

public import Oberwolfach.OrdinaryProtectedCorrectionWithForbiddenEdit

@[expose] public section
/-! A protected correction removes no rim or spoke inside the protected pair.
After an avoiding reservoir is removed, the sole local sample edit is the
bounded-degree forbidden-rim deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_correction_forbidden_zero_inner
    (R F JQ:SimpleGraph V) (J JH:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (X Y:Finset V) (Z B:Finset U) (hXY:X⊆Y) (hZB:Z⊆B)
    (hJQ:∀v∈Y,∀w∈Y,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Y ∧ u∈B))
    (havoid:Disjoint K (ordinaryRootResources Y B)) (LF:ℝ) (hLF:0≤LF)
    (hF:∀v,(F.degree v:ℝ)≤LF):
    let V₁:=↥X;let U₁:=↥Z;
    let Q:=(R\F)\JQ;
    let H:=fun v u=>J v u∧¬JH v u;
    let R₁:=R.induce (X:Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let G₁:=(Q\ordinaryResourceRim Q K).induce (X:Set V);
    let Hs₁:=fun (v:V₁) (u:U₁)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K);
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤LF:=by
  intro V₁ U₁ Q H R₁ J₁ G₁ Hs₁
  have hr:∀v∈Y,∀w∈Y,(R\F).Adj v w↔Q.Adj v w:=by
    intro v hv w hw
    change (R\F).Adj v w ↔ (R\F).Adj v w ∧ ¬JQ.Adj v w
    simp [hJQ v hv w hw]
  have hs:∀v∈Y,∀u∈B,¬JH v u→(J v u↔H v u):=by
    intro v hv u hu h
    simp [H,h]
  have hz:∀v∈X,∀u∈Z,¬JH v u:=by
    intro v hv u hu hj
    exact hJH v u hj ⟨hXY hv,hZB hu⟩
  have hrow:∀v:V₁,((Finset.univ.filter (fun u:U₁=>JH v.val u.val)).card:ℝ)≤0:=by
    intro v
    have he:Finset.univ.filter (fun u:U₁=>JH v.val u.val)=∅:=by
      ext u
      simp [hz v.val v.property u.val u.property]
    simp [he]
  have hcol:∀u:U₁,((Finset.univ.filter (fun v:V₁=>JH v.val u.val)).card:ℝ)≤0:=by
    intro u
    have he:Finset.univ.filter (fun v:V₁=>JH v.val u.val)=∅:=by
      ext v
      simp [hz v.val v.property u.val u.property]
    simp [he]
  have hh:=ordinary_protected_correction_forbidden_local_edit R F Q J H JH K X Y Z B hXY hZB hr hs havoid LF 0 hLF hF hrow hcol
  intro a
  have hh':=((hh a))
  simpa only [add_zero] using hh'
end Oberwolfach
