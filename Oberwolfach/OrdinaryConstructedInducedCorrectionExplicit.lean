module

public import Oberwolfach.OrdinaryProtectedCorrectionExplicit
public import Oberwolfach.OrdinaryLiftInducedCorrection
public import Oberwolfach.OrdinaryProtectedCorrectionModular

@[expose] public section
/-! Apply the sparse correction theorem to the induced inner pair and lift
    the resulting protected correction to the ambient physical host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_constructed_induced_correction_explicit
    (r:ℕ) (hr:3≤r) (ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4)
    (hξ:0<ξ) (hξh:ξ≤h/100):
    ∃η₀:ℝ,η₀=δ*ω*ξ/1000 ∧ 0<η₀ ∧ ∃n₀:ℕ,∀η:ℝ,0≤η→η≤η₀→
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
      (Q:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (B W:Finset U),T⊆I→W⊆B→
      n₀≤I.card→ω*I.card≤B.card→B.card≤I.card→
      (T.card:ℝ)≤h*I.card→(W.card:ℝ)≤h*B.card→
    ∀(R:I→I→Prop),
      (∀x y,relationMultiplicity R x y+relationMultiplicity R y x=
        if (Q.induce (I:Set V)).Adj x y then 1 else 0)→
      BipartiteLargeCut (relationMultiplicity R) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity (fun v:I=>fun u:B=>H v.val u.val)) δ (2*h)→
      (∀v:I,|(((Q.induce (I:Set V)).degree v):ℝ)-
        2*(Finset.univ.filter (fun u:B=>H v.val u.val)).card|≤η*I.card)→
    ∃(D:SimpleGraph V) (J:V→U→Prop),
      D≤spanningRestriction Q I ∧ (∀v∈T,∀w∈T,¬D.Adj v w) ∧
      (∀v u,J v u→(H v u∧v∈I∧u∈B) ∧ ¬(v∈T∧u∈W)) ∧
      (∀v,((spanningRestriction Q I)\D).degree v=
        2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀x:V⊕U,((ordinaryPhysicalGraph D J).degree x:ℝ)≤10*ξ*I.card):=by
  obtain ⟨N,hmain⟩:=ordinary_protected_correction_at_order_explicit r hr ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨δ*ω*ξ/1000,rfl,by positivity,max N 1,?_⟩
  intro η hη hη0 V U _ _ _ _ Q H I T B W hTI hWB hn hωI hBI hT hW R horient hcutR hcutH hbalance
  let TI:=Finset.univ.filter (fun v:I=>v.val∈T)
  let WB:=Finset.univ.filter (fun u:B=>u.val∈W)
  have hTIcard:TI.card=T.card:=by
    have hi:TI.image Subtype.val=T:=by
      ext v
      simp only [TI,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨a,ha,rfl⟩;exact ha
      · intro hv;exact ⟨⟨v,hTI hv⟩,hv,rfl⟩
    rw [←hi,Finset.card_image_of_injective _ Subtype.val_injective]
  have hWBcard:WB.card=W.card:=by
    have hi:WB.image Subtype.val=W:=by
      ext u
      simp only [WB,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨a,ha,rfl⟩;exact ha
      · intro hu;exact ⟨⟨u,hWB hu⟩,hu,rfl⟩
    rw [←hi,Finset.card_image_of_injective _ Subtype.val_injective]
  have hn0:0<Fintype.card I:=by
    have hi:0<I.card:=by omega
    simpa only [Fintype.card_coe] using hi
  obtain ⟨D,J,hD,hDavoid,hJ,hbal,hdiv,hrow,hcol⟩:=
    hmain I B η hη hη0
      (by simpa only [Fintype.card_coe] using (show N≤I.card by omega)) hn0
      (by simpa only [Fintype.card_coe] using hωI)
      (by simpa only [Fintype.card_coe] using hBI)
      (Q.induce (I:Set V)) (fun v:I=>fun u:B=>H v.val u.val) R TI WB h
      hh.le le_rfl (by simpa only [hTIcard,Fintype.card_coe] using hT)
      (by simpa only [hWBcard,Fintype.card_coe] using hW) horient hcutR hcutH
      (by intro v
          simp only [Fintype.card_coe]
          convert hbalance v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  obtain ⟨D',J',hDeq,hJeq,hDsub,hJsub,hbal',hdiv',hdeg⟩:=ordinary_lift_induced_correction Q H I B D J r (10*ξ*I.card)
    hD (fun v u hj=>(hJ v u hj).1)
    (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by positivity)
    (by intro v;simpa only [Fintype.card_coe] using hrow v)
    (by intro u;simpa only [Fintype.card_coe] using hcol u)
  refine ⟨D',J',hDsub,?_,?_,hbal',hdiv',hdeg⟩
  · intro v hv w hw he
    rw [hDeq] at he
    obtain ⟨a,b,hab,ha,hb⟩:=(SimpleGraph.map_adj (⟨Subtype.val,Subtype.val_injective⟩:I↪V) D v w).mp he
    have haT:a∈TI:=by simp only [TI,Finset.mem_filter,Finset.mem_univ,true_and];change a.val=v at ha;rw [ha];exact hv
    have hbT:b∈TI:=by simp only [TI,Finset.mem_filter,Finset.mem_univ,true_and];change b.val=w at hb;rw [hb];exact hw
    exact hDavoid a haT b hbT hab
  · intro v u hvu
    have hin:=hJsub v u hvu
    have hc:=hvu
    rw [hJeq] at hc
    obtain ⟨a,b,hab,ha,hb⟩:=hc
    refine ⟨hin,?_⟩
    rintro ⟨hv,hu⟩
    have haT:a∈TI:=by simp only [TI,Finset.mem_filter,Finset.mem_univ,true_and];change a.val=v at ha;rw [ha];exact hv
    have hbW:b∈WB:=by simp only [WB,Finset.mem_filter,Finset.mem_univ,true_and];change b.val=u at hb;rw [hb];exact hu
    exact (hJ a b hab).2 ⟨haT,hbW⟩
end Oberwolfach
