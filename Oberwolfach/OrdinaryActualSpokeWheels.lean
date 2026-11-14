module

public import Oberwolfach.TransformerActualData
public import Oberwolfach.OrdinarySpokeWheelFamilies

@[expose] public section

/-! Actual spoke-edge wheel pairs, retaining the original and image hub
separately. No injectivity of either vertex map is assumed; only injectivity
on the physical old spokes is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 structure OrdinaryActualSpokeWheels (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (ψ:U→U) (r:ℕ)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c)) where
  first : {e:V×U // H₀ e.1 e.2}→OrdinaryWheel Q F H r
  second : {e:V×U // H₀ e.1 e.2}→OrdinaryWheel Q F H r
  first_hub : ∀ e,ordinaryWheelHub (first e)=e.val.2
  second_hub : ∀ e,ordinaryWheelHub (second e)=ψ e.val.2
  first_support : ∀ e v,v∈(ordinaryWheelRim (first e)).support↔v=e.val.1∨v∈(p (.inr e)).2.2.support
  second_support : ∀ e v,v∈(ordinaryWheelRim (second e)).support↔v=φ e.val.1∨v∈(p (.inr e)).2.2.support
  first_disjoint : ∀ e f,e≠f→Disjoint (ordinaryWheelResources (first e)) (ordinaryWheelResources (first f))
  second_disjoint : ∀ e f,e≠f→Disjoint (ordinaryWheelResources (second e)) (ordinaryWheelResources (second f))
  rim_difference : ∀ i e,
    (if Sum.inl e∈ordinaryWheelResources (first i) then (1:ℤ) else 0)-
      (if Sum.inl e∈ordinaryWheelResources (second i) then 1 else 0)=
    (if e=s(i.val.1,(p (.inr i)).1) then 1 else 0)+(if e=s(i.val.1,(p (.inr i)).2.1) then 1 else 0)-
      (if e=s(φ i.val.1,(p (.inr i)).1) then 1 else 0)-(if e=s(φ i.val.1,(p (.inr i)).2.1) then 1 else 0)
  spoke_difference : ∀ i v z,
    (if Sum.inr (v,z)∈ordinaryWheelResources (first i) then (1:ℤ) else 0)-
      (if Sum.inr (v,z)∈ordinaryWheelResources (second i) then 1 else 0)=
    (if v=i.val.1∧z=i.val.2 then 1 else 0)-(if v=φ i.val.1∧z=ψ i.val.2 then 1 else 0)+
    (if v∈(p (.inr i)).2.2.support∧z=i.val.2 then 1 else 0)-
      (if v∈(p (.inr i)).2.2.support∧z=ψ i.val.2 then 1 else 0)

 theorem ordinary_actual_spoke_wheels (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (ψ:U→U) (r:ℕ) (hr:3≤r)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (R:Finset V) (hroot:∀ e:{e:V×U // H₀ e.1 e.2},e.val.1∈R∧φ e.val.1∈R∧e.val.1≠φ e.val.1)
    (hpath:∀ e:{e:V×U // H₀ e.1 e.2},(p (.inr e)).2.2.IsPath∧(p (.inr e)).2.2.length=r-2)
    (hends:∀ e:{e:V×U // H₀ e.1 e.2},Q.Adj e.val.1 (p (.inr e)).1∧
      Q.Adj (φ e.val.1) (p (.inr e)).1∧Q.Adj e.val.1 (p (.inr e)).2.1∧Q.Adj (φ e.val.1) (p (.inr e)).2.1)
    (havoid:∀ i,∀ v∈(p i).2.2.support,v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (hF:∀ e:{e:V×U // H₀ e.1 e.2},∀ v∈insert e.val.1 (insert (φ e.val.1) (p (.inr e)).2.2.support.toFinset),
      ∀ w∈insert e.val.1 (insert (φ e.val.1) (p (.inr e)).2.2.support.toFinset),¬F.Adj v w)
    (hH:∀ e:{e:V×U // H₀ e.1 e.2},H e.val.1 e.val.2∧H (φ e.val.1) (ψ e.val.2))
    (hHp:∀ e:{e:V×U // H₀ e.1 e.2},∀ v∈(p (.inr e)).2.2.support,H v e.val.2∧H v (ψ e.val.2))
    (hφedge:Function.Injective (fun e:{e:V×U // H₀ e.1 e.2}=>(φ e.val.1,ψ e.val.2))):
    Nonempty (OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p):=by
  obtain ⟨W,W',hh,hs,hs',hd,hd',hrim,hspoke⟩:=ordinary_spoke_wheel_families Q F H r hr R
    (fun e:{e:V×U // H₀ e.1 e.2}=>e.val.1) (fun e=>φ e.val.1) (fun e=>e.val.2) (fun e=>ψ e.val.2)
    (fun e=>p (.inr e)) (fun e=>⟨(hroot e).1,(hroot e).2.1⟩) (fun e=>(hroot e).2.2) hpath
    (fun e=>⟨(hends e).1,(hends e).2.2.1,(hends e).2.1,(hends e).2.2.2⟩)
    (fun e=>havoid (.inr e))
    (fun e f he=>hdis (.inr e) (.inr f) (fun hh=>he (Sum.inr.inj hh)))
    hF hH hHp (by intro e f he;exact Subtype.ext (Prod.ext (Prod.mk.inj he).1 (Prod.mk.inj he).2)) hφedge
  exact ⟨⟨W,W',fun e=>(hh e).1,fun e=>(hh e).2,hs,hs',hd,hd',hrim,hspoke⟩⟩

 theorem balanced_spoke_root_mem_support (G:SimpleGraph V) (H₀:V→U→Prop)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (e:{e:V×U // H₀ e.1 e.2}):e.val.1∈G.support:=by
  have hn:0<((Finset.univ:Finset U).filter (H₀ e.val.1)).card:=
    Finset.card_pos.mpr ⟨e.val.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.property⟩⟩
  by_contra he
  have hh:=(G.degree_eq_zero_iff_notMem_support e.val.1).mpr he
  rw [hbalance] at hh
  omega

end Oberwolfach
