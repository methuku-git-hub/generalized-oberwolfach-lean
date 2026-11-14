module

public import Oberwolfach.OrdinaryDiagramAbsorber
public import Oberwolfach.OrdinaryHostDiagramBudgets

@[expose] public section

/-! The ordinary relative host absorber for r ≥ 4. The five graph pairs
and four transformers are all constructed, and all numerical budgets are
discharged. The original common-pair cycle profiles are never recomputed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

theorem ordinary_relative_host_absorber (r:ℕ) (hr:3≤r)
    (Tpls:Tpl→VertexAbsorberTemplate r) (β a b B:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hB:0<B) :
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/4∧∀ m:ℕ,∃ a₀ b₀:ℕ,∀ f:ℕ,∀ d:ℝ,0≤d→∃ n₀:ℕ,
    ∀ (V₀ U₀ V U:Type) [Fintype V₀] [DecidableEq V₀] [Fintype U₀] [DecidableEq U₀]
      [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      n₀≤Fintype.card V→Fintype.card V₀+Fintype.card U₀≤m→
      ∀ (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (Q F:SimpleGraph V) (H:V→U→Prop)
      (A Z W:Finset V) (B₀:Finset U) (φ:V₀↪V) (ψ:U₀↪U),
      (∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀ u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      (∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→(∀ v u,Hs v u→H (φ v) (ψ u))→
      (∀ u,ψ u∈B₀)→(∀ v w,Q.Adj v w→¬F.Adj v w)→
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→W.card≤f→(B₀.card:ℝ)≤ε*Fintype.card V+f→
      (∀ v,(F.degree v:ℝ)≤d)→
      (∀ v w,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (r=4→∀ v w x,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))→
      (r=3→∀ w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (r=3→∀ u u' w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (∀ T:Finset V,T.card≤r+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      OrdinaryCommonCycleProfiles Q F H r Tpls β a b B η→
      ∃ C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources (G.map φ) (ordinaryMappedSpokes Hs φ ψ)) C∧
        C⊆ordinaryHostResources Q H∧(ordinaryResourceRows C).card≤a₀∧(ordinaryResourceHubs C).card≤b₀∧
        ordinaryResourceRows C⊆(Finset.univ.image φ)∪A∧
        (∀ v∈ordinaryResourceRows C,v∈W→v∈Finset.univ.image φ)∧
        (∀ u∈ordinaryResourceHubs C,u∈B₀→u∈Finset.univ.image ψ)∧
        Disjoint C (ordinaryRootResources W B₀) := by
  obtain ⟨η,ε,hη,hε,hεβ,habs⟩:=ordinary_diagram_absorber r hr Tpls β a b B hβ ha hb hB
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro m
  obtain ⟨a₀,b₀,habs⟩:=habs (ordinaryDiagramSize r m)
  refine ⟨a₀,b₀,?_⟩
  intro f d hd
  obtain ⟨N₀,habs⟩:=habs f d hd
  obtain ⟨N₁,hN₁,hbudget⟩:=ordinary_host_diagram_budgets β ε d hβ hd hεβ r m (ordinaryDiagramSize r m) f
  refine ⟨max N₀ N₁,?_⟩
  intro V₀ U₀ V U _ _ _ _ _ _ _ _ hn hm G Hs Q F H A Z W B₀ φ ψ hbal hdiv hG hHs hψ hQF
    hA hZ hW hB₀ hF hcount hpair hthree hfour hspfour hhub P
  have hn1:1≤Fintype.card V:=hN₁.trans ((le_max_right _ _).trans hn)
  haveI : Nonempty V:=Fintype.card_pos_iff.mp (by omega)
  let v₀:V:=Classical.arbitrary V
  have hn0:0≤(Fintype.card V:ℝ):=by positivity
  have hhalf:(β/2)*Fintype.card V≤β*Fintype.card V:=by nlinarith only [mul_nonneg hβ.le hn0]
  have hZhalf:(Z.card:ℝ)≤(β/2)*Fintype.card V:=by
    have he:=mul_le_mul_of_nonneg_right hεβ hn0
    nlinarith only [hZ,he,mul_nonneg hβ.le hn0]
  have hlower (S:Finset V) (hS:β*Fintype.card V≤(S.card:ℝ)):
      (β/2)*Fintype.card V≤((S\Z).card:ℝ):=by
    have hh:(S.card:ℝ)≤(S\Z).card+Z.card:=by exact_mod_cast Finset.card_le_card_sdiff_add_card (s:=S) (t:=Z)
    linarith only [hS,hh,hZhalf]
  have hcount':∀ v w,(β/2)*Fintype.card V≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ):=by
    intro v w
    have he:(Q.neighborFinset v∩Q.neighborFinset w)\Z=A∩Q.neighborFinset v∩Q.neighborFinset w:=by
      ext x;simp [hA];tauto
    simpa only [he] using hlower _ (hcount v w)
  have hpair':∀ u u' v w,(β/2)*Fintype.card V≤(((A.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ):=by
    intro u u' v w
    have he:((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w)\Z=
        (A.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w:=by
      ext x;simp [hA];tauto
    simpa only [he] using hlower _ (hpair u u' v w)
  have hAsize:(β/2)*Fintype.card V≤(A.card:ℝ):=
    (hcount' v₀ v₀).trans (by exact_mod_cast Finset.card_le_card ((Finset.inter_subset_left).trans Finset.inter_subset_left))
  have hUsize:(β/2)*Fintype.card V≤(Fintype.card U:ℝ):=by
    have hh:=hhub ∅ (by simp) (by simp)
    simpa [common] using hhalf.trans hh
  have hRcard:(Finset.univ.image φ).card≤m:=by
    rw [Finset.card_image_of_injective _ φ.injective,Finset.card_univ]
    omega
  obtain ⟨hb1,hb2⟩:=hbudget (Fintype.card V) ((le_max_right _ _).trans hn) W.card (Finset.univ.image φ).card B₀.card hW hRcard hB₀
  obtain ⟨D⟩:=ordinary_host_diagram G Hs r m (by omega) hm hbal hdiv Q F H A W (Finset.univ.image φ) B₀ φ ψ
    (fun v=>Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩) hψ hG hHs hQF d
    ((β/2)*Fintype.card V) ((β/2)*Fintype.card V) hd hF hAsize hUsize hcount' hpair'
    (fun T hTc hTF=>hhalf.trans (hhub T (by omega) hTF)) hb1 hb2
  exact habs V U ((le_max_left _ _).trans hn) Q F H A Z W (Finset.univ.image φ) B₀ (Finset.univ.image ψ)
    (ordinaryHostResources (G.map φ) (ordinaryMappedSpokes Hs φ ψ)) hA hZ hW hB₀ hF hcount hpair hthree hfour hspfour hhub P D

end Oberwolfach
