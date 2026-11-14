module

public import Oberwolfach.TriangleBoundedDiagramAbsorber
public import Oberwolfach.TriangleDiagramGeometry

@[expose] public section
/-! Construct the finite diagram and its triangle absorber directly from
minimum degree and near-complete spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_dense_host_absorber (β:ℝ) (hβ:0<β):
  ∃ ε₀:ℝ,0<ε₀ ∧ ∀ m f:ℕ,∃ N₀ K₀:ℕ,
  ∀ (V₀ U₀ V U:Type) [Fintype V₀] [Fintype U₀] [DecidableEq V₀] [DecidableEq U₀]
    [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→K₀≤Fintype.card U→Fintype.card V₀+Fintype.card U₀≤m→
  ∀ (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (Q:SimpleGraph V) (H:V→U→Prop)
    (W:Finset V) (B₀:Finset U) (φ:V₀↪V) (ψ:U₀↪U),
    (∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀ u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    (∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→
    (∀ v u,Hs v u→H (φ v) (ψ u))→(∀ u,ψ u∈B₀)→
    W.card≤f→B₀.card≤f→
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))→
  ∀ ε:ℝ,0≤ε→ε≤ε₀→
    (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))→
    (∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))→
  ∃ C:Finset (Sym2 V⊕(V×U)),
    IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
      (ordinaryHostResources (G.map φ) (ordinaryMappedSpokes Hs φ ψ)) C ∧
    C⊆ordinaryHostResources Q H ∧
    (ordinaryResourceRows C).card≤5*ordinaryDiagramSize 3 m+2*(max f m)+4*K₀ ∧
    (ordinaryResourceHubs C).card≤5*ordinaryDiagramSize 3 m+2*(max f m)+4*K₀ ∧
    Disjoint C (ordinaryRootResources ((Finset.univ.image φ)∪W) B₀) :=by
  obtain ⟨εa,hεa,habs⟩:=triangle_bounded_diagram_absorber β hβ
  let ε₀:=min εa (min β (1/18))
  have hε₀:0<ε₀:=by dsimp [ε₀];positivity
  refine ⟨ε₀,hε₀,?_⟩
  intro m f
  let M:=ordinaryDiagramSize 3 m
  let f':=max f m
  obtain ⟨Na,Ka,habs⟩:=habs M f'
  obtain ⟨Nbig,hNbig⟩:=exists_nat_gt (((f+m+6*M+9:ℕ):ℝ)/β)
  let N₀:=max Na (max Nbig 1)
  let K₀:=max Ka (2*(f+6*M)+2)
  refine ⟨N₀,K₀,?_⟩
  intro V₀ U₀ V U _ _ _ _ _ _ _ _ hn hU hm G Hs Q H W B₀ φ ψ hbal hdiv hG hHs hψ hW hB hdeg ε hε hεsmall hnearV hnearU
  have hnA:Na≤Fintype.card V:=(le_max_left _ _).trans hn
  have hnBig:Nbig≤Fintype.card V:=(le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1:1≤Fintype.card V:=(le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hUK:Ka≤Fintype.card U:=(le_max_left _ _).trans hU
  have hUbig:2*(f+6*M)+2≤Fintype.card U:=(le_max_right _ _).trans hU
  haveI : Nonempty V:=Fintype.card_pos_iff.mp (by omega)
  let v₀:V:=Classical.arbitrary V
  have hεa':ε≤εa:=hεsmall.trans (min_le_left _ _)
  have hεβ:ε≤β:=hεsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε18:ε≤1/18:=hεsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hpair,hpairH,hhub⟩:=triangle_diagram_dense_geometry Q H β ε hβ hε hεβ hε18 hdeg hnearV hnearU
  have hNreal:(((f+m+6*M+9:ℕ):ℝ)/β)<Fintype.card V:=by
    have hh:(Nbig:ℝ)≤Fintype.card V:=by exact_mod_cast hnBig
    linarith
  have hbudget:((f+m+6*M+9:ℕ):ℝ)<β*Fintype.card V:=by
    have hh:(((f+m+6*M+9:ℕ):ℝ)/β)*β<(Fintype.card V:ℝ)*β:=mul_lt_mul_of_pos_right hNreal hβ
    simpa [div_mul_cancel₀ _ (ne_of_gt hβ),mul_comm] using hh
  have hR:(Finset.univ.image φ).card≤m:=by
    rw [Finset.card_image_of_injective _ φ.injective,Finset.card_univ]
    omega
  have hA:β*(Fintype.card V:ℝ)≤((Finset.univ:Finset V).card:ℝ):=by
    have h:=hpair v₀ v₀
    have hh:((Q.neighborFinset v₀∩Q.neighborFinset v₀).card:ℝ)≤(Fintype.card V:ℝ):=by exact_mod_cast Finset.card_le_univ _
    simpa using h.trans hh
  have hUreal:((2*(f+6*M)+2:ℕ):ℝ)≤Fintype.card U:=by exact_mod_cast hUbig
  obtain ⟨D⟩:=ordinary_host_diagram G Hs 3 m (by omega) hm hbal hdiv Q ⊥ H Finset.univ W (Finset.univ.image φ) B₀ φ ψ
    (by intro v; exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩) hψ hG hHs
    (by simp) 0 (β*Fintype.card V) ((1/2:ℝ)*Fintype.card U) (by norm_num) (by simp)
    hA (by nlinarith) (by intro v w; simpa using hpair v w)
    (by intro u u' v w;simpa using hpairH u u' v w)
    (by intro T hT _;exact hhub T hT)
    (by
      have hw:(W.card:ℝ)≤f:=by exact_mod_cast hW
      have hr:((Finset.univ.image φ).card:ℝ)≤m:=by exact_mod_cast hR
      push_cast at hbudget
      norm_num
      linarith only [hw,hr,hbudget])
    (by
      have hb:(B₀.card:ℝ)≤f:=by exact_mod_cast hB
      push_cast at hUreal
      nlinarith)
  obtain ⟨C,hC,hhost,hrows,hhubs,havoid⟩:=habs V U hnA hUK Q H _ Finset.univ W (Finset.univ.image φ) B₀ (Finset.univ.image ψ) D
    (hW.trans (le_max_left _ _)) (hR.trans (le_max_right _ _)) (hB.trans (le_max_left _ _)) hdeg ε hε hεa' hnearV hnearU
  have hk:Ka≤K₀:=le_max_left _ _
  refine ⟨C,hC,hhost,?_,?_,havoid⟩ <;> dsimp [M,f'] at * <;> omega
end Oberwolfach
