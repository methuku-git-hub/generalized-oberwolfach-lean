module

public import Oberwolfach.EndpointBoundaryCompletion
public import Oberwolfach.SelectedHubFactorWheels
public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section

/-! Finish the ordinary boundary from the actual selected hub factors and
endpoint assignments. The resulting wheel decomposition covers every
exterior incidence and leaves an induced-domain remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_selected_boundary_finish (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (x:I↪V) (u:J↪U)
    (hx:∀ i,x i∉X) (hu:∀ j,u j∉Z)
    (hxcover:∀ a∉X,∃ i,x i=a) (hucover:∀ z∉Z,∃ j,u j=z)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀ i,A i⊆X) (hB:∀ i,B i⊆Z) (hY:∀ j,Y j⊆X)
    (hQr:∀ i a,Q.Adj (x i) a↔a∈A i)
    (hHr:∀ i z,H (x i) z↔z∈B i)
    (hHc:∀ j a,H a (u j)↔a∈Y j)
    (hFroot:∀ i,∀ a∈A i,¬F.Adj (x i) a)
    (r K D d₀ e₀:ℕ) (hr:4≤r) (hK:0<K)
    (M:∀ j,Finset (LocalOrdinaryCycle Q F (T j) r))
    (hM:∀ j,∀ C∈M j,∀ C'∈M j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C'))
    (hcover:∀ j,(M j).biUnion localOrdinaryVertices=Y j)
    (hMdis:∀ i j,i≠j→Disjoint (localOrdinaryFactorGraph (M i)) (localOrdinaryFactorGraph (M j)))
    (hMdeg:∀ a,(⨆ j,localOrdinaryFactorGraph (M j)).degree a≤d₀)
    (hYsize:∀ j,(Y j).card≤e₀)
    (P:∀ i,EndpointPairing (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A i).image Sum.inl) ((B i).image Sum.inr))
    (hPdis:∀ i j,i≠j→Disjoint (P i).graph (P j).graph)
    (hsize:∀ i,(B i).card≤D)
    (hmemA:∀ a,(Finset.univ.filter (fun i=>a∈A i)).card≤D)
    (hmemB:∀ z,(Finset.univ.filter (fun i=>z∈B i)).card≤D)
    (L b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hcount:∀ i,∀ z∈B i,∀ a∈X,∀ c∈X,
      b≤(((X.filter (fun v=>H v z))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:(Fintype.card (Σ i,B i)*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(L+1)+
      2*((d₀:ℝ)+2*(K+D:ℕ))+e₀+(D*r:ℕ)+3*D<b):
    ∃ R:SimpleGraph V,∃ S:V→U→Prop,
      R≤Q ∧ (∀ a z,S a z→H a z) ∧ HasOrdinaryWheelDecomposition R S r ∧
      (Q\R).support⊆(X:Set V) ∧
      (∀ a z,H a z∧¬S a z→a∈X∧z∈Z) ∧
      (∀ a,R.degree a≤d₀+2*(K+D)) ∧
      (∀ a,(Z.filter (S a)).card≤K+D) ∧
      (∀ z∈Z,(Finset.univ.filter (fun a=>S a z)).card≤D*r):=by
  obtain ⟨W,hW,hWr,hWs,hWdis,hWdec⟩:=selected_hub_factor_wheels Q F H r T Y u M hM hcover
    (fun j a ha=>(hHc j a).mpr ha) hMdis
  let D₀:=wheelFamilyRim W
  let E₀:=wheelFamilySpokes W
  have hDsupport:∀ a b,D₀.Adj a b→a∈X∧b∈X:=by
    intro a b hab
    rw [show D₀=(⨆ j,localOrdinaryFactorGraph (M j)) from hWr] at hab
    obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hab
    have hh:=(spanningRestriction_adj Q (Y j) a b).mp
      (localOrdinaryFactorGraph_restriction (M j) (Y j) (hcover j) hj)
    exact ⟨hY j hh.2.1,hY j hh.2.2⟩
  have hDdeg:∀ a,D₀.degree a≤d₀:=by change ∀ a,(wheelFamilyRim W).degree a≤d₀;rw [hWr];exact hMdeg
  have hEout (a:V) (z:U) (he:E₀ a z):z∉Z:=by
    obtain ⟨j,hj,_⟩:=(hWs a z).mp he
    exact hj ▸ hu j
  have hEcol (z:U):(Finset.univ.filter (fun a=>E₀ a z)).card≤e₀:=by
    by_cases hz:∃ j,u j=z
    · obtain ⟨j,hj⟩:=hz
      apply le_trans _ (hYsize j)
      apply Finset.card_le_card
      intro a ha
      obtain ⟨k,hk,ha⟩:=(hWs a z).mp (Finset.mem_filter.mp ha).2
      have he:k=j:=u.injective (hk.trans hj.symm)
      exact he ▸ ha
    · have he:(Finset.univ.filter (fun a=>E₀ a z))=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨j,hj,_⟩:=(hWs a z).mp (Finset.mem_filter.mp ha).2
        exact hz ⟨j,hj⟩
      rw [he];simp
  have hPold (i:I):Disjoint (P i).graph (ordinaryPhysicalGraph D₀ E₀):=by
    obtain ⟨v,w,_hadj,_hdis,_hcover,_hval,hgraph⟩:=typed_endpoint_pairing Q F H (A i) (B i) (P i)
    rw [hgraph]
    apply disjoint_iff_inf_le.mpr
    intro a z haz
    cases a with
    | inl a=>
      cases z with
      | inl z=>exact haz.1.elim
      | inr z=>
        obtain ⟨b,hb,_⟩:=haz.1
        exact (hEout a z haz.2 (hb.symm ▸ hB i b.property)).elim
    | inr a=>
      cases z with
      | inl z=>
        obtain ⟨b,hb,_⟩:=haz.1
        exact (hEout z a haz.2 (hb.symm ▸ hB i b.property)).elim
      | inr z=>exact haz.1.elim
  obtain ⟨C,hC,hCdis,hCdec,hCr,hCs,hCd,hCrow,hCcol⟩:=endpoint_boundary_completion Q D₀ F H E₀ X x A B hx hA
    (fun i a ha=>⟨(hQr i a).mpr ha,fun hd=>hx i (hDsupport _ _ hd).1,hFroot i a ha⟩)
    (fun i z hz=>⟨(hHr i z).mpr hz,fun he=>hEout _ _ he (hB i hz)⟩)
    P hPdis hPold r K D hr hK hsize hmemA hmemB L d₀ e₀ b hL hF
    (by intro a ha;exact_mod_cast hDdeg a)
    (by
      intro z
      have hh:((Finset.univ.filter (fun a=>E₀ a z)).card:ℝ)≤(e₀:ℝ):=by exact_mod_cast hEcol z
      convert hh using 1)
    hcount hbudget
  have hdisR:Disjoint D₀ (wheelFamilyRim C):=by
    apply disjoint_iff_inf_le.mpr
    intro a z haz
    obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp haz.2
    exact (Finset.disjoint_left.mp (hC i).2.2
      ((ordinaryWheelResources_rim (C i) s(a,z)).mpr hi)
      ((ordinaryHostResources_rim D₀ E₀ s(a,z)).mpr haz.1)).elim
  have hdisS:∀ a z,¬(E₀ a z∧wheelFamilySpokes C a z):=by
    rintro a z ⟨ha,i,hi,hz⟩
    exact Finset.disjoint_left.mp (hC i).2.2
      ((ordinaryWheelResources_spoke (C i) a z).mpr ⟨hi,hz⟩)
      ((ordinaryHostResources_spoke D₀ E₀ a z).mpr ha)
  let R:=D₀⊔wheelFamilyRim C
  let S:V→U→Prop:=fun a z=>E₀ a z∨wheelFamilySpokes C a z
  have hRQ:R≤Q:=sup_le (wheelFamily_subhost W).1 (wheelFamily_subhost C).1
  have hSH:∀ a z,S a z→H a z:=fun a z h=>h.elim
    ((wheelFamily_subhost W).2 a z) ((wheelFamily_subhost C).2 a z)
  have hdec:HasOrdinaryWheelDecomposition R S r:=
    ordinary_wheel_decomposition_union D₀ (wheelFamilyRim C) E₀ (wheelFamilySpokes C) r hWdec hCdec hdisR hdisS
  have hrowrim (a:V) (ha:a∉X) (b:V) (hab:Q.Adj a b):R.Adj a b:=by
    obtain ⟨i,hi⟩:=hxcover a ha
    exact Or.inr ((hCr a ha b).mpr ⟨i,hi.symm,(hQr i b).mp (hi.symm ▸ hab)⟩)
  have hrowspoke (a:V) (ha:a∉X) (z:U) (haz:H a z):S a z:=by
    obtain ⟨i,hi⟩:=hxcover a ha
    exact Or.inr ((hCs a ha z).mpr ⟨i,hi.symm,(hHr i z).mp (hi.symm ▸ haz)⟩)
  have hcolspoke (z:U) (hz:z∉Z) (a:V) (haz:H a z):S a z:=by
    obtain ⟨j,hj⟩:=hucover z hz
    exact Or.inl ((hWs a z).mpr ⟨j,hj,(hHc j a).mp (hj.symm ▸ haz)⟩)
  refine ⟨R,S,hRQ,hSH,hdec,?_,?_,?_,?_,?_⟩
  · intro a ha
    by_contra hn
    obtain ⟨b,hb⟩:=ha
    exact hb.2 (hrowrim a hn b hb.1)
  · intro a z haz
    exact ⟨by by_contra hn;exact haz.2 (hrowspoke a hn z haz.1),
      by by_contra hn;exact haz.2 (hcolspoke z hn a haz.1)⟩
  · intro a
    simpa only [←SimpleGraph.ncard_neighborSet] using
      (graph_degree_sup_le D₀ (wheelFamilyRim C) a).trans (Nat.add_le_add (hDdeg a) (hCd a))
  · intro a
    apply le_trans _ (hCrow a)
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter] at hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz.2.resolve_left (fun he=>hEout a z he hz.1)⟩
  · intro z hz
    apply le_trans _ (hCcol z)
    apply Finset.card_le_card
    intro a ha
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha.resolve_left (fun he=>hEout a z he hz)⟩

end Oberwolfach
