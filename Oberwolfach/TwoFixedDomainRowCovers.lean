module

public import Oberwolfach.FixedDomainRowCovers
public import Oberwolfach.FixedHubDomainCounts
public import Oberwolfach.HubDomainWheels

@[expose] public section

/-! Successive row covers in the original host from counts on fixed vertex
and hub domains. All output wheels retain ambient hub endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_two_fixed_domain_row_covers
    (r:ℕ) (hr:4≤r) (C₀ α ω p₀:ℝ) (hC₀:0≤C₀)
    (hα:0<α) (hω:0<ω) (hp₀:0<p₀) (hp₀1:p₀≤1) :
    ∃ K:ℕ,0<K ∧ ∃ θ ε₀:ℝ,0<θ ∧ 0<ε₀ ∧ ∀ d:ℕ,∃ N:ℕ,
      ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      ∀ (P Q F:SimpleGraph V) (H:V→U→Prop) (n:ℕ) (x:Fin n→V) (A X:Finset V) (B:Finset U) (q p ε:ℝ),
      N≤A.card → (n:ℝ)≤θ*A.card → ω*A.card≤(B.card:ℝ) →
      (B.card:ℝ)≤C₀*A.card → p₀≤q → p₀≤p → p≤1 → 0≤ε → ε≤ε₀ →
      Function.Injective x → X⊆A → (∀ i,x i∉X) → Q≤P →
      ((A\X).card:ℝ)≤p₀^6*(min α 1)*A.card/8 →
      (∀ i,Q.neighborFinset (x i)⊆X) →
      (∀ i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card) →
      (∀ i u,H (x i) u → u∈B) →
      (∀ a,F.degree a≤d) → (∀ i a,Q.Adj (x i) a → ¬F.Adj (x i) a) →
      (∀ a,(1/2+α)*A.card≤((A∩P.neighborFinset a).card:ℝ)) →
      (∀ S:Finset V,∀ J:Finset U,J⊆B → S.card≤2 → J.card≤1 →
        |((common (common A S (fun v=>Q.neighborFinset v)) J
          (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
          q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card) →
      (∀ S:Finset V,S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
        |((common B S (fun v=>Finset.univ.filter (H v))).card:ℝ)-p^S.card*B.card|≤ε*B.card) →
      ∃ C:Fin n→Finset (OrdinaryWheel Q F H r),
        (∀ i,OrdinaryRowCover (C i) (x i) X K) ∧
        (∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) ∧
        (∀ a∈X,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree a≤n*(2*(K+1))) ∧
        (∀ a∈X,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) a)).card≤n*(K+1)) ∧
        (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion C) a u)).card≤n*r)  := by
  obtain ⟨K,hK,θ,ε₀,hθ,hε₀,hcover⟩:=ordinary_fixed_domain_row_covers r hr C₀ α ω p₀ hC₀ hα hω hp₀ hp₀1
  refine ⟨K,hK,θ,ε₀,hθ,hε₀,?_⟩
  intro d
  obtain ⟨N,hN⟩:=hcover d
  refine ⟨N,?_⟩
  intro V U _ _ _ _ P Q F H n x A X B q p ε hn hnθ hmlo hmhi hq hp hp1 hε hεsmall
    hx hXA hxA hQP hmissing hSA hbal hrootB hF hFx hdeg hrow hindex
  let HB:V→B→Prop:=fun v u=>H v u.val
  have hbalB (i:Fin n):Q.degree (x i)=2*(Finset.univ.filter (HB (x i))).card:=by
    have he:B.filter (H (x i))=Finset.univ.filter (H (x i)):=by
      ext u;simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun hh=>hh.2,fun hh=>⟨hrootB i u hh,hh⟩⟩
    rw [finite_domain_predicate_card B (H (x i)),he]
    exact hbal i
  obtain ⟨C,hC,hdis,hdegC,hrowC,hcolC⟩:=hN V B P Q F HB n x A X q p ε hn hnθ
    (by simpa only [Fintype.card_coe] using hmlo) (by simpa only [Fintype.card_coe] using hmhi)
    hq hp hp1 hε hεsmall hx hXA hxA hQP hmissing hSA hbalB hF hFx hdeg
    (by
      intro S J hS hJ
      let e:B↪U:=⟨Subtype.val,Subtype.val_injective⟩
      have hh:=hrow S (J.map e) (by rintro u hu;obtain ⟨z,_,rfl⟩:=Finset.mem_map.mp hu;exact z.property)
        hS (by simpa only [Finset.card_map] using hJ)
      simpa only [common_index_map,Finset.card_map,HB,e,Function.Embedding.coeFn_mk] using hh)
    (by
      intro S hS hI
      simpa only [common_hub_domain_card,Fintype.card_coe,HB] using hindex S hS hI)
  refine ⟨fun i=>ordinaryHubDomainPacking B (C i),?_,?_,?_,?_,?_⟩
  · intro i;exact ordinaryRowCover_of_hub_domain B (C i) (x i) X K (hC i) (hrootB i)
  · intro i j hij;exact ordinaryHubDomainPacking_disjoint B (C i) (C j) (hdis i j hij)
  · intro a ha
    have he:ordinaryWheelRimGraph (Finset.univ.biUnion (fun i=>ordinaryHubDomainPacking B (C i)))=
        ordinaryWheelRimGraph (Finset.univ.biUnion C):=by
      rw [ordinaryHubDomainPacking_biUnion,ordinaryHubDomainPacking_rim]
    convert hdegC a ha using 1 <;> rw [he]
  · intro a ha
    rw [ordinaryHubDomainPacking_biUnion,ordinaryHubDomainPacking_row_card]
    exact hrowC a ha
  · intro u
    rw [ordinaryHubDomainPacking_biUnion]
    by_cases hu:u∈B
    · rw [ordinaryHubDomainPacking_column_card B _ ⟨u,hu⟩]
      exact hcolC ⟨u,hu⟩
    · rw [ordinaryHubDomainPacking_column_empty B _ u hu,Finset.card_empty]
      exact Nat.zero_le _

end Oberwolfach
