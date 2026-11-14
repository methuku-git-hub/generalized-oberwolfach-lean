module

public import Oberwolfach.OrdinaryOutsideSparseCleanupRootFree
public import Oberwolfach.OrdinaryOutsidePhysicalRemainder
public import Oberwolfach.OrdinarySparseCleanupParametersExplicit

@[expose] public section
/-! A sufficiently sparse unreserved remainder can be cleaned outside the
inner pair, preserving disjointness from the earlier packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_outside_cleanup_root_free_with_margins_explicit (r:ℕ) (hr:3≤r) (bV bU ν:ℝ)
    (hV:0<bV) (hU:0<bU) (hν:0<ν):
    ∃τ:ℝ,τ=ordinarySparseCleanupScale r bV bU ν/2 ∧ 0<τ ∧ ∀(L:ℝ),0≤L→∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop)
      (X T:Finset V) (Z W:Finset U) (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool),
    T⊆X→W⊆Z→ ordinaryPhysicalGraph Q H≤ordinaryPhysicalGraph Q₀ H₀\C→Disjoint Q F→
    (∀v,(F.degree v:ℝ)≤L)→
    (∀u a c,bV*Fintype.card (V⊕U)≤((((X\T).filter (fun w=>H w u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))→
    (∀x∉X,∀y∉X,Q.Adj x y→bU*Fintype.card (V⊕U)≤(((Z\W).filter (fun u=>H x u∧H y u)).card:ℝ))→
    (∀w,((((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)≤τ*Fintype.card (V⊕U))→
    ∃(Nr Ns:ℕ) (M:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r),
      (∀i j,i≠j→Disjoint (ordinaryWheelResources (M i)) (ordinaryWheelResources (M j))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim M) (wheelFamilySpokes M) r ∧
      (∀v∉X,∀w∉X,¬(Q\wheelFamilyRim M).Adj v w) ∧
      (∀v∉X,∀u∉Z,¬(H v u∧¬wheelFamilySpokes M v u)) ∧
      (∀w:V⊕U,((ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)).degree w:ℝ)≤ν*Fintype.card (V⊕U)) ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)) C ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)) (ordinaryDeepRootStar T W):=by
  obtain ⟨θ,hθeq,hθ,hθ1,hparams⟩:=ordinary_sparse_cleanup_parameter_choice_explicit r hr bV bU ν hV hU hν
  refine ⟨θ/2,by rw [hθeq],by positivity,?_⟩
  intro L hL
  obtain ⟨N₀,hN₀⟩:=hparams L hL
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (2/θ)
  refine ⟨max 1 (max N₀ N₁),?_⟩
  intro V U _ _ _ _ hn Q₀ Q F H₀ H X T Z W C σ hTX hWZ hpost hQF hF hcount hubs hdegree
  let n:=Fintype.card (V⊕U)
  have hn0:0<n:=by dsimp [n];omega
  have hnR:(0:ℝ)<n:=Nat.cast_pos.mpr hn0
  have hnN:(N₀:ℕ)≤n:=by dsimp [n] at *;omega
  have hn1:(N₁:ℝ)≤n:=by exact_mod_cast (show N₁≤n by dsimp [n] at *;omega)
  have hscale:1≤(θ/2)*n:=by
    have hh:2/θ≤(n:ℝ):=hN₁.le.trans hn1
    have hmul:2≤(n:ℝ)*θ:=(div_le_iff₀ hθ).mp hh
    nlinarith only [hmul]
  let D:=Nat.ceil ((θ/2)*(n:ℝ))
  have hDhi:(D:ℝ)≤θ*n:=by
    have hh:(D:ℝ)≤(θ/2)*n+1:=(Nat.ceil_lt_add_one (by positivity:0≤(θ/2)*(n:ℝ))).le
    linarith only [hh,hscale]
  have hDN:∀w,(((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w≤D:=by
    intro w
    have hc:((((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)≤D:=
      (hdegree w).trans (Nat.le_ceil _)
    exact_mod_cast hc
  let E:=ordinaryHostResources (spanningRestriction Q (Finset.univ\X)) (fun v u=>H v u∧v∉X∧u∉Z)
  have he:=ordinary_outside_resources_bounded_by_unreserved_remainder Q₀ Q H₀ H X Z C σ D hpost hDN
  change (∀w,(E.filter (ordinaryResourceIncident w)).card≤D) ∧ E.card≤n*D at he
  obtain ⟨K,hK,hbr,hbu,hbs,hsmall⟩:=hN₀ n D E.card hnN he.2 hDhi
  obtain ⟨Nr,Ns,M,hdis,hdec,hNoR,hNoS,hbound,hstar⟩:=ordinary_sparse_outside_cleanup_root_free Q F H X T Z W r K D hr hK hQF
    L (bV*n) (bU*n) hL hF hTX hWZ hcount hubs
    (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using he.1)
    (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using hbr)
    (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using hbu)
    (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using hbs)
  have hsub:=wheelFamily_subhost M
  have hphys:ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)≤ordinaryPhysicalGraph Q H:=by
    intro a b hab
    cases a with
    | inl v=>
      cases b with
      | inl w=>exact hsub.1 hab
      | inr u=>exact hsub.2 v u hab
    | inr u=>
      cases b with
      | inl v=>exact hsub.2 v u hab
      | inr u'=>exact hab.elim
  have hdisC:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)) C:=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    exact (hpost (hphys hab.1)).2 hab.2
  refine ⟨Nr,Ns,M,hdis,hdec,hNoR,hNoS,?_,hdisC,hstar⟩
  intro w
  exact (hbound w).trans (by simpa only [Nat.cast_max,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hsmall)
end Oberwolfach
