module

public import Oberwolfach.OrdinaryTransformerFromProfiles
public import Oberwolfach.UniformNamedSubgraphTransformer

@[expose] public section
/-! Construct the ordinary transformer from the prescribed path and wheel
stage in a regular host, using root-separated hub trades above the ordinary
cycle-decomposition threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_transformer_from_paths_regular_host_succ (m:ℕ) (hm2:2≤m)
    (α:ℝ) (hα:0<α) (hα1:α≤1):
    ∃ ξ:ℝ,0<ξ ∧ ∀ q nU:ℕ,∃ t:ℕ,∀ (F₀ d:ℝ) (f:ℕ),0≤F₀→0≤d→∃ N₀:ℕ,
    ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],N₀≤Fintype.card V→
      ∀ (G Q GHost F Fdel:SimpleGraph V) (Dhost:ℕ),
      GHost.IsRegularOfDegree Dhost→Fdel.edgeFinset.card≤f→
      cycleThreshold (m+1)+α≤(Dhost:ℝ)/Fintype.card V→
      Q=GHost\Fdel→
      ∀ (H₀ H:V→U→Prop),
      (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ξ*Fintype.card V)→
      ∀ (φ:V→V) (ψ:U→U)
      (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
      (σ:∀ v,Equiv.Perm (G.neighborSet v)),(∀ v w,σ v w≠w)→
      ∀ p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c),
      ∀ (A R W:Finset V) (B:Finset U),R⊆W→
      (∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)→
      (∀ u,(m+1)∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)→
      (∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤q)→
      Fintype.card {u:U // ∃ v,H₀ v u}≤nU→
      (∀ v∈G.support,v∈R∧φ v∈R)→
      (∀ v∈G.support,∀ w∈G.support,φ v≠w)→
      (∀ u,(∃ v,H₀ v u)→u≠ψ u)→
      (∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→
      Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2))→
      Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2))→
      (∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)→
      (∀ i,(p i).2.2.IsPath)→((m+1)≠3→∀ i,0<(p i).2.2.length)→
      ((m+1)=3→∀ e:G.edgeFinset,(p (.inl e)).2.2.length=0)→
      ((m+1)=3→∀ d:Σ v,G.neighborSet v,Q.Adj (transformerRimEndpoint G Q H₀ p d)
        (transformerSpokeEndpoint G Q H₀ b p d))→
      (∀ i:{e:V×U // H₀ e.1 e.2},(p (.inr i)).2.2.length=(m+1)-2)→
      (∀ i,∀ v∈(p i).2.2.support,v∈W∧v∉R)→
      (∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)→
      (∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w)→
      (∀ i,∀ v∈(p i).2.2.support,∀ w∈R,¬F.Adj v w)→
      (∀ e:G.edgeFinset,Q.Adj e.val.out.1 (p (.inl e)).1 ∧
        Q.Adj (φ e.val.out.1) (p (.inl e)).1 ∧ Q.Adj e.val.out.2 (p (.inl e)).2.1 ∧
        Q.Adj (φ e.val.out.2) (p (.inl e)).2.1)→
      (∀ e:{e:V×U // H₀ e.1 e.2},Q.Adj e.val.1 (p (.inr e)).1 ∧
        Q.Adj (φ e.val.1) (p (.inr e)).1 ∧ Q.Adj e.val.1 (p (.inr e)).2.1 ∧
        Q.Adj (φ e.val.1) (p (.inr e)).2.1)→
      (∀ v,(F.degree v:ℝ)≤d)→∀ c:ℝ,
      ((m+1)≠3→∀ u v w,c≤(((A.filter (fun x=>H x u))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      ((m+1)≠3→W.card+Fintype.card (Σ v,G.neighborSet v)*(m+1)+(((m+1):ℝ)+4)*(d+1)<c)→
      W.card+2*((m+1):ℝ)*Fintype.card (Σ v,G.neighborSet v)≤F₀→
      ∀ E:OrdinaryActualRimWheels G Q F H₀ H φ (m+1) B b σ p,
      ∀ S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ (m+1) p,
      ∃ N:Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
        N.card≤(m+1)*(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2}+Fintype.card (Σ v,G.neighborSet v))+nU*(t+(m+1)*q)∧
        IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=(m+1)))
          (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) K∧
        K⊆ordinaryHostResources Q H∧
        (∀ v v',Sum.inl s(v,v')∈K→v∈N∧v'∈N)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈N)∧
        (∀ v∈R,∀ v'∈R,Sum.inl s(v,v')∉K)∧
        (∀ v∈R,∀ a∈B,Sum.inr (v,a)∉K):=by
  have hr:3≤m+1:=by omega
  have hm:2≤(m+1)-1:=by omega
  have hmr:(m+1)-1+1=(m+1):=by omega
  have hh:=regular_host_indexed_hub_transformer_uniform_named_subgraph ((m+1)-1) hm α hα hα1
  try simp only [hmr] at hh
  obtain ⟨ξh,hξh,hbase⟩:=hh
  refine ⟨ξh/2,by positivity,?_⟩
  intro q nU
  obtain ⟨t,hbase⟩:=hbase q nU
  refine ⟨t,?_⟩
  intro F₀ d f hF₀ hd
  obtain ⟨N₁,hbase⟩:=hbase d f hd
  obtain ⟨N₂,hN₂⟩:=eventually_constant_le_linear F₀ (ξh/2) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro V U _ _ _ _ hn G Q GHost F Fdel Dhost hreg hdel hthreshold hQeq H₀ H hHnear φ ψ b σ hσ p A R W B hRW hbalance hdiv hq hnU hroot hcross hu
    hφQ hφedge hψedge hB hp hlen hrim3 hadj3 hslen hpW hdis hFF hFR hends hspends hF c hcount hbudget hWbudget E S
  have hstage:∃ D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H (m+1) d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d),
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
    let Z:U→Finset V:=transformerSpokeRows Q H₀ (fun i=>p (.inr i))
    (∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
      (transformerSpokeEndpoint G Q H₀ b p d),v∈A∧v∉W∧v≠φ d.1)∧
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Plus i)) (ordinaryWheelResources (Plus j)))∧
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Minus i)) (ordinaryWheelResources (Minus j)))∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim Plus) (wheelFamilySpokes Plus) (m+1)∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim Minus) (wheelFamilySpokes Minus) (m+1)∧
    ∀ e:Sym2 V⊕(V×U),
      (if e∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus) then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus) then 1 else 0)=
      (if e∈ordinaryHostResources G H₀ then 1 else 0)-(if e∈transformerImageResources G H₀ φ ψ then 1 else 0)+
      ∑ u:U,((if e∈(Z u).image (fun v=>Sum.inr (v,u)) then 1 else 0)-
        (if e∈(Z u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0)):=by
    by_cases hr3:(m+1)=3
    · have hm3:m=2:=by omega
      subst m
      obtain ⟨D,hD,hrest⟩:=triangular_transformer_vertex_stage_realization G Q F H₀ H φ ψ b σ hσ p R W B hRW
        hbalance hroot hcross hφQ hφedge hψedge hB (hrim3 rfl)
        (fun i=>⟨hp _,by rw [hslen];norm_num⟩) hpW hdis hFF hFR hends hspends (hadj3 rfl) E S
      exact ⟨D,(fun d v hv=>(hD d v hv).elim),hrest⟩
    · exact ordinary_transformer_vertex_stage_realization
        G Q F H₀ H φ ψ b σ hσ p A R W B hRW hbalance hroot hcross hφQ hφedge hψedge hB
        hp (hlen hr3) hpW hdis hFF hFR hends hspends (m+1) (by omega) d c hd hF (hcount hr3) (by simpa only [Nat.cast_add,Nat.cast_one] using hbudget hr3) E S
  obtain ⟨D,hD,hPlus,hMinus,_,_,hid⟩:=hstage
  let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
  let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
  obtain ⟨W',hWW',hW'card,hPW',hMW'⟩:=ordinary_transformer_row_buffer G Q F H₀ H φ ψ (m+1) R W B hRW b σ p
    hbalance hroot (fun i v hv=>(hpW i v hv).1) E S D
  let Z:U→Finset V:=transformerSpokeRows Q H₀ (fun i=>p (.inr i))
  have hHp (i:{e:V×U // H₀ e.1 e.2}) (v:V) (hv:v∈(p (.inr i)).2.2.support):H v i.val.2∧H v (ψ i.val.2):=by
    have h₁:H v (ordinaryWheelHub (S.first i)):=(S.first i).property.1 v ((S.first_support i v).mpr (Or.inr hv))
    have h₂:H v (ordinaryWheelHub (S.second i)):=(S.second i).property.1 v ((S.second_support i v).mpr (Or.inr hv))
    rw [S.first_hub] at h₁
    rw [S.second_hub] at h₂
    exact ⟨h₁,h₂⟩
  have hZ:=ordinary_transformer_spoke_sets Q F H₀ H ψ (m+1) (by omega) (fun i=>p (.inr i))
    (fun i=>⟨hp _,hslen i⟩) (fun i j hij=>hdis (.inr i) (.inr j) (fun he=>hij (Sum.inr.inj he)))
    (fun i j=>hFF (.inr i) (.inr j)) hHp hdiv
  change (∀ u,(Z u).card=((m+1)-1)*((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)∧
    (∀ u,(m+1)∣(Z u).card)∧(∀ u u',u≠u'→Disjoint (Z u) (Z u'))∧_ at hZ
  let I:={u:U // ∃ v,H₀ v u}
  let z:I→ℕ:=fun i=>(Z i.val).card/(m+1)
  have hZcard (i:I):(Z i.val).card=(m+1)*z i:=(Nat.mul_div_cancel' (hZ.2.1 i.val)).symm
  have hz (i:I):z i≤q:=by
    have hz':z i≤((Finset.univ:Finset V).filter (fun v=>H₀ v i.val)).card:=by
      have hh:=(hZ.1 i.val).symm.trans (hZcard i)
      have hr1:(m+1)-1+1=(m+1):=by omega
      nlinarith
    exact hz'.trans (hq i.val)
  have hZW (i:I):Z i.val⊆W':=by
    intro v hv
    obtain ⟨e,_,he⟩:=(transformerSpokeRows_mem Q H₀ _ i.val v).mp hv
    exact hWW' (hpW _ _ he).1
  have hW'bound:(W'.card:ℝ)≤F₀:=by
    have hc:(W'.card:ℝ)≤W.card+2*((m+1):ℝ)*Fintype.card (Σ v,G.neighborSet v):=by exact_mod_cast hW'card
    exact hc.trans hWbudget
  have hsp:=ordinary_transformer_hub_trade_spoke_avoidance G Q F H₀ H φ ψ (m+1) R B b σ p
    hbalance hroot (fun i v hv=>(hpW i v hv).2) hdis hB hu E S D
  have hidentity:∀ e,
      (if e∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus) then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus) then 1 else 0)=
      (if e∈ordinaryHostResources G H₀ then 1 else 0)-(if e∈transformerImageResources G H₀ φ ψ then 1 else 0)+
      ∑ i:I,((if e∈(Z i.val).image (fun v=>Sum.inr (v,i.val)) then 1 else 0)-
        (if e∈(Z i.val).image (fun v=>Sum.inr (v,ψ i.val)) then 1 else 0)):=by
    intro e
    rw [hid e]
    exact congrArg ((if e∈ordinaryHostResources G H₀ then (1:ℤ) else 0)-
      (if e∈transformerImageResources G H₀ φ ψ then 1 else 0)+·)
      (transformerSpokeRows_active_sum Q H₀ ψ (fun i=>p (.inr i)) e)
  have hW'budget:(W'.card:ℝ)≤ξh*Fintype.card V:=by
    have hh:=hN₂ (Fintype.card V) (by omega)
    have hn0:(0:ℝ)≤Fintype.card V:=by positivity
    nlinarith [hW'bound]
  have hHnear':∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ξh*Fintype.card V:=by
    intro u
    have hh:=hHnear u
    have hn0:(0:ℝ)≤Fintype.card V:=by positivity
    nlinarith
  have hbase' := hbase V U I (G.edgeFinset⊕({e:V×U // H₀ e.1 e.2}⊕(Σ v,G.neighborSet v)))
      (by omega) hnU GHost F Fdel Dhost hreg hdel hF Q hQeq H (fun i=>i.val) (fun i=>ψ i.val)
      W' (fun i=>Z i.val) z (fun i=>hu i.val i.property) hz hZcard hZW
      (fun i j hij=>hZ.2.2.1 i.val j.val (fun he=>hij (Subtype.ext he)))
      (fun i=>hZ.2.2.2.1 i.val) (fun i=>hZ.2.2.2.2 i.val)
      (fun i=>hHnear' i.val) (fun i=>hHnear' (ψ i.val)) hW'budget hthreshold
  try simp only [hmr] at hbase'
  obtain ⟨Anew,K,hAnew,hAsep,hAconf,hK,hKQ,hnewR,hnewS,hExactR,hExactS⟩:=
    hbase' Plus Minus hPlus hMinus hPW' hMW' (fun i=>hsp i.val)
      (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ)
      (transformer_root_resources_disjoint G H₀ φ ψ hbalance hcross) hidentity
  have hold:=ordinary_transformer_positive_root_restriction G Q F H₀ H φ ψ (m+1) R W B hRW b σ p
    (fun i v hv=>(hpW i v hv).2) E S D (fun i v hv=>(hD i v hv).2.1)
  let Zall:=Finset.univ.biUnion (fun i:I=>Z i.val)
  let Nfresh:=Finset.univ.biUnion Anew
  let Nall:=(wheelFamilyRim Plus).support.toFinset∪Nfresh∪Zall
  have hZall:Zall.card≤nU*((m+1)*q):=by
    calc
      Zall.card≤∑ i:I,(Z i.val).card:=Finset.card_biUnion_le
      _≤∑ _i:I,((m+1)*q):=Finset.sum_le_sum (fun i _=>by rw [hZcard];exact Nat.mul_le_mul_left _ (hz i))
      _=Fintype.card I*((m+1)*q):=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
      _≤nU*((m+1)*q):=Nat.mul_le_mul_right _ hnU
  have hNfresh:Nfresh.card≤nU*t:=by
    calc
      Nfresh.card≤∑ i:I,(Anew i).card:=Finset.card_biUnion_le
      _≤∑ _i:I,t:=Finset.sum_le_sum (fun i _=>(hAnew i).1)
      _=Fintype.card I*t:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
      _≤nU*t:=Nat.mul_le_mul_right _ hnU
  have hNW:Disjoint Nfresh W':=by
    apply Finset.disjoint_left.mpr
    intro v hv hvW
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hAnew i).2 hi hvW
  refine ⟨Nall,K,?_,hK,hKQ,hExactR,hExactS,?_,?_⟩
  · have hc:=(wheelFamily_vertex_bound Plus).1
    simp only [Fintype.card_sum,Fintype.card_coe] at hc
    have h₁:=Finset.card_union_le (wheelFamilyRim Plus).support.toFinset Nfresh
    have h₂:=Finset.card_union_le ((wheelFamilyRim Plus).support.toFinset∪Nfresh) Zall
    dsimp only [Nall]
    nlinarith only [hc,h₁,h₂,hNfresh,hZall]
  · intro v hv v' hv' he
    rcases hnewR v v' he with heP|⟨i,hi|hi⟩
    · have hG:=hold.1 v hv v' hv' ((ordinaryHostResources_rim _ _ _).mp heP)
      exact Finset.disjoint_left.mp hK.1 he ((ordinaryHostResources_rim G H₀ _).mpr hG)
    · have hvN:v∈Nfresh:=Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩
      exact Finset.disjoint_left.mp hNW hvN (hWW' (hRW hv))
    · have hvN:v'∈Nfresh:=Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩
      exact Finset.disjoint_left.mp hNW hvN (hWW' (hRW hv'))
  · intro v hv a ha he
    rcases hnewS v a he with heP|⟨i,hi|hi⟩
    · have hH:=hold.2 v hv a ha ((ordinaryHostResources_spoke _ _ _ _).mp heP)
      exact Finset.disjoint_left.mp hK.1 he ((ordinaryHostResources_spoke G H₀ v a).mpr hH)
    · have hvN:v∈Nfresh:=Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩
      exact Finset.disjoint_left.mp hNW hvN (hWW' (hRW hv))
    · obtain ⟨j,_,hj⟩:=(transformerSpokeRows_mem Q H₀ _ i.val v).mp hi
      exact (hpW _ _ hj).2 hv
end Oberwolfach
