module

public import Oberwolfach.TriangleSelectedTradeAssembly
public import Oberwolfach.TriangleTransformerVertexStage
public import Oberwolfach.OrdinaryTransformerRowBuffer
public import Oberwolfach.OrdinaryTransformerRootRestriction
public import Oberwolfach.OrdinaryTransformerVertexAvoidance

@[expose] public section
/-! Connect the actual triangle vertex wheels to the near-complete hub
trades and their signed-resource assembly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option synthInstance.maxSize 2048
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_vertex_wheels_and_hub_trades_complete
    (K₀ L:ℕ) (β:ℝ) (hβ:0<β) (hβ1:β≤1):
    ∃ s₀:ℕ,∀ s:ℕ,s₀≤s→3∣s→∃ N₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→∀ (G Q:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (R W:Finset V) (B:Finset U) (hRW:R⊆W)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hdiv:∀ u,3∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)
    (hsize:∀ u,2*((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤L)
    (hactive:Fintype.card {u:U // ∃v,H₀ v u}≤K₀)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hu:∀ u,(∃v,H₀ v u)→u≠ψ u)
    (hφQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hφedge:Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2)))
    (hψedge:Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2)))
    (hB:∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)
    (hrim:∀ e:G.edgeFinset,(p (.inl e)).2.2.length=0)
    (hsp:∀ e:{e:V×U // H₀ e.1 e.2},(p (.inr e)).2.2.IsPath∧(p (.inr e)).2.2.length=1)
    (hpW:∀ i,∀ v∈(p i).2.2.support,v∈W∧v∉R)
    (W₀:Finset V) (hW₀:W₀⊆W) (hp₀:∀ i,∀ v∈(p i).2.2.support,v∉W₀)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (hends:∀ e:G.edgeFinset,Q.Adj e.val.out.1 (p (.inl e)).1 ∧
      Q.Adj (φ e.val.out.1) (p (.inl e)).1 ∧ Q.Adj e.val.out.2 (p (.inl e)).2.1 ∧
      Q.Adj (φ e.val.out.2) (p (.inl e)).2.1)
    (hspends:∀ e:{e:V×U // H₀ e.1 e.2},Q.Adj e.val.1 (p (.inr e)).1 ∧
      Q.Adj (φ e.val.1) (p (.inr e)).1 ∧ Q.Adj e.val.1 (p (.inr e)).2.1 ∧
      Q.Adj (φ e.val.1) (p (.inr e)).2.1)
    (hab:∀ d:Σ v,G.neighborSet v,Q.Adj
      (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d))
    (E:OrdinaryActualRimWheels G Q ⊥ H₀ H φ 3 B b σ p)
    (S:OrdinaryActualSpokeWheels G Q ⊥ H₀ H φ ψ 3 p)
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))
    (ε:ℝ) (hnear:∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))
    (hbudget:2*ε*(Fintype.card V:ℝ)+((W.card+6*Fintype.card (Σ v,G.neighborSet v):ℕ):ℝ)
      ≤(β/4)*(Fintype.card V:ℝ)),
    ∃ W' N:Finset V,∃ T:Finset (Sym2 V⊕(V×U)),
      W⊆W' ∧ W'.card≤W.card+6*Fintype.card (Σ v,G.neighborSet v) ∧
      Disjoint N W' ∧ N.card≤K₀*s ∧
      IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) T ∧
      (∀ v w,Sum.inl s(v,w)∈T→v∈W'∪N∧w∈W'∪N) ∧
      (∀ v z,Sum.inr (v,z)∈T→v∈W'∪N) ∧
      (∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉T) ∧
      (∀ v∈R,∀ z∈B,Sum.inr (v,z)∉T) ∧
      (∀ v∈W₀,∀ w,Sum.inl s(v,w)∈T→v∈R) ∧
      (∀ v∈W₀,∀ z,Sum.inr (v,z)∈T→v∈R) ∧
      (∀ v z,z∈B→Sum.inr (v,z)∈T→∃ u,(∃x,H₀ x u) ∧ (z=u∨z=ψ u)) ∧
      (∀ v z,Sum.inr (v,z)∈T→(∃ e:G.edgeFinset,z=E.hub e)∨∃ u,(∃x,H₀ x u) ∧ (z=u∨z=ψ u)) :=by
  obtain ⟨s₀,hs⟩:=triangular_transformer_simultaneous_wheel_trades K₀ L β hβ hβ1
  refine ⟨s₀,?_⟩
  intro s hs₀ hsdiv
  obtain ⟨N₀,hN₀⟩:=hs s hs₀ hsdiv
  refine ⟨N₀,?_⟩
  intro V U _ _ _ _ hn G Q H₀ H φ ψ b σ hσ p R W B hRW hbalance hdiv hsize hactive
    hroot hcross hu hφQ hφedge hψedge hB hrim hsp hpW W₀ hW₀ hp₀ hdis hends hspends hab E S hdeg ε hnear hbudget
  obtain ⟨D,hD,hPlus,hMinus,_,_,hid⟩:=triangular_transformer_vertex_stage_realization G Q ⊥ H₀ H φ ψ b σ hσ p R W B hRW
    hbalance hroot hcross hφQ hφedge hψedge hB hrim
    (by intro e;exact ⟨(hsp e).1,by rw [(hsp e).2];norm_num⟩) hpW hdis
    (by intro i j v hv w hw;simp) (by intro i v hv w hw;simp) hends hspends hab E S
  let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
  let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
  obtain ⟨W',hWW',hW'card,hPW,hMW⟩:=ordinary_transformer_row_buffer G Q ⊥ H₀ H φ ψ 3 R W B hRW b σ p
    hbalance hroot (fun i v hv=>(hpW i v hv).1) E S D
  let I:Type:={u:U // ∃v,H₀ v u}
  let ι:I↪U:=⟨Subtype.val,Subtype.val_injective⟩
  let ps: {e:V×U // H₀ e.1 e.2}→(Σ a:V,Σ c:V,Q.Walk a c):=fun i=>p (.inr i)
  let Z:U→Finset V:=transformerSpokeRows Q H₀ ps
  have hHp (i:{e:V×U // H₀ e.1 e.2}) (v:V) (hv:v∈(ps i).2.2.support):H v i.val.2∧H v (ψ i.val.2):=by
    have h₁:H v (ordinaryWheelHub (S.first i)):=(S.first i).property.1 v ((S.first_support i v).mpr (Or.inr hv))
    have h₂:H v (ordinaryWheelHub (S.second i)):=(S.second i).property.1 v ((S.second_support i v).mpr (Or.inr hv))
    rw [S.first_hub] at h₁
    rw [S.second_hub] at h₂
    exact ⟨h₁,h₂⟩
  have hZW (i:I):Z i.val⊆W':=by
    intro v hv
    obtain ⟨e,_,he⟩:=(transformerSpokeRows_mem Q H₀ ps i.val v).mp hv
    exact hWW' (hpW _ _ he).1
  have hbudget':2*ε*(Fintype.card V:ℝ)+(W'.card:ℝ)≤(β/4)*(Fintype.card V:ℝ):=by
    have hc:(W'.card:ℝ)≤((W.card+6*Fintype.card (Σ v,G.neighborSet v):ℕ):ℝ):=by exact_mod_cast hW'card
    linarith
  obtain ⟨A,RR,hA,hpair,_,_⟩:=hN₀ V U I hn hactive ι Q Q ⊥ H₀ H ψ ps
    (by intro i;simpa [ps] using hsp i)
    (by intro i j hij;exact hdis (.inr i) (.inr j) (fun h=>hij (Sum.inr.inj h)))
    (by intro i j v hv w hw;simp) hHp hdiv hsize hdeg W' ε hnear hbudget'
    (by intro i;exact hZW i) (by intro i;exact hu i.val i.property)
  have hspokes:=ordinary_transformer_hub_trade_spoke_avoidance G Q ⊥ H₀ H φ ψ 3 R B b σ p
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
      (transformerSpokeRows_active_sum Q H₀ ψ ps e)
  obtain ⟨N,T,hNW,hNcard,hT,hRsupport,hSsupport,hnewR,hnewS,hExactR,hHub⟩:=triangle_selected_hub_trades_finish Q H A
    (fun i:I=>Z i.val) (fun i=>i.val) (fun i=>ψ i.val) RR W' s K₀ hactive
    (fun i=>⟨(hA i).1,(hA i).2.1⟩) hZW hpair (fun i=>(hA i).2.2.2)
    Plus Minus hPlus hMinus hPW hMW (fun i=>hspokes i.val)
    (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ)
    (transformer_root_resources_disjoint G H₀ φ ψ hbalance hcross) hidentity
  have hold:=ordinary_transformer_positive_root_restriction G Q ⊥ H₀ H φ ψ 3 R W B hRW b σ p
    (fun i v hv=>(hpW i v hv).2) E S D (fun i v hv=>(hD i v hv).elim)
  have hpositive:=ordinary_transformer_positive_row_avoidance G Q ⊥ H₀ H φ ψ 3 R W W₀ B hW₀ b σ p
    hbalance hroot hp₀ E S D (fun i v hv=>(hD i v hv).elim)
  refine ⟨W',N,T,hWW',by simpa using hW'card,hNW,hNcard,hT,hRsupport,hSsupport,?_,?_,?_,?_,?_,?_⟩
  · intro v hv w hw he
    rcases hnewR v w he with heP|hn|hn
    · have hG:=hold.1 v hv w hw ((ordinaryHostResources_rim _ _ _).mp heP)
      exact Finset.disjoint_left.mp hT.1 he ((ordinaryHostResources_rim G H₀ _).mpr hG)
    · exact Finset.disjoint_left.mp hNW hn (hWW' (hRW hv))
    · exact Finset.disjoint_left.mp hNW hn (hWW' (hRW hw))
  · intro v hv z hz he
    rcases hnewS v z he with heP|hn|⟨i,hi⟩
    · have hH:=hold.2 v hv z hz ((ordinaryHostResources_spoke _ _ _ _).mp heP)
      exact Finset.disjoint_left.mp hT.1 he ((ordinaryHostResources_spoke G H₀ v z).mpr hH)
    · exact Finset.disjoint_left.mp hNW hn (hWW' (hRW hv))
    · obtain ⟨j,_,hj⟩:=(transformerSpokeRows_mem Q H₀ ps i.val v).mp hi
      exact (hpW _ _ hj).2 hv
  · intro v hv w he
    rcases (hExactR v w he).1 with heP|hn|⟨i,hi⟩
    · obtain ⟨w',hw'⟩:=Set.mem_toFinset.mp heP
      obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hw'
      exact hpositive j v hj.mem_support_left hv
    · exact (Finset.disjoint_left.mp hNW hn (hWW' (hW₀ hv))).elim
    · obtain ⟨j,_,hj⟩:=(transformerSpokeRows_mem Q H₀ ps i.val v).mp hi
      exact (hp₀ _ _ hj hv).elim
  · intro v hv z he
    rcases hnewS v z he with heP|hn|⟨i,hi⟩
    · obtain ⟨j,_,hj⟩:=(ordinaryHostResources_spoke _ _ _ _).mp heP
      exact hpositive j v hj hv
    · exact (Finset.disjoint_left.mp hNW hn (hWW' (hW₀ hv))).elim
    · obtain ⟨j,_,hj⟩:=(transformerSpokeRows_mem Q H₀ ps i.val v).mp hi
      exact (hp₀ _ _ hj hv).elim
  · intro v z hz he
    rcases hHub v z he with heP|⟨i,hi⟩
    · obtain ⟨j,hj,_⟩:=heP
      rcases j with j|(j|j)
      · change ordinaryWheelHub (E.first j)=z at hj
        rw [E.first_hub] at hj
        exact (E.hub_avoid j (hj.symm ▸ hz)).elim
      · change ordinaryWheelHub (S.first j)=z at hj
        rw [S.first_hub] at hj
        exact ⟨j.val.2,⟨j.val.1,j.property⟩,Or.inl hj.symm⟩
      · change ordinaryWheelHub (D j).second=z at hj
        rw [(D j).second_hub] at hj
        exact (E.hub_avoid _ (hj.symm ▸ hz)).elim
    · exact ⟨i.val,i.property,hi⟩
  · intro v z he
    rcases hHub v z he with heP|⟨i,hi⟩
    · obtain ⟨j,hj,_⟩:=heP
      rcases j with j|(j|j)
      · change ordinaryWheelHub (E.first j)=z at hj
        rw [E.first_hub] at hj
        exact Or.inl ⟨j,hj.symm⟩
      · change ordinaryWheelHub (S.first j)=z at hj
        rw [S.first_hub] at hj
        exact Or.inr ⟨j.val.2,⟨j.val.1,j.property⟩,Or.inl hj.symm⟩
      · change ordinaryWheelHub (D j).second=z at hj
        rw [(D j).second_hub] at hj
        exact Or.inl ⟨(shiftedIncidenceEquiv G σ j).1,hj.symm⟩
    · exact Or.inr ⟨i.val,i.property,hi⟩
end Oberwolfach
