module

public import Oberwolfach.TriangleTransformerVertexStage
public import Oberwolfach.OrdinaryTransformerRowLocation
public import Oberwolfach.OrdinaryProfileTransformerCompletion
public import Oberwolfach.OrdinaryTransformerRowBuffer
public import Oberwolfach.OrdinaryTransformerRootRestriction
public import Oberwolfach.OrdinaryTransformerVertexAvoidance

@[expose] public section

/-! Construct the vertex wheels and hub trades over the actual previously
chosen paths and edge-wheel pairs. The resulting transformer uses only
wheels in the supplied host with the supplied forbidden-pair condition.
The profile coefficients are never recomputed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option synthInstance.maxSize 512
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem ordinary_transformer_from_paths_and_profiles (r:ℕ) (hr:3≤r)
    (Tpls:Tpl→VertexAbsorberTemplate r) (α b₀ B₀:ℝ) (hα:0<α) (hb₀:0<b₀) (hB₀:0<B₀):
    ∃ η:ℝ,0<η∧∀ q nU:ℕ,∃ t:ℕ,1≤t∧∀ F₀ d:ℝ,0≤F₀→0≤d→
      ∃ k₀:ℝ,1<k₀∧
      ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
      (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
      (σ:∀ v,Equiv.Perm (G.neighborSet v)),(∀ v w,σ v w≠w)→
      ∀ p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c),
      ∀ (A R W:Finset V) (B:Finset U),R⊆W→
      (∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)→
      (∀ u,r∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)→
      (∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤q)→
      Fintype.card {u:U // ∃ v,H₀ v u}≤nU→
      (∀ v∈G.support,v∈R∧φ v∈R)→
      (∀ v∈G.support,∀ w∈G.support,φ v≠w)→
      (∀ u,(∃ v,H₀ v u)→u≠ψ u)→
      (∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→
      Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2))→
      Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2))→
      (∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)→
      (∀ i,(p i).2.2.IsPath)→(r≠3→∀ i,0<(p i).2.2.length)→
      (r=3→∀ e:G.edgeFinset,(p (.inl e)).2.2.length=0)→
      (r=3→∀ d:Σ v,G.neighborSet v,Q.Adj (transformerRimEndpoint G Q H₀ p d)
        (transformerSpokeEndpoint G Q H₀ b p d))→
      (∀ i:{e:V×U // H₀ e.1 e.2},(p (.inr i)).2.2.length=r-2)→
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
      (r≠3→∀ u v w,c≤(((A.filter (fun x=>H x u))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (r≠3→W.card+Fintype.card (Σ v,G.neighborSet v)*r+((r:ℝ)+4)*(d+1)<c)→
      W.card+2*(r:ℝ)*Fintype.card (Σ v,G.neighborSet v)≤F₀→
      ∀ E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p,
      ∀ S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p,
      ∀ (T:{u:U // ∃ v,H₀ v u}→Finset V) (k:{u:U // ∃ v,H₀ v u}→ℝ),
      (∀ i,k₀≤k i)→(∀ i,∀ v∈T i,H v i.val∧H v (ψ i.val))→
      (∀ i,((T i).card:ℝ)=r*k i)→
      (∀ i,transformerSpokeRows Q H₀ (fun e=>p (.inr e)) i.val⊆T i)→
      ∀ w:∀ i,LocalOrdinaryCycle Q F (T i) r→ℝ,
      (∀ i C,b₀/(k i)^(r-1)≤w i C∧w i C≤B₀/(k i)^(r-1))→
      (∀ i,∀ v∈T i,|1-hypergraphWeightedDegree localOrdinaryVertices (w i) v|≤η)→
      (∀ i,∀ X:Finset V,X⊆T i→X.card=r→α*(k i)^(r*r)≤
        Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T i) (r:=r)) Tpls X))→
      ∃ N:Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
        N.card≤r*(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2}+Fintype.card (Σ v,G.neighborSet v))+nU*r*(t+q)∧
        IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) K∧
        K⊆ordinaryHostResources Q H∧
        (∀ v v',Sum.inl s(v,v')∈K→v∈N∧v'∈N)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈N)∧
        (∀ v∈R,∀ v'∈R,Sum.inl s(v,v')∉K)∧
        (∀ v∈R,∀ a∈B,Sum.inr (v,a)∉K)∧
        ∃ B':Finset U,B'.card≤G.edgeFinset.card+2*nU∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B')∧
          (∀ W₀:Finset V,W₀⊆W→(∀ i,∀ v∈(p i).2.2.support,v∉W₀)→
            (∀ v∈W₀,∀ v',Sum.inl s(v,v')∈K→v∈R)∧
            (∀ v∈W₀,∀ a,Sum.inr (v,a)∈K→v∈R))∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B→∃ i:{u:U // ∃ v,H₀ v u},a=i.val∨a=ψ i.val)∧
          ((∀ i,T i⊆A)→(∀ i,∀ v∈(p i).2.2.support,v∈A)→N⊆R∪A):=by
  obtain ⟨η,hη,hbase⟩:=ordinary_profile_transformer_completion r (by omega) Tpls α b₀ B₀ hα hb₀ hB₀
  refine ⟨η,hη,?_⟩
  intro q nU
  obtain ⟨t,ht,hbase⟩:=hbase q nU
  refine ⟨t,ht,?_⟩
  intro F₀ d hF₀ hd
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ d hF₀ hd
  refine ⟨k₀,hk₀,?_⟩
  intro V U _ _ _ _ G Q F H₀ H φ ψ b σ hσ p A R W B hRW hbalance hdiv hq hnU hroot hcross hu
    hφQ hφedge hψedge hB hp hlen hrim3 hadj3 hslen hpW hdis hFF hFR hends hspends hF c hcount hbudget hWbudget E S T k hk hTsp hT hZT w hw herr habs
  have hstage:∃ D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d),
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
    let Z:U→Finset V:=transformerSpokeRows Q H₀ (fun i=>p (.inr i))
    (∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
      (transformerSpokeEndpoint G Q H₀ b p d),v∈A∧v∉W∧v≠φ d.1)∧
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Plus i)) (ordinaryWheelResources (Plus j)))∧
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Minus i)) (ordinaryWheelResources (Minus j)))∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim Plus) (wheelFamilySpokes Plus) r∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim Minus) (wheelFamilySpokes Minus) r∧
    ∀ e:Sym2 V⊕(V×U),
      (if e∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus) then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus) then 1 else 0)=
      (if e∈ordinaryHostResources G H₀ then 1 else 0)-(if e∈transformerImageResources G H₀ φ ψ then 1 else 0)+
      ∑ u:U,((if e∈(Z u).image (fun v=>Sum.inr (v,u)) then 1 else 0)-
        (if e∈(Z u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0)):=by
    by_cases hr3:r=3
    · subst r
      obtain ⟨D,hD,hrest⟩:=triangular_transformer_vertex_stage_realization G Q F H₀ H φ ψ b σ hσ p R W B hRW
        hbalance hroot hcross hφQ hφedge hψedge hB (hrim3 rfl)
        (fun i=>⟨hp _,by rw [hslen];norm_num⟩) hpW hdis hFF hFR hends hspends (hadj3 rfl) E S
      exact ⟨D,(fun d v hv=>(hD d v hv).elim),hrest⟩
    · exact ordinary_transformer_vertex_stage_realization
        G Q F H₀ H φ ψ b σ hσ p A R W B hRW hbalance hroot hcross hφQ hφedge hψedge hB
        hp (hlen hr3) hpW hdis hFF hFR hends hspends r (by omega) d c hd hF (hcount hr3) (hbudget hr3) E S
  obtain ⟨D,hD,hPlus,hMinus,_,_,hid⟩:=hstage
  let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
  let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
  obtain ⟨W',hWW',hW'card,hPW',hMW'⟩:=ordinary_transformer_row_buffer G Q F H₀ H φ ψ r R W B hRW b σ p
    hbalance hroot (fun i v hv=>(hpW i v hv).1) E S D
  let Z:U→Finset V:=transformerSpokeRows Q H₀ (fun i=>p (.inr i))
  have hHp (i:{e:V×U // H₀ e.1 e.2}) (v:V) (hv:v∈(p (.inr i)).2.2.support):H v i.val.2∧H v (ψ i.val.2):=by
    have h₁:H v (ordinaryWheelHub (S.first i)):=(S.first i).property.1 v ((S.first_support i v).mpr (Or.inr hv))
    have h₂:H v (ordinaryWheelHub (S.second i)):=(S.second i).property.1 v ((S.second_support i v).mpr (Or.inr hv))
    rw [S.first_hub] at h₁
    rw [S.second_hub] at h₂
    exact ⟨h₁,h₂⟩
  have hZ:=ordinary_transformer_spoke_sets Q F H₀ H ψ r (by omega) (fun i=>p (.inr i))
    (fun i=>⟨hp _,hslen i⟩) (fun i j hij=>hdis (.inr i) (.inr j) (fun he=>hij (Sum.inr.inj he)))
    (fun i j=>hFF (.inr i) (.inr j)) hHp hdiv
  change (∀ u,(Z u).card=(r-1)*((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)∧
    (∀ u,r∣(Z u).card)∧(∀ u u',u≠u'→Disjoint (Z u) (Z u'))∧_ at hZ
  let I:={u:U // ∃ v,H₀ v u}
  let z:I→ℕ:=fun i=>(Z i.val).card/r
  have hZcard (i:I):(Z i.val).card=r*z i:=(Nat.mul_div_cancel' (hZ.2.1 i.val)).symm
  have hz (i:I):z i≤q:=by
    have hz':z i≤((Finset.univ:Finset V).filter (fun v=>H₀ v i.val)).card:=by
      have hh:=(hZ.1 i.val).symm.trans (hZcard i)
      have hr1:r-1+1=r:=by omega
      nlinarith
    exact hz'.trans (hq i.val)
  have hZW (i:I):Z i.val⊆W':=by
    intro v hv
    obtain ⟨e,_,he⟩:=(transformerSpokeRows_mem Q H₀ _ i.val v).mp hv
    exact hWW' (hpW _ _ he).1
  have hW'bound:(W'.card:ℝ)≤F₀:=by
    have hc:(W'.card:ℝ)≤W.card+2*(r:ℝ)*Fintype.card (Σ v,G.neighborSet v):=by exact_mod_cast hW'card
    exact hc.trans hWbudget
  have hsp:=ordinary_transformer_hub_trade_spoke_avoidance G Q F H₀ H φ ψ r R B b σ p
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
  obtain ⟨N,K,hNW,hNcard,hK,hKQ,_hKr,_hKs,hnewR,hnewS,hExactR,hExactS,hHub,hNT⟩:=hbase V U I
    (G.edgeFinset⊕({e:V×U // H₀ e.1 e.2}⊕(Σ v,G.neighborSet v))) hnU Q F H T (fun i=>Z i.val)
    (fun i=>i.val) (fun i=>ψ i.val) k z W' hk (fun i=>hu i.val i.property) hTsp hT hF
    w hw herr habs hW'bound hZT hZW hZcard hz
    (fun i j hij=>hZ.2.2.1 i.val j.val (fun he=>hij (Subtype.ext he)))
    Plus Minus hPlus hMinus hPW' hMW' (fun i=>hsp i.val)
    (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ)
    (transformer_root_resources_disjoint G H₀ φ ψ hbalance hcross) hidentity
  have hold:=ordinary_transformer_positive_root_restriction G Q F H₀ H φ ψ r R W B hRW b σ p
    (fun i v hv=>(hpW i v hv).2) E S D (fun i v hv=>(hD i v hv).2.1)
  let Zall:=Finset.univ.biUnion (fun i:I=>Z i.val)
  let Nall:=(wheelFamilyRim Plus).support.toFinset∪N∪Zall
  have hZall:Zall.card≤nU*(r*q):=by
    calc
      Zall.card≤∑ i:I,(Z i.val).card:=Finset.card_biUnion_le
      _≤∑ _i:I,(r*q):=Finset.sum_le_sum (fun i _=>by rw [hZcard];exact Nat.mul_le_mul_left _ (hz i))
      _=Fintype.card I*(r*q):=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
      _≤nU*(r*q):=Nat.mul_le_mul_right _ hnU
  refine ⟨Nall,K,?_,hK,hKQ,hExactR,hExactS,?_,?_,?_⟩
  · have hc:=(wheelFamily_vertex_bound Plus).1
    simp only [Fintype.card_sum,Fintype.card_coe] at hc
    have h₁:=Finset.card_union_le (wheelFamilyRim Plus).support.toFinset N
    have h₂:=Finset.card_union_le ((wheelFamilyRim Plus).support.toFinset∪N) Zall
    dsimp only [Nall]
    nlinarith only [hc,h₁,h₂,hNcard,hZall]
  · intro v hv v' hv' he
    rcases hnewR v v' he with heP|hn|hn
    · have hG:=hold.1 v hv v' hv' ((ordinaryHostResources_rim _ _ _).mp heP)
      exact Finset.disjoint_left.mp hK.1 he ((ordinaryHostResources_rim G H₀ _).mpr hG)
    · exact Finset.disjoint_left.mp hNW hn (hWW' (hRW hv))
    · exact Finset.disjoint_left.mp hNW hn (hWW' (hRW hv'))
  · intro v hv a ha he
    rcases hnewS v a he with heP|hn|⟨i,hi⟩
    · have hH:=hold.2 v hv a ha ((ordinaryHostResources_spoke _ _ _ _).mp heP)
      exact Finset.disjoint_left.mp hK.1 he ((ordinaryHostResources_spoke G H₀ v a).mpr hH)
    · exact Finset.disjoint_left.mp hNW hn (hWW' (hRW hv))
    · obtain ⟨j,_,hj⟩:=(transformerSpokeRows_mem Q H₀ _ i.val v).mp hi
      exact (hpW _ _ hj).2 hv

  · let B':=(Finset.univ.image E.hub)∪(Finset.univ.image (fun i:I=>i.val))∪
      (Finset.univ.image (fun i:I=>ψ i.val))
    have hE (i:G.edgeFinset):E.hub i∈B':=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    have hO (i:I):i.val∈B':=
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    have hI (i:I):ψ i.val∈B':=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    refine ⟨B',?_,?_,?_,?_,?_⟩
    · have h₁:=Finset.card_union_le (Finset.univ.image E.hub) (Finset.univ.image (fun i:I=>i.val))
      have h₂:=Finset.card_union_le
        ((Finset.univ.image E.hub)∪(Finset.univ.image (fun i:I=>i.val))) (Finset.univ.image (fun i:I=>ψ i.val))
      have he:(Finset.univ.image E.hub).card≤G.edgeFinset.card:=by
        simpa only [Finset.card_univ,Fintype.card_coe] using (Finset.card_image_le (s:=(Finset.univ:Finset G.edgeFinset)) (f:=E.hub))
      have ho:(Finset.univ.image (fun i:I=>i.val)).card≤nU:=
        (Finset.card_image_le).trans (by simpa only [Finset.card_univ] using hnU)
      have hi:(Finset.univ.image (fun i:I=>ψ i.val)).card≤nU:=
        (Finset.card_image_le).trans (by simpa only [Finset.card_univ] using hnU)
      dsimp only [B']
      omega
    · intro v a ha
      rcases hHub v a ha with hp|⟨i,hi⟩
      · obtain ⟨j,hj,_⟩:=hp
        rcases j with j|(j|j)
        · change ordinaryWheelHub (E.first j)=a at hj
          rw [E.first_hub] at hj
          exact hj ▸ hE j
        · change ordinaryWheelHub (S.first j)=a at hj
          rw [S.first_hub] at hj
          exact hj ▸ hO ⟨j.val.2,⟨j.val.1,j.property⟩⟩
        · change ordinaryWheelHub (D j).second=a at hj
          rw [(D j).second_hub] at hj
          exact hj ▸ hE _
      · rcases hi with hi|hi
        · exact hi.symm ▸ hO i
        · exact hi.symm ▸ hI i

    · intro W₀ hW₀ hp₀
      have hpositive:=ordinary_transformer_positive_row_avoidance G Q F H₀ H φ ψ r R W W₀ B hW₀ b σ p
        hbalance hroot hp₀ E S D (fun i v hv=>(hD i v hv).2.1)
      have hrows (v:V) (hv:v∈(wheelFamilyRim Plus).support.toFinset∪N∪Zall) (hv₀:v∈W₀):v∈R:=by
        rcases Finset.mem_union.mp hv with hv|hv
        · rcases Finset.mem_union.mp hv with hv|hv
          · obtain ⟨w,hw⟩:=Set.mem_toFinset.mp hv
            obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp hw
            exact hpositive i v hi.mem_support_left hv₀
          · exact (Finset.disjoint_left.mp hNW hv (hWW' (hW₀ hv₀))).elim
        · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
          obtain ⟨j,_,hj⟩:=(transformerSpokeRows_mem Q H₀ _ i.val v).mp hi
          exact (hp₀ _ _ hj hv₀).elim
      exact ⟨fun v hv v' he=>hrows v (hExactR v v' he).1 hv,
        fun v hv a he=>hrows v (hExactS v a he) hv⟩
    · intro v a ha haB
      rcases hHub v a ha with hp|hi
      · obtain ⟨j,hj,_⟩:=hp
        rcases j with j|(j|j)
        · change ordinaryWheelHub (E.first j)=a at hj
          rw [E.first_hub] at hj
          exact (E.hub_avoid j (hj.symm ▸ haB)).elim
        · change ordinaryWheelHub (S.first j)=a at hj
          rw [S.first_hub] at hj
          exact ⟨⟨j.val.2,⟨j.val.1,j.property⟩⟩,Or.inl hj.symm⟩
        · change ordinaryWheelHub (D j).second=a at hj
          rw [(D j).second_hub] at hj
          exact (E.hub_avoid _ (hj.symm ▸ haB)).elim
      · exact hi

    · intro hTA hpA v hv
      rcases Finset.mem_union.mp hv with hv|hv
      · rcases Finset.mem_union.mp hv with hv|hv
        · obtain ⟨w,hw⟩:=Set.mem_toFinset.mp hv
          obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp hw
          exact ordinary_transformer_positive_row_location G Q F H₀ H φ ψ r A R B b σ p
            hbalance hroot hpA E S D (fun i v hv=>(hD i v hv).1) i v hi.mem_support_left
        · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp (hNT hv)
          exact Finset.mem_union_right _ (hTA i hi)
      · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
        exact Finset.mem_union_right _ (hTA i (hZT i hi))

end Oberwolfach
