module

public import Oberwolfach.TriangleProfileHostTransformer
public import Oberwolfach.OrdinaryRowProfileRestriction
public import Oberwolfach.OrdinaryTransformerForbiddenEdges

@[expose] public section

/-! The ordinary transformer from original ambient-scale common-cycle
profiles. Linear row deletion restricts the unchanged weights. A bounded
forbidden edge set is excluded by its endpoints, without changing the host.
The order bound is chosen before the later forbidden-set allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem triangular_parent_profile_host_transformer
    (Tpls:Tpl→VertexAbsorberTemplate 3) (β a b B₀:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hB₀:0<B₀):
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/2∧∀ q nU:ℕ,∃ t:ℕ,1≤t∧∀ F₀ d:ℝ,0≤F₀→0≤d→
      ∃ n₀:ℕ,
      ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      n₀≤Fintype.card V→
      ∀ (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
      (A Z R W:Finset V) (B:Finset U) (L:Finset (Sym2 V⊕(V×U))),
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→
      ordinaryResourceRows L⊆W→ ordinaryResourceHubs L⊆B→R⊆W→
      (∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)→
      (∀ u,3∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)→
      (∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤q)→
      Fintype.card {u:U // ∃ v,H₀ v u}≤nU→
      (∀ v∈G.support,v∈R∧φ v∈R)→
      (∀ v∈G.support,∀ w∈G.support,φ v≠w)→
      (∀ u,(∃ v,H₀ v u)→u≠ψ u)→
      G≤Q→(∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→
      Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2))→
      Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2))→
      (∀ v u,H₀ v u→H v u∧H (φ v) (ψ u))→
      (∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)→
      (∀ v w,G.Adj v w→∀ a∈({v,w,φ v,φ w}:Finset V),
        ∀ c∈({v,w,φ v,φ w}:Finset V),¬F.Adj a c)→
      (∀ v,(F.degree v:ℝ)≤d)→∀ c cH:ℝ,
      (∀ w x y z,c≤((A.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (∀ u u' w x y z,c≤((A.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      W.card+((R.card:ℝ)+G.edgeFinset.card+2*Fintype.card {e:V×U // H₀ e.1 e.2}+1)*(d+1)<c→
      W.card+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*(3-1:ℕ)+
        2*(3:ℝ)*Fintype.card (Σ v,G.neighborSet v)≤F₀→
      (∀ T:Finset V,T.card≤3+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        cH≤((common (Finset.univ:Finset U) T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      B.card+G.edgeFinset.card<cH→
      (∀ i:{u:U // ∃ v,H₀ v u},β*Fintype.card V≤
        ((Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val))).card:ℝ))→
      ∀ w:∀ i:{u:U // ∃ v,H₀ v u},
        LocalOrdinaryCycle Q F (Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val))) 3→ℝ,
      (∀ i C,b/(Fintype.card V:ℝ)^(3-1)≤w i C∧w i C≤B₀/(Fintype.card V:ℝ)^(3-1))→
      (∀ i:{u:U // ∃ v,H₀ v u},∀ v∈Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val)),
        |1-hypergraphWeightedDegree localOrdinaryVertices (w i) v|≤η)→
      (∀ i:{u:U // ∃ v,H₀ v u},∀ X:Finset V,X⊆Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val))→X.card=3→
        a*(Fintype.card V:ℝ)^(3*3)≤Fintype.card
          (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F)
            (T:=Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val))) (r:=3)) Tpls X))→
      ∃ N:Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
        N.card≤nU*3*(t+5*q)∧
        IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=3))
          (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) K∧
        K⊆ordinaryHostResources Q H∧
        (∀ v v',Sum.inl s(v,v')∈K→v∈N∧v'∈N)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈N)∧
        (∀ v∈R,∀ v'∈R,Sum.inl s(v,v')∉K)∧
        (∀ v∈R,∀ a∈B,Sum.inr (v,a)∉K)∧
        ∃ B':Finset U,B'.card≤nU*(q+2)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B')∧
          (∀ v∈W,∀ v',Sum.inl s(v,v')∈K→v∈R)∧
          (∀ v∈W,∀ a,Sum.inr (v,a)∈K→v∈R)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B→∃ i:{u:U // ∃ v,H₀ v u},a=i.val∨a=ψ i.val)∧
          (ordinaryPhysicalGraph (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)).support.toFinset.card≤
            nU*(3*(t+5*q)+q+2)∧N⊆R∪A∧Disjoint K L := by
  let α := (a/2)*(3:ℝ)^(3*3)
  let b₁ := b*(β/2)^(3-1)/(3:ℝ)^(3-1)
  let B₁ := B₀/(3:ℝ)^(3-1)
  have hrR : (0:ℝ)<3 := by exact_mod_cast (show 0<3 by omega)
  have hα : 0<α := by dsimp [α];positivity
  have hb₁ : 0<b₁ := by dsimp [b₁];positivity
  have hB₁ : 0<B₁ := by dsimp [B₁];positivity
  obtain ⟨τ,hτ,htrans⟩ := triangular_profile_host_transformer Tpls α b₁ B₁ hα hb₁ hB₁
  obtain ⟨ε,hε,hεβ,N₀,hN₀,hrestrict⟩ := ordinary_row_profile_restriction 3 (by omega)
    Tpls β a b B₀ τ hβ ha hb hB₀ hτ
  refine ⟨τ/4,ε,by positivity,hε,hεβ,?_⟩
  intro q nU
  obtain ⟨t,ht,htrans⟩ := htrans q nU
  refine ⟨t,ht,?_⟩
  intro F₀ d hF₀ hd
  obtain ⟨k₀,hk₀,htrans⟩ := htrans F₀ d hF₀ hd
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (2*(3:ℝ)*k₀/β)
  refine ⟨max N₀ N₁,?_⟩
  intro V U _ _ _ _ hn G Q F H₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW
    hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
    c cH hfour hspfour hpathbudget hWbudget hhub hhubBudget hT w hw herr habs
  have hn₀ : N₀≤Fintype.card V := (le_max_left _ _).trans hn
  have hn₁ : (N₁:ℝ)≤Fintype.card V := by exact_mod_cast (le_max_right N₀ N₁).trans hn
  have hscale : (3:ℝ)*k₀≤(β/2)*Fintype.card V := by
    have hh := (div_lt_iff₀ hβ).mp (hN₁.trans_le hn₁)
    linarith only [hh]
  let T (i:{u:U // ∃ v,H₀ v u}) := A.filter (fun v=>H v i.val∧H v (ψ i.val))
  let k (i:{u:U // ∃ v,H₀ v u}) : ℝ := ((T i).card:ℝ)/3
  have hprofile (i:{u:U // ∃ v,H₀ v u}) : k₀≤k i ∧
      ∃ w' : LocalOrdinaryCycle Q F (T i) 3→ℝ,
        (∀ C,b₁/(k i)^(3-1)≤w' C∧w' C≤B₁/(k i)^(3-1)) ∧
        (∀ v∈T i,|1-hypergraphWeightedDegree localOrdinaryVertices w' v|≤τ) ∧
        (∀ X:Finset V,X⊆T i→X.card=3→α*(k i)^(3*3)≤
          Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T i) (r:=3)) Tpls X)) := by
    let T₀ : Finset V := Finset.univ.filter (fun v=>H v i.val∧H v (ψ i.val))
    have he : T₀\Z=T i := by ext v;simp [T₀,T,hA];tauto
    obtain ⟨hk,hlo,hhi,hbounds,herr',habs'⟩ :=
      hrestrict V hn₀ Q F T₀ Z (hT i) hZ (w i) (hw i) (herr i) (habs i)
    have hlow : (β/2)*Fintype.card V≤(3:ℝ)*k i := by simpa only [he,Nat.cast_ofNat,k] using hlo
    refine ⟨(mul_le_mul_iff_right₀ hrR).mp (hscale.trans hlow),?_⟩
    have hh : ∃ w' : LocalOrdinaryCycle Q F (T₀\Z) 3→ℝ,
        (∀ C,b₁/(((T₀\Z).card:ℝ)/3)^(3-1)≤w' C ∧ w' C≤B₁/(((T₀\Z).card:ℝ)/3)^(3-1)) ∧
        (∀ v∈T₀\Z,|1-hypergraphWeightedDegree localOrdinaryVertices w' v|≤τ) ∧
        (∀ X:Finset V,X⊆T₀\Z→X.card=3→α*(((T₀\Z).card:ℝ)/3)^(3*3)≤
          Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T₀\Z) (r:=3)) Tpls X)) :=
      ⟨fun C=>w i (localOrdinaryRestrictionParent le_rfl Finset.sdiff_subset C),hbounds,
        (fun v hv=>(herr' v hv).trans (by linarith only [hτ])),habs'⟩
    dsimp [k]
    have htransport (T' T'' : Finset V) (heq:T'=T'') :
        (∃ w' : LocalOrdinaryCycle Q F T' 3→ℝ,
          (∀ C,b₁/((T'.card:ℝ)/3)^(3-1)≤w' C ∧ w' C≤B₁/((T'.card:ℝ)/3)^(3-1)) ∧
          (∀ v∈T',|1-hypergraphWeightedDegree localOrdinaryVertices w' v|≤τ) ∧
          (∀ X:Finset V,X⊆T'→X.card=3→α*((T'.card:ℝ)/3)^(3*3)≤
            Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T') (r:=3)) Tpls X))) →
        (∃ w' : LocalOrdinaryCycle Q F T'' 3→ℝ,
          (∀ C,b₁/((T''.card:ℝ)/3)^(3-1)≤w' C ∧ w' C≤B₁/((T''.card:ℝ)/3)^(3-1)) ∧
          (∀ v∈T'',|1-hypergraphWeightedDegree localOrdinaryVertices w' v|≤τ) ∧
          (∀ X:Finset V,X⊆T''→X.card=3→α*((T''.card:ℝ)/3)^(3*3)≤
            Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T'') (r:=3)) Tpls X))) := by
      subst T''
      exact id
    exact htransport _ _ he hh
  choose hk w' hw' herr' habs' using hprofile
  have hsize (i:{u:U // ∃ v,H₀ v u}) : ((T i).card:ℝ)=3*k i := by dsimp [k];field_simp
  obtain ⟨N,K,hNc,hK,hKQ,hKr,hKs,hRR,hRB,B',hBc,hBh,havoid,hspoke,hHavoid,horder,hNloc⟩ :=
    htrans V U G Q F H₀ H φ ψ A R W B hRW hbalance hdiv hq hnU hroot hcross hu hQ hφQ
      hφedge hψedge hH hB hFroots hF c cH hfour hspfour hpathbudget hWbudget
      hhub hhubBudget k hk hsize w' hw' herr' habs'
  exact ⟨N,K,hNc,hK,hKQ,hKr,hKs,hRR,hRB,B',hBc,hBh,havoid,hspoke,hHavoid,horder,hNloc,
    ordinary_transformer_forbidden_edges K L R W B hrows hhubs havoid hspoke hRR hRB⟩

end Oberwolfach
