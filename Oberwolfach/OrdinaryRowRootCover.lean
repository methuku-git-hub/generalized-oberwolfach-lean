module

public import Oberwolfach.NeighbourPairDomains
public import Oberwolfach.CappedRootWheelPacking

@[expose] public section

/-! Cover every rim and spoke edge at one row root. The assignment of
its neighbours is proved from degree and cut bounds, then completed by
the capped path construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_row_root_cover (lam:ℝ) (hlam:0<lam) :
    ∀ d:ℕ,∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      ∀ (Q F:SimpleGraph V) (H:V→U→Prop) (r K:ℕ),4≤r → 0<K →
      ∀ (x:V) (A:Finset V),x∉A → Q.neighborFinset x⊆A →
      ∀ b:ℝ,
      let T:=Finset.univ.filter (H x)
      N≤T.card → Q.degree x=2*T.card →
      (∀ a,F.degree a≤d) →
      (∀ a,Q.Adj x a → ¬F.Adj x a) →
      (∀ a,Q.Adj x a → lam*T.card≤((T.filter (H a)).card:ℝ)) →
      (∀ u∈T,2*lam*T.card≤(((Q.neighborFinset x).filter (fun a=>H a u)).card:ℝ)) →
      (∀ S⊆Q.neighborFinset x,∀ J⊆T,lam/16*T.card≤(S.card:ℝ) → lam/16*T.card≤(J.card:ℝ) →
        lam*S.card*J.card≤(bipartiteMatrixCut (fun a u=>if H a u then 1 else 0) S J:ℝ)) →
      (∀ u∈T,∀ a,a≠x → ∀ c,c≠x →
        b≤(((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)) →
      (T.card*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(d+1)+4*(K+1)<b →
      ∃ C:Fin T.card→OrdinaryWheel Q F H r,
        (∀ i,∀ a∈(ordinaryWheelRim (C i)).support,a=x∨a∈A) ∧
        (∀ i,H x (ordinaryWheelHub (C i))) ∧
        (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
        (∀ a,(wheelFamilyRim C).Adj x a ↔ Q.Adj x a) ∧
        (∀ u,wheelFamilySpokes C x u ↔ H x u) ∧
        (∀ a,a≠x → (wheelFamilyRim C).degree a≤2*(K+1)) ∧
        (∀ a,a≠x → (Finset.univ.filter (fun u=>wheelFamilySpokes C a u)).card≤K+1) ∧
        (∀ u,(Finset.univ.filter (fun a=>wheelFamilySpokes C a u)).card≤r) := by
  intro d
  obtain ⟨N,hN⟩:=ordinary_neighbour_pairs_on_domains lam hlam d
  refine ⟨N,?_⟩
  intro V U _ _ _ _ Q F H r K hr hK x A hxA hSA b T hn hbal hF hFx hrow hcol hcut hcount hbudget
  let S:=Q.neighborFinset x
  obtain ⟨v,w,u,hu,huT,hucov,hpair,hvw,hdis,hcover⟩:=by
    exact hN V U S T hn
      (by simpa only [S,SimpleGraph.card_neighborFinset_eq_degree] using hbal) H F
      (fun a ha=>hrow a ((Q.mem_neighborFinset x a).mp ha)) hcol hF hcut
  have hxv (i:Fin T.card):Q.Adj x (v i):=(Q.mem_neighborFinset x _).mp (hpair i).1
  have hxw (i:Fin T.card):Q.Adj x (w i):=(Q.mem_neighborFinset x _).mp (hpair i).2.1
  have hroot (i:Fin T.card) : ∀ a∈({x,v i,w i}:Finset V),∀ c∈({x,v i,w i}:Finset V),¬F.Adj a c:=by
    intro a ha c hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hc
    rcases ha with rfl|rfl|rfl <;> rcases hc with rfl|rfl|rfl
    · exact F.loopless.irrefl _
    · exact hFx (v i) (hxv i)
    · exact hFx (w i) (hxw i)
    · exact fun h=>hFx (v i) (hxv i) h.symm
    · exact F.loopless.irrefl (v i)
    · exact (hpair i).2.2.2.2
    · exact fun h=>hFx (w i) (hxw i) h.symm
    · exact fun h=>(hpair i).2.2.2.2 h.symm
    · exact F.loopless.irrefl (w i)
  obtain ⟨C,hC,hCdis,hcap,hdeg,hCR,hCH,hrowdeg,hcoldeg⟩:=capped_ordinary_root_wheels Q F H
    r T.card K hr hK x v w u hu hvw hdis (fun i=>A.filter (fun a=>H a (u i)))
    (fun i hx=>hxA (Finset.mem_filter.mp hx).1) hxv hxw hroot
    (fun i=>⟨(Finset.mem_filter.mp (huT i)).2,(hpair i).2.2.1,(hpair i).2.2.2.1⟩)
    (fun i a ha=>(Finset.mem_filter.mp ha).2) d b (by positivity)
    (fun a=>Nat.cast_le.mpr (hF a)) (fun i a ha c hc=>hcount (u i) (huT i) a ha c hc) hbudget
  refine ⟨C,?_,?_,hCdis,?_,?_,hdeg,hrowdeg,hcoldeg⟩
  · intro i a ha
    rcases (hC i).2.2.2 a ha with ha|ha
    · simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl|rfl
      · exact Or.inl rfl
      · exact Or.inr (hSA (hpair i).1)
      · exact Or.inr (hSA (hpair i).2.1)
    · exact Or.inr (Finset.mem_filter.mp ha).1
  · intro i
    rw [(hC i).1]
    exact (Finset.mem_filter.mp (huT i)).2
  · intro a
    rw [hCR,←hcover]
    exact Q.mem_neighborFinset x a
  · intro z
    rw [hCH]
    constructor
    · rintro ⟨i,rfl⟩;exact (Finset.mem_filter.mp (huT i)).2
    · intro hz;exact hucov z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)

end Oberwolfach
