module

public import Oberwolfach.FixedLengthPaths
public import Oberwolfach.TransferCyclePositions
public import Oberwolfach.FractionalDecompositions

@[expose] public section

/-! Closing a simple prescribed-length path gives an actual embedded
cycle graph, preserving both specified endpoints and all forbidden
vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem embedded_cycle_from_simple_path (G : SimpleGraph V) (S : Finset V)
    (r : ℕ) (hr : 3 ≤ r) (x y : V) (p : G.Walk x y)
    (hp : p.IsPath) (hlen : p.length=r-1) (hxy : G.Adj x y)
    (havoid : ∀ v∈p.support,v∉S) :
    ∃ C : SimpleGraph V,IsEmbeddedCycle C r ∧ C ≤ G ∧ C.Adj x y ∧ ∀ v∈C.support,v∉S := by
  let f : Fin r ↪ V := ⟨fun i => p.getVert i.val,by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (by change i.val ≤ p.length;rw [hlen];omega)
      (by change j.val ≤ p.length;rw [hlen];omega) he⟩
  let C := (SimpleGraph.cycleGraph r).map f
  have hadj (i j : Fin r) (h : (SimpleGraph.cycleGraph r).Adj i j) : G.Adj (f i) (f j) := by
    change G.Adj (p.getVert i.val) (p.getVert j.val)
    rcases cycleGraph_adj_natural_cases r hr i j h with hij|hji|⟨hi,hj⟩|⟨hj,hi⟩
    · rw [← hij]
      exact p.adj_getVert_succ (by rw [hlen];have hj:=j.isLt;omega)
    · rw [← hji]
      exact (p.adj_getVert_succ (by rw [hlen];have hi:=i.isLt;omega)).symm
    · rw [hi,hj,← hlen,p.getVert_zero,p.getVert_length]
      exact hxy
    · rw [hj,hi,← hlen,p.getVert_zero,p.getVert_length]
      exact hxy.symm
  refine ⟨C,⟨hr,f,rfl⟩,?_,?_,?_⟩
  · intro v w h
    obtain ⟨i,j,hij,rfl,rfl⟩ := (SimpleGraph.map_adj f _ _ _).mp h
    exact hadj i j hij
  · let i : Fin r := ⟨0,by omega⟩
    let j : Fin r := ⟨r-1,by omega⟩
    apply (SimpleGraph.map_adj f _ _ _).mpr
    refine ⟨i,j,?_,?_,?_⟩
    · apply (cycleGraph_modular_adj (by omega) i j).mpr
      right
      change (r-1+1)%r=0
      rw [show r-1+1=r by omega,Nat.mod_self]
    · exact p.getVert_zero
    · change p.getVert (r-1)=y
      rw [← hlen,p.getVert_length]
  · intro v hv
    obtain ⟨w,hw⟩ := hv
    obtain ⟨i,j,hij,hi,hj⟩ := (SimpleGraph.map_adj f _ _ _).mp hw
    rw [← hi]
    exact havoid _ (p.getVert_mem_support _)

theorem fixed_cycle_through_edge (β : ℝ) (hβ : 0 < β) (r b : ℕ) (hr : 3 ≤ r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ (V : Type*) [Fintype V] [DecidableEq V],Fintype.card V ≤ n →
    ∀ (G : SimpleGraph V),(∀ v,(1/2+β)*(n:ℝ) ≤ G.degree v) →
    ∀ (x y : V),G.Adj x y → ∀ S : Finset V,S.card ≤ b → x∉S → y∉S →
    ∃ C : SimpleGraph V,IsEmbeddedCycle C r ∧ C ≤ G ∧ C.Adj x y ∧ ∀ v∈C.support,v∉S := by
  obtain ⟨n₀,hn₀⟩ := fixed_length_path β hβ (r-1) b (by omega)
  refine ⟨n₀,?_⟩
  intro n hn V _ _ hV G hdeg x y hxy S hS hx hy
  obtain ⟨p,hp,hlen,havoid⟩ := hn₀ n hn V hV G hdeg x y hxy.ne S hS hx hy
  exact embedded_cycle_from_simple_path G S r hr x y p hp hlen hxy havoid

theorem fixed_cycle_through_vertex (β : ℝ) (hβ : 0 < β) (r b : ℕ) (hr : 3 ≤ r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ (V : Type*) [Fintype V] [DecidableEq V],Fintype.card V ≤ n →
    ∀ (G : SimpleGraph V),(∀ v,(1/2+β)*(n:ℝ) ≤ G.degree v) →
    ∀ (x : V) (S : Finset V),S.card ≤ b → x∉S →
    ∃ C : SimpleGraph V,IsEmbeddedCycle C r ∧ C ≤ G ∧ x∈C.support ∧ ∀ v∈C.support,v∉S := by
  obtain ⟨n₁,hn₁⟩ := fixed_cycle_through_edge β hβ r b hr
  refine ⟨max n₁ (2*(b+1)),?_⟩
  intro n hn V _ _ hV G hdeg x S hS hx
  have hnR : (2:ℝ)*((b:ℝ)+1) ≤ n := by
    exact_mod_cast (show 2*(b+1) ≤ n from (le_max_right _ _).trans hn)
  have hSR : (S.card:ℝ) ≤ b := by exact_mod_cast hS
  have hsize : S.card < (G.neighborFinset x).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hgt : (S.card:ℝ) < G.degree x := by nlinarith [hdeg x]
    exact_mod_cast hgt
  obtain ⟨y,hy,hys⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  have hxy : G.Adj x y := by simpa only [SimpleGraph.mem_neighborFinset] using hy
  obtain ⟨C,hC,hCG,hCxy,havoid⟩ := hn₁ n ((le_max_left _ _).trans hn) V hV G hdeg x y hxy S hS hx hys
  exact ⟨C,hC,hCG,hCxy.mem_support_left,havoid⟩

end Oberwolfach
