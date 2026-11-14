module

public import Oberwolfach.RootedLargeSubsetCycle

@[expose] public section

/-! Embed the expansion of a formal spoke, whether or not that spoke is
an edge of the host. Both cross-spokes are constructed in the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_spoke_expansion_embedding (β : ℝ) (hβ : 0<β) (r b : ℕ) (hr : 3≤r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ (V U : Type*) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],Fintype.card V=n →
    ∀ (G : SimpleGraph V) (H : V → U → Prop),
    (∀ a,(1/2+β)*(n:ℝ)≤G.degree a) →
    (∀ a,(1/2:ℝ)*(Fintype.card U:ℝ)≤(Finset.univ.filter (H a)).card) →
    (∀ u,((Finset.univ.filter (fun v => ¬H v u)).card:ℝ)≤(β/2)*n) →
    (∀ u,((Finset.univ.filter (fun v => ¬H v u)).card:ℝ)≤(n:ℝ)/4) →
    ∀ (R : Finset V) (B : Finset U) (x : V) (u : U),R.card≤b → x∈R → u∈B → 2*B.card<Fintype.card U →
    ∃ (f : Fin r ↪ V) (u' : U),
      (∀ i j,(SimpleGraph.cycleGraph r).Adj i j → G.Adj (f i) (f j)) ∧
      (∀ i,H (f i) u') ∧ (∀ i,f i∉R) ∧ u'∉B ∧
      H x u' ∧ H (f ⟨0,by omega⟩) u := by
  obtain ⟨n₁,hcycle⟩ := rooted_cycle_inside_large_subset β hβ r b hr
  refine ⟨max n₁ (2*b+1),?_⟩
  intro n hn V U _ _ _ _ hV G H hdeg hrow hcol hquarter R B x u hR hx hu hB
  have hBsize : B.card<(Finset.univ.filter (H x)).card := by
    have hBR : 2*(B.card:ℝ)<Fintype.card U := by exact_mod_cast hB
    have hh : (B.card:ℝ)<(Finset.univ.filter (H x)).card := by linarith [hrow x]
    exact_mod_cast hh
  obtain ⟨u',hu',hu'B⟩ := Finset.exists_mem_notMem_of_card_lt_card hBsize
  have hxu' : H x u' := (Finset.mem_filter.mp hu').2
  let A := Finset.univ.filter (fun v => H v u')
  let D := Finset.univ.filter (fun v => H v u)
  have heAset : Finset.univ\A=Finset.univ.filter (fun v => ¬H v u') := by ext v;simp [A]
  have heDset : Finset.univ\D=Finset.univ.filter (fun v => ¬H v u) := by ext v;simp [D]
  have hAc : ((Finset.univ\A).card:ℝ)≤(β/2)*n := by
    rw [heAset]
    exact hcol u'
  have hAc' : ((Finset.univ\A).card:ℝ)≤(n:ℝ)/4 := by
    rw [heAset]
    exact hquarter u'
  have hDc : ((Finset.univ\D).card:ℝ)≤(n:ℝ)/4 := by
    rw [heDset]
    exact hquarter u
  have heA : A.card+(Finset.univ\A).card=n := by
    simpa only [Finset.univ_inter,Finset.card_univ,hV] using Finset.card_inter_add_card_sdiff Finset.univ A
  have heD : D.card+(Finset.univ\D).card=n := by
    simpa only [Finset.univ_inter,Finset.card_univ,hV] using Finset.card_inter_add_card_sdiff Finset.univ D
  have heI := Finset.card_union_add_card_inter A D
  have hUnion : (A∪D).card≤n := by simpa only [hV] using Finset.card_le_univ (A∪D)
  have hInt : (n:ℝ)/2≤((A∩D).card:ℝ) := by
    have heAR : (A.card:ℝ)+(Finset.univ\A).card=n := by exact_mod_cast heA
    have heDR : (D.card:ℝ)+(Finset.univ\D).card=n := by exact_mod_cast heD
    have heIR : ((A∪D).card:ℝ)+(A∩D).card=(A.card:ℝ)+D.card := by exact_mod_cast heI
    have hUnionR : ((A∪D).card:ℝ)≤n := by exact_mod_cast hUnion
    linarith
  have hbound : 2*b<n := by have hh := (le_max_right n₁ (2*b+1)).trans hn;omega
  have hsize : R.card<(A∩D).card := by
    have hbR : 2*(b:ℝ)<n := by exact_mod_cast hbound
    have hRR : (R.card:ℝ)≤b := by exact_mod_cast hR
    have hh : (R.card:ℝ)<(A∩D).card := by linarith
    exact_mod_cast hh
  obtain ⟨x',hx',hx'R⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  obtain ⟨f,hf,hhom,hfA,hfR⟩ := hcycle n ((le_max_left _ _).trans hn) V hV.le G hdeg
    A R hAc hR x' (Finset.mem_inter.mp hx').1 hx'R
  refine ⟨f,u',hhom,(fun i => (Finset.mem_filter.mp (hfA i)).2),hfR,hu'B,hxu',?_⟩
  rw [hf]
  exact (Finset.mem_filter.mp (Finset.mem_inter.mp hx').2).2

end Oberwolfach
