module

public import Oberwolfach.ListColouringLocalLemma
public import Oberwolfach.RemainingColourDegrees
public import Oberwolfach.HypergraphLineGraph

@[expose] public section

/-! Deterministic extension of a partial list colouring. The residual
lists exclude every colour already assigned to an adjacent vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem extend_partial_list_colouring
    {V C : Type*} (G : SimpleGraph V) (L : V → Finset C)
    (p : V → Option C)
    (hlist : ∀ v c,p v=some c → c∈L v)
    (hproper : ∀ u v,G.Adj u v → ∀ c,p u=some c → p v≠some c)
    (L' : {v // p v=none} → Finset C)
    (hsub : ∀ v,L' v⊆L v.val)
    (havoid : ∀ v c,c∈L' v → ∀ u,G.Adj v.val u → p u≠some c)
    (f : {v // p v=none} → C) (hf : ∀ v,f v∈L' v)
    (hfproper : ∀ u v,G.Adj u.val v.val → f u≠f v) :
    ∃ g : V → C,(∀ v,g v∈L v) ∧ ∀ u v,G.Adj u v → g u≠g v := by
  classical
  let g (v : V) : C := if h : p v=none then f ⟨v,h⟩ else (p v).get (Option.isSome_iff_ne_none.mpr h)
  have hnone (v : V) (h : p v=none) : g v=f ⟨v,h⟩ := by simp [g,h]
  have hsome (v : V) (c : C) (h : p v=some c) : g v=c := by simp [g,h]
  refine ⟨g,?_,?_⟩
  · intro v
    cases hv : p v with
    | none => rw [hnone v hv];exact hsub ⟨v,hv⟩ (hf ⟨v,hv⟩)
    | some c => rw [hsome v c hv];exact hlist v c hv
  · intro u v huv he
    cases hu : p u with
    | none =>
      cases hv : p v with
      | none =>
        rw [hnone u hu,hnone v hv] at he
        exact hfproper ⟨u,hu⟩ ⟨v,hv⟩ huv he
      | some c =>
        rw [hnone u hu,hsome v c hv] at he
        exact havoid ⟨u,hu⟩ c (he ▸ hf ⟨u,hu⟩) v huv hv
    | some c =>
      cases hv : p v with
      | none =>
        rw [hsome u c hu,hnone v hv] at he
        exact havoid ⟨v,hv⟩ c (he.symm ▸ hf ⟨v,hv⟩) u huv.symm hu
      | some d =>
        rw [hsome u c hu,hsome v d hv] at he
        exact hproper u v huv c hu (hv.trans (congrArg some he.symm))

theorem hypergraph_available_list_avoids_retained
    {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (σ : E → C×Bool)
    (e : E) (c : C)
    (hc : c∈nibbleAvailableColours (hypergraphLineGraph R) (R e)
      (hypergraphVertexClique R) (L e) σ)
    (f : E) (hef : (hypergraphLineGraph R).Adj e f) :
    coinRetainedColour (hypergraphLineGraph R) σ f≠some c := by
  have hh := (nibbleAvailableColours_mem_iff (hypergraphLineGraph R) (R e)
    (hypergraphVertexClique R) (fun v _=>hypergraphVertexClique_isClique R v) (L e) σ c).mp hc
  have ha := (clique_no_retained_iff_card (hypergraphLineGraph R) (R e)
    (hypergraphVertexClique R) (fun v _=>hypergraphVertexClique_isClique R v) σ c).mpr hh.2
  obtain ⟨v,hve,hvf⟩ := Finset.not_disjoint_iff.mp hef.2
  exact ha v hve f (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvf⟩)

theorem hypergraph_extend_retained_colouring
    {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (σ : E → C×Bool)
    (hσ : ∀ e,(σ e).1∈L e)
    (f : {e // coinRetainedColour (hypergraphLineGraph R) σ e=none} → C)
    (hf : ∀ e,f e∈nibbleAvailableColours (hypergraphLineGraph R) (R e.val)
      (hypergraphVertexClique R) (L e.val) σ)
    (hfproper : ∀ e g,(hypergraphLineGraph R).Adj e.val g.val → f e≠f g) :
    ∃ g : E → C,(∀ e,g e∈L e) ∧
      ∀ e f,(hypergraphLineGraph R).Adj e f → g e≠g f := by
  apply extend_partial_list_colouring (hypergraphLineGraph R) L
    (coinRetainedColour (hypergraphLineGraph R) σ)
    (fun e c hc=>by rw [← ((coinRetainedColour_eq_some _ _ _ _).mp hc).1];exact hσ e)
    (fun e f hef c hc=>coinRetainedColour_proper _ _ hef c hc)
    (fun e=>nibbleAvailableColours (hypergraphLineGraph R) (R e.val)
      (hypergraphVertexClique R) (L e.val) σ)
    (fun e c hc=>by
      have hm : c∈L e.val ∧ ∀ j∈R e.val,∀ v∈hypergraphVertexClique R j,
          coinRetainedColour (hypergraphLineGraph R) σ v≠some c := by
        simpa only [nibbleAvailableColours,Finset.mem_filter] using hc
      exact hm.1)
    (fun e c hc f hef=>hypergraph_available_list_avoids_retained R L σ e.val c hc f hef)
    f hf hfproper

end Oberwolfach
