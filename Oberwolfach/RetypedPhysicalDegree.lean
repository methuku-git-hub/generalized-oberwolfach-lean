module

public import Oberwolfach.MarkedIndegreeCorrection
public import Oberwolfach.PhysicalEdgeGraph

@[expose] public section
/-! The physical degree of changed directed arcs is bounded by their changed
incoming and outgoing counts. This remains valid if physical pairs coincide. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E:Type} [Fintype V] [Fintype E]

def retypedPhysicalEdges (tail head:E→V) (M M₀:E→Bool) : Finset (Finset V) :=
  (Finset.univ.filter (fun e=>M e≠M₀ e)).image (fun e=>({tail e,head e}:Finset V))

theorem retyped_physical_degree_le (tail head:E→V) (M M₀:E→Bool) (v:V) :
    (physicalEdgeGraph (retypedPhysicalEdges tail head M M₀)).degree v ≤
      (∑ e, if head e=v ∧ M e≠M₀ e then (1:ℕ) else 0) +
      (∑ e, if tail e=v ∧ M e≠M₀ e then (1:ℕ) else 0) := by
  let D := Finset.univ.filter (fun e=>M e≠M₀ e)
  let H := D.filter (fun e=>head e=v)
  let T := D.filter (fun e=>tail e=v)
  let pair := fun e:E=>({tail e,head e}:Finset V)
  have hsub : ((retypedPhysicalEdges tail head M M₀).filter (fun s=>v∈s)) ⊆
      H.image pair ∪ T.image pair := by
    intro s hs
    obtain ⟨hs,hv⟩ := Finset.mem_filter.mp hs
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with htail|hhead
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,htail.symm⟩,rfl⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hhead.symm⟩,rfl⟩
  have hbound := (physicalEdgeGraph_degree_le_incident (retypedPhysicalEdges tail head M M₀) v).trans
    ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
  have h1 : (H.image pair).card ≤ H.card := Finset.card_image_le
  have h2 : (T.image pair).card ≤ T.card := Finset.card_image_le
  have hH : H.card = ∑ e, if head e=v ∧ M e≠M₀ e then (1:ℕ) else 0 := by
    have heq : H = Finset.univ.filter (fun e=>head e=v ∧ M e≠M₀ e) := by
      ext e
      simp only [H,D,Finset.mem_filter,Finset.mem_univ,true_and]
      tauto
    rw [heq,Finset.card_filter]
  have hT : T.card = ∑ e, if tail e=v ∧ M e≠M₀ e then (1:ℕ) else 0 := by
    have heq : T = Finset.univ.filter (fun e=>tail e=v ∧ M e≠M₀ e) := by
      ext e
      simp only [T,D,Finset.mem_filter,Finset.mem_univ,true_and]
      tauto
    rw [heq,Finset.card_filter]
  omega
theorem marked_indegree_correction_physical
    [Nonempty V] (tail head:E→V) (M₀:E→Bool) (A:E→Prop) (b:ℕ) (rho eta:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hpair:Function.Injective (fun e:E=>(tail e,head e)))
    (hdev:∀ v, |(markedHeadCount head M₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (hmarked:∀ v, rho*Fintype.card V≤(markedFlexibleIncoming head M₀ A v true:ℝ))
    (hunmarked:∀ v, rho*Fintype.card V≤(markedFlexibleIncoming head M₀ A v false:ℝ)) :
    ∃ M:E→Bool,
      (∀ v, markedHeadCount head M v=b) ∧
      (∀ e, M e≠M₀ e → A e) ∧
      (∀ v, ((physicalEdgeGraph (retypedPhysicalEdges tail head M M₀)).degree v:ℝ) ≤
        (1+1/rho)*eta*Fintype.card V+1) := by
  obtain ⟨M,hM,hA,hhead,htail⟩ := marked_flexible_retyping tail head M₀ A b rho eta hrho heta hetaR
    hpair hdev hmarked hunmarked
  refine ⟨M,hM,hA,?_⟩
  let n : ℝ := Fintype.card V
  have hn : 0<n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hs : n*(eta*n/(rho*n))=eta*n/rho := by
    field_simp
  have ha : 0≤eta*n/rho := div_nonneg (mul_nonneg heta.le hn.le) hrho.le
  have hc : ((⌈eta*n/rho⌉₊:ℕ):ℝ) ≤ eta*n/rho+1 := (Nat.ceil_lt_add_one ha).le
  intro v
  have hd := retyped_physical_degree_le tail head M M₀ v
  have hd' : ((physicalEdgeGraph (retypedPhysicalEdges tail head M M₀)).degree v:ℝ) ≤
      ((∑ e, if head e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ) +
      ((∑ e, if tail e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ) := by exact_mod_cast hd
  have hh := hhead v
  change _ ≤ eta*n at hh
  have htail' : ((∑ e, if tail e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ) ≤
      ((⌈eta*n/rho⌉₊:ℕ):ℝ) := by
    have ht := htail v
    have hce : ⌈n*(eta*n/(rho*n))⌉₊ = ⌈eta*n/rho⌉₊ := congrArg Nat.ceil hs
    rw [hce] at ht
    exact_mod_cast ht
  calc
    _ ≤ eta*n + (⌈eta*n/rho⌉₊:ℕ) := hd'.trans (add_le_add hh htail')
    _ ≤ eta*n + (eta*n/rho+1) := by linarith
    _ = (1+1/rho)*eta*Fintype.card V+1 := by dsimp [n]; ring
theorem marked_indegree_correction_manuscript_bound
    [Nonempty V] (tail head:E→V) (M₀:E→Bool) (A:E→Prop) (b:ℕ) (rho eta:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hpair:Function.Injective (fun e:E=>(tail e,head e)))
    (hdev:∀ v, |(markedHeadCount head M₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (hmarked:∀ v, rho*Fintype.card V≤(markedFlexibleIncoming head M₀ A v true:ℝ))
    (hunmarked:∀ v, rho*Fintype.card V≤(markedFlexibleIncoming head M₀ A v false:ℝ)) :
    ∃ M:E→Bool,
      (∀ v, markedHeadCount head M v=b) ∧
      (∀ e, M e≠M₀ e → A e) ∧
      (∀ v, ((physicalEdgeGraph (retypedPhysicalEdges tail head M M₀)).degree v:ℝ) ≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) := by
  obtain ⟨M,hM,hA,hdeg⟩ := marked_indegree_correction_physical tail head M₀ A b rho eta
    hrho heta hetaR hpair hdev hmarked hunmarked
  refine ⟨M,hM,hA,?_⟩
  intro v
  have hn : (1:ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp : (1:ℝ) ≤ (Fintype.card V:ℝ)^(3/5:ℝ) := Real.one_le_rpow hn (by norm_num)
  have hextra : 0≤eta*(Fintype.card V:ℝ)/rho := by positivity
  have h := hdeg v
  have hr : (1+2/rho)*eta*(Fintype.card V:ℝ) =
      (1+1/rho)*eta*(Fintype.card V:ℝ)+eta*(Fintype.card V:ℝ)/rho := by ring
  rw [hr]
  linarith
theorem marked_indegree_correction_oriented_graph
    [Nonempty V] (P:V×V→Prop)
    (M₀:{e:V×V // P e}→Bool) (A:{e:V×V // P e}→Prop) (b:ℕ) (rho eta:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hdev:∀ v, |(markedHeadCount (fun e=>e.val.2) M₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (hmarked:∀ v, rho*Fintype.card V≤(markedFlexibleIncoming (fun e=>e.val.2) M₀ A v true:ℝ))
    (hunmarked:∀ v, rho*Fintype.card V≤(markedFlexibleIncoming (fun e=>e.val.2) M₀ A v false:ℝ)) :
    ∃ M:{e:V×V // P e}→Bool,
      (∀ v, markedHeadCount (fun e=>e.val.2) M v=b) ∧
      (∀ e, M e≠M₀ e → A e) ∧
      (∀ v, ((physicalEdgeGraph (retypedPhysicalEdges (fun e=>e.val.1) (fun e=>e.val.2) M M₀)).degree v:ℝ) ≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) := by
  apply marked_indegree_correction_manuscript_bound (fun e:{e:V×V // P e}=>e.val.1)
    (fun e=>e.val.2) M₀ A b rho eta hrho heta hetaR
  · intro e e' h
    apply Subtype.ext
    exact h
  · exact hdev
  · exact hmarked
  · exact hunmarked
end Oberwolfach
