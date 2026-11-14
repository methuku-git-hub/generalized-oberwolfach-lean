module

public import Oberwolfach.SparseRootWheels
public import Oberwolfach.OrdinaryLocalExtensions

@[expose] public section

/-! The source ordinary local-extension hypotheses produce a physical
wheel through prescribed root edges. The vertex-exclusion allowance and
common-neighbour tolerance are fixed before the conflict radius. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_wheels_from_local_extensions (r : ℕ) (hr : 4≤r) (α ρ₀ s₀ : ℝ)
    (hα : 0<α) (hρ₀ : 0<ρ₀) (hρ₀1 : ρ₀≤1) (hs₀ : 0<s₀) (hs₀1 : s₀≤1) :
    ∃ θ ε₀ : ℝ,0<θ ∧ 0<ε₀ ∧ ∀ d : ℕ,∃ N : ℕ,
      ∀ (V U : Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (P R : SimpleGraph V) (H : V→U→Prop) (π : Equiv.Perm V)
        (A : Finset V) (B : Finset U) (ρ s ε : ℝ),N≤A.card →
      ρ₀≤ρ → s₀≤s → ε≤ε₀ →
      (∀ v,(cycleThreshold r+α)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      (∀ X : Finset V,∀ J : Finset U,X.card≤ordinaryExtensionRootBound r → J.card≤2 →
        (ρ*s)^X.card*s^J.card*((common A X (fun v=>(P\permutationConflictGraph π (3*d)).neighborFinset v)).card:ℝ)-ε*A.card≤
          ((common (common A X (fun v=>R.neighborFinset v)) J
            (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)) →
      (∀ X : Finset V,X.card≤r+6 →
        (∀ v∈X,∀ w∈X,¬(permutationConflictGraph π (3*d)).Adj v w) →
        (s^X.card-ε)*B.card≤((common B X (fun v=>Finset.univ.filter (H v))).card:ℝ)) →
      ∀ (W : Finset V),W.card≤θ*A.card → ∀ (x v w : V) (u:U),v≠w →
      R.Adj x v → R.Adj x w → H x u → H v u → H w u →
      (∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬(permutationConflictGraph π (3*d)).Adj a b) →
      ∃ C : OrdinaryWheel R (permutationConflictGraph π (3*d)) H r,ordinaryWheelHub C=u ∧
        (ordinaryWheelRim C).Adj x v ∧ (ordinaryWheelRim C).Adj x w ∧
        (∀ a∈(ordinaryWheelRim C).support,a∈({x,v,w}:Finset V) ∨ a∈A∧a∉W) := by
  obtain ⟨β,ε₀,hβ,hε,hN⟩:=ordinary_local_extensions r (by omega) α ρ₀ s₀ hα hρ₀ hρ₀1 hs₀ hs₀1
  refine ⟨β/4,ε₀,by positivity,hε,?_⟩
  intro d
  obtain ⟨N₀,hN₀⟩:=hN d
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (4*((r:ℝ)+3)*(6*d+1)/β)
  refine ⟨max N₀ (max N₁ 1),?_⟩
  intro V U _ _ _ _ P R H π A B ρ s ε hn hρ hs hε' hdeg hrows hindices W hW x v w u hvw hxv hxw hHx hHv hHw hFroot
  have hAN : N₀≤A.card:=(le_max_left _ _).trans hn
  have hN₁A : (N₁:ℝ)≤A.card:=Nat.cast_le.mpr (by omega)
  have hAbig : 4*((r:ℝ)+3)*(6*d+1)<β*A.card:=by
    have hh:=(div_lt_iff₀ hβ).mp (hN₁.trans_le hN₁A)
    nlinarith only [hh]
  have hApos : (0:ℝ)<A.card:=by exact_mod_cast (show 0<A.card by omega)
  have hext:=((hN₀ V U P R H π A B ρ s ε hAN hρ hs hε' hdeg hrows hindices).1)
  let T:=A∩Finset.univ.filter (fun a=>H a u)
  have hcount (a b:V) : β*A.card≤((T∩R.neighborFinset a∩R.neighborFinset b).card:ℝ):=by
    have hh:=hext {a,b} {u} (Finset.card_le_two.trans (by unfold ordinaryExtensionRootBound;split_ifs <;> omega)) (by simp)
    have he : common (common A {a,b} (fun v=>R.neighborFinset v)) {u}
        (fun u=>Finset.univ.filter (fun v=>H v u))=T∩R.neighborFinset a∩R.neighborFinset b:=by
      ext z
      simp only [common,Finset.mem_filter,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
        forall_eq_or_imp,forall_eq,Finset.mem_univ,true_and,T]
      tauto
    rw [he] at hh
    exact hh
  have hF (a:V) : ((permutationConflictGraph π (3*d)).degree a:ℝ)≤6*d:=by
    have hh:=permutationConflictGraph_degree_le π (3*d) a
    exact_mod_cast (show (permutationConflictGraph π (3*d)).degree a≤6*d by omega)
  obtain ⟨C,hCu,hCxv,hCxw,hCs⟩:=ordinary_root_wheel_from_common_counts R (permutationConflictGraph π (3*d)) H T W x v w u hvw hxv hxw hFroot
    ⟨hHx,hHv,hHw⟩ (fun a ha=>(Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2)
    r hr (6*d) (β*A.card) (by positivity) hF hcount (by nlinarith only [hW,hAbig,mul_pos hβ hApos])
  refine ⟨C,hCu,hCxv,hCxw,?_⟩
  intro a ha
  rcases hCs a ha with ha'|ha'
  · exact Or.inl ha'
  · exact Or.inr ⟨(Finset.mem_inter.mp ha'.1).1,ha'.2⟩

end Oberwolfach
