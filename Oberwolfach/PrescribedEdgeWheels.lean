module

public import Oberwolfach.SparseRootWheels

@[expose] public section

/-! Ordinary wheels through one prescribed rim edge or one prescribed
spoke. Every other rim vertex is chosen in the stated free set, avoiding
the supplied forbidden vertices; all lengths at least three are included. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_rim_edge_wheel_from_common_counts (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W:Finset V) (x y:V) (u:U) (hxy:Q.Adj x y) (hFxy:¬F.Adj x y)
    (hHx:H x u) (hHy:H y u) (hHA:∀ a∈A,H a u)
    (r:ℕ) (hr:3≤r) (L b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hcount:∀ a c,b≤((A∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:W.card+((r:ℝ)+2)*(L+1)<b) :
    ∃ C:OrdinaryWheel Q F H r,ordinaryWheelHub C=u ∧
      (ordinaryWheelRim C).Adj x y ∧
      (∀ a∈(ordinaryWheelRim C).support,a=x ∨ a=y ∨ a∈A∧a∉W) := by
  have hroot:∀ a∈({x,y}:Finset V),∀ c∈({x,y}:Finset V),¬F.Adj a c:=by
    intro a ha c hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hc
    rcases ha with rfl|rfl <;> rcases hc with rfl|rfl
    · exact F.loopless.irrefl _
    · exact hFxy
    · exact fun h=>hFxy h.symm
    · exact F.loopless.irrefl _
  have hcard:(({x,y}:Finset V).card:ℝ)≤2:=by exact_mod_cast (Finset.card_le_two (a:=x) (b:=y))
  have hk:((r-1:ℕ):ℝ)≤r:=by exact_mod_cast Nat.sub_le r 1
  obtain ⟨p,hp,hlen,hclass,hind,hroots⟩:=sparse_fixed_length_forbidden_path Q F A W {x,y}
    x y hxy.ne (by simp) (by simp) hroot (r-1) (by omega) L b hL hF hcount (by
      have hh:=mul_le_mul_of_nonneg_right (show (({x,y}:Finset V).card:ℝ)+(r-1:ℕ)≤(r:ℝ)+2 by linarith only [hcard,hk])
        (show 0≤L+1 by linarith only [hL])
      linarith only [hbudget,hh])
  obtain ⟨C,hC,hCQ,hCxy,hCs,_⟩:=embedded_cycle_from_path_with_support Q r hr x y p hp hlen hxy
  have hH (a:V) (ha:a∈C.support):H a u:=by
    rcases hclass a ((hCs a).mp ha) with rfl|rfl|ha
    · exact hHx
    · exact hHy
    · exact hHA a ha.1
  have hFC:∀ a∈C.support,∀ c∈C.support,¬F.Adj a c:=by
    intro a ha c hc
    exact hind a ((hCs a).mp ha) c ((hCs c).mp hc)
  refine ⟨⟨(⟨⟨C,hC⟩,hCQ⟩,u),hH,hFC⟩,rfl,hCxy,?_⟩
  intro a ha
  rcases hclass a ((hCs a).mp ha) with he|he|ha
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr ⟨ha.1,ha.2.1⟩)

theorem ordinary_spoke_wheel_from_common_counts (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W:Finset V) (x:V) (u:U) (hHx:H x u) (hHA:∀ a∈A,H a u)
    (r:ℕ) (hr:3≤r) (L b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hcount:∀ a c,b≤((A∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:W.card+((r:ℝ)+2)*(L+1)<b) :
    ∃ C:OrdinaryWheel Q F H r,ordinaryWheelHub C=u ∧ x∈(ordinaryWheelRim C).support ∧
      (∀ a∈(ordinaryWheelRim C).support,a=x ∨ a∈A∧a∉W) := by
  obtain ⟨y,hyA,hyW,hyx,hxy,_,hFy⟩:=sparse_common_neighbour_avoiding Q F A W {x}
    x x L b hL hF (hcount x x) (by
      simp only [Finset.card_singleton,Nat.cast_one]
      have hr0:(0:ℝ)≤r:=Nat.cast_nonneg _
      nlinarith only [hbudget,hL,hr0])
  obtain ⟨C,hCu,hCxy,hCs⟩:=ordinary_rim_edge_wheel_from_common_counts Q F H A W x y u hxy
    (fun h=>hFy x (Finset.mem_singleton_self _) h.symm) hHx (hHA y hyA) hHA
    r hr L b hL hF hcount hbudget
  refine ⟨C,hCu,hCxy.mem_support_left,?_⟩
  intro a ha
  rcases hCs a ha with he|he|ha
  · exact Or.inl he
  · exact Or.inr (he ▸ ⟨hyA,hyW⟩)
  · exact Or.inr ha

end Oberwolfach
