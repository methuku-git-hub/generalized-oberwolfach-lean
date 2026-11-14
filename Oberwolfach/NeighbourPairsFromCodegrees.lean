module

public import Oberwolfach.DegreeCodegreeCuts
public import Oberwolfach.NeighbourPairAssignment

@[expose] public section

/-! The endpoint pairing with the large-cut hypothesis derived from the
actual degree and separated-codegree bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_neighbour_pairs_from_codegrees (p:ℝ) (hp:0<p) (hp1:p≤1) :
    ∃ ε:ℝ,0<ε ∧ ∀ b:ℕ,∃ N:ℕ,
      ∀ (X Y:Type) [Fintype X] [Fintype Y],∀ m:ℕ,N≤m →
      Fintype.card X=2*m → Fintype.card Y=m →
      ∀ (H:X→Y→Prop) (F:SimpleGraph X),
      (∀ x,F.degree x≤b) →
      (∀ x,(p-ε)*m≤∑ u,bipAdj H x u) →
      (∀ u,p*m≤∑ x,bipAdj H x u) →
      (∀ x y,x≠y → ¬F.Adj x y → ∑ u,bipAdj H x u*bipAdj H y u≤(p^2+ε)*m) →
      ∃ v w:Y↪X,(∀ u,H (v u) u∧H (w u) u∧¬F.Adj (v u) (w u)) ∧
        Disjoint (Set.range v) (Set.range w) ∧ (∀ x,(∃ u,v u=x)∨∃ u,w u=x) := by
  let η:=p/64
  have hη:0<η:=by dsimp [η];positivity
  let ε:=min (p/2) (p^2*η/24)
  have hε:0<ε:=by dsimp [ε];positivity
  refine ⟨ε,hε,?_⟩
  intro b
  obtain ⟨N₀,hN⟩:=ordinary_neighbour_pair_assignment (p/4) (by positivity) b
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (8*(b+1)/(p^2*η^2):ℝ)
  refine ⟨max N₀ (max N₁ 1),?_⟩
  intro X Y _ _ m hm hX hY H F hF hrow hcol hcodeg
  classical
  have hmpos:0<m:=by omega
  have hmass:(b+1:ℝ)≤p^2*η^2*m/8:=by
    have hh:=(div_lt_iff₀ (mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos hη))).mp
      (hN₁.trans_le (Nat.cast_le.mpr (show N₁≤m by omega)))
    nlinarith only [hh]
  let E:X→Finset X:=fun x=>insert x (F.neighborFinset x)
  have hE (x:X):((E x).card:ℝ)≤b+1:=by
    have hh:(E x).card≤b+1:=by
      have hh:=Finset.card_insert_le x (F.neighborFinset x)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hh
      exact hh.trans (Nat.add_le_add_right (hF x) 1)
    exact_mod_cast hh
  have hcodeg' (x y:X) (hy:y∉E x):∑ u,bipAdj H x u*bipAdj H y u≤(p^2+ε)*Fintype.card Y:=by
    have hne:x≠y:=by intro he;apply hy;simp [E,he]
    have hFxy:¬F.Adj x y:=by intro he;apply hy;exact Finset.mem_insert_of_mem ((F.mem_neighborFinset x y).mpr he)
    simpa only [hY] using hcodeg x y hne hFxy
  apply hN X Y m (by omega) hX hY H F
  · intro x
    have he:((Finset.univ.filter (H x)).card:ℝ)=∑ u,bipAdj H x u:=by simp only [bipAdj,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [he]
    have hsmall:ε≤p/2:=min_le_left _ _
    have hh:=mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg m : (0:ℝ)≤m)
    have hpos:0≤p*m:=by positivity
    nlinarith only [hrow x,hh,hpos]
  · intro u
    have he:((Finset.univ.filter (fun x=>H x u)).card:ℝ)=∑ x,bipAdj H x u:=by simp only [bipAdj,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [he]
    have hpos:0≤p*m:=by positivity
    nlinarith only [hcol u,hpos]
  · exact hF
  · intro S T hS hT
    have hSl:η*Fintype.card Y≤(S.card:ℝ):=by simpa only [hY,η,div_div,show (4*16:ℝ)=64 by norm_num] using hS
    have hTl:η*Fintype.card Y≤(T.card:ℝ):=by simpa only [hY,η,div_div,show (4*16:ℝ)=64 by norm_num] using hT
    have hh:=bipartite_cuts_from_degrees_and_codegrees H p ε (b+1) η hp hp1 hε.le hη
      (by simpa only [hY] using hmpos) E hE (by simpa only [hY] using hrow) hcodeg'
      (min_le_right _ _) (by simpa only [hY] using hmass) S T hSl hTl
    have hnonneg:0≤p*S.card*T.card:=by positivity
    nlinarith only [hh,hnonneg]

end Oberwolfach
