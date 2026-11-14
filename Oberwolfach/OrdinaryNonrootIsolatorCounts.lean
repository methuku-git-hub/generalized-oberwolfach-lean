module

public import Oberwolfach.IsolatorDeletionCounts

@[expose] public section
/-! An excluded nonroot vertex occurs in only a controlled number of
isolator configurations rooted at a retained edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U]
  {P Q F:SimpleGraph V} {H:V→U→Prop} {k:ℕ} {θ α:ℝ} {x y:V}

theorem ordinary_isolator_excluded_vertex_count (hxy:x≠y) (hk:3≤k)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (z:V) (hzx:z≠x) (hzy:z≠y):
    (∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if z∈C.vertices.val then (1:ℝ) else 0)≤(Fintype.card V:ℝ)^(k-2):=by
  have hc:({x,y,z}:Finset V).card=3:=by simp [hxy,hzx.symm,hzy.symm]
  have hh:=isolator_configuration_root_count (P:=P) (Q:=Q) (F:=F) (H:=H)
    (k:=k) (θ:=θ) (α:=α) (x:=x) (y:=y) {x,y,z} (by rw [hc];exact hk)
  rw [hc] at hh
  have he:(∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if z∈C.vertices.val then (1:ℝ) else 0)=
      ∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if ({x,y,z}:Finset V)⊆C.vertices.val then (1:ℝ) else 0:=by
    apply Finset.sum_congr rfl
    intro C _
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,C.endpoints.1,C.endpoints.2,true_and]
  rw [he]
  apply hh.trans
  have hu':(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hu
  calc
    _ ≤ (Fintype.card V:ℝ)*(Fintype.card V:ℝ)^(k-3):=mul_le_mul_of_nonneg_right hu' (by positivity)
    _ = (Fintype.card V:ℝ)^(k-2):=by
      have hp:k-3+1=k-2:=by omega
      rw [←hp,pow_succ];ring
theorem ordinary_isolator_excluded_roots_loss (hxy:x≠y) (hk:3≤k)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (T:Finset V) (W:Finset U) (hx:x∉T) (hy:y∉T):
    (∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if C.hub∈W ∨ ∃z∈T,z∈C.vertices.val then (1:ℝ) else 0)≤
      ((T.card:ℝ)+W.card)*(Fintype.card V:ℝ)^(k-2):=by
  let M:ℝ:=(Fintype.card V:ℝ)^(k-2)
  have hp (C:OrdinaryIsolatorConfiguration P Q F H k θ α x y):
      (if C.hub∈W ∨ ∃z∈T,z∈C.vertices.val then (1:ℝ) else 0)≤
      (∑z∈T,if z∈C.vertices.val then (1:ℝ) else 0)+
      (∑u∈W,if C.hub=u then (1:ℝ) else 0):=by
    have h1:(0:ℝ)≤∑z∈T,if z∈C.vertices.val then (1:ℝ) else 0:=by
      apply Finset.sum_nonneg;intro z hz;split_ifs <;> norm_num
    have h2:(0:ℝ)≤∑u∈W,if C.hub=u then (1:ℝ) else 0:=by
      apply Finset.sum_nonneg;intro u hu;split_ifs <;> norm_num
    by_cases hb:C.hub∈W ∨ ∃z∈T,z∈C.vertices.val
    · rw [if_pos hb]
      rcases hb with hh|⟨z,hz,hzC⟩
      · have hs:=Finset.single_le_sum (s:=W) (a:=C.hub)
          (f:=fun u=>if C.hub=u then (1:ℝ) else 0)
          (fun u _=>by split_ifs <;> norm_num) hh
        simp only [ite_true] at hs
        linarith
      · have hs:=Finset.single_le_sum (s:=T) (a:=z)
          (f:=fun z=>if z∈C.vertices.val then (1:ℝ) else 0)
          (fun z _=>by split_ifs <;> norm_num) hz
        rw [if_pos hzC] at hs
        linarith
    · rw [if_neg hb];linarith
  have hV (z:V) (hz:z∈T):
      (∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x y,
        if z∈C.vertices.val then (1:ℝ) else 0)≤M:=by
    have hzx:z≠x:=by intro he;subst z;exact hx hz
    have hzy:z≠y:=by intro he;subst z;exact hy hz
    exact ordinary_isolator_excluded_vertex_count hxy hk hn hu z hzx hzy
  have hU (u:U):
      (∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x y,
        if C.hub=u then (1:ℝ) else 0)≤M:=
    isolator_configuration_hub_count u hxy (by omega)
  calc
    _ ≤ ∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x y,
        ((∑z∈T,if z∈C.vertices.val then (1:ℝ) else 0)+
        (∑u∈W,if C.hub=u then (1:ℝ) else 0)):=Finset.sum_le_sum (fun C _=>hp C)
    _ = (∑z∈T,∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x y,
          if z∈C.vertices.val then (1:ℝ) else 0)+
        (∑u∈W,∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x y,
          if C.hub=u then (1:ℝ) else 0):=by
      rw [Finset.sum_add_distrib]
      congr 1 <;> rw [Finset.sum_comm]
    _ ≤ (∑_z∈T,M)+(∑_u∈W,M):=
      add_le_add (Finset.sum_le_sum hV) (Finset.sum_le_sum (fun u _=>hU u))
    _ = _:=by simp [M];ring

end Oberwolfach
