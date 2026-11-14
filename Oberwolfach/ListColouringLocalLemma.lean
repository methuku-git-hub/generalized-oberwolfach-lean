module

public import Oberwolfach.ListColourConflicts
public import Oberwolfach.ConditionalRealization
public import Oberwolfach.InterfaceFamilyRegularization

@[expose] public section

/-! A proper list colouring when each list is at least sixteen times the
largest number of neighbours that can use one specified colour. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_two_coordinate_values
    {V C : Type*} [Fintype V] [Fintype C]
    (μ : V → FiniteLaw C) (u v : V) (hne : u≠v) (a b : C) :
    (FiniteLaw.pi μ).probability (fun σ=>σ u=a ∧ σ v=b)=(μ u).mass a*(μ v).mass b := by
  classical
  have hh := finiteLaw_disjoint_supported_events μ {u} {v} (by simpa using hne)
    (fun σ=>σ u=a) (fun σ=>σ v=b)
    (fun σ τ he=>by rw [he u (by simp)])
    (fun σ τ he=>by rw [he v (by simp)])
  rw [finiteLaw_pi_coordinate_probability,finiteLaw_pi_coordinate_probability] at hh
  exact hh

theorem finite_list_colouring_of_colour_degree
    {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) {l d : ℕ}
    (hd : 0<d) (hcard : ∀ v,(L v).card=l)
    (hdegree : ∀ v c,(colourNeighbourSet G L v c).card≤d)
    (hlarge : 16*d≤l) :
    ∃ f : V → C,(∀ v,f v∈L v) ∧ ∀ u v,G.Adj u v → f u≠f v := by
  classical
  have hl : 0<l := by omega
  have hL (v : V) : (L v).Nonempty := Finset.card_pos.mp (by rw [hcard];exact hl)
  let μ := fun v=>FiniteLaw.uniformOn (L v) (hL v)
  let A := fun (p : ListColourConflict G L) (σ : V → C)=>σ p.val.1=p.val.2.2 ∧ σ p.val.2.1=p.val.2.2
  have hs (p : ListColourConflict G L) (σ τ : V → C)
      (he : ∀ v∈listColourConflictSupport G L p,σ v=τ v) : A p σ ↔ A p τ := by
    dsimp only [A]
    rw [he p.val.1 (by simp [listColourConflictSupport]),
      he p.val.2.1 (by simp [listColourConflictSupport])]
  have hp (p : ListColourConflict G L) :
      (FiniteLaw.pi μ).probability (A p)≤1/(4*((2*(2*l*d) : ℕ) : ℝ)) := by
    have hc : G.Adj p.val.1 p.val.2.1 ∧ p.val.2.2∈L p.val.1 ∧ p.val.2.2∈L p.val.2.1 := by
      simpa only [listColourConflicts,Finset.mem_filter,Finset.mem_univ,true_and] using p.property
    have hne : p.val.1≠p.val.2.1 := hc.1.ne
    rw [show A p=(fun σ=>σ p.val.1=p.val.2.2 ∧ σ p.val.2.1=p.val.2.2) from rfl,
      finiteLaw_two_coordinate_values μ _ _ hne]
    simp only [μ,FiniteLaw.uniformOn,hc.2.1,hc.2.2,ite_true,hcard]
    have hdr : (0 : ℝ)<d := by exact_mod_cast hd
    have hlr : (0 : ℝ)<l := by exact_mod_cast hl
    have hnum : (16 : ℝ)*(d : ℝ)≤l := by exact_mod_cast hlarge
    calc
      _ = 1/((l : ℝ)*(l : ℝ)) := by ring
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by
        norm_num only [Nat.cast_mul,Nat.cast_ofNat]
        nlinarith [mul_nonneg hlr.le (sub_nonneg.mpr hnum)])
  obtain ⟨f,hf,hgood⟩ := finiteLaw_coordinate_localLemma_degree μ A
    (listColourConflictSupport G L) hs (by norm_num : 0<2)
    (by positivity : 0<2*l*d) (listColourConflictSupport_size G L)
    (listColourConflictSupport_incidence G L hcard hdegree) hp
  have hlist (v : V) : f v∈L v := by
    have hh := finiteLaw_pi_positive_coordinates μ f hf v
    by_contra hn
    simp only [μ,FiniteLaw.uniformOn,hn,ite_false] at hh
    exact (lt_irrefl 0) hh
  refine ⟨f,hlist,?_⟩
  intro u v huv he
  let p : ListColourConflict G L := ⟨(u,v,f u),Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,huv,hlist u,by simpa only [he] using hlist v⟩⟩
  exact hgood p ⟨rfl,he.symm⟩

end Oberwolfach
