module

public import Oberwolfach.VortexApplications
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section
/-! The initial vortex domains are the full parent domains, and the initial
reference degree is the original regular degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
theorem vortex_initial_parent_identities (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (hD:0<D) (hρ:0 < initialIndexDensity U D):
    (Q.vertices 0).card=Fintype.card V ∧ (Q.indices 0).card=Fintype.card U ∧
    2*((Q.indices 0).card:ℝ)/initialIndexDensity U D=D ∧
    ∀ x:Q.vertices 0,((G.comap (Subtype.val:Q.vertices 0→V)).degree x:ℝ)=(G.degree x.val:ℝ) := by
  have hU:0<(Fintype.card U:ℝ):=by
    have hDr:0<(D:ℝ):=by exact_mod_cast hD
    dsimp [initialIndexDensity] at hρ
    have hh:0<2*(Fintype.card U:ℝ):=(div_pos_iff_of_pos_right hDr).mp hρ
    linarith
  have hDr:(D:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  have hUr:(Fintype.card U:ℝ)≠0:=ne_of_gt hU
  refine ⟨by simp [Q.initial],by simp [Q.indices_initial],?_,?_⟩
  · simp only [Q.indices_initial,Finset.card_univ,initialIndexDensity]
    field_simp
  · intro x
    let e:Q.vertices 0↪V:=⟨Subtype.val,Subtype.val_injective⟩
    have himage:Finset.univ.image e=Finset.univ:=by
      ext v
      simp only [Finset.mem_univ,iff_true,Finset.mem_image,true_and,e,Function.Embedding.coeFn_mk]
      exact ⟨⟨v,by rw [Q.initial];simp⟩,rfl⟩
    have hh:=graph_comap_degree_into_image G e x
    rw [himage,Finset.inter_univ] at hh
    exact_mod_cast hh
end Oberwolfach
