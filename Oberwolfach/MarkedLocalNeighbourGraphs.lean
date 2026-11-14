module

public import Oberwolfach.MarkedLocalNeighbourCounts

@[expose] public section

/-! Converting the fixed inner-domain counts to graph neighbourhoods,
including permutation images and all roots outside the inner domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem invariant_finset_image (π : Equiv.Perm V) (A : Finset V) (hA : ∀ x,π x∈A ↔ x∈A) :
    A.image π=A := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (hA y).mpr hy
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨π.symm x,?_,π.apply_symm_apply x⟩
    exact (hA (π.symm x)).mp (by simpa only [Equiv.apply_symm_apply] using hx)

theorem rawMarkedLocal_graph_event (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (P : SimpleGraph V) (A : Finset V) (hA : A.Nonempty) (hInv : ∀ x,π x∈A ↔ x∈A)
    (K ε : ℝ) (hK : 1≤K) (hε : 0<ε)
    (hV : (Fintype.card V:ℝ)≤K*A.card) (hU : (Fintype.card U:ℝ)≤K*A.card)
    (g : Γ) (j : Color) (s₀ t₀ : ℝ) (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀) :
    1-12*K^2*(A.card:ℝ)^2*Real.exp (-(2*ε^2/((4*(d:ℝ)+3)^2*K))*A.card)≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ (b : Bool) (u : U),
          let T := rawMarkedLocalClass π d σ g j A b u
          let a := if b then t₀ else s₀
          |(T.card:ℝ)-a*A.card|<ε*A.card ∧
          (∀ x,|((P.neighborFinset x∩T).card:ℝ)-a*(P.neighborFinset x∩A).card|<ε*A.card) ∧
          (∀ x,|((P.neighborFinset x∩T.image π).card:ℝ)-a*(P.neighborFinset x∩A).card|<ε*A.card)) := by
  have hh := rawMarkedLocal_domain_event π d hd q hq hQ s hs hS hnoshort P A hA K ε hK hε hV hU g j s₀ t₀ hg hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ b u
  let T := rawMarkedLocalClass π d σ g j A b u
  refine ⟨hσ b u none,?_,?_⟩
  · intro x
    have hf : (P.neighborFinset x∩A).filter (fun v=>rawMarkedSpokes π d σ g j b v u)=P.neighborFinset x∩T := by
      ext v;simp only [T,rawMarkedLocalClass,Finset.mem_filter,Finset.mem_inter,and_assoc]
    simpa only [markedLocalDomain,hf] using hσ b u (some (Sum.inl x))
  · intro x
    have hf : (A.filter (fun v=>P.Adj x (π v))).filter (fun v=>rawMarkedSpokes π d σ g j b v u)=
        T.filter (fun v=>P.Adj x (π v)) := by
      ext v;simp only [T,rawMarkedLocalClass,Finset.mem_filter];tauto
    have hc : (A.filter (fun v=>P.Adj x (π v))).card=(P.neighborFinset x∩A).card := by
      rw [permutation_neighbour_filter_card,invariant_finset_image π A hInv]
    have hi := hσ b u (some (Sum.inr x))
    simpa only [markedLocalDomain,hf,hc,permutation_neighbour_filter_card] using hi

end Oberwolfach
