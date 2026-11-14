module

public import Oberwolfach.SeparatedCandidatePairs

@[expose] public section

/-! All triangular edge-stage vertices are chosen from the supplied
four-neighbour counts. The rim vertices are chosen first. Each subsequent
pair uses those fixed vertices, and its second choice also uses its first
vertex. This is the exposure order used in the manuscript. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E J:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq J]

theorem triangular_transformer_vertices (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W R:Finset V) (x y x' y':E→V) (v v':J→V) (u u':J→U) (e₀ e₁:J→E)
    (d c:ℝ) (hd:0≤d) (hF:∀ w,(F.degree w:ℝ)≤d)
    (hfour:∀ w x y z,c≤((A.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))
    (hspfour:∀ j w x y z,c≤((A.filter (fun a=>H a (u j)∧H a (u' j)∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+Fintype.card E+2*Fintype.card J+1)*(d+1)<c):
    ∃ (p:E↪V) (a b:J→V),
      (∀ e,p e∈A∧p e∉W∧p e∉R∧∀ w∈R,¬F.Adj (p e) w)∧
      (∀ e,Q.Adj (x e) (p e)∧Q.Adj (y e) (p e)∧Q.Adj (x' e) (p e)∧Q.Adj (y' e) (p e))∧
      (∀ j,a j∈A∧b j∈A∧Q.Adj (v j) (a j)∧Q.Adj (v' j) (a j)∧Q.Adj (p (e₀ j)) (a j)∧
        Q.Adj (v j) (b j)∧Q.Adj (v' j) (b j)∧Q.Adj (p (e₁ j)) (b j)∧Q.Adj (a j) (b j)∧
        H (a j) (u j)∧H (a j) (u' j)∧H (b j) (u j)∧H (b j) (u' j))∧
      (∀ j,∀ w∈({a j,b j}:Finset V),w∉W∧w∉R∧(∀ e,w≠p e)∧
        (∀ z∈R,¬F.Adj w z)∧∀ e,¬F.Adj w (p e))∧
      (∀ i j,i≠j→Disjoint ({a i,b i}:Finset V) {a j,b j})∧
      (∀ i j,¬F.Adj (p i) (p j))∧
      (∀ i j,∀ w∈({a i,b i}:Finset V),∀ z∈({a j,b j}:Finset V),¬F.Adj w z):=by
  let C:E→Finset V:=fun e=>A.filter (fun w=>Q.Adj (x e) w∧Q.Adj (y e) w∧Q.Adj (x' e) w∧Q.Adj (y' e) w)
  have hc:∀ e,c≤((C e).card:ℝ):=fun e=>hfour (x e) (y e) (x' e) (y' e)
  have hsmall:W.card+((R.card:ℝ)+Fintype.card E)*(d+1)<c:=by
    have ht:0≤(2*(Fintype.card J:ℝ)+1)*(d+1):=by positivity
    nlinarith only [hbudget,ht]
  obtain ⟨p,hp,hpp⟩:=separated_candidate_vertices F C W R d c hd hF hc hsmall
  let R':=R∪Finset.univ.image p
  have hR':(R'.card:ℝ)≤R.card+Fintype.card E:=by
    have hh:=Finset.card_union_le R (Finset.univ.image p)
    rw [Finset.card_image_of_injective _ p.injective,Finset.card_univ] at hh
    exact_mod_cast hh
  let C₀:J→Finset V:=fun j=>A.filter (fun w=>H w (u j)∧H w (u' j)∧Q.Adj (v j) w∧Q.Adj (v' j) w∧Q.Adj (p (e₀ j)) w)
  let C₁:J→V→Finset V:=fun j a=>A.filter (fun w=>H w (u j)∧H w (u' j)∧Q.Adj (v j) w∧Q.Adj (v' j) w∧Q.Adj (p (e₁ j)) w∧Q.Adj a w)
  have hC₀ (j:J):c≤((C₀ j).card:ℝ):=by
    simpa only [C₀,and_self] using hspfour j (v j) (v' j) (p (e₀ j)) (p (e₀ j))
  have hC₁ (j:J) (a:V) (_ha:a∈C₀ j):c≤((C₁ j a).card:ℝ):=
    hspfour j (v j) (v' j) (p (e₁ j)) a
  have hb:W.card+((R'.card:ℝ)+2*Fintype.card J+1)*(d+1)<c:=by
    have hh:=mul_le_mul_of_nonneg_right hR' (show 0≤d+1 by linarith)
    nlinarith only [hbudget,hh]
  obtain ⟨a,b,hab,havoid,hdis,hff⟩:=separated_candidate_pairs F C₀ C₁ W R' d c hd hF hC₀ hC₁ hb
  refine ⟨p,a,b,?_,?_,?_,?_,hdis,hpp,hff⟩
  · intro e;exact ⟨(Finset.mem_filter.mp (hp e).1).1,(hp e).2⟩
  · intro e;exact (Finset.mem_filter.mp (hp e).1).2
  · intro j
    have ha:=Finset.mem_filter.mp (hab j).1
    have hb:=Finset.mem_filter.mp (hab j).2.1
    exact ⟨ha.1,hb.1,ha.2.2.2.1,ha.2.2.2.2.1,ha.2.2.2.2.2,
      hb.2.2.2.1,hb.2.2.2.2.1,hb.2.2.2.2.2.1,hb.2.2.2.2.2.2,ha.2.1,ha.2.2.1,hb.2.1,hb.2.2.1⟩
  · intro j w hw
    have hh:=havoid j w hw
    refine ⟨hh.1,fun h=>hh.2.1 (Finset.mem_union_left _ h),?_,?_,?_⟩
    · intro e he
      exact hh.2.1 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,he.symm⟩))
    · intro z hz;exact hh.2.2 z (Finset.mem_union_left _ hz)
    · intro e;exact hh.2.2 (p e) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩))

end Oberwolfach
