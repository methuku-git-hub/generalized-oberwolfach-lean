module

public import Oberwolfach.EndpointRelativeCounts

@[expose] public section

/-! Ordinary endpoint degrees and codegrees, with the original domain
normalisations. The index tests are imposed on independent sets only. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_endpoint_counts_from_common (P R F : SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (B:Finset U) (x:V) (q s ε:ℝ)
    (hRP:R≤P) (hFx:∀ v,R.Adj x v → ¬F.Adj x v)
    (hrow:∀ S:Finset V,∀ J:Finset U,S.card≤1 → J.card≤1 →
      |((common (common A S (fun v=>R.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
        q^S.card*s^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card)
    (hindex:∀ S:Finset V,S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common B S (fun v=>Finset.univ.filter (H v))).card:ℝ)-s^S.card*B.card|≤ε*B.card) :
    let E:=A∩P.neighborFinset x
    let S:=A∩R.neighborFinset x
    let T:=B.filter (H x)
    |(S.card:ℝ)-q*E.card|≤ε*A.card ∧
    |(T.card:ℝ)-s*B.card|≤ε*B.card ∧
    (∀ v∈S,|((T.filter (H v)).card:ℝ)-s^2*B.card|≤ε*B.card) ∧
    (∀ u∈B,|((S.filter (fun v=>H v u)).card:ℝ)-q*s*E.card|≤ε*A.card) ∧
    (∀ v∈S,∀ w∈S,v≠w → ¬F.Adj v w →
      ((T.filter (fun u=>H v u∧H w u)).card:ℝ)≤s^3*B.card+ε*B.card) := by
  dsimp only
  have hs (G:SimpleGraph V):common A ({x}:Finset V) (fun v=>G.neighborFinset v)=A∩G.neighborFinset x:=by
    ext a;simp [mem_common_iff]
  have he (K:Finset V):common K (∅:Finset U) (fun u=>Finset.univ.filter (fun v=>H v u))=K:=by
    ext a;simp [mem_common_iff]
  have hi (Z:Finset V):common B Z (fun v=>Finset.univ.filter (H v))=
      B.filter (fun u=>∀ v∈Z,H v u):=by ext u;simp [mem_common_iff]
  have hx (v:V) (hv:v∈A∩R.neighborFinset x):P.Adj x v:=hRP ((R.mem_neighborFinset x v).mp (Finset.mem_inter.mp hv).2)
  have hxv (v:V) (hv:v∈A∩R.neighborFinset x):x≠v:=(hx v hv).ne
  have hf (v:V) (hv:v∈A∩R.neighborFinset x):¬F.Adj x v:=hFx v ((R.mem_neighborFinset x v).mp (Finset.mem_inter.mp hv).2)
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hh:=hrow {x} ∅ (by simp) (by simp)
    simpa only [Finset.card_singleton,Finset.card_empty,pow_one,pow_zero,mul_one,he,hs] using hh
  · have hh:=hindex {x} (by simp) (by intros v hv w hw;simp only [Finset.mem_singleton] at hv hw;subst v;subst w;exact F.loopless.irrefl x)
    simpa only [hi,Finset.mem_singleton,forall_eq,Finset.card_singleton,pow_one] using hh
  · intro v hv
    have hsep:∀ a∈({x,v}:Finset V),∀ b∈({x,v}:Finset V),¬F.Adj a b:=by
      intros a ha b hb hab
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
      · exact F.loopless.irrefl _ hab
      · exact hf _ hv hab
      · exact hf _ hv hab.symm
      · exact F.loopless.irrefl _ hab
    have hh:=hindex {x,v} (by simp [hxv v hv]) hsep
    have hc:({x,v}:Finset V).card=2:=Finset.card_pair (hxv v hv)
    have ht:(B.filter (fun u=>∀ a∈({x,v}:Finset V),H a u))=(B.filter (H x)).filter (H v):=by
      ext u;simp;tauto
    rw [hi,ht,hc] at hh
    exact hh
  · intro u hu
    have hh:=hrow {x} {u} (by simp) (by simp)
    have ht:common (common A ({x}:Finset V) (fun v=>R.neighborFinset v)) ({u}:Finset U)
      (fun u=>Finset.univ.filter (fun v=>H v u))=(A∩R.neighborFinset x).filter (fun v=>H v u):=by
        ext v;simp [mem_common_iff]
    rw [ht,hs] at hh
    simpa only [Finset.card_singleton,pow_one] using hh
  · intro v hv w hw hvw hfw
    have hsep:∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬F.Adj a b:=by
      intros a ha b hb hab
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
      · exact F.loopless.irrefl _ hab
      · exact hf _ hv hab
      · exact hf _ hw hab
      · exact hf _ hv hab.symm
      · exact F.loopless.irrefl _ hab
      · exact hfw hab
      · exact hf _ hw hab.symm
      · exact hfw hab.symm
      · exact F.loopless.irrefl _ hab
    have hc:({x,v,w}:Finset V).card=3:=by simp [hxv v hv,hxv w hw,hvw]
    have hh:=hindex {x,v,w} (by rw [hc]) hsep
    have ht:(B.filter (fun u=>∀ a∈({x,v,w}:Finset V),H a u))=
      (B.filter (H x)).filter (fun u=>H v u∧H w u):=by ext u;simp;tauto
    rw [hi,ht,hc] at hh
    linarith only [(abs_le.mp hh).2]

end Oberwolfach
