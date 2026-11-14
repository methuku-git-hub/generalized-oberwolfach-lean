module

public import Oberwolfach.RootOmittedLocalStability
public import Oberwolfach.ResourceForbiddenPairWeights
public import Oberwolfach.AbsorberGeneralPairRestriction

@[expose] public section

/-! Local alteration and pair-deletion losses at the sampled order.
The coefficients in these estimates do not involve the sampling density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T:Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Fintype T] [DecidableEq T] {c:ℕ}

theorem root_omitted_local_change_scale (R:C→Finset V) (c J:ℕ) (hc:2≤c)
    (hR:∀ i,(R i).card=c) (hJ:∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J)
    (w:C→ℝ) (B k L ζ:ℝ) (hB:0≤B) (hk:0<k) (hL:0≤L) (hζ:0≤ζ)
    (hw:∀ i,0≤w i ∧ w i≤B/k^(c-1)) (A D:Finset V) (v:V)
    (hchange:((A\D).card+(D\A).card:ℕ)≤ζ*k)
    (hsize:((A∪D).card:ℝ)+1≤L*k):
    |resourceRootOmittedLoad R w (fun x=>x∈A) v-
      resourceRootOmittedLoad R w (fun x=>x∈D) v|≤ζ*(J:ℝ)*L^(c-2)*B:=by
  have hh:=root_omitted_load_local_change R c J hc hR hJ w (B/k^(c-1)) (by positivity) hw A D v
  apply hh.trans
  calc
    _≤(ζ*k)*(J:ℝ)*(L*k)^(c-2)*(B/k^(c-1)):=by gcongr
    _=_:=by
      rw [mul_pow]
      have he:k^(c-1)=k^(c-2)*k:=by rw [←pow_succ];congr 1;omega
      rw [he]
      field_simp

theorem absorber_ground_change_scale (R:C→Finset V)
    (S:T→VertexAbsorberTemplate c) (hc:1≤c) (X A D:Finset V) (hX:X.card=c)
    (J:ℕ) (hJ:∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J)
    (k L ζ:ℝ) (hk:0≤k) (hL:0≤L) (hζ:0≤ζ)
    (hchange:((A\D).card+(D\A).card:ℕ)≤ζ*k)
    (hsize:((A∪D).card:ℝ)≤L*k):
    |absorberGroundCount R S X A-absorberGroundCount R S X D|≤
      ζ*((c*c)*Fintype.card T*c^c*J^(2*c+1):ℕ)*L^(c*c-1)*k^(c*c):=by
  have hh:=absorber_ground_local_change R S X A D J hJ
  rw [hX] at hh
  push_cast at hh hchange
  apply hh.trans
  calc
    _≤(ζ*k)*((c:ℝ)*c*Fintype.card T*(c:ℝ)^c*(L*k)^(c*c-1)*(J:ℝ)^(2*c+1)):=by gcongr
    _=_:=by
      have hcc:1≤c*c:=by nlinarith
      have he:k^(c*c)=k^(c*c-1)*k:=by
        rw [←pow_succ]
        congr 1
        omega
      rw [mul_pow,he]
      push_cast
      ring

theorem resource_sparse_pairs_degree_loss_scale (R:C→Finset V) (c J:ℕ) (hc:3≤c)
    (hR:∀ i,(R i).card=c) (hJ:∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J)
    (w:C→ℝ) (B k L ζ:ℝ) (hB:0≤B) (hk:0<k) (hL:0≤L) (hζ:0≤ζ)
    (hw:∀ i,0≤w i ∧ w i≤B/k^(c-1)) (Y:Finset V) (hY:(Y.card:ℝ)≤L*k)
    (E:Finset (V×V)) (hE:∀ e∈E,e.1≠e.2) (v:V)
    (hd:((E.filter (fun e=>v=e.1 ∨ v=e.2)).card:ℝ)≤ζ*k)
    (hsize:(E.card:ℝ)≤ζ*k^2):
    0≤hypergraphWeightedDegree R (inducedResourceWeight R w Y) v-
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v ∧
    hypergraphWeightedDegree R (inducedResourceWeight R w Y) v-
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v≤
      ζ*(J:ℝ)*B*(L^(c-2)+L^(c-3)):=by
  obtain ⟨hlo,hhi⟩:=resource_forbidden_pairs_degree_loss R c J hc hR hJ w
    (B/k^(c-1)) (by positivity) hw Y E hE v
  have hs:((E.filter (fun e=>¬(v=e.1 ∨ v=e.2))).card:ℝ)≤ζ*k^2:=
    (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hsize
  refine ⟨hlo,hhi.trans ?_⟩
  calc
    _≤(ζ*k)*((J:ℝ)*(L*k)^(c-2)*(B/k^(c-1)))+
        (ζ*k^2)*((J:ℝ)*(L*k)^(c-3)*(B/k^(c-1))):=by gcongr
    _=_:=by
      have he1:k^(c-1)=k^(c-3)*k^2:=by rw [←pow_add];congr 1;omega
      have he2:k^(c-2)=k^(c-3)*k:=by rw [←pow_succ];congr 1;omega
      rw [mul_pow,mul_pow,he1,he2]
      field_simp
      <;> ring

theorem finite_pairs_incident_set_real_bound (E:Finset (V×V)) (X:Finset V) (d:ℝ)
    (hd:∀ v∈X,((E.filter (fun e=>v=e.1 ∨ v=e.2)).card:ℝ)≤d):
    ((E.filter (fun e=>e.1∈X ∨ e.2∈X)).card:ℝ)≤X.card*d:=by
  have hs:E.filter (fun e=>e.1∈X ∨ e.2∈X)⊆
      X.biUnion (fun v=>E.filter (fun e=>v=e.1 ∨ v=e.2)):=by
    intro e he
    obtain ⟨he,hx⟩:=Finset.mem_filter.mp he
    rcases hx with hx|hx
    · exact Finset.mem_biUnion.mpr ⟨e.1,hx,Finset.mem_filter.mpr ⟨he,Or.inl rfl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨e.2,hx,Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩⟩
  calc
    _≤((X.biUnion (fun v=>E.filter (fun e=>v=e.1 ∨ v=e.2))).card:ℝ):=Nat.cast_le.mpr (Finset.card_le_card hs)
    _≤∑ v∈X,((E.filter (fun e=>v=e.1 ∨ v=e.2)).card:ℝ):=by exact_mod_cast Finset.card_biUnion_le
    _≤∑ _v∈X,d:=Finset.sum_le_sum hd
    _=_:=by simp

theorem absorber_ground_sparse_pairs_scale (R:C→Finset V) (S:T→VertexAbsorberTemplate c)
    (hc:2≤c) (X Y:Finset V) (hX:X.card=c) (J:ℕ)
    (hJ:∀ U:Finset V,Fintype.card {i:C // R i=U}≤J)
    (E:Finset (V×V)) (hE:∀ e∈E,e.1≠e.2)
    (k L ζ:ℝ) (hk:0≤k) (hL:0≤L) (hζ:0≤ζ) (hY:(Y.card:ℝ)≤L*k)
    (hd:∀ v∈X,((E.filter (fun e=>v=e.1 ∨ v=e.2)).card:ℝ)≤ζ*k)
    (hsize:(E.card:ℝ)≤ζ*k^2):
    absorberGroundCount R S X Y≤
      absorberGroundCount (candidateResourceSet R
        (fun i=>∀ e:E,¬(e.val.1∈R i ∧ e.val.2∈R i))) S X Y+
      ζ*(Fintype.card T:ℝ)*(c:ℝ)^c*(J:ℝ)^(2*c+1)*
        ((c:ℝ)*(c*c:ℕ)*L^(c*c-1)+((c*c:ℕ):ℝ)^2*L^(c*c-2))*k^(c*c):=by
  have hh:=candidate_absorber_ground_general_pair_loss R S X Y J hJ E hE
  have hinc:=finite_pairs_incident_set_real_bound E X (ζ*k) hd
  rw [hX] at hinc hh
  have hnon:((E.filter (fun e=>¬(e.1∈X ∨ e.2∈X))).card:ℝ)≤ζ*k^2:=
    (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hsize
  push_cast at hh
  apply hh.trans
  apply add_le_add le_rfl
  calc
    _≤((c:ℝ)*(ζ*k))*((c:ℝ)*c*Fintype.card T*(c:ℝ)^c*(L*k)^(c*c-1)*(J:ℝ)^(2*c+1))+
        (ζ*k^2)*(((c:ℝ)*c)^2*Fintype.card T*(c:ℝ)^c*(L*k)^(c*c-2)*(J:ℝ)^(2*c+1)):=by gcongr
    _=_:=by
      have hcc:2≤c*c:=by nlinarith
      have he1:k^(c*c)=k^(c*c-2)*k^2:=by rw [←pow_add];congr 1;omega
      have he2:k^(c*c-1)=k^(c*c-2)*k:=by rw [←pow_succ];congr 1;omega
      rw [mul_pow,mul_pow,he1,he2]
      push_cast
      ring

end Oberwolfach
