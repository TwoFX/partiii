import data.mv_polynomial.comm_ring
import ring_theory.ideal.basic

open mv_polynomial

variables {k : Type*} [field k] {n : ℕ}

def is_affine_variety (V : set (fin n → k)) : Prop :=
∃ F : set (mv_polynomial (fin n) k), F.finite ∧
    ∀ x, x ∈ V ↔ ∀ (f : mv_polynomial (fin n) k), f ∈ F → eval x f = 0

def I (V : set (fin n → k)) : set (mv_polynomial (fin n) k) :=
{ f | ∀ x ∈ V, eval x f = 0 }

def V (I : set (mv_polynomial (fin n) k)) : set (fin n → k) :=
{ x | ∀ f ∈ I, eval x f = 0 }

lemma I_empty : I (∅ : set (fin n → k)) = set.univ :=
begin
  rw set.eq_univ_iff_forall,
  intros f x,
  simp only [set.mem_empty_eq, forall_prop_of_false, not_false_iff]
end

theorem ex_1 (I₁ I₂ : set (mv_polynomial (fin n) k)) (h : I₁ ⊆ I₂) : V I₂ ⊆ V I₁ :=
λ x hx f hf, hx _ (h hf)

theorem ex_2 (V₁ V₂ : set (fin n → k)) (h : V₁ ⊆ V₂) : I V₂ ⊆ I V₁ :=
λ x hx f hf, hx _ (h hf)

theorem ex_3 (V₁ : set (fin n → k)) : is_affine_variety V₁ → V (I V₁) = V₁ :=
begin
  rintro ⟨F, ⟨-, hF⟩⟩,
  have hF' : F ⊆ I V₁ := λ f hf x hx, (hF x).1 hx _ hf,
  apply set.subset.antisymm,
  { exact λ x hx, (hF x).2 (λ f hf, hx _ (hF' hf)) },
  { exact λ x hx f hf, hf _ hx }
end

def rad (I : set (mv_polynomial (fin n) k)) : set (mv_polynomial (fin n) k) :=
{ f | ∃ m : ℕ, f ^ m ∈ I }

lemma rad_eq (I : ideal (mv_polynomial (fin n) k)) :
  rad I.carrier = { f | ∃ m : ℕ, 0 < m ∧ f ^ m ∈ I } :=
begin
  apply set.subset.antisymm,
  { rintros f ⟨m, hm⟩,
    by_cases h : 0 < m,
    { exact ⟨m, ⟨h, hm⟩⟩ },
    simp only [le_zero_iff_eq, not_lt] at h,
    subst h,
    change f ^ 0 ∈ I at hm,
    simp only [pow_zero, ←ideal.eq_top_iff_one] at hm,
    subst hm,
    exact ⟨1, ⟨dec_trivial, submodule.mem_top⟩⟩ },
  { rintros f ⟨m, ⟨-, hm⟩⟩,
    exact ⟨m, hm⟩ }
end

theorem lem {f : mv_polynomial (fin n) k} {m : ℕ} {x : fin n → k}
  (hfx : eval x (f^m) = 0) : eval x f = 0 :=
begin
  induction m with m hm,
  { rw [pow_zero, ring_hom.map_one] at hfx,
    exact false.elim (one_ne_zero hfx) },
  { rw [pow_succ, ring_hom.map_mul] at hfx,
    cases eq_zero_or_eq_zero_of_mul_eq_zero hfx,
    { exact h },
    { exact hm h } }
end

theorem ex_4 (I₁ : set (mv_polynomial (fin n) k)) : rad I₁ ⊆ I (V I₁) :=
λ f ⟨m, hfm⟩ x hx, lem (hx _ hfm)