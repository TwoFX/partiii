import ring_theory.ideal.basic

variables {R : Type*} [comm_ring R]

def mult (S : set R) : Prop :=
(1 : R) ∈ S ∧ ∀ x y, (x ∈ S ∧ y ∈ S) → x * y ∈ S

def saturated (S : set R) : Prop :=
∀ x y, x * y ∈ S → (x ∈ S ∧ y ∈ S)

lemma saturated_iff (S : set R) (h : mult S) :
  saturated S ↔ ∃ {ι : Type} (p : ι → ideal R), (∀ i, (p i).is_prime) ∧ Sᶜ = ⋃ i, (p i).carrier :=
begin
  classical, split,
  { sorry },
  { rintros ⟨ι, p, ⟨hp, hS⟩⟩ x y hxy,
    contrapose hxy,
    rw not_and_distrib at hxy,
    cases hxy;
    { rw [←set.mem_compl_iff, hS, set.mem_Union] at hxy,
      rcases hxy with ⟨i, hi⟩,
      have : x * y ∈ (p i).carrier := ideal.mul_mem_right _ hi <|>
      have : x * y ∈ (p i).carrier := ideal.mul_mem_left _ hi,
      rw [←set.mem_compl_iff, hS, set.mem_Union],
      exact ⟨_, this⟩ } }
end