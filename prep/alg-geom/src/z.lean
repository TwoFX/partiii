import ring_theory.ideal.operations

universe u
variables {A : Type u} [comm_ring A]

section
variables (A)

def Spec := { p : ideal A // p.is_prime }
end

def V (I : ideal A) : set (Spec A) :=
{ p | I.carrier ⊆ p.val.carrier }

@[simps]
instance : has_inter (ideal A) :=
{ inter := λ I J,
  { carrier := I.carrier ∩ J.carrier,
    zero_mem' := ⟨ideal.zero_mem _, ideal.zero_mem _⟩,
    add_mem' := λ a b ⟨haI, haJ⟩ ⟨hbI, hbJ⟩, ⟨ideal.add_mem _ haI hbI, ideal.add_mem _ haJ hbJ⟩,
    smul_mem' := λ c _ ⟨hI, hJ⟩, ⟨ideal.mul_mem_left _ hI, ideal.mul_mem_left _ hJ⟩ } }

lemma inter_sub_prime {I₁ I₂ p : ideal A} (hp : p.is_prime) (h : I₁ ∩ I₂ ≤ p) : I₁ ≤ p ∨ I₂ ≤ p :=
begin
  contrapose! h,
  change ¬I₁.carrier ⊆ p.carrier ∧ ¬I₂.carrier ⊆ p.carrier at h,
  simp only [set.not_subset] at h,
  rcases h with ⟨⟨i, hi, hi'⟩, ⟨j, hj, hj'⟩⟩,
  have : i * j ∈ I₁ ∩ I₂ := ⟨ideal.mul_mem_right _ hi, ideal.mul_mem_left _ hj⟩,
  intro h,
  cases ideal.is_prime.mem_or_mem hp (h this) with h' h',
  { exact hi' h' },
  { exact hj' h' }
end

lemma V_inter (I₁ I₂ : ideal A) : V (I₁ ∩ I₂) = V I₁ ∪ V I₂ :=
begin
  ext, simp [V],
  refine ⟨inter_sub_prime x.2, _⟩,
  rintros (h|h);
  refine set.subset.trans _ h;
  simp
end