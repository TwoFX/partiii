import topology.sheaves.sheaf
import category_theory.abelian.basic

open_locale classical
noncomputable theory

universes v u

open category_theory
open category_theory.limits
open opposite

variables {C : Type u} [category.{v} C] [has_products C] [abelian C]
variables {X : Top.{v}}

local attribute [instance] has_zero_object.has_zero

def skyscraper (p : X) (A : C) : Top.sheaf C X :=
{ presheaf :=
  { obj := λ U, if p ∈ unop U then A else 0,
    map := λ V U hVU,
    begin
      
    end,
    map_id' := _,
    map_comp' := _ },
  sheaf_condition := _ }