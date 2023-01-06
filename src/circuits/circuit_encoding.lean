import circuits.basic
import polytime.lemmas

open tencodable tree
open_locale tree complexity_class

variables {α β : Type} [tencodable α] [tencodable β]

def encode_function [fintype α] : tencodable (α → β) :=
by haveI : decidable_eq α := decidable_eq_of_encodable α; exact 
tencodable.of_left_injection (λ f, ((finset.univ : finset α).sort lift_le).map (λ x, (⟨x, f x⟩ : Σ _ : α, β)))
  (λ l, if H : ∀ a, a ∈ l.keys then some (λ x, option.get (list.lookup_is_some.mpr (H x))) else none) 
  (λ b, begin
    have : ∀ (a : α) (f : α → β), (((finset.univ : finset α).sort lift_le).map (λ x, (⟨x, f x⟩ : Σ _ : α, β))).lookup a = some (f a),
    { intros a f, apply list.mem_lookup, { simp [list.nodupkeys, list.keys], }, simp, },
    rw dif_pos, swap, { simp [← list.lookup_is_some, this], },
    rw option.some_inj, ext a, simp [this],
  end)

#check sigma.mk

