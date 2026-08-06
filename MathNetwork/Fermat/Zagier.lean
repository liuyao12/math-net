import Archive.ZagierTwoSquares

namespace MathNetwork.Fermat

open Zagier

/--
The Fermat two-square theorem through the fixed-point/involution route.

The finite set, the two involutions, their fixed-point lemmas, and the
involution parity theorem are imported from mathlib's archived Zagier
development. The final assembly is written locally so this proposition has a
distinct proof-route node in Math Network rather than being a synonym for the
finished mathlib theorem.
-/
theorem fermat_two_squares_involution {p : ℕ} [h : Fact p.Prime]
    (hp : p % 4 = 1) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  rw [← Nat.div_add_mod p 4, hp] at h ⊢
  let k := p / 4
  apply sq_add_sq_of_nonempty_fixedPoints
  have key :=
    (Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1)
      (obvInvo_sq k)).symm.trans
    (Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1)
      (complexInvo_sq k))
  contrapose key
  rw [Set.not_nonempty_iff_eq_empty] at key
  simp_rw [k, key, Fintype.card_eq_zero, card_fixedPoints_eq_one]
  decide

end MathNetwork.Fermat
