import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

variable (k : ℕ)

def d (h : ℕ) (m : ℕ) : ℤ :=
  if m ∣ h ∨ m = 0 then 0 else m - h%m

def h : ℕ → ℕ
  | 0 => 0
  | 1 => k
  | m+2 => (h (m+1)) + 2 * (d (h (m+1)) (m+2)).toNat

lemma d_nonneg : ∀ h m, d h m ≥ 0 := by
  intro h m
  by_cases hyp : m ∣ h <;> unfold d <;> norm_num [hyp]
  by_cases mp : m=0
  · omega
  norm_num [mp]
  apply le_of_lt
  apply Int.emod_lt_of_pos ↑h
  omega

def bc (m : ℕ) : ℤ :=
  d (h k m) (m+1)

lemma bc_lt_m : ∀ m, bc k m < m+1 := by
  intro m
  unfold bc d
  by_cases hyp : m+1 ∣ h k m <;> norm_num [hyp]
  norm_cast
  omega

lemma bc_nonneg : ∀ m, bc k m ≥ 0 := by
  unfold bc
  exact fun m => d_nonneg (h k m) (m+1)

def r (m : ℕ) : ℤ :=
  h k m + bc k m

lemma r_nonneg : ∀ m, r k m ≥ 0 := by
  intro m
  unfold r
  linarith [bc_nonneg k m]

def q (m : ℕ) : ℤ :=
  (r k m) / (m+1)

lemma q_nonneg : ∀ m, q k m ≥ 0 := by
  intro m
  unfold q
  apply Int.ediv_nonneg
  apply r_nonneg k m
  omega

lemma qrm : r k m = q k m * (m+1) := by
  unfold q
  symm
  apply Int.ediv_mul_cancel
  unfold r bc d
  norm_num
  by_cases hyp : (m+1) ∣ h k m <;> norm_num [hyp]
  · norm_cast
  ring_nf
  apply Int.modEq_iff_dvd.1
  simp only [Int.modEq_modulus_add_iff]
  exact Int.mod_modEq (↑(h k m)) (1 + ↑m)

lemma rh (m : ℕ) (mpos : m > 0) : h k (m+1) = r k m + bc k m := by
  let mm := m-1
  rw [show m = mm+1 by omega]
  unfold h r bc
  push_cast
  rw [Int.toNat_of_nonneg (d_nonneg _ _)]
  ring

lemma qbc (m : ℕ) : r k (m+2) = r k (m+1) + bc k (m+1) + bc k (m+2) := by
  unfold r bc
  rw [h]
  push_cast
  rw [Int.toNat_of_nonneg (d_nonneg _ _)]
  ring

-- q k m is the factor of m+1 in its minimal multiple that is >= h k m
lemma q_h (m : ℕ) : (q k m - 1) * (m+1) < h k m ∧ h k m ≤ q k m * (m+1) := by
  constructor
  · rw [sub_mul]
    rw [←qrm k]
    unfold r
    rw [←add_sub]
    norm_num [bc_lt_m k m]
  · rw [←qrm k]
    unfold r
    norm_num [bc_nonneg]

-- This lemma is unused
lemma q_ceil (m : ℕ) : q k m = ⌈(↑(h k m) : ℚ) / (↑(m+1) : ℚ)⌉ := by
  symm
  have qh := q_h k m
  norm_cast at qh
  have t : 0 < (↑(m+1) : ℚ) := by norm_cast; norm_num
  apply Int.ceil_eq_iff.mpr
  constructor
  · apply (lt_div_iff₀ t).2
    norm_cast
    linarith
  · apply (div_le_iff₀' t).2
    norm_cast
    linarith

lemma q_h' (m : ℕ) (qq : ℤ) (h : (qq - 1) * (m+1) < h k m ∧ h k m ≤ qq * (m+1)) : qq = q k m := by
  rcases h with ⟨h1, h2⟩
  apply eq_iff_le_not_lt.2
  constructor
  · contrapose! h2
    have : q k m ≤ qq - 1 := by omega
    have : r k m < h k m := calc
      _ = q k m * (m+1) := by rw [qrm k]
      _ ≤ (qq-1) * (m+1) := by norm_num [this]
      _ < _ := h1
    unfold r at this
    linarith [bc_nonneg k m]
  · contrapose! h1
    have : q k m - 1 ≥ qq := by omega
    have : h k m ≤ r k m - (↑m+1) := calc
      _ ≤ _ := h2
      _ ≤ (q k m - 1) * (m+1) := by norm_num [this]
      _ = q k m * (m+1) - (m+1) := by linarith
      _ = _ := by rw [←qrm k]
    unfold r at this
    linarith [bc_lt_m k m]


def bc_periodic := ∃ m₀, ∀ m > m₀, bc k m = bc k (m+2)

def q_const := ∃m₁, ∀ m > m₁, q k m = q k (m+1)

lemma q_stays_const (hyp : ∃m>0, q k m = q k (m+1)) : q_const k := by
  unfold q_const
  rcases hyp with ⟨m₁, mpos, hyp⟩
  use m₁
  intro m hm
  induction' m with m ih
  · trivial
  have mhyp : q k m = q k (m+1) := by
    by_cases mm : m = m₁
    · rwa [mm]
    · exact ih (by omega)
  --
  apply q_h' k (m+1+1) (q k (m+1))
  norm_num
  unfold h;  rw [←bc.eq_def k (m+1)];  norm_num [bc_nonneg]
  rw [two_mul, ←add_assoc, ←r.eq_def k (m+1)]
  rw [qrm, ←mhyp]
  norm_num
  have mpos : m > 0 := by omega
  have q_dr : q k m = r k (m+1) - r k m := by
    rw [qrm, qrm, ←mhyp]
    norm_num
    ring
  have hyp₂ : bc k (m+1) ≤ q k m := by
    rw [q_dr]
    trans r k (m+1) - h k (m+1)
    · unfold r
      norm_num
    · rw [sub_le_sub_iff]
      apply add_le_add_right
      unfold r
      trans ↑(h k m) + bc k m + bc k m
      · norm_num [bc_nonneg]
      rw [h.eq_def k (m+1)]
      let mm := m-1
      have t : m = mm+1 := by omega
      norm_num [t, ←bc.eq_def, bc_nonneg]
      omega
  symm
  constructor
  · linarith
  · suffices q k m - bc k (m+1) < ↑m+3 by linarith
    have aux : m-1+1 = m ∧ m-1+2 = m+1 := by omega
    have : q k m - bc k (m+1) = bc k m := by
      have qbcl := qbc k (m-1)
      norm_num [mpos, aux] at qbcl
      rw [q_dr, qbcl]
      ring
    rw [this]
    have := (q_h k m).1
    rw [sub_mul, ←qrm] at this
    norm_num at this
    unfold r at this
    trans ↑m+1 <;> linarith

lemma need_q_const (hyp : q_const k) : bc_periodic k := by
  unfold bc_periodic
  rcases hyp with ⟨m₁, hyp⟩
  use m₁
  intro m hm
  have mp : m > 0 := by omega
  have h1 := hyp m hm
  have h2 := hyp (m+1) (by omega)
  have qbc1 := qbc k (m-1)
  rw [←Nat.sub_add_comm (by omega), ←Nat.sub_add_comm (by omega)] at qbc1
  norm_num at qbc1
  have dr_eq_q : r k (m+1) - r k m = q k m := by
    rw [qrm, qrm, ←h1, Nat.cast_add]
    ring
  have dr_eq_q2 : r k (m+2) - r k (m+1) = q k (m+1) := by
    rw [qrm, qrm, h2]
    norm_num
    ring
  calc
    bc k m = r k (m+1) - r k m - bc k (m+1) := by rw [qbc1]; omega
    _ = q k m - bc k (m+1) := by rw [dr_eq_q]
    _ = q k (m+1) - bc k (m+1) := by rw [h1]
    _ = _ := by rw [←dr_eq_q2]
    _ = _ := by rw [qbc]; ring

lemma q_nonincreasing (m : ℕ) (mpos : m>0) (q_ge_m : q k m ≥ m+1)
 : q k (m+1) ≤ q k m := by
  have qh := (q_h k (m+1)).1
  have hyp : h k (m+1) < q k m * (m+2) := calc
    _ = q k m * (m+1) + bc k m := by rw [rh k m mpos, qrm]
    _ ≤ q k m * (m+1) + m := by linarith [bc_lt_m k m]
    _ < q k m * (m+1) + q k m := by omega -- q_ge_m used here
    _ = _ := by ring
  have := lt_trans qh hyp
  norm_num at this
  apply Int.le_of_sub_one_lt
  apply lt_of_mul_lt_mul_right _ (show (m:ℤ)+2 ≥ 0 by omega)
  linarith

lemma q_decr_not_so_fast (m : ℕ) (mpos : m>0) (hyp : q k m > m+2)
 : q k (m+1) ≥ m+2 := by
  by_contra hyp₁
  have := calc
    (m+3) * (m+1) ≤ q k m * (m+1) :=
     Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    _ ≤ h k (m+1) := by rw [←qrm, rh k m mpos]; norm_num [bc_nonneg]
    _ ≤ q k (m+1) * (m+2) := by exact_mod_cast (q_h k (m+1)).2
    _ ≤ (m+1) * (m+2) := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  linarith


theorem bc_are_periodic : bc_periodic k := by
  apply need_q_const
  apply q_stays_const
  by_cases hyp : ∃ m, q k (m+1) ≥ m+2 ∧ q k (m+1) = q k (m+2)
  · rcases hyp with ⟨m, hyp⟩
    use m+1
    norm_num [hyp]
  push Not at hyp
  have large_q_decreases : ∀ (m : ℕ), q k (m+1) ≥ ↑m+2 → q k (m+2) < q k (m+1) := by
    intro m m_small
    have h1 := q_nonincreasing k (m+1) (by omega) (by omega)
    have h2 := hyp m m_small
    symm at h2
    exact Int.lt_iff_le_and_ne.2 ⟨h1, h2⟩
  by_cases k_big_enough : k ≤ 3
  · use 1
    unfold q r bc d h d h
    norm_num
    by_cases k=0; subst k; norm_num
    by_cases k=1; subst k; norm_num
    by_cases k=2; subst k; norm_num
    have : k=3 := by omega
    subst k; norm_num
  push Not at k_big_enough
  have base : q k 1 ≥ 2 := by
    unfold q r bc d h
    norm_num
    omega -- k_big_enough needed here
  have ⟨m, ⟨hm1, hm2⟩⟩ :
   ∃ m, q k (m+1) ≥ ↑m+2 ∧ q k (m+2) < ↑m+3 := by
    by_contra hyp₁
    push Not at hyp₁
    have h1 : ∀ m, ↑m+2 ≤ q k (m+1) := by
      intro m
      induction' m with m ih
      · norm_num [base]
      exact_mod_cast hyp₁ m ih
    have h2 : ∀ m, q k (m+1) ≤ q k 1 := by
      intro m
      induction' m with m ih
      · norm_num
      trans q k (m+1)
      · linarith [large_q_decreases m (h1 m)]
      · exact ih
    have : ∀ m : ℕ, ↑m+2 ≤ q k 1 := by
      intro m
      exact le_trans (h1 m) (h2 m)
    have := this (q k 1).toNat
    norm_num [q_nonneg] at this
  have hdr : q k (m+1) * (↑m+2) ≤ q k (m+2) * (↑m+3) := by
    show q k (m+1) * (↑(m+1)+1) ≤ q k (m+2) * (↑(m+2)+1)
    rw [←qrm, ←qrm, qbc]
    linarith [bc_nonneg k (m+1), bc_nonneg k (m+2)]
  have AB_alternative : q k (m+1) = m+2 ∨ q k (m+1) = m+3 := by
    have := q_decr_not_so_fast k (m+1) (by omega)
    contrapose! this
    push_cast
    rw [add_assoc]
    norm_num [hm2]
    omega
  rcases AB_alternative with hm | hm
  · use m+1
    rw [add_assoc, hm]
    norm_num
    have : q k (m+2) > ↑m+1 := by
      by_contra hyp
      push Not at hyp
      have := calc
        (↑m+2) * (↑m+2) = q k (m+1) * (↑m+2) := by nth_rw 1 [←hm]
        _ ≤ q k (m+2) * (↑m+3) := hdr
        _ ≤ (↑m+1) * (↑m+3) := mul_le_mul_of_nonneg_right hyp (by omega)
      linarith
    omega
  · use m+2
    have : m+2 ≤ q k (m+2) := by
      apply le_of_mul_le_mul_right _ (show 0 < (m:ℤ)+3 by omega)
      nth_rw 1 [←hm]
      rw [mul_comm]
      exact hdr
    by_cases q k (m+2) = m+3
    · omega
    have q_eq_m : q k (m+2) = m+2 := by omega
    rw [q_eq_m]
    norm_num
    have rr : r k (m+1) = r k (m+2) := by
      rw [qrm, qrm, hm, q_eq_m]
      norm_cast
      ring
    have : bc k (m+2) = 0 := by
      have := qbc k m
      rw [rr] at this
      linarith [bc_nonneg k (m+1), bc_nonneg k (m+2)]
    apply q_h' k (m+3) _
    rw [rh _ _ (by omega), this, qrm, q_eq_m]
    push_cast
    constructor <;> linarith
