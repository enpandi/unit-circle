import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import AngleNiceness

/-!
# Specification layer (Mathlib)

`AngleNiceness.lean` keeps the executable implementation; this file states what
that implementation is supposed to compute — `nicenessSpec`, defined with
Mathlib's `Nat.totient` — and proves:

* **bridges**: the executable `phi`/`niceness` agree with `Nat.totient`/
  `nicenessSpec` (exhaustively checked ranges, via `native_decide`);
* **unbounded theorems**: for *all* k, n, the niceness of x = 2πk/n is
  invariant under x ↦ −x (reflection across the x-axis) and under
  x ↦ π − x (reflection across the y-axis), and {0, π/2, π, 3π/2} all have
  niceness 1.
-/

namespace AngleNiceness

/-! ## the specification -/

/-- D as a function of the reduced denominator m: φ(m)/2 if 4 ∣ m, else φ(m). -/
def Dden (m : ℕ) : ℕ := if 4 ∣ m then m.totient / 2 else m.totient

/-- What `niceness` is supposed to compute: `D = [ℚ(cos x, sin x) : ℚ]` for
    x = 2πk/n depends only on the reduced denominator of k/n. -/
def nicenessSpec (k n : ℕ) : ℕ := Dden (n / Nat.gcd k n)

/-! ## bridges: the executable code agrees with the spec -/

/-- The trial-division `phi` is `Nat.totient` (checked for n ≤ 1000). -/
theorem phi_agrees_totient :
    ((List.range 1000).all fun n =>
      phi (Int.ofNat n + 1) == Int.ofNat (Nat.totient (n + 1))) = true := by
  native_decide

/-- The executable `niceness` agrees with `nicenessSpec`
    (checked for all 0 ≤ k ≤ n ≤ 900, past the `completeDens 10` scan bound 882). -/
theorem niceness_agrees_spec :
    ((List.range 900).all fun i => (List.range (i + 2)).all fun k =>
      niceness (Int.ofNat k) (Int.ofNat i + 1) == Int.ofNat (nicenessSpec k (i + 1))) = true := by
  native_decide

/-! ## small helpers -/

private theorem coprime_two_of_odd {b : ℕ} (h : b % 2 = 1) : Nat.Coprime 2 b := by
  unfold Nat.Coprime
  rw [Nat.gcd_rec 2 b, h]
  exact Nat.gcd_one_left 2

private theorem odd_dvd_cancel_two {d m : ℕ} (hd : d % 2 = 1) (h : d ∣ 2 * m) : d ∣ m :=
  ((coprime_two_of_odd hd).symm).dvd_of_dvd_mul_left h

/-- A common divisor of a and b is 1 when a, b are coprime. -/
private theorem eq_one_of_dvd_coprime {d a b : ℕ} (hab : Nat.Coprime a b)
    (ha : d ∣ a) (hb : d ∣ b) : d = 1 :=
  Nat.dvd_one.mp (hab ▸ Nat.dvd_gcd ha hb)

/-! ## reflection across the y-axis: x ↦ π − x

For x = 2πk/n, π − x = 2π(n−2k)/(2n). If b is the reduced denominator of
k/n, the reduced denominator of (n−2k)/(2n) is `reflectDen b`:
2b for odd b, b/2 for b ≡ 2 (mod 4), b for 4 ∣ b. -/

def reflectDen (b : ℕ) : ℕ :=
  if b % 2 = 1 then 2 * b else if b % 4 = 2 then b / 2 else b

/-- D is unchanged by `reflectDen` — the totient computation. -/
theorem Dden_reflectDen (b : ℕ) : Dden (reflectDen b) = Dden b := by
  by_cases h2 : b % 2 = 1
  · -- odd b: reflectDen b = 2b, and φ(2b) = φ(2)·φ(b) = φ(b); 4 divides neither
    have h1 : reflectDen b = 2 * b := by simp [reflectDen, h2]
    have hnd : ¬ 4 ∣ 2 * b := by omega
    have hnd' : ¬ 4 ∣ b := by omega
    rw [h1]
    unfold Dden
    rw [if_neg hnd, if_neg hnd', Nat.totient_mul (coprime_two_of_odd h2),
        Nat.totient_two, one_mul]
  · by_cases h42 : b % 4 = 2
    · -- b = 2t with t odd: reflectDen b = t, and φ(b) = φ(2t) = φ(t)
      have h1 : reflectDen b = b / 2 := by simp [reflectDen, h2, h42]
      have ht : (b / 2) % 2 = 1 := by omega
      have hb2 : b = 2 * (b / 2) := by omega
      have hnd : ¬ 4 ∣ b := by omega
      have hnd' : ¬ 4 ∣ b / 2 := by omega
      rw [h1]
      unfold Dden
      rw [if_neg hnd', if_neg hnd]
      conv_rhs => rw [hb2]
      rw [Nat.totient_mul (coprime_two_of_odd ht), Nat.totient_two, one_mul]
    · -- 4 ∣ b: reflectDen b = b
      have h1 : reflectDen b = b := by simp [reflectDen, h2, h42]
      rw [h1]

/-- The gcd underlying the reduced denominator of (b−2a)/(2b), coprime case. -/
theorem gcd_reflect_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    Nat.gcd ((b : ℤ) - 2 * a).natAbs (2 * b) =
      if b % 2 = 1 then 1 else if b % 4 = 2 then 4 else 2 := by
  by_cases h2 : b % 2 = 1
  · -- odd b: any common divisor is odd, hence divides b and a, hence is 1
    simp only [h2, if_pos]
    set d := Nat.gcd ((b : ℤ) - 2 * a).natAbs (2 * b) with hd
    have hdu : d ∣ ((b : ℤ) - 2 * a).natAbs := Nat.gcd_dvd_left ..
    have hdv : d ∣ 2 * b := Nat.gcd_dvd_right ..
    have hzu : (d : ℤ) ∣ (b : ℤ) - 2 * a := Int.natCast_dvd.mpr hdu
    have hodd : d % 2 = 1 := by
      by_contra hcon
      have h2d : (2 : ℤ) ∣ (d : ℤ) := by
        exact_mod_cast Int.natCast_dvd_natCast.mpr (show 2 ∣ d by omega)
      have : (2 : ℤ) ∣ (b : ℤ) - 2 * a := dvd_trans h2d hzu
      omega
    have hdb : d ∣ b := odd_dvd_cancel_two hodd hdv
    have hz2a : (d : ℤ) ∣ 2 * (a : ℤ) := by
      have hzb : (d : ℤ) ∣ (b : ℤ) := Int.natCast_dvd_natCast.mpr hdb
      have := dvd_sub hzb hzu
      have heq : (b : ℤ) - ((b : ℤ) - 2 * a) = 2 * a := by ring
      rwa [heq] at this
    have hda : d ∣ a := by
      have : d ∣ 2 * a := by
        have := Int.natCast_dvd.mp hz2a
        simpa using this
      exact odd_dvd_cancel_two hodd this
    exact eq_one_of_dvd_coprime hab hda hdb
  · have ha : a % 2 = 1 := by
      -- a must be odd since gcd(a, b) = 1 and b is even
      by_contra ha
      have h2a : 2 ∣ a := by omega
      have h2b : 2 ∣ b := by omega
      have := eq_one_of_dvd_coprime hab h2a h2b
      omega
    by_cases h42 : b % 4 = 2
    · -- b = 2t, t odd: b − 2a = 4s and 2b = 4t with gcd(s, t) = 1
      simp only [h2, h42, if_pos, if_false]
      set t := b / 2 with htdef
      have hbt : b = 2 * t := by omega
      have hts : (2 : ℤ) ∣ ((t : ℤ) - a) := by omega
      obtain ⟨s, hs⟩ := hts
      have hkey : (b : ℤ) - 2 * a = 4 * s := by push_cast [hbt]; omega
      have habs : ((b : ℤ) - 2 * a).natAbs = 4 * s.natAbs := by
        rw [hkey, Int.natAbs_mul]; rfl
      have h2b4t : 2 * b = 4 * t := by omega
      rw [habs, h2b4t, Nat.gcd_mul_left]
      -- gcd(|s|, t) = 1: a common divisor divides t and a = t − 2s
      have : Nat.gcd s.natAbs t = 1 := by
        set e := Nat.gcd s.natAbs t with he
        have heu : e ∣ s.natAbs := Nat.gcd_dvd_left ..
        have hev : e ∣ t := Nat.gcd_dvd_right ..
        have hzs : (e : ℤ) ∣ s := Int.natCast_dvd.mpr heu
        have hzt : (e : ℤ) ∣ (t : ℤ) := Int.natCast_dvd_natCast.mpr hev
        have hza : (e : ℤ) ∣ (a : ℤ) := by
          have h1 : (e : ℤ) ∣ (t : ℤ) - 2 * s := dvd_sub hzt (Dvd.dvd.mul_left hzs 2)
          have h2' : (t : ℤ) - 2 * s = a := by omega
          rwa [h2'] at h1
        have hea : e ∣ a := Int.natCast_dvd_natCast.mp hza
        have heb : e ∣ b := hbt ▸ Dvd.dvd.mul_left hev 2
        exact eq_one_of_dvd_coprime hab hea heb
      rw [this]
    · -- 4 ∣ b: b − 2a = 2·(odd) and 2b = 2·(2t); the odd part is coprime to 2t
      simp only [h2, h42, if_false]
      set t := b / 2 with htdef
      have hbt : b = 2 * t := by omega
      have ht4 : t % 2 = 0 := by omega
      have hkey : (b : ℤ) - 2 * a = 2 * ((t : ℤ) - a) := by push_cast [hbt]; ring
      have habs : ((b : ℤ) - 2 * a).natAbs = 2 * ((t : ℤ) - a).natAbs := by
        rw [hkey, Int.natAbs_mul]; rfl
      have h2b : 2 * b = 2 * (2 * t) := by omega
      rw [habs, h2b, Nat.gcd_mul_left]
      have : Nat.gcd ((t : ℤ) - a).natAbs (2 * t) = 1 := by
        set e := Nat.gcd ((t : ℤ) - a).natAbs (2 * t) with he
        have heu : e ∣ ((t : ℤ) - a).natAbs := Nat.gcd_dvd_left ..
        have hev : e ∣ 2 * t := Nat.gcd_dvd_right ..
        have hzu : (e : ℤ) ∣ (t : ℤ) - a := Int.natCast_dvd.mpr heu
        have hodd : e % 2 = 1 := by
          by_contra hcon
          have h2e : (2 : ℤ) ∣ (e : ℤ) := by
            exact_mod_cast Int.natCast_dvd_natCast.mpr (show 2 ∣ e by omega)
          have : (2 : ℤ) ∣ (t : ℤ) - a := dvd_trans h2e hzu
          omega
        have het : e ∣ t := odd_dvd_cancel_two hodd hev
        have hza : (e : ℤ) ∣ (a : ℤ) := by
          have hzt : (e : ℤ) ∣ (t : ℤ) := Int.natCast_dvd_natCast.mpr het
          have h1 : (e : ℤ) ∣ (t : ℤ) - ((t : ℤ) - a) := dvd_sub hzt hzu
          have h2' : (t : ℤ) - ((t : ℤ) - a) = a := by ring
          rwa [h2'] at h1
        have hea : e ∣ a := Int.natCast_dvd_natCast.mp hza
        have heb : e ∣ b := hbt ▸ Dvd.dvd.mul_left het 2
        exact eq_one_of_dvd_coprime hab hea heb
      rw [this]

/-- Reduced denominator of (b−2a)/(2b) in the coprime case. -/
theorem den_reflect_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    2 * b / Nat.gcd ((b : ℤ) - 2 * a).natAbs (2 * b) = reflectDen b := by
  rw [gcd_reflect_coprime hab]
  unfold reflectDen
  split_ifs <;> omega

/-! ## the headline theorems, unbounded -/

/-- {0, π/2, π, 3π/2} — i.e. 2πk/4 for k = 0, 1, 2, 3 — all have niceness 1. -/
theorem nicenessSpec_cardinal :
    nicenessSpec 0 4 = 1 ∧ nicenessSpec 1 4 = 1 ∧
    nicenessSpec 2 4 = 1 ∧ nicenessSpec 3 4 = 1 := by decide

/-- Negation x ↦ −x (reflection across the x-axis): 2πk/n ↦ 2π(n−k)/n
    leaves the niceness unchanged, for **all** k ≤ n. -/
theorem nicenessSpec_neg (k n : ℕ) (h : k ≤ n) :
    nicenessSpec (n - k) n = nicenessSpec k n := by
  unfold nicenessSpec
  rw [Nat.gcd_self_sub_left h]

/-- Reflection x ↦ π − x (across the y-axis): 2πk/n ↦ 2π(n−2k)/(2n)
    leaves the niceness unchanged, for **all** k and n > 0. -/
theorem nicenessSpec_reflect (k n : ℕ) (hn : 0 < n) :
    nicenessSpec ((n : ℤ) - 2 * k).natAbs (2 * n) = nicenessSpec k n := by
  set g := Nat.gcd k n with hg
  have hgn : g ∣ n := Nat.gcd_dvd_right k n
  have hgk : g ∣ k := Nat.gcd_dvd_left k n
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right k hn
  set a := k / g with hadef
  set b := n / g with hbdef
  have hk : k = g * a := (Nat.mul_div_cancel' hgk).symm
  have hn' : n = g * b := (Nat.mul_div_cancel' hgn).symm
  have hab : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hg0
  -- (n : ℤ) − 2k = g·(b − 2a), so its |·| is g·|b − 2a|
  have hfac : (n : ℤ) - 2 * k = (g : ℤ) * ((b : ℤ) - 2 * a) := by
    rw [hk, hn']; push_cast; ring
  have habs : ((n : ℤ) - 2 * k).natAbs = g * ((b : ℤ) - 2 * a).natAbs := by
    rw [hfac, Int.natAbs_mul, Int.natAbs_natCast]
  have h2n : 2 * n = g * (2 * b) := by rw [hn']; ring
  unfold nicenessSpec
  rw [habs, h2n, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hg0,
      den_reflect_coprime hab, Dden_reflectDen]

/-! ## the full reflection group

The picture has three mirror symmetries: the x-axis (x ↦ −x), the y-axis
(x ↦ π − x), and the diagonal (x ↦ π/2 − x, which swaps cos and sin).
All three preserve D, hence so does any finite composition of them
(`nicenessSpec_reflections` below). On fractions of a full turn they act as

  x-axis:   k/n ↦ (n − k)/n
  y-axis:   k/n ↦ (n − 2k)/(2n)
  diagonal: k/n ↦ (n − 4k)/(4n)

(numerators via |·| so the maps are total). Note the denominator can grow —
that is why a drawn point's mirror can fall outside a picture that only
enumerates denominators up to some bound, e.g. 80° = 2π·2/9 is drawn for
n ≤ 24 but its diagonal mirror 10° = 2π·1/36 is not. -/

private theorem totient_two_mul_odd {b : ℕ} (h : b % 2 = 1) :
    Nat.totient (2 * b) = Nat.totient b := by
  rw [Nat.totient_mul (coprime_two_of_odd h), Nat.totient_two, one_mul]

private theorem totient_four_mul_odd {b : ℕ} (h : b % 2 = 1) :
    Nat.totient (4 * b) = 2 * Nat.totient b := by
  have h2 := coprime_two_of_odd h
  have h4 : Nat.Coprime 4 b := Nat.Coprime.mul_left h2 h2
  rw [Nat.totient_mul h4, show Nat.totient 4 = 2 by decide]

/-- Reflection across the x-axis, total form: D is unchanged for all k, n. -/
theorem nicenessSpec_reflX (k n : ℕ) :
    nicenessSpec ((n : ℤ) - k).natAbs n = nicenessSpec k n := by
  have hg : Nat.gcd ((n : ℤ) - k).natAbs n = Nat.gcd k n := by
    apply Nat.dvd_antisymm
    · set d := Nat.gcd ((n : ℤ) - k).natAbs n with hd
      have hzu : (d : ℤ) ∣ (n : ℤ) - k := Int.natCast_dvd.mpr (Nat.gcd_dvd_left ..)
      have hzn : (d : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right ..)
      have hzk : (d : ℤ) ∣ (k : ℤ) := by
        have := dvd_sub hzn hzu
        rwa [show (n : ℤ) - ((n : ℤ) - k) = k by ring] at this
      exact Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hzk) (Nat.gcd_dvd_right ..)
    · set e := Nat.gcd k n with he
      have hzk : (e : ℤ) ∣ (k : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left ..)
      have hzn : (e : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right ..)
      exact Nat.dvd_gcd (Int.natCast_dvd.mp (dvd_sub hzn hzk)) (Nat.gcd_dvd_right ..)
  unfold nicenessSpec
  rw [hg]

/-- The diagonal reflection, coprime case: D of the reduced denominator of
    (b − 4a)/(4b) equals D of b. Unlike the axis reflections, the reduced
    denominator here can depend on a (when 4 ∣ b), so the statement goes
    through `Dden` directly. -/
theorem Dden_diag_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    Dden (4 * b / Nat.gcd ((b : ℤ) - 4 * a).natAbs (4 * b)) = Dden b := by
  by_cases h2 : b % 2 = 1
  · -- odd b: the gcd is 1 and the reduced denominator is 4b
    have hg : Nat.gcd ((b : ℤ) - 4 * a).natAbs (4 * b) = 1 := by
      set d := Nat.gcd ((b : ℤ) - 4 * a).natAbs (4 * b) with hd
      have hzu : (d : ℤ) ∣ (b : ℤ) - 4 * a := Int.natCast_dvd.mpr (Nat.gcd_dvd_left ..)
      have hdv : d ∣ 4 * b := Nat.gcd_dvd_right ..
      have hodd : d % 2 = 1 := by
        by_contra hcon
        have h2d : (2 : ℤ) ∣ (d : ℤ) := by
          exact_mod_cast Int.natCast_dvd_natCast.mpr (show 2 ∣ d by omega)
        have : (2 : ℤ) ∣ (b : ℤ) - 4 * a := dvd_trans h2d hzu
        omega
      have hdb : d ∣ b := by
        have h1 : d ∣ 2 * (2 * b) := by rwa [show 2 * (2 * b) = 4 * b by ring]
        exact odd_dvd_cancel_two hodd (odd_dvd_cancel_two hodd h1)
      have hda : d ∣ a := by
        have hzb : (d : ℤ) ∣ (b : ℤ) := Int.natCast_dvd_natCast.mpr hdb
        have hz4a : (d : ℤ) ∣ 4 * (a : ℤ) := by
          have := dvd_sub hzb hzu
          rwa [show (b : ℤ) - ((b : ℤ) - 4 * a) = 4 * a by ring] at this
        have h4a : d ∣ 4 * a := by
          have := Int.natCast_dvd.mp hz4a
          simpa using this
        have h1 : d ∣ 2 * (2 * a) := by rwa [show 2 * (2 * a) = 4 * a by ring]
        exact odd_dvd_cancel_two hodd (odd_dvd_cancel_two hodd h1)
      exact eq_one_of_dvd_coprime hab hda hdb
    rw [hg, Nat.div_one]
    unfold Dden
    rw [if_pos ⟨b, rfl⟩, if_neg (show ¬ 4 ∣ b by omega), totient_four_mul_odd h2]
    omega
  · have ha : a % 2 = 1 := by
      by_contra ha
      have := eq_one_of_dvd_coprime hab (show 2 ∣ a by omega) (show 2 ∣ b by omega)
      omega
    by_cases h42 : b % 4 = 2
    · -- b = 2t with t odd: the reduced denominator is 4t = 2b
      set t := b / 2 with htdef
      have hbt : b = 2 * t := by omega
      have htodd : t % 2 = 1 := by omega
      have hkey : (b : ℤ) - 4 * a = 2 * ((t : ℤ) - 2 * a) := by push_cast [hbt]; ring
      have habs : ((b : ℤ) - 4 * a).natAbs = 2 * ((t : ℤ) - 2 * a).natAbs := by
        rw [hkey, Int.natAbs_mul]; rfl
      have h4b : 4 * b = 2 * (4 * t) := by omega
      rw [habs, h4b, Nat.gcd_mul_left]
      have hinner : Nat.gcd ((t : ℤ) - 2 * a).natAbs (4 * t) = 1 := by
        set e := Nat.gcd ((t : ℤ) - 2 * a).natAbs (4 * t) with he
        have hzu : (e : ℤ) ∣ (t : ℤ) - 2 * a := Int.natCast_dvd.mpr (Nat.gcd_dvd_left ..)
        have hev : e ∣ 4 * t := Nat.gcd_dvd_right ..
        have hodd : e % 2 = 1 := by
          by_contra hcon
          have h2e : (2 : ℤ) ∣ (e : ℤ) := by
            exact_mod_cast Int.natCast_dvd_natCast.mpr (show 2 ∣ e by omega)
          have : (2 : ℤ) ∣ (t : ℤ) - 2 * a := dvd_trans h2e hzu
          omega
        have het : e ∣ t := by
          have h1 : e ∣ 2 * (2 * t) := by rwa [show 2 * (2 * t) = 4 * t by ring]
          exact odd_dvd_cancel_two hodd (odd_dvd_cancel_two hodd h1)
        have hea : e ∣ a := by
          have hzt : (e : ℤ) ∣ (t : ℤ) := Int.natCast_dvd_natCast.mpr het
          have hz2a : (e : ℤ) ∣ 2 * (a : ℤ) := by
            have := dvd_sub hzt hzu
            rwa [show (t : ℤ) - ((t : ℤ) - 2 * a) = 2 * a by ring] at this
          have h2a : e ∣ 2 * a := by
            have := Int.natCast_dvd.mp hz2a
            simpa using this
          exact odd_dvd_cancel_two hodd h2a
        have heb : e ∣ b := hbt ▸ Dvd.dvd.mul_left het 2
        exact eq_one_of_dvd_coprime hab hea heb
      rw [hinner, mul_one, show 2 * (4 * t) / 2 = 4 * t by omega]
      unfold Dden
      rw [if_pos ⟨t, rfl⟩, if_neg (show ¬ 4 ∣ b by omega), totient_four_mul_odd htodd,
          hbt, totient_two_mul_odd htodd]
      omega
    · -- 4 ∣ b, say b = 4v; the reduced denominator depends on (v − a) mod 4
      set v := b / 4 with hvdef
      have hbv : b = 4 * v := by omega
      have hkey : (b : ℤ) - 4 * a = 4 * ((v : ℤ) - a) := by push_cast [hbv]; ring
      have habs : ((b : ℤ) - 4 * a).natAbs = 4 * ((v : ℤ) - a).natAbs := by
        rw [hkey, Int.natAbs_mul]; rfl
      have h16 : 4 * b = 4 * (4 * v) := by omega
      rw [habs, h16, Nat.gcd_mul_left]
      by_cases hveven : v % 2 = 0
      · -- v − a odd: gcd is 1, reduced denominator is 4v = b itself
        have hinner : Nat.gcd ((v : ℤ) - a).natAbs (4 * v) = 1 := by
          set e := Nat.gcd ((v : ℤ) - a).natAbs (4 * v) with he
          have hzu : (e : ℤ) ∣ (v : ℤ) - a := Int.natCast_dvd.mpr (Nat.gcd_dvd_left ..)
          have hev : e ∣ 4 * v := Nat.gcd_dvd_right ..
          have hodd : e % 2 = 1 := by
            by_contra hcon
            have h2e : (2 : ℤ) ∣ (e : ℤ) := by
              exact_mod_cast Int.natCast_dvd_natCast.mpr (show 2 ∣ e by omega)
            have : (2 : ℤ) ∣ (v : ℤ) - a := dvd_trans h2e hzu
            omega
          have hevv : e ∣ v := by
            have h1 : e ∣ 2 * (2 * v) := by rwa [show 2 * (2 * v) = 4 * v by ring]
            exact odd_dvd_cancel_two hodd (odd_dvd_cancel_two hodd h1)
          have hea : e ∣ a := by
            have hzv : (e : ℤ) ∣ (v : ℤ) := Int.natCast_dvd_natCast.mpr hevv
            have hza : (e : ℤ) ∣ (a : ℤ) := by
              have := dvd_sub hzv hzu
              rwa [show (v : ℤ) - ((v : ℤ) - a) = a by ring] at this
            exact Int.natCast_dvd_natCast.mp hza
          have heb : e ∣ b := hbv ▸ Dvd.dvd.mul_left hevv 4
          exact eq_one_of_dvd_coprime hab hea heb
        rw [hinner, mul_one, show 4 * (4 * v) / 4 = 4 * v by omega, ← hbv]
      · have hvodd : v % 2 = 1 := by omega
        by_cases hw4 : ((v : ℤ) - a) % 4 = 0
        · -- v ≡ a (mod 4): reduced denominator is v (odd)
          obtain ⟨sZ, hs⟩ := (show (4 : ℤ) ∣ ((v : ℤ) - a) by omega)
          have habs2 : ((v : ℤ) - a).natAbs = 4 * sZ.natAbs := by
            rw [hs, Int.natAbs_mul]; rfl
          rw [habs2, Nat.gcd_mul_left]
          have hinner : Nat.gcd sZ.natAbs v = 1 := by
            set e := Nat.gcd sZ.natAbs v with he
            have hzs : (e : ℤ) ∣ sZ := Int.natCast_dvd.mpr (Nat.gcd_dvd_left ..)
            have hevv : e ∣ v := Nat.gcd_dvd_right ..
            have hea : e ∣ a := by
              have hzv : (e : ℤ) ∣ (v : ℤ) := Int.natCast_dvd_natCast.mpr hevv
              have hza : (e : ℤ) ∣ (a : ℤ) := by
                have := dvd_sub hzv (Dvd.dvd.mul_left hzs 4)
                rwa [show (v : ℤ) - 4 * sZ = a by omega] at this
              exact Int.natCast_dvd_natCast.mp hza
            have heb : e ∣ b := hbv ▸ Dvd.dvd.mul_left hevv 4
            exact eq_one_of_dvd_coprime hab hea heb
          rw [hinner, mul_one, show 4 * (4 * v) / (4 * 4) = v by omega]
          unfold Dden
          rw [if_neg (show ¬ 4 ∣ v by omega), hbv, if_pos ⟨v, rfl⟩,
              totient_four_mul_odd hvodd]
          omega
        · -- v − a ≡ 2 (mod 4): reduced denominator is 2v
          obtain ⟨uZ, hu⟩ := (show (2 : ℤ) ∣ ((v : ℤ) - a) by omega)
          have huodd : uZ % 2 = 1 := by omega
          have habs2 : ((v : ℤ) - a).natAbs = 2 * uZ.natAbs := by
            rw [hu, Int.natAbs_mul]; rfl
          rw [habs2, show 4 * v = 2 * (2 * v) by ring, Nat.gcd_mul_left]
          have hinner : Nat.gcd uZ.natAbs (2 * v) = 1 := by
            set e := Nat.gcd uZ.natAbs (2 * v) with he
            have hzu : (e : ℤ) ∣ uZ := Int.natCast_dvd.mpr (Nat.gcd_dvd_left ..)
            have hev : e ∣ 2 * v := Nat.gcd_dvd_right ..
            have hodd : e % 2 = 1 := by
              by_contra hcon
              have h2e : (2 : ℤ) ∣ (e : ℤ) := by
                exact_mod_cast Int.natCast_dvd_natCast.mpr (show 2 ∣ e by omega)
              have : (2 : ℤ) ∣ uZ := dvd_trans h2e hzu
              omega
            have hevv : e ∣ v := odd_dvd_cancel_two hodd hev
            have hea : e ∣ a := by
              have hzv : (e : ℤ) ∣ (v : ℤ) := Int.natCast_dvd_natCast.mpr hevv
              have hza : (e : ℤ) ∣ (a : ℤ) := by
                have := dvd_sub hzv (Dvd.dvd.mul_left hzu 2)
                rwa [show (v : ℤ) - 2 * uZ = a by omega] at this
              exact Int.natCast_dvd_natCast.mp hza
            have heb : e ∣ b := hbv ▸ Dvd.dvd.mul_left hevv 4
            exact eq_one_of_dvd_coprime hab hea heb
          rw [hinner, mul_one, show 4 * (2 * (2 * v)) / (4 * 2) = 2 * v by omega]
          unfold Dden
          rw [if_neg (show ¬ 4 ∣ 2 * v by omega), totient_two_mul_odd hvodd,
              hbv, if_pos ⟨v, rfl⟩, totient_four_mul_odd hvodd]
          omega

/-- Reflection across the diagonal x ↦ π/2 − x (which swaps cos x and sin x):
    2πk/n ↦ 2π(n−4k)/(4n) leaves the niceness unchanged, for all k and n > 0.
    This is the symmetry relating 80° = 2π·2/9 and 10° = 2π·1/36. -/
theorem nicenessSpec_diag (k n : ℕ) (hn : 0 < n) :
    nicenessSpec ((n : ℤ) - 4 * k).natAbs (4 * n) = nicenessSpec k n := by
  set g := Nat.gcd k n with hg
  have hgn : g ∣ n := Nat.gcd_dvd_right k n
  have hgk : g ∣ k := Nat.gcd_dvd_left k n
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right k hn
  set a := k / g with hadef
  set b := n / g with hbdef
  have hk : k = g * a := (Nat.mul_div_cancel' hgk).symm
  have hn' : n = g * b := (Nat.mul_div_cancel' hgn).symm
  have hab : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hg0
  have hfac : (n : ℤ) - 4 * k = (g : ℤ) * ((b : ℤ) - 4 * a) := by
    rw [hk, hn']; push_cast; ring
  have habs : ((n : ℤ) - 4 * k).natAbs = g * ((b : ℤ) - 4 * a).natAbs := by
    rw [hfac, Int.natAbs_mul, Int.natAbs_natCast]
  have h4n : 4 * n = g * (4 * b) := by rw [hn']; ring
  unfold nicenessSpec
  rw [habs, h4n, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hg0, Dden_diag_coprime hab]

/-! ## closure: any sequence of reflections preserves the niceness -/

/-- The three mirror symmetries of the picture. -/
inductive Refl where
  | acrossX    -- x ↦ −x
  | acrossY    -- x ↦ π − x
  | acrossDiag -- x ↦ π/2 − x
  deriving DecidableEq, Repr

/-- The action of a reflection on (k, n) representing the angle 2πk/n. -/
def applyRefl : Refl → ℕ × ℕ → ℕ × ℕ
  | .acrossX, (k, n) => (((n : ℤ) - k).natAbs, n)
  | .acrossY, (k, n) => (((n : ℤ) - 2 * k).natAbs, 2 * n)
  | .acrossDiag, (k, n) => (((n : ℤ) - 4 * k).natAbs, 4 * n)

theorem applyRefl_pos (r : Refl) (p : ℕ × ℕ) (h : 0 < p.2) : 0 < (applyRefl r p).2 := by
  obtain ⟨k, n⟩ := p
  cases r <;> simp [applyRefl] <;> omega

/-- One reflection preserves the niceness. -/
theorem nicenessSpec_applyRefl (r : Refl) (k n : ℕ) (hn : 0 < n) :
    nicenessSpec (applyRefl r (k, n)).1 (applyRefl r (k, n)).2 = nicenessSpec k n := by
  cases r
  · exact nicenessSpec_reflX k n
  · exact nicenessSpec_reflect k n hn
  · exact nicenessSpec_diag k n hn

/-- **Any number of reflections, in any order, across the x-axis, the y-axis
    or the diagonal, leaves the niceness unchanged.** -/
theorem nicenessSpec_reflections (ops : List Refl) (k n : ℕ) (hn : 0 < n) :
    nicenessSpec (ops.foldl (fun p r => applyRefl r p) (k, n)).1
                 (ops.foldl (fun p r => applyRefl r p) (k, n)).2
      = nicenessSpec k n := by
  induction ops generalizing k n with
  | nil => rfl
  | cons r ops ih =>
    rw [List.foldl_cons]
    have hpos : 0 < (applyRefl r (k, n)).2 := applyRefl_pos r (k, n) hn
    have hstep := ih (applyRefl r (k, n)).1 (applyRefl r (k, n)).2 hpos
    rw [show ((applyRefl r (k, n)).1, (applyRefl r (k, n)).2) = applyRefl r (k, n)
          from rfl] at hstep
    rw [hstep, nicenessSpec_applyRefl r k n hn]

/-- The observed instance: 10° = 2π·1/36 is the diagonal mirror of
    80° = 2π·2/9, and both have niceness 6 (the page draws only denominators
    n ≤ 24, which is why 10° is missing from the picture). -/
theorem eighty_and_ten_degrees :
    applyRefl .acrossDiag (2, 9) = (1, 36) ∧
    nicenessSpec 2 9 = 6 ∧ nicenessSpec 1 36 = 6 := by decide


/-! ## complete sets: inverting D

`Dden n ≤ T` forces `n ≤ 2(2T+1)²`, via the elementary bound n ≤ 2·φ(n)².
So the set of all angles with niceness ≤ T is finite and can be constructed
directly by a bounded scan — no enumeration cutoff, no reflection-closure
needed. `Gen.lean` draws exactly `completeDens MAXD`. -/

/-- Odd numbers satisfy m ≤ φ(m)². -/
theorem le_totient_sq_of_odd : ∀ m : ℕ, m % 2 = 1 → m ≤ m.totient ^ 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases eq_or_ne m 1 with rfl | hm1
    · decide
    have hm0 : 0 < m := by omega
    set p := m.minFac with hpdef
    have hpp : p.Prime := Nat.minFac_prime hm1
    have hpd : p ∣ m := Nat.minFac_dvd m
    have hpodd : p % 2 = 1 := by
      by_contra h
      have : 2 ∣ m := dvd_trans (show 2 ∣ p by omega) hpd
      omega
    have hp3 : 3 ≤ p := by have := hpp.two_le; omega
    set q := m / p with hqdef
    have hmm : m = p * q := (Nat.mul_div_cancel' hpd).symm
    have hqlt : q < m := Nat.div_lt_self hm0 (by omega)
    have hqodd : q % 2 = 1 := by
      by_contra h
      have : 2 ∣ m := hmm ▸ Dvd.dvd.mul_left (show 2 ∣ q by omega) p
      omega
    have ihq := ih q hqlt hqodd
    by_cases hcase : p ∣ q
    · -- φ(m) = p·φ(q), and m = p·q ≤ p·φ(q)² ≤ (p·φ(q))²
      have hphi : m.totient = p * q.totient := by
        rw [hmm]; exact Nat.totient_mul_of_prime_of_dvd hpp hcase
      have h1 : m ≤ p * q.totient ^ 2 := by
        rw [hmm]; exact Nat.mul_le_mul_left p ihq
      have h2 : p * q.totient ^ 2 ≤ p ^ 2 * q.totient ^ 2 := by
        have hp2 : p ≤ p ^ 2 := by nlinarith
        exact Nat.mul_le_mul_right _ hp2
      calc m ≤ p ^ 2 * q.totient ^ 2 := le_trans h1 h2
        _ = (p * q.totient) ^ 2 := by ring
        _ = m.totient ^ 2 := by rw [hphi]
    · -- φ(m) = (p−1)·φ(q), and p ≤ (p−1)² since p ≥ 3
      have hcop : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hcase
      have hphi : m.totient = (p - 1) * q.totient := by
        rw [hmm, Nat.totient_mul hcop, Nat.totient_prime hpp]
      have hsq : p ≤ (p - 1) ^ 2 := by
        have h1 : 2 * (p - 1) ≤ (p - 1) * (p - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : (p - 1) ^ 2 = (p - 1) * (p - 1) := by ring
        omega
      have h1 : m ≤ (p - 1) ^ 2 * q := by
        rw [hmm]; exact Nat.mul_le_mul_right q hsq
      have h2 : (p - 1) ^ 2 * q ≤ (p - 1) ^ 2 * q.totient ^ 2 :=
        Nat.mul_le_mul_left _ ihq
      calc m ≤ (p - 1) ^ 2 * q.totient ^ 2 := le_trans h1 h2
        _ = ((p - 1) * q.totient) ^ 2 := by ring
        _ = m.totient ^ 2 := by rw [hphi]

/-- Every n satisfies n ≤ 2·φ(n)². -/
theorem le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    by_cases hodd : n % 2 = 1
    · have := le_totient_sq_of_odd n hodd; omega
    · set m := n / 2 with hmdef
      have hnm : n = 2 * m := by omega
      have hm0 : 0 < m := by omega
      by_cases hm2 : 2 ∣ m
      · -- φ(n) = 2·φ(m)
        have hphi : n.totient = 2 * m.totient := by
          rw [hnm]; exact Nat.totient_mul_of_prime_of_dvd Nat.prime_two hm2
        have ihm := ih m (by omega)
        have hexp : n.totient ^ 2 = 4 * m.totient ^ 2 := by rw [hphi]; ring
        omega
      · -- m odd: φ(n) = φ(m) and the odd bound applies
        have hmodd : m % 2 = 1 := by omega
        have hphi : n.totient = m.totient := by
          rw [hnm, Nat.totient_mul (coprime_two_of_odd hmodd), Nat.totient_two, one_mul]
        have := le_totient_sq_of_odd m hmodd
        rw [hphi]; omega

/-- **Inverting the niceness**: D ≤ T caps the denominator at 2(2T+1)². -/
theorem denominator_le_of_Dden_le {T n : ℕ} (h : Dden n ≤ T) :
    n ≤ 2 * (2 * T + 1) ^ 2 := by
  have hphi : n.totient ≤ 2 * T + 1 := by
    unfold Dden at h
    split_ifs at h <;> omega
  have h1 := le_two_mul_totient_sq n
  have h2 : n.totient ^ 2 ≤ (2 * T + 1) ^ 2 := Nat.pow_le_pow_left hphi 2
  omega

/-- The **complete** list of denominators of niceness ≤ T. -/
def completeDens (T : ℕ) : List ℕ :=
  (List.range (2 * (2 * T + 1) ^ 2 + 1)).filter fun n => 0 < n && Dden n ≤ T

/-- Nothing is missing: n appears in `completeDens T` **iff** Dden n ≤ T. -/
theorem mem_completeDens {T n : ℕ} :
    n ∈ completeDens T ↔ 0 < n ∧ Dden n ≤ T := by
  simp only [completeDens, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.lt_succ_of_le (denominator_le_of_Dden_le h2), h1, h2⟩


end AngleNiceness
