/-!
# Angle niceness — verified math backend

This file is the **single implementation** of the mathematics behind
`angle-niceness.html`. The HTML page is a thin frontend: all values it shows
(the angle table, exact radicals, minimal polynomials, niceness degrees, and
the step-by-step derivation trees) are computed here and emitted by the `gen`
executable (`Gen.lean`) into `angle-niceness-data.js`.

Layout:
* math core (this file) — `#guard` tests and theorems at the bottom;
  the file compiles **iff** every test passes.
* `AngleNicenessSpec.lean` — Mathlib specification layer: the same properties
  proved against `Nat.totient`, including unbounded proofs.
* `Gen.lean` — the page-data generator (`lake exe gen`).

Conventions kept from the original JavaScript implementation this replaced:
integers are `Int` everywhere (all divisions in this code are exact), and
radicand identity in `norm`/`sameRad` plus the sign/denesting guards in
`vsqrt`/`cosSym` are decided numerically with tolerance 1e-9.
-/

/-- Used only where the numeric side calls `cos`/`sin`/`sqrt`. -/
def Int.toFloat (i : Int) : Float := Float.ofInt i

namespace AngleNiceness

/-! ## integers -/

/-- Greatest common divisor, result ≥ 0 (`gcd 0 0 = 0`). -/
partial def gcd (a b : Int) : Int :=
  if b != 0 then gcd b (a.tmod b) else (a.natAbs : Int)

/-- Least common multiple. -/
def lcm (a b : Int) : Int := a / gcd a b * b

/-- Euler's totient φ(n), by trial division. -/
def phi (n : Int) : Int := Id.run do
  let mut r := n
  let mut m := n
  let mut p : Int := 2
  while p * p <= m do
    if m.tmod p == 0 then
      r := r - r / p
      while m.tmod p == 0 do
        m := m / p
    p := p + 1
  return if m > 1 then r - r / m else r

/-- Largest square factor: m = s²·f with f squarefree; returns (s, f). -/
def sqfree (m : Int) : Int × Int := Id.run do
  let mut m := m
  let mut s : Int := 1
  let mut i : Int := 2
  while i * i <= m do
    while m.tmod (i * i) == 0 do
      m := m / (i * i)
      s := s * i
    i := i + 1
  return (s, m)

/-! ## exact rationals: (num, den), den > 0, reduced -/

abbrev Frac := Int × Int

/-- Build a reduced fraction (den > 0). -/
def frac (n d : Int) : Frac :=
  let (n, d) := if d < 0 then (-n, -d) else (n, d)
  let g := let g := gcd (n.natAbs : Int) d; if g == 0 then 1 else g
  (n / g, d / g)

/-- Fraction addition. -/
def fadd (x y : Frac) : Frac := frac (x.1 * y.2 + y.1 * x.2) (x.2 * y.2)

/-- Fraction multiplication. -/
def fmul (x y : Frac) : Frac := frac (x.1 * y.1) (x.2 * y.2)

/-- Integer square root ⌊√n⌋ (0 for n ≤ 0), by Newton iteration. -/
def isqrt (n : Int) : Int := Id.run do
  if n <= 0 then return 0
  let mut x := n
  let mut y := (x + 1) / 2
  while y < x do
    x := y
    y := (x + n / x) / 2
  return x

/-- √f if f is the square of a rational, else `none`. -/
def isSquare (f : Frac) : Option Frac :=
  if f.1 < 0 then none else
  let p := isqrt f.1
  let q := isqrt f.2
  if p * p == f.1 && q * q == f.2 then some (frac p q) else none

/-! ## values: exact sums of terms c·√r, where c is a rational and
    r = `.none` (√r means 1) | a squarefree integer | a nested value.
    A term c·√r is the pair `(c, r) : Frac × Rad`. -/

inductive Rad where
  | none : Rad                              -- √(nothing): the term is just c
  | int (m : Int) : Rad                     -- √(squarefree integer)
  | val (V : List (Frac × Rad)) : Rad       -- √(nested value)

instance : Inhabited Rad := ⟨Rad.none⟩

abbrev Term := Frac × Rad
abbrev Value := List Term

/-- The value with the single rational term f. -/
def one (f : Frac) : Value := [(f, Rad.none)]

/-- numeric (floating-point) evaluation of a value. -/
partial def vnum (V : Value) : Float :=
  V.foldl (fun s (c, r) => s + c.1.toFloat / c.2.toFloat *
    (match r with
     | .none => 1
     | .int m => Float.sqrt m.toFloat
     | .val W => Float.sqrt (vnum W))) 0

/-- do two radicands denote the same number?
    (nested case decided numerically) -/
def sameRad (r u : Rad) : Bool :=
  match r, u with
  | .none, .none => true
  | .int m, .int m' => m == m'
  | .val V, .val W => (vnum V - vnum W).abs < 1e-9
  | _, _ => false

/-- combine like terms, drop zero terms. -/
def norm (V : Value) : Value := Id.run do
  let mut out : Array Term := #[]
  for (c, r) in V do
    if c.1 == 0 then continue
    match out.findIdx? (fun (_, r') => sameRad r' r) with
    | some i => let (c', r') := out[i]!; out := out.set! i (fadd c' c, r')
    | none => out := out.push (c, r)
  return out.toList.filter fun (c, _) => c.1 != 0

/-- Scale a value by a rational. -/
def vscale (V : Value) (f : Frac) : Value :=
  norm (V.map fun (c, r) => (fmul c f, r))

/-- Sum of two values. -/
def vadd (V W : Value) : Value := norm (V ++ W)

mutual
/-- product of two terms (c·√r)(c'·√r'), as a
    (usually one-term) value. -/
partial def mulTerm (a b : Term) : Value :=
  let c := fmul a.1 b.1
  match a.2, b.2 with
  | .none, r => [(c, r)]
  | r, .none => [(c, r)]
  | .int m, .int m' =>
    let (s, f) := sqfree (m * m')                    -- √r·√r' = s·√f
    [(fmul c (s, 1), if f == 1 then Rad.none else Rad.int f)]
  | .int m, .val W => [(c, Rad.val (vscale W (m, 1)))]
  | .val W, .int m => [(c, Rad.val (vscale W (m, 1)))]
  | .val X, .val Y =>
    if sameRad (Rad.val X) (Rad.val Y) then vscale X c   -- √W·√W = W
    else [(c, Rad.val (vmul X Y))]

/-- Product of two values. -/
partial def vmul (V W : Value) : Value :=
  norm (V.flatMap fun a => W.flatMap fun b => mulTerm a b)
end

/-- `vsqrt V sg` = sg·√V, sg = ±1 picks the sign.
    Tries a perfect-square rational, then denesting √(A+B√m) = √u ± √v,
    else keeps V as a nested radicand. -/
partial def vsqrt (V : Value) (sg : Int) : Value :=
  let V := norm V
  if V.isEmpty then [] else
  match V with
  | [(f, .none)] =>                                  -- rational radicand
    (match isSquare f with
     | some s => one (fmul s (sg, 1))
     | none =>
       let (g, m) := sqfree (f.1 * f.2)              -- √(p/q) = √(pq)/q
       [(frac (sg * g) f.2, Rad.int m)])
  | _ =>
    let denested : Option Value := do                -- try denesting √(A+B√m)
      guard (V.length == 2)
      let rt ← V.find? fun (_, r) => r matches Rad.none
      let st ← V.find? fun (_, r) => r matches Rad.int _
      let A := rt.1; let B := st.1
      let m ← match st.2 with | .int m => some m | _ => Option.none
      let s ← isSquare (fadd (fmul A A) (fmul (fmul B B) (-m, 1)))  -- √(A²−B²m)
      let u := fmul (fadd A s) (1, 2)
      let v := fmul (fadd A (fmul s (-1, 1))) (1, 2)
      guard (u.1 >= 0 && v.1 >= 0)
      let R := vscale (vadd (vsqrt (one u) 1)
                            (vsqrt (one v) (if B.1 < 0 then -1 else 1))) (sg, 1)
      guard ((vnum R - sg.toFloat * Float.sqrt (vnum V)).abs < 1e-9)
      pure R
    match denested with
    | some R => R
    | none =>
      let d := V.foldl (fun d (c, _) => lcm d c.2) 1        -- √V = √(V·d²)/d
      let g := V.foldl (fun g (c, _) => gcd g ((c.1 * d * d / c.2).natAbs : Int)) 0
      let (e, _) := sqfree g                                -- pull square content e² out of V·d²
      [(frac (sg * e) d, Rad.val (vscale V (frac (d * d) (e * e))))]

/-! ## cos(2πk/n), sin(2πk/n) as exact radicals -/

def pi : Float := 3.141592653589793

mutual
/-- cos(2πk/n) as an exact value, `none` when no closed
    form is built (odd part of n ∉ {1,3,5,15}). -/
partial def cosSym (k n : Int) : Option Value :=
  let g := let g := gcd k n; if g == 0 then 1 else g
  let n := n / g
  let k := ((k / g).tmod n + n).tmod n
  if n == 1 then some (one (1, 1))
  else if n == 2 then some (one (-1, 1))
  else if n == 3 then some (one (-1, 2))
  else if n == 5 then
    some [((-1, 4), Rad.none), (((if k == 1 || k == 4 then 1 else -1 : Int), 4), Rad.int 5)]
  else if n == 15 then do                            -- k/15 = 2k/5 − k/3
    let c5 ← cosSym (2 * k) 5; let c3 ← cosSym k 3
    let s5 ← sinOdd (2 * k) 5; let s3 ← sinOdd k 3
    pure (vadd (vmul c5 c3) (vmul s5 s3))
  else if n.tmod 2 == 0 then do                      -- half angle: cos x = ±√((1+cos 2x)/2)
    let P ← cosSym k (n / 2)
    pure (vsqrt (vscale (vadd P (one (1, 1))) (1, 2))
                (if Float.cos (2 * pi * k.toFloat / n.toFloat) < -1e-9 then -1 else 1))
  else none

/-- sin = ±√(1−cos²), for the small odd n where cosSym exists. -/
partial def sinOdd (k n : Int) : Option Value := do
  let c ← cosSym k n
  pure (vsqrt (vadd (one (1, 1)) (vscale (vmul c c) (-1, 1)))
              (if Float.sin (2 * pi * k.toFloat / n.toFloat) < -1e-9 then -1 else 1))
end

/-- sin x = cos(π/2 − x): 2πk/n ↦ 2π(n−4k)/(4n). -/
def sinSym (k n : Int) : Option Value :=
  cosSym (((n - 4 * k).tmod (4 * n) + 4 * n).tmod (4 * n)) (4 * n)

/-! ## LaTeX rendering of a value -/

/-- LaTeX rendering of a value. -/
partial def tex (V : Value) : String :=
  let V := norm V
  if V.isEmpty then "0" else
  if V.all (fun (c, _) => c.1 < 0) then "-" ++ tex (vscale V (-1, 1)) else
  -- sort: positive terms first, then the rational term, then by numeric size
  let le : Term → Term → Bool := fun a b =>
    if (a.1.1 > 0) != (b.1.1 > 0) then a.1.1 > 0
    else match a.2, b.2 with
      | .none, _ => true
      | _, .none => false
      | _, _ => vnum [a] <= vnum [b]
  let V := V.mergeSort le
  let d := V.foldl (fun d (c, _) => lcm d c.2) 1     -- common denominator
  let s := String.join <| V.zipIdx.map fun ((c, r), i) =>
    let cd := c.1 * d / c.2
    let a := (cd.natAbs : Int)
    let sgn := if cd < 0 then "-" else if i != 0 then "+" else ""
    let rad := match r with
      | .none => ""
      | .int m => "\\sqrt{" ++ toString m ++ "}"
      | .val W => "\\sqrt{" ++ tex W ++ "}"
    sgn ++ (if a != 1 || rad == "" then toString a else "") ++ rad
  if d == 1 then s else "\\frac{" ++ s ++ "}{" ++ toString d ++ "}"

/-! ## polynomials over ℤ, as coefficient arrays #[a0, a1, …] -/

abbrev Poly := Array Int

/-- Polynomial addition. -/
def padd (a b : Poly) : Poly :=
  .ofFn (n := max a.size b.size) fun i => a.getD i 0 + b.getD i 0

/-- Polynomial scaling. -/
def pscale (a : Poly) (c : Int) : Poly := a.map (· * c)

/-- Polynomial multiplication. -/
def pmul (a b : Poly) : Poly := Id.run do
  let mut r : Poly := Array.replicate (a.size + b.size - 1) 0
  for i in [0:a.size] do
    for j in [0:b.size] do
      r := r.set! (i + j) (r[i + j]! + a[i]! * b[j]!)
  return r

/-- quotient a ÷ b, used only where the division is exact
    and b is monic. -/
def pdiv (a b : Poly) : Poly := Id.run do
  let mut a := a
  let mut q : Poly := Array.replicate (a.size - b.size + 1) 0
  for idx in [0:q.size] do
    let i := q.size - 1 - idx
    q := q.set! i (a[i + b.size - 1]! / b[b.size - 1]!)
    for j in [0:b.size] do
      a := a.set! (i + j) (a[i + j]! - q[i]! * b[j]!)
  return q

/-- n-th cyclotomic polynomial: Φn = (xⁿ − 1) / Π_{d|n, d<n} Φd. -/
partial def cyclo (n : Int) : Poly := Id.run do
  let N := n.toNat
  let mut u : Poly := Array.replicate (N + 1) 0
  u := u.set! 0 (-1)
  u := u.set! N 1
  let mut d : Poly := #[1]
  for k in [1:N] do
    if N % k == 0 then d := pmul d (cyclo k)
  return pdiv u d

/-- minimal polynomial of cos(2πk/n) over ℚ (any k with
    gcd(k,n)=1), obtained by folding the palindromic Φn with
    x^j + x^{−j} = p_j(x + x^{−1}), then substituting y = 2t. -/
def cosMinPoly (n : Int) : Poly := Id.run do
  if n == 1 then return #[-1, 1]
  if n == 2 then return #[1, 1]
  let a := cyclo n
  let m := (a.size - 1) / 2
  let mut Q : Poly := #[a[m]!]
  let mut p2 : Poly := #[2]                          -- p_0 = 2
  let mut p1 : Poly := #[0, 1]                       -- p_1 = y
  Q := padd Q (pscale p1 a[m + 1]!)
  for j in [2:m + 1] do
    let p := padd (pmul #[0, 1] p1) (pscale p2 (-1)) -- p_j = y·p_{j−1} − p_{j−2}
    Q := padd Q (pscale p a[m + j]!)
    p2 := p1
    p1 := p
  let c := Q.mapIdx fun i x => x * 2 ^ i             -- substitute y = 2t
  let g := c.foldl (fun u v => gcd u v) 0
  return c.map (· / g)

/-- LaTeX for a coefficient array. -/
def texPoly (p : Poly) (v : String) : String := Id.run do
  let mut t : Array String := #[]
  for idx in [0:p.size] do
    let i := p.size - 1 - idx
    let c := p[i]!
    if c == 0 then continue
    let s := if t.size > 0 then (if c < 0 then "-" else "+")
             else (if c < 0 then "-" else "")
    let a := (c.natAbs : Int)
    t := t.push <| s ++ (if a == 1 && i > 0 then "" else toString a)
                     ++ (if i > 0 then v else "")
                     ++ (if i > 1 then "^{" ++ toString i ++ "}" else "")
  return String.join t.toList

/-! ## niceness: D = [ℚ(cos x, sin x) : ℚ] for x = 2πk/n -/

/-- D = [ℚ(cos x, sin x) : ℚ] for x = 2πk/n. -/
def niceness (k n : Int) : Int :=
  let n := n / (let g := gcd k n; if g == 0 then 1 else g)  -- only the reduced denominator matters
  let f := phi n
  if n.tmod 4 != 0 then f else f / 2

/-!
# Tests

Everything below is test-only machinery.
`#guard` fails at compile time if the expression is not `true`;
the theorems are checked by the compiler via `native_decide`.
-/

/-! ## test helpers -/

/-- Structural equality on radicands (test-only). -/
partial def Rad.beq : Rad → Rad → Bool
  | .none, .none => true
  | .int m, .int m' => m == m'
  | .val V, .val W =>
    V.length == W.length &&
    (V.zip W).all fun ((c, r), (c', r')) => c == c' && Rad.beq r r'
  | _, _ => false

instance : BEq Rad := ⟨Rad.beq⟩

/-- Exact equality of values: V − W normalizes to the empty sum.
    (Structural list equality is too strict — term order may differ.) -/
def veq (V W : Value) : Bool := (vadd V (vscale W (-1, 1))).isEmpty

def oveq : Option Value → Option Value → Bool
  | some V, some W => veq V W
  | none, none => true
  | _, _ => false

def close (a b : Float) : Bool := (a - b).abs < 1e-9

def evalPoly (p : Poly) (x : Float) : Float :=
  p.foldr (fun c acc => acc * x + c.toFloat) 0

def cosNum (k n : Int) : Float := Float.cos (2 * pi * k.toFloat / n.toFloat)
def sinNum (k n : Int) : Float := Float.sin (2 * pi * k.toFloat / n.toFloat)

/-- The odd part of n. -/
partial def oddPart (n : Int) : Int := if n.tmod 2 == 0 then oddPart (n / 2) else n

/-! ## tests: integers -/

#guard gcd 12 18 == 6
#guard gcd (-8) 6 == 2
#guard gcd 0 7 == 7
#guard lcm 4 6 == 12
#guard (List.range 12).map (fun (i : Nat) => phi ((i : Int) + 1)) == [1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4]
#guard phi 100 == 40
#guard (List.range 200).all fun (n : Nat) =>
  let s := isqrt n
  s * s <= (n : Int) && (n : Int) < (s + 1) * (s + 1)
#guard sqfree 12 == (2, 3)
#guard sqfree 49 == (7, 1)
#guard sqfree 1 == (1, 1)
#guard sqfree 720 == (12, 5)

/-! ## tests: rationals -/

#guard frac 2 (-4) == (-1, 2)
#guard frac (-6) (-9) == (2, 3)
#guard frac 0 5 == (0, 1)
#guard fadd (1, 2) (1, 3) == (5, 6)
#guard fadd (1, 2) (-1, 2) == (0, 1)
#guard fmul (2, 3) (3, 4) == (1, 2)
#guard isSquare (9, 4) == some (3, 2)
#guard isSquare (8, 1) == none
#guard isSquare (-9, 1) == none          -- negative: not a rational square

/-! ## tests: value arithmetic -/

-- √2·√3 = √6, √2·√2 = 2, √2·√8 = 4
#guard vmul [((1, 1), Rad.int 2)] [((1, 1), Rad.int 3)] == [((1, 1), Rad.int 6)]
#guard vmul [((1, 1), Rad.int 2)] [((1, 1), Rad.int 2)] == one (2, 1)
#guard vmul [((1, 1), Rad.int 2)] [((1, 1), Rad.int 8)] == one (4, 1)
-- (1+√2) + (1−√2) = 2 ; (1+√2)(1−√2) = −1
#guard vadd [((1, 1), Rad.none), ((1, 1), Rad.int 2)]
            [((1, 1), Rad.none), ((-1, 1), Rad.int 2)] == one (2, 1)
#guard vmul [((1, 1), Rad.none), ((1, 1), Rad.int 2)]
            [((1, 1), Rad.none), ((-1, 1), Rad.int 2)] == one (-1, 1)
#guard vscale (one (1, 2)) (2, 3) == one (1, 3)
#guard norm [((1, 2), Rad.int 3), ((0, 1), Rad.int 5), ((1, 2), Rad.int 3)] == [((1, 1), Rad.int 3)]

/-! ## tests: vsqrt -/

#guard vsqrt (one (4, 9)) 1 == one (2, 3)            -- perfect square
#guard vsqrt (one (4, 9)) (-1) == one (-2, 3)        -- sign
#guard vsqrt (one (8, 1)) 1 == [((2, 1), Rad.int 2)] -- √8 = 2√2
#guard vsqrt (one (1, 2)) 1 == [((1, 2), Rad.int 2)] -- √(1/2) = √2/2
#guard vsqrt [] 1 == []                              -- √0 = 0
-- denesting: √(3+2√2) = 1+√2, √(7+4√3) = 2+√3
#guard veq (vsqrt [((3, 1), Rad.none), ((2, 1), Rad.int 2)] 1)
           [((1, 1), Rad.none), ((1, 1), Rad.int 2)]
#guard veq (vsqrt [((7, 1), Rad.none), ((4, 1), Rad.int 3)] 1)
           [((2, 1), Rad.none), ((1, 1), Rad.int 3)]
-- non-denestable: √(1+√2) squares back to 1+√2, numerically
#guard let V := vsqrt [((1, 1), Rad.none), ((1, 1), Rad.int 2)] 1
       close (vnum V * vnum V) (1 + Float.sqrt 2)

/-! ## tests: cosSym / sinSym -/

#guard oveq (cosSym 0 1) (some (one (1, 1)))         -- cos 0 = 1
#guard oveq (cosSym 1 2) (some (one (-1, 1)))        -- cos π = −1
#guard oveq (cosSym 1 4) (some [])                   -- cos π/2 = 0 (the empty sum)
#guard oveq (cosSym 3 4) (some [])                   -- cos 3π/2 = 0
#guard oveq (cosSym 1 3) (some (one (-1, 2)))        -- cos 2π/3 = −1/2
#guard oveq (cosSym 1 6) (some (one (1, 2)))         -- cos 2π/6 = cos 60° = 1/2
#guard oveq (cosSym 1 12) (some [((1, 2), Rad.int 3)]) -- cos 2π/12 = cos 30° = √3/2
#guard oveq (sinSym 0 1) (some [])                   -- sin 0 = 0
#guard oveq (sinSym 1 4) (some (one (1, 1)))         -- sin π/2 = 1
#guard oveq (sinSym 1 2) (some [])                   -- sin π = 0
#guard oveq (sinSym 3 4) (some (one (-1, 1)))        -- sin 3π/2 = −1

-- cosSym exists exactly when the odd part of n is 1, 3, 5 or 15 (n ≤ 24)
#guard (List.range 24).all fun i =>
  let n : Int := i + 1
  (cosSym 1 n).isSome == (oddPart n == 1 || oddPart n == 3 || oddPart n == 5 || oddPart n == 15)

-- numeric agreement: vnum (cosSym k n) = cos(2πk/n), same for sin, all k, n ≤ 24
#guard (List.range 24).all fun i => (List.range (i + 1)).all fun k =>
  let n : Int := i + 1
  match cosSym k n with
  | some V => close (vnum V) (cosNum k n)
  | none => true
#guard (List.range 24).all fun i => (List.range (i + 1)).all fun k =>
  let n : Int := i + 1
  match sinSym k n with
  | some V => close (vnum V) (sinNum k n)
  | none => true

-- Pythagoras, exactly: cos² + sin² − 1 normalizes to the empty sum.
-- Excluded: odd part of n = 15, where cos and sin are built by *different*
-- routes (angle-difference formula vs. half-angle tower), so the difference
-- has numerically-cancelling terms whose radical shapes never merge.
-- Those cases are covered by the numeric test below.
#guard (List.range 24).all fun i => (List.range (i + 1)).all fun k =>
  let n : Int := i + 1
  oddPart n == 15 ||
  match cosSym k n, sinSym k n with
  | some C, some S => (vadd (vadd (vmul C C) (vmul S S)) (one (-1, 1))).isEmpty
  | _, _ => true

-- Pythagoras, numerically, for every n ≤ 24 (including odd part 15)
#guard (List.range 24).all fun i => (List.range (i + 1)).all fun k =>
  let n : Int := i + 1
  match cosSym k n, sinSym k n with
  | some C, some S => close (vnum C * vnum C + vnum S * vnum S) 1
  | _, _ => true

-- unreduced arguments reduce first: cos(2π·2/8) = cos(2π/4)
#guard oveq (cosSym 2 8) (cosSym 1 4)
#guard oveq (cosSym 10 4) (cosSym 1 2)               -- also k mod n

/-! ## tests: tex -/

#guard tex [] == "0"
#guard tex (one (1, 1)) == "1"
#guard tex (one (-1, 2)) == "-\\frac{1}{2}"
#guard tex ((cosSym 1 6).get!) == "\\frac{1}{2}"                       -- cos 60°
#guard tex ((cosSym 1 12).get!) == "\\frac{\\sqrt{3}}{2}"              -- cos 30°
#guard tex ((cosSym 1 8).get!) == "\\frac{\\sqrt{2}}{2}"               -- cos 45°
#guard tex ((cosSym 1 5).get!) == "\\frac{\\sqrt{5}-1}{4}"             -- cos 72°
#guard tex ((cosSym 1 24).get!) == "\\frac{\\sqrt{2}+\\sqrt{6}}{4}"    -- cos 15°
#guard tex (vsqrt [((3, 1), Rad.none), ((2, 1), Rad.int 2)] 1) == "1+\\sqrt{2}"

/-! ## tests: polynomials -/

#guard padd #[1, 2] #[3, 4, 5] == #[4, 6, 5]
#guard pscale #[1, -2, 3] (-2) == #[-2, 4, -6]
#guard pmul #[1, 1] #[1, 1] == #[1, 2, 1]
#guard pmul #[1, 1] #[-1, 1] == #[-1, 0, 1]
#guard pdiv #[-1, 0, 1] #[1, 1] == #[-1, 1]          -- (x²−1)/(x+1) = x−1
#guard pdiv (pmul #[1, 2, 3] #[1, 4]) #[1, 4] == #[1, 2, 3]

#guard cyclo 1 == #[-1, 1]
#guard cyclo 2 == #[1, 1]
#guard cyclo 3 == #[1, 1, 1]
#guard cyclo 4 == #[1, 0, 1]
#guard cyclo 6 == #[1, -1, 1]
#guard cyclo 12 == #[1, 0, -1, 0, 1]
#guard (cyclo 105)[7]! == -2                         -- first coefficient ∉ {0,±1}
#guard (List.range 30).all fun i =>                  -- deg Φn = φ(n)
  ((cyclo (i + 1)).size - 1 : Int) == phi (i + 1)

#guard cosMinPoly 1 == #[-1, 1]                      -- t − 1        (cos 0 = 1)
#guard cosMinPoly 2 == #[1, 1]                       -- t + 1        (cos π = −1)
#guard cosMinPoly 3 == #[1, 2]                       -- 2t + 1       (cos 2π/3 = −1/2)
#guard cosMinPoly 4 == #[0, 1]                       -- t            (cos π/2 = 0)
#guard cosMinPoly 5 == #[-1, 2, 4]                   -- 4t² + 2t − 1
#guard cosMinPoly 7 == #[-1, -4, 4, 8]               -- 8t³ + 4t² − 4t − 1
#guard cosMinPoly 9 == #[1, -6, 0, 8]                -- 8t³ − 6t + 1
#guard texPoly (cosMinPoly 7) "t" == "8t^{3}+4t^{2}-4t-1"
#guard (List.range 28).all fun i =>                  -- deg = φ(n)/2 for n ≥ 3
  ((cosMinPoly (i + 3)).size - 1 : Int) == phi (i + 3) / 2
#guard (List.range 28).all fun i =>                  -- cos(2π/n) is a root, numerically
  let n : Int := i + 3
  (evalPoly (cosMinPoly n) (cosNum 1 n)).abs < 1e-6

/-! ## tests: niceness (the headline properties) -/

-- x = 0, π/2, π, 3π/2 are 2πk/4 for k = 0,1,2,3: all have the same complexity, D = 1.
theorem cardinal_angles_equally_nice :
    niceness 0 4 = 1 ∧ niceness 1 4 = 1 ∧ niceness 2 4 = 1 ∧ niceness 3 4 = 1 := by
  native_decide

-- Invariance under negation x ↦ −x (reflection across the x-axis):
-- 2πk/n ↦ 2π(n−k)/n. Checked exhaustively for all 1 ≤ n ≤ 100, 0 ≤ k ≤ n.
theorem niceness_neg_invariant :
    ((List.range 100).all fun i => (List.range (i + 2)).all fun k =>
      let n : Int := i + 1
      niceness k n == niceness (n - k) n) = true := by
  native_decide

-- Invariance under x ↦ π − x (reflection across the y-axis):
-- 2πk/n ↦ 2π(n−2k)/(2n). Checked exhaustively for all 1 ≤ n ≤ 100, 0 ≤ k ≤ n.
theorem niceness_reflect_y_invariant :
    ((List.range 100).all fun i => (List.range (i + 2)).all fun k =>
      let n : Int := i + 1
      niceness k n == niceness (n - 2 * k) (2 * n)) = true := by
  native_decide

-- Invariance under the diagonal reflection x ↦ π/2 − x (swapping cos and sin):
-- 2πk/n ↦ 2π(n−4k)/(4n). Checked exhaustively for all 1 ≤ n ≤ 100, 0 ≤ k ≤ n.
theorem niceness_diag_invariant :
    ((List.range 100).all fun i => (List.range (i + 2)).all fun k =>
      let n : Int := i + 1
      niceness k n == niceness (n - 4 * k) (4 * n)) = true := by
  native_decide

-- the observed pair: 80° = 2π·2/9 and its diagonal mirror 10° = 2π·1/36
#guard niceness 2 9 == 6 && niceness 1 36 == 6

-- spot values: D(60°) = D(45°) = D(30°) = 2, D(72°) = 4, D(2π/7) = 6
#guard niceness 1 6 == 2 && niceness 1 8 == 2 && niceness 1 12 == 2
#guard niceness 1 5 == 4 && niceness 1 7 == 6
-- reduction: D depends only on the reduced fraction
#guard niceness 2 8 == niceness 1 4 && niceness 0 24 == niceness 0 1

-- consistency with the polynomial machinery: for reduced 2πk/n, n ≥ 3,
-- D = [ℚ(cos):ℚ]·[ℚ(cos,sin):ℚ(cos)] = deg(cosMinPoly n) · (2 if 4∤n else 1)
#guard (List.range 28).all fun i =>
  let n : Int := i + 3
  niceness 1 n == (if n.tmod 4 != 0 then 2 else 1) * ((cosMinPoly n).size - 1 : Int)

/-! ## tests: the same two reflections hold for the symbolic values themselves -/

-- cos(−x) = cos x and sin(−x) = −sin x, as exact values (n ≤ 24, all k)
theorem symbolic_neg_invariant :
    ((List.range 24).all fun i => (List.range (i + 2)).all fun k =>
      let n : Int := i + 1
      oveq (cosSym (n - k) n) (cosSym k n) &&
      oveq (sinSym (n - k) n) ((sinSym k n).map (vscale · (-1, 1)))) = true := by
  native_decide

-- cos(π−x) = −cos x and sin(π−x) = sin x, as exact values (n ≤ 24, all k).
-- Exception, cos only: odd part of n = 15, where cos(2πk/15) comes from the
-- angle-difference formula but cos(π−x) from the half-angle tower at 2n = 30 —
-- numerically equal, structurally different; covered by the numeric test below.
theorem symbolic_reflect_y_invariant :
    ((List.range 24).all fun i => (List.range (i + 2)).all fun k =>
      let n : Int := i + 1
      (oddPart n == 15 ||
       oveq (cosSym (n - 2 * k) (2 * n)) ((cosSym k n).map (vscale · (-1, 1)))) &&
      oveq (sinSym (n - 2 * k) (2 * n)) (sinSym k n)) = true := by
  native_decide

-- cos(π−x) = −cos x, numerically, for every n ≤ 24 (including odd part 15)
#guard (List.range 24).all fun i => (List.range (i + 2)).all fun k =>
  let n : Int := i + 1
  match cosSym (n - 2 * k) (2 * n), cosSym k n with
  | some A, some B => close (vnum A) (-(vnum B))
  | none, none => true
  | _, _ => false

end AngleNiceness
