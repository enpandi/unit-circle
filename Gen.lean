import AngleNiceness
import AngleNicenessSpec

/-!
# Page-data generator

Everything the frontend displays is computed here, from the verified math in
`AngleNiceness.lean`, and written to `angle-niceness-data.js` as
`const DATA = {...}`. Run with `lake exe gen`.

LaTeX is emitted as `<span class="ktx">…</span>` placeholders; the frontend
renders them with KaTeX. `angle-niceness.html` contains no math at all.
-/

open AngleNiceness

/- Mathlib (imported via `AngleNicenessSpec`) also exports root-level `gcd` and
`lcm`; in this file the bare names always mean the `AngleNiceness` ones. -/
local notation "gcd" => AngleNiceness.gcd
local notation "lcm" => AngleNiceness.lcm

/-! ## string helpers -/

def htmlEscape (s : String) : String :=
  ((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;"

def jsEscape (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (if c == '\\' then "\\\\"
            else if c == '"' then "\\\""
            else if c == '\n' then "\\n"
            else toString c)) ""

/-- A KaTeX placeholder; the frontend renders `.ktx` spans client-side. -/
def kx (t : String) : String := "<span class=\"ktx\">" ++ htmlEscape t ++ "</span>"

/-- Fixed-point decimal formatting (like JS `toFixed`), enough for display. -/
def toFixed (x : Float) (d : Nat) : String :=
  let neg := x < 0
  let p : Nat := 10 ^ d
  let y : Nat := ((Float.abs x * Float.ofNat p).round).toUInt64.toNat
  let ip := y / p
  let fp := y % p
  let fs := toString fp
  let fs := String.ofList (List.replicate (d - fs.length) '0') ++ fs
  (if neg && y != 0 then "-" else "") ++ toString ip ++
  (if d == 0 then "" else "." ++ fs)

def stripDot0 (s : String) : String :=
  if s.endsWith ".0" then String.ofList s.toList.dropLast.dropLast else s

def fmax (a b : Float) : Float := if a < b then b else a

/-! ## presentation-level math (ported from the old page UI) -/

/-- `p·π/q` as LaTeX (`fr2` in the old UI). -/
def fr2 (p q : Int) : String :=
  if p == 0 then "0"
  else (if p == 1 then "\\pi" else toString p ++ "\\pi") ++
       (if q == 1 then "" else "/" ++ toString q)

/-- Prime factorization [(p, e), …]. -/
def factor (n : Int) : List (Int × Nat) := Id.run do
  let mut n := n
  let mut f : Array (Int × Nat) := #[]
  let mut p : Int := 2
  while p * p <= n do
    if n.tmod p == 0 then
      let mut e : Nat := 0
      while n.tmod p == 0 do
        n := n / p
        e := e + 1
      f := f.push (p, e)
    p := p + 1
  if n > 1 then f := f.push (n, 1)
  return f.toList

/-- `texPoly`, but long polynomials are elided with ⋯ . -/
def texPolyShort (c : Poly) (v : String) : String := Id.run do
  let mut T : Array String := #[]
  for idx in [0:c.size] do
    let i := c.size - 1 - idx
    let x := c[i]!
    if x == 0 then continue
    let s := if T.size > 0 then (if x < 0 then "-" else "+")
             else (if x < 0 then "-" else "")
    let m := (x.natAbs : Int)
    T := T.push <| s ++ (if m == 1 && i > 0 then "" else toString m)
                     ++ (if i > 0 then v else "")
                     ++ (if i > 1 then "^{" ++ toString i ++ "}" else "")
  return if T.size > 9
    then String.join (T.toList.take 3) ++ "+\\cdots" ++ String.join (T.toList.drop (T.size - 2))
    else String.join T.toList

/-- An expandable `<details>` block (`D_` in the old UI). -/
def detailsB (s body : String) (opn : Bool := false) : String :=
  "<details" ++ (if opn then " open" else "") ++ "><summary>" ++ s ++ "</summary>"
  ++ body ++ "</details>"

/-- English ordinal: 1st, 2nd, 3rd, 4th, …, 11th–13th, 21st, … -/
def ordinal (n : Int) : String :=
  let m := (n.tmod 100).natAbs
  let u := (n.tmod 10).natAbs
  toString n ++
    (if 11 <= m && m <= 13 then "th"
     else if u == 1 then "st" else if u == 2 then "nd"
     else if u == 3 then "rd" else "th")

/-- `p^e` as LaTeX: `1` for e = 0, `p` for e = 1, else `p^{e}`. -/
def powTex (p : Int) (e : Nat) : String :=
  if e == 0 then "1"
  else toString p ++ (if e > 1 then "^{" ++ toString e ++ "}" else "")

/-- "a" or "an", for use before an ordinal like 8th or 11th. -/
def artOrd (n : Int) : String :=
  if n == 8 || n == 11 || n == 18 then "an" else "a"

/-! ### the derivation tree

The derivation is a tree of short declarative claims: every node states one
fact, and its children justify it. Branch nodes render as collapsible
`<details>`, leaves as bullet lines. All mathematics — including single
variables and numerals used as math — is emitted as `.ktx` LaTeX spans. -/

inductive Node where
  | leaf (text : String) : Node
  | node (claim : String) (children : List Node) : Node

partial def renderNode : Node → String
  | .leaf t => "<div class=\"lf\">" ++ t ++ "</div>"
  | .node c cs => detailsB c (String.join (cs.map renderNode))

def kids (ns : List Node) : String := String.join (ns.map renderNode)

/-- Justification bullets for φ(n) = f, shaped by the factorization of n. -/
def phiBullets (n f : Int) : List Node :=
  let ns := toString n
  let fac := factor n
  let defLeaf : Node := .leaf (kx ("\\varphi(" ++ ns ++ ")")
    ++ " — Euler’s totient — counts how many of " ++ kx ("1, 2, \\ldots, " ++ ns)
    ++ " share no common factor bigger than " ++ kx "1" ++ " with " ++ kx ns ++ ".")
  match fac with
  | [(_, 1)] =>  -- n prime
    [ defLeaf,
      .leaf (kx ns ++ " is prime, so every number below it counts: "
        ++ kx ("\\varphi(" ++ ns ++ ")=" ++ ns ++ "-1=" ++ toString f) ++ ".") ]
  | [(P, e)] =>  -- one prime power
    [ defLeaf,
      .leaf ("exactly the multiples of " ++ kx (toString P) ++ " are excluded — "
        ++ toString (n / P) ++ " of them: "
        ++ kx ("\\varphi(" ++ powTex P e ++ ")=" ++ powTex P e ++ "-" ++ powTex P (e-1)
               ++ "=" ++ ns ++ "-" ++ toString (n / P) ++ "=" ++ toString f) ++ ".") ]
  | _ =>  -- several prime factors
    [ defLeaf,
      .leaf ("for each prime-power factor of " ++ kx (ns ++ "="
          ++ ("\\cdot".intercalate (fac.map fun (P, e) => powTex P e))) ++ ": "
        ++ ",&ensp;".intercalate (fac.map fun (P, e) =>
             kx ("\\varphi(" ++ powTex P e ++ ")=" ++ powTex P e ++ "-" ++ powTex P (e-1)
                 ++ "=" ++ toString (phi (P ^ e)))) ++ "."),
      .leaf (kx "\\varphi" ++ " multiplies across coprime factors, so "
        ++ kx ("\\varphi(" ++ ns ++ ")="
               ++ ("\\cdot".intercalate (fac.map fun (P, e) => toString (phi (P ^ e))))
               ++ "=" ++ toString f) ++ ".") ]

/-- The derivation of D as a tree of declarative claims.
    k/n must be reduced; f = φ(n), D = niceness. -/
def dTree (k n f D : Int) : String :=
  -- trivial angles: cos and sin are rational, no machinery needed
  if n == 1 || n == 2 || n == 4 then
    detailsB ("how " ++ kx "D = 1" ++ " is computed")
      (kids [
        .leaf (kx "\\cos x" ++ " and " ++ kx "\\sin x"
          ++ " are rational — their values are shown above."),
        .leaf ("rational numbers generate the smallest possible field, "
          ++ kx "\\mathbb{Q}" ++ " itself, so "
          ++ kx "D=[\\mathbb{Q}(\\cos x,\\sin x):\\mathbb{Q}]=1"
          ++ ". These are the nicest points on the circle.")]) true
  else
  let ns := toString n
  let ks := toString k
  let fs := toString f
  let Ds := toString D
  let g := let g := gcd (2 * k) n; if g == 0 then 1 else g
  let piFrac := fr2 (2 * k / g) (n / g)
  let zeta := "\\zeta_{" ++ ns ++ "}"
  let L := lcm 4 n
  let Ls := toString L
  let zetaL := "\\zeta_{" ++ Ls ++ "}"
  let QzL := "\\mathbb{Q}(" ++ zetaL ++ ")"
  let Qre := "\\mathbb{Q}(\\cos x,\\sin x)"

  let s1 : Node := .node ("1. " ++ kx ("x/2\\pi=" ++ ks ++ "/" ++ ns)
      ++ " in lowest terms — this defines " ++ kx ("k = " ++ ks)
      ++ " and " ++ kx ("n = " ++ ns))
    [ .leaf ("a full turn is " ++ kx "2\\pi" ++ ", and "
        ++ kx ("\\frac{x}{2\\pi}=\\frac{" ++ piFrac ++ "}{2\\pi}=\\frac{" ++ ks ++ "}{" ++ ns ++ "}") ++ "."),
      .leaf (kx ("\\gcd(" ++ ks ++ ", " ++ ns ++ ") = 1")
        ++ ", so the fraction is fully reduced; everything below uses only "
        ++ kx "k" ++ " and " ++ kx "n" ++ ".") ]

  let s2 : Node := .node ("2. " ++ kx ("e^{ix}=" ++ zeta ++ "^{" ++ ks ++ "}")
      ++ " is a primitive " ++ ordinal n ++ " root of unity")
    [ .leaf ("the point on the unit circle at angle " ++ kx "x"
        ++ ", read as a complex number, is " ++ kx "e^{ix}=\\cos x+i\\sin x" ++ "."),
      .leaf (kx (zeta ++ "=e^{2\\pi i/" ++ ns ++ "}") ++ " is the " ++ ordinal n
        ++ " root of unity one step counterclockwise from " ++ kx "1" ++ "; "
        ++ kx "x" ++ " is " ++ kx "k/n" ++ " of a full turn, so "
        ++ kx ("e^{ix}=" ++ zeta ++ "^{" ++ ks ++ "}") ++ "."),
      .node ("<i>primitive</i>: it is " ++ artOrd n ++ " " ++ ordinal n
          ++ " root of unity but not an " ++ kx "m" ++ "-th root for any smaller " ++ kx "m")
        [ .leaf ("the order of " ++ kx (zeta ++ "^{k}") ++ " is "
            ++ kx "n/\\gcd(k, n)" ++ ", and "
            ++ kx ("\\gcd(" ++ ks ++ ", " ++ ns ++ ") = 1")
            ++ " — so the order of " ++ kx "e^{ix}" ++ " is exactly " ++ kx ns ++ ".") ] ]

  let s3 : Node := .node ("3. " ++ kx "\\mathbb{Q}(e^{ix})" ++ " has degree "
      ++ kx ("\\varphi(" ++ ns ++ ") = " ++ fs) ++ " over " ++ kx "\\mathbb{Q}")
    [ .node (kx "[\\mathbb{Q}(\\alpha):\\mathbb{Q}]" ++ ", the <i>degree</i> of a number "
        ++ kx "\\alpha" ++ ", is the degree of its minimal polynomial")
        [ .leaf ("the minimal polynomial of " ++ kx "\\alpha"
            ++ " is the lowest-degree polynomial with rational coefficients that has "
            ++ kx "\\alpha" ++ " as a root."),
          .leaf ("rational numbers have degree " ++ kx "1" ++ ", " ++ kx "\\sqrt{2}"
            ++ " has degree " ++ kx "2"
            ++ ", … — higher degree means harder to describe with rationals."),
          .leaf ("equivalently: the degree is the dimension of " ++ kx "\\mathbb{Q}(\\alpha)"
            ++ " — all numbers buildable from " ++ kx "\\alpha" ++ " and rationals with "
            ++ kx "+,\\;-,\\;\\times,\\;\\div" ++ " — as a vector space over "
            ++ kx "\\mathbb{Q}" ++ ".") ],
      .node ("the minimal polynomial of " ++ kx "e^{ix}" ++ " is the cyclotomic polynomial "
          ++ kx ("\\Phi_{" ++ ns ++ "}(t)=" ++ texPolyShort (cyclo n) "t")
          ++ ", of degree " ++ kx ("\\varphi(" ++ ns ++ ")"))
        [ .leaf (kx ("\\Phi_{" ++ ns ++ "}(t)=\\prod_j\\,(t-" ++ zeta ++ "^{j})")
            ++ ", with one factor for each of the " ++ fs ++ " exponents " ++ kx "j"
            ++ " coprime to " ++ kx ns ++ " — the primitive " ++ ordinal n
            ++ " roots of unity."),
          .leaf ("a classical theorem: " ++ kx ("\\Phi_{" ++ ns ++ "}")
            ++ " is irreducible over " ++ kx "\\mathbb{Q}"
            ++ ", so no smaller polynomial has " ++ kx "e^{ix}" ++ " as a root.") ],
      .node (kx ("\\varphi(" ++ ns ++ ") = " ++ fs)) (phiBullets n f) ]

  let bridge : Node := .node (kx "\\mathbb{Q}(e^{ix},i)=\\mathbb{Q}(\\cos x,\\sin x,i)"
      ++ " — adding " ++ kx "i" ++ " to either side gives the same field")
    [ .leaf ("one direction: " ++ kx "e^{ix}=\\cos x+i\\sin x" ++ "."),
      .leaf ("the other: " ++ kx "\\cos x=\\tfrac{1}{2}\\,(e^{ix}+e^{-ix})" ++ " and "
        ++ kx "\\sin x=\\tfrac{1}{2i}\\,(e^{ix}-e^{-ix})" ++ ", where "
        ++ kx "e^{-ix}=1/e^{ix}" ++ ".") ]

  let iNotReal : Node := .leaf ("everything in " ++ kx Qre ++ " is real, and "
    ++ kx "i" ++ " is not — so " ++ kx ("i \\notin " ++ Qre) ++ ".")
  let tSquared : Node := .leaf ("whenever " ++ kx "i" ++ " is missing from a field "
    ++ kx "F" ++ ", " ++ kx "t^2+1" ++ " is irreducible over " ++ kx "F"
    ++ ", and adjoining its root " ++ kx "i" ++ " multiplies the degree by exactly "
    ++ kx "2" ++ ".")

  let s4 : Node :=
    if n.tmod 4 == 0 then
      .node ("4. " ++ kx ("D=\\varphi(" ++ ns ++ ")/2=" ++ Ds))
        [ bridge,
          .node (kx "i" ++ " already lies in " ++ kx "\\mathbb{Q}(e^{ix})"
              ++ ", so the identity becomes "
              ++ kx "\\mathbb{Q}(e^{ix})=\\mathbb{Q}(\\cos x,\\sin x)(i)")
            [ .leaf (kx "4" ++ " divides " ++ kx ("n = " ++ ns) ++ ", so " ++ kx "i"
                ++ " is a power of " ++ kx zeta ++ ": "
                ++ kx ("i=" ++ zeta ++ "^{" ++ toString (n / 4) ++ "}") ++ "."),
              .leaf (kx ("\\mathbb{Q}(e^{ix})=\\mathbb{Q}(" ++ zeta ++ ")")
                ++ ", because " ++ kx "e^{ix}"
                ++ " is primitive — so it contains every power of " ++ kx zeta ++ ".") ],
          .node ("adjoining " ++ kx "i" ++ " to " ++ kx Qre ++ " is a degree-"
              ++ kx "2" ++ " step")
            [ iNotReal, tSquared ],
          .leaf ("degrees multiply in a tower: "
            ++ kx ("\\varphi(" ++ ns ++ ") = " ++ fs ++ " = D \\cdot 2") ++ ", so "
            ++ kx ("D=" ++ fs ++ "/2=" ++ Ds) ++ ".") ]
    else
      .node ("4. " ++ kx ("D=\\varphi(" ++ ns ++ ")=" ++ Ds))
        [ bridge,
          .node (kx ("\\mathbb{Q}(e^{ix},i)=" ++ QzL) ++ ", of degree "
              ++ kx ("\\varphi(" ++ Ls ++ ")=2\\,\\varphi(" ++ ns ++ ")=" ++ toString (2 * f)))
            [ .leaf (kx (zeta ++ "=" ++ zetaL ++ "^{" ++ toString (L / n) ++ "}") ++ " and "
                ++ kx ("i=" ++ zetaL ++ "^{" ++ toString (L / 4) ++ "}")
                ++ ", so both generators lie in " ++ kx QzL ++ "."),
              .leaf ("conversely " ++ kx (zeta ++ "\\cdot i=" ++ zetaL ++ "^{"
                  ++ toString (L / n + L / 4) ++ "}") ++ ", whose exponent is coprime to "
                ++ kx Ls ++ " — so " ++ kx zetaL
                ++ " itself is recovered, and the fields are equal.") ],
          .node ("the step from " ++ kx "\\mathbb{Q}(e^{ix})" ++ " up to " ++ kx QzL
              ++ " is degree " ++ kx "2" ++ ", because "
              ++ kx "i \\notin \\mathbb{Q}(e^{ix})")
            [ .leaf (kx ("\\mathbb{Q}(e^{ix})=\\mathbb{Q}(" ++ zeta ++ ")")
                ++ ", because " ++ kx "e^{ix}" ++ " is primitive."),
              .leaf ("a standard fact about cyclotomic fields: the only roots of unity inside "
                ++ kx ("\\mathbb{Q}(" ++ zeta ++ ")") ++ " are the " ++ ordinal (lcm 2 n)
                ++ " roots of unity — the powers " ++ kx ("\\pm" ++ zeta ++ "^{j}") ++ "."),
              .leaf (kx "\\pm i" ++ " have order " ++ kx "4" ++ ", and "
                ++ kx ("4 \\nmid " ++ toString (lcm 2 n)) ++ " — so " ++ kx "i"
                ++ " is not among them."),
              tSquared ],
          .node ("the step from " ++ kx Qre ++ " up to " ++ kx QzL
              ++ " is also degree " ++ kx "2" ++ ", because " ++ kx "i" ++ " is not real")
            [ iNotReal, tSquared ],
          .leaf ("each field sits one degree-" ++ kx "2" ++ " step below degree "
            ++ kx (toString (2 * f)) ++ ", so both have degree "
            ++ kx (toString (2 * f) ++ "/2 = " ++ fs) ++ " — and "
            ++ kx ("D=\\varphi(" ++ ns ++ ")=" ++ Ds) ++ ".") ]

  detailsB ("how " ++ kx ("D = " ++ Ds) ++ " is computed") (kids [s1, s2, s3, s4]) true

/-- A power of two rendered as a product of 2s: 8 ↦ "2\cdot2\cdot2". -/
partial def twosTex (f : Int) : String :=
  if f <= 2 then toString f else "2\\cdot" ++ twosTex (f / 2)

/-- The full info panel for one angle. -/
def angleInfo (k n : Int) : String :=
  let f := phi n
  let D := niceness k n
  let g := let g := gcd (2 * k) n; if g == 0 then 1 else g
  let fr := fr2 (2 * k / g) (n / g)
  let C := cosSym k n
  let S := sinSym k n
  let ms := ((n - 4 * k).tmod (4 * n) + 4 * n).tmod (4 * n)
  let ns := 4 * n / gcd (if ms == 0 then 4 * n else ms) (4 * n)
  let x := 2 * pi * Float.ofInt k / Float.ofInt n
  let line := fun (name : String) (V : Option Value) (val : Float) (nn : Int) =>
    match V with
    | some V => kx (name ++ " = " ++ tex V)
    | none => kx (name ++ " \\approx " ++ toFixed val 5) ++ ", a root of "
              ++ kx (texPoly (cosMinPoly nn) "t" ++ "=0")
  let deg := stripDot0 (toFixed (360 * Float.ofInt k / Float.ofInt n) 1)
  let con := f.toNat &&& (f.toNat - 1) == 0        -- φ a power of two
  kx ("x = " ++ fr ++ " = " ++ deg ++ "^{\\circ}") ++ "<br>"
  ++ line "\\cos x" C (Float.cos x) n ++ "<br>"
  ++ line "\\sin x" S (Float.sin x) ns ++ "<br>"
  ++ dTree k n f D
  ++ "<small>"
  ++ (if n == 1 || n == 2 || n == 4 then
        "constructible ✓ — the coordinates are rational"
      else if con then
        (if C.isSome then
          detailsB ("constructible ✓ — " ++ kx ("\\varphi(" ++ toString n ++ ") = " ++ toString f)
              ++ " is a power of " ++ kx "2" ++ ", so square-root formulas exist")
            (kids [
              .leaf ("each square root can at most double a field’s degree, so a tower of"
                ++ " nested square roots always has degree " ++ kx "2^j" ++ " over "
                ++ kx "\\mathbb{Q}" ++ "."),
              .leaf ("here " ++ kx ("\\varphi(" ++ toString n ++ ") = " ++ toString f
                  ++ " = " ++ twosTex f) ++ ": the tower up to "
                ++ kx "\\mathbb{Q}(\\cos x,\\sin x)"
                ++ " factors into quadratic steps, and the formulas above climb exactly"
                ++ " that tower."),
              .leaf ("equivalently (Gauss–Wantzel): the regular " ++ kx (toString n)
                ++ "-gon is constructible with straightedge and compass.") ])
         else
          "constructible ✓ — " ++ kx "\\varphi(17) = 16" ++ " is a power of " ++ kx "2"
          ++ ", so nested square roots suffice; but the tower for " ++ kx "\\cos x"
          ++ " has degree " ++ kx "8"
          ++ " and is omitted here, so only its minimal polynomial is shown")
      else
        let m := f / 2
        let op := oddPart m
        detailsB ("not constructible ✗ — " ++ kx ("\\varphi(" ++ toString n ++ ") = " ++ toString f)
            ++ " has an odd factor, so there is no square-root formula")
          (kids [
            .leaf ("each square root can at most double a field’s degree, so a tower of"
              ++ " nested square roots always has degree " ++ kx "2^j" ++ " over "
              ++ kx "\\mathbb{Q}" ++ " — never divisible by an odd number bigger than "
              ++ kx "1" ++ "."),
            .leaf ("but the degree of " ++ kx "\\cos x" ++ " is "
              ++ kx ("\\varphi(" ++ toString n ++ ")/2 = " ++ toString m)
              ++ (if op == m then " — odd" else " — odd factor " ++ kx (toString op))
              ++ " (its minimal polynomial is shown above), so "
              ++ kx "\\mathbb{Q}(\\cos x)"
              ++ " cannot sit inside any square-root tower. No matter how small "
              ++ kx "D" ++ " is, what matters is that it factors into " ++ kx "2"
              ++ "s."),
            .leaf ("this is exactly why the regular " ++ kx (toString n)
              ++ "-gon admits no straightedge-and-compass construction."),
            .leaf ("higher radicals do not rescue it over the reals: all " ++ kx (toString m)
              ++ " conjugates of " ++ kx "\\cos x"
              ++ " are real (they are cosines of related angles), and by a theorem of"
              ++ " Isaacs such a totally real number has a real-radical formula only when"
              ++ " its degree is a power of " ++ kx "2" ++ " — any radical expression for "
              ++ kx "\\cos x"
              ++ " must pass through non-real complex numbers (for degree "
              ++ kx "3" ++ " this is the classical <i>casus irreducibilis</i>).") ]))
  ++ "</small>"

/-! ## the angle table and JS emission -/

/-- The niceness threshold. The page shows the **complete** set of angles
    with D ≤ MAXD — constructed directly, not by enumerating denominators to
    an arbitrary cutoff: `Dden n ≤ T` forces `n ≤ 2(2T+1)²` (theorem
    `denominator_le_of_Dden_le` in `AngleNicenessSpec.lean`), so
    `completeDens MAXD` provably contains every qualifying denominator
    (`mem_completeDens`). The set is closed under every D-preserving symmetry
    by construction — see the reflection guards in the test section. -/
def MAXD : ℕ := 10

/-- All reduced fractions k/n over the complete denominator list. -/
def angleList : List (Int × Int) :=
  (completeDens MAXD).flatMap fun n =>
    if n == 1 then [((0 : Int), (1 : Int))]
    else (List.range n).filterMap fun kk =>
      let k : Int := Int.ofNat kk
      if gcd k (Int.ofNat n) != 1 then none else some (k, Int.ofNat n)

structure Row where
  k : Int
  n : Int
  D : Int
  cx : Float          -- point on the circle (radius 120, center 150/150)
  cy : Float
  x1 : Float          -- radial tick endpoints, half-length scaled by 1/√D
  y1 : Float
  x2 : Float
  y2 : Float
  hoverTex : String   -- LaTeX for the cursor tooltip: θ, exact x and y, D
  info : String

def mkRow (k n : Int) : Row :=
  let D := niceness k n
  let θ := 2 * pi * Float.ofInt k / Float.ofInt n
  let c := Float.cos θ
  let si := Float.sin θ
  let h := fmax 2.5 (8 / Float.sqrt (Float.ofInt D))   -- tick half-length
  let g := let g := gcd (2 * k) n; if g == 0 then 1 else g
  { k, n, D
    cx := 150 + 120 * c
    cy := 150 - 120 * si
    x1 := 150 + (120 - h) * c
    y1 := 150 - (120 - h) * si
    x2 := 150 + (120 + h) * c
    y2 := 150 - (120 + h) * si
    hoverTex :=
      let coord := fun (name : String) (V : Option Value) (val : Float) =>
        match V with
        | some V => name ++ " = " ++ tex V
        | none => name ++ " \\approx " ++ toFixed val 5
      "\\theta = " ++ fr2 (2 * k / g) (n / g) ++ " = "
      ++ stripDot0 (toFixed (360 * Float.ofInt k / Float.ofInt n) 1) ++ "^{\\circ}"
      ++ ",\\;\\; " ++ coord "x" (cosSym k n) c
      ++ ",\\;\\; " ++ coord "y" (sinSym k n) si
      ++ ",\\;\\; D = " ++ toString D
    info := angleInfo k n }

def rowJson (color : String) (r : Row) : String :=
  "{\"k\":" ++ toString r.k ++ ",\"n\":" ++ toString r.n ++ ",\"D\":" ++ toString r.D
  ++ ",\"cx\":" ++ toString r.cx ++ ",\"cy\":" ++ toString r.cy
  ++ ",\"x1\":" ++ toString r.x1 ++ ",\"y1\":" ++ toString r.y1
  ++ ",\"x2\":" ++ toString r.x2 ++ ",\"y2\":" ++ toString r.y2
  ++ ",\"c\":\"" ++ color ++ "\""
  ++ ",\"hoverTex\":\"" ++ jsEscape r.hoverTex ++ "\""
  ++ ",\"info\":\"" ++ jsEscape r.info ++ "\"}"

/-- Fixed palette for D levels, nicest first, in **spectral order**
    (increasing wavelength): violet, blue, teal, green, orange, red.
    Yellow is skipped (poor contrast on white); each neighbor pair stays
    clearly distinguishable. -/
def palette : List String :=
  ["hsl(275,65%,48%)", "hsl(222,75%,45%)", "hsl(185,90%,33%)",
   "hsl(130,60%,35%)", "hsl(28,95%,43%)", "hsl(0,75%,45%)"]

/-- Color of a D level; falls back to a hue ramp if there are ever more
    levels than palette entries. -/
def colorOf (levels : List Int) (D : Int) : String :=
  let idx := levels.idxOf D
  match palette[idx]? with
  | some c => c
  | none =>
    let L := levels.length
    let hue := if L <= 1 then 0 else 220 - 220 * idx / (L - 1)
    "hsl(" ++ toString hue ++ ",75%,42%)"

def main : IO Unit := do
  let rows := angleList.map fun (k, n) => mkRow k n
  let levels := (rows.map (·.D)).eraseDups.mergeSort (fun a b => decide (a <= b))
  let out :=
    "// Generated by `lake exe gen` from AngleNiceness.lean — do not edit.\n"
    ++ "const DATA = {\n"
    ++ "\"maxD\": " ++ toString MAXD ++ ",\n"
    ++ "\"levels\": [" ++ ",".intercalate (levels.map toString) ++ "],\n"
    ++ "\"colors\": [" ++ ",".intercalate (levels.map fun d => "\"" ++ colorOf levels d ++ "\"") ++ "],\n"
    ++ "\"angles\": [\n"
    ++ ",\n".intercalate (rows.map fun r => rowJson (colorOf levels r.D) r)
    ++ "\n]};\n"
  IO.FS.writeFile "angle-niceness-data.js" out
  IO.println s!"wrote angle-niceness-data.js: {rows.length} angles, {levels.length} levels"

/-! ## tests for the presentation helpers -/

#guard toFixed 51.42857142 1 == "51.4"
#guard toFixed 135.0 1 == "135.0"
#guard stripDot0 (toFixed 135.0 1) == "135"
#guard toFixed (-0.90096886) 5 == "-0.90097"
#guard toFixed 0.5 0 == "1"    -- rounds
#guard fr2 0 1 == "0"
#guard fr2 1 4 == "\\pi/4"
#guard fr2 3 4 == "3\\pi/4"
#guard fr2 1 1 == "\\pi"
#guard fr2 2 1 == "2\\pi"
#guard factor 1 == []
#guard factor 12 == [(2, 2), (3, 1)]
#guard factor 17 == [(17, 1)]
#guard factor 24 == [(2, 3), (3, 1)]
#guard texPolyShort (cosMinPoly 7) "t" == "8t^{3}+4t^{2}-4t-1"
#guard texPolyShort (cyclo 23) "t" == "t^{22}+t^{21}+t^{20}+\\cdots+t+1"   -- elision
#guard htmlEscape "a<b & c" == "a&lt;b &amp; c"
#guard jsEscape "a\\b\"c" == "a\\\\b\\\"c"
#guard (angleList.filter fun (_, n) => n == 24).length == 8   -- φ(24) reduced fractions

/-- Canonical form of an angle fraction: reduce and take k mod n. -/
def reduceAngle (k n : Int) : Int × Int :=
  let g := let g := gcd k n; if g == 0 then 1 else g
  let n' := n / g
  (((k / g).tmod n' + n').tmod n', n')

-- the drawn set is COMPLETE for D ≤ MAXD, hence closed under all three
-- D-preserving reflections (x-axis, y-axis, diagonal)
#guard angleList.all fun (k, n) =>
  [(n - k, n), (n - 2 * k, 2 * n), (n - 4 * k, 4 * n)].all fun (k', n') =>
    angleList.contains (reduceAngle k' n')
#guard angleList.contains (1, 36)          -- 10° = 2π·1/36 is in the picture now
#guard angleList.all fun (k, n) => niceness k n <= 10
#guard angleList.length == 216
-- claim used in the derivation text: for 4 ∤ n, ζₙ·i = ζ_L^(L/n+L/4) is a
-- *primitive* L-th root of unity, L = lcm(4, n)
#guard (List.range 200).all fun (i : Nat) =>
  let n : Int := (i : Int) + 1
  n.tmod 4 == 0 ||
  (let L := lcm 4 n
   gcd (L / n + L / 4) L == 1)
