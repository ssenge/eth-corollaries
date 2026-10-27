import EthCor.HamIso

/-! # Hamiltonian cycle with one-sided error in time 2^{o(n)}, for O(n) edges

The input is the code of G followed by the code of a seed ω (`seedCode`): W in unary, then the
numbers k, m₁, mm, M, the checks and the fixings of ω, each as a block of W bits 1^v 0^{W−v}. The
front end `preI` reads G and ω (`dk`, `dRows`, `dFixes` recover them, `decode_seedCode`) and writes
the compact code of the formula `hcI n E ω` of `EthCor.HamI` (width 3, NI = 5m + n + 2 + mm·k
variables). The machine of `MainTheoremForms.MainTheoremCompact` counts it, and the last step keeps
the low bit (`hcI_tm`). One machine serves every k, t and mm, since it reads them from the input.
With `HamI.iso_decide`: for graphs with at most D·n edges, for every δ > 0, the machine runs within
2^{εn} steps and outputs, for a random seed, 0 always if G has no Hamiltonian cycle, and 1 with
probability at least 2^{−δn} if it has one (`ham_randomized`). -/

namespace EthCor.HamITM

open Groundwork Groundwork.Prog Groundwork.Decode CountKSat GraphProblems Turing EthCor.Ham EthCor.HamS
  EthCor.HamTM EthCor.HamSTM EthCor.HamI EthCor.Iso

/-! ### Numbers in blocks of W bits -/

/-- v in a block of W bits. -/
def ublk (W v : ℕ) : List Bool := List.replicate v true ++ List.replicate (W - v) false

/-- The number in block p of a word of W-bit blocks. -/
def nm (W : ℕ) (b : List Bool) (p : ℕ) : ℕ := (((b.drop (p * W)).take W).takeWhile id).length

theorem length_ublk {W v : ℕ} (h : v ≤ W) : (ublk W v).length = W := by
  simp [ublk]; omega

theorem nm_flatMap (W : ℕ) : ∀ (L : List ℕ), (∀ v ∈ L, v ≤ W) → ∀ p, nm W (L.flatMap (ublk W)) p = L.getD p 0
  | [], _, p => by simp [nm]
  | a :: L, h, 0 => by
    have ha := h a (by simp)
    rw [nm, List.flatMap_cons, zero_mul, List.drop_zero, List.take_left' (length_ublk ha), ublk,
      List.takeWhile_append_of_pos (by simp), List.takeWhile_replicate]
    simp
  | a :: L, h, p + 1 => by
    have ha := h a (by simp)
    have e : nm W ((a :: L).flatMap (ublk W)) (p + 1) = nm W (L.flatMap (ublk W)) p := by
      rw [nm, nm, List.flatMap_cons, show (p + 1) * W = W + p * W by ring, ← List.drop_drop,
        List.drop_left' (length_ublk ha)]
    rw [e, nm_flatMap W L (fun v hv => h v (by simp [hv])) p]
    simp

theorem getD_flatMap_fin {r c : ℕ} (f : Fin r → List ℕ) (hf : ∀ i, (f i).length = c) {i j : ℕ} (hi : i < r)
    (hj : j < c) (d : ℕ) : ((List.finRange r).flatMap f).getD (i * c + j) d = (f ⟨i, hi⟩).getD j d := by
  rw [Read.getD_flatMap f c d hj _ (fun a _ => hf a) i, List.getElem?_eq_getElem (by simpa using hi)]
  simp [List.getElem_finRange]

theorem length_flatMap_fin {r c : ℕ} (f : Fin r → List ℕ) (hf : ∀ i, (f i).length = c) :
    ((List.finRange r).flatMap f).length = r * c := by
  rw [List.length_flatMap]
  simp [hf]

/-! ### The code of a seed -/

section Code

variable {M k t mm : ℕ}

/-- Term l of check i: j_l and c_l. -/
def termNums (ω : Seed M k t mm) (i : Fin mm) (l : Fin k) : List ℕ := [((ω.2.1.1 i).1 l).val, ((ω.2.1.1 i).2 l).toNat]

/-- Check i: the terms, then the right-hand side. -/
def rowNums (ω : Seed M k t mm) (i : Fin mm) : List ℕ :=
  (List.finRange k).flatMap (termNums ω i) ++ [(ω.2.1.2 i).toNat]

/-- Coordinate j: 0 if it is fixed, then the bit. -/
def fixNums (ω : Seed M k t mm) (j : Fin M) : List ℕ :=
  [if (ω.2.2 j).1.val = 0 then 0 else 1, (ω.2.2 j).2.toNat]

def seedNums (ω : Seed M k t mm) : List ℕ :=
  [k, ω.1.val, mm, M] ++ ((List.finRange mm).flatMap (rowNums ω) ++ (List.finRange M).flatMap (fixNums ω))

/-- **The code of a seed**: W = M + k + mm + 1 in unary, then the numbers in blocks of W bits. -/
def seedCode (ω : Seed M k t mm) : List Bool :=
  unary (M + k + mm + 1) ++ (seedNums ω).flatMap (ublk (M + k + mm + 1))

theorem length_rowNums (ω : Seed M k t mm) (i : Fin mm) : (rowNums ω i).length = 2 * k + 1 := by
  rw [rowNums, List.length_append, length_flatMap_fin (c := 2) (termNums ω i) (fun _ => rfl)]
  simp; ring

theorem le_seedW (ω : Seed M k t mm) : ∀ v ∈ seedNums ω, v ≤ M + k + mm + 1 := by
  have hm₁ : ω.1.val ≤ mm := Nat.lt_succ_iff.1 ω.1.2
  have hb : ∀ b : Bool, b.toNat ≤ M + k + mm + 1 := fun b => (Bool.toNat_le b).trans (by omega)
  intro v hv
  rcases List.mem_append.1 hv with hv | hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  · rcases List.mem_append.1 hv with hv | hv
    · obtain ⟨i, -, hv⟩ := List.mem_flatMap.1 hv
      rcases List.mem_append.1 hv with hv | hv
      · obtain ⟨l, -, hv⟩ := List.mem_flatMap.1 hv
        simp only [termNums, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · have := ((ω.2.1.1 i).1 l).2; omega
        · exact hb _
      · rw [List.mem_singleton] at hv; subst hv; exact hb _
    · obtain ⟨j, -, hv⟩ := List.mem_flatMap.1 hv
      simp only [fixNums, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · split_ifs <;> omega
      · exact hb _

theorem getD_hdr (ω : Seed M k t mm) :
    (seedNums ω).getD 0 0 = k ∧ (seedNums ω).getD 1 0 = ω.1.val ∧ (seedNums ω).getD 2 0 = mm ∧
      (seedNums ω).getD 3 0 = M := by
  simp [seedNums]

theorem getD_body (ω : Seed M k t mm) (q : ℕ) :
    (seedNums ω).getD (4 + q) 0 = ((List.finRange mm).flatMap (rowNums ω) ++ (List.finRange M).flatMap (fixNums ω)).getD q 0 := by
  rw [seedNums, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem getD_row (ω : Seed M k t mm) {i : ℕ} (hi : i < mm) {p : ℕ} (hp : p < 2 * k + 1) :
    (seedNums ω).getD (4 + (i * (2 * k + 1) + p)) 0 = (rowNums ω ⟨i, hi⟩).getD p 0 := by
  rw [getD_body, List.getD_append _ _ _ _ ?_, getD_flatMap_fin _ (length_rowNums ω) hi hp]
  rw [length_flatMap_fin _ (length_rowNums ω)]
  calc i * (2 * k + 1) + p < i * (2 * k + 1) + (2 * k + 1) := by omega
    _ = (i + 1) * (2 * k + 1) := by ring
    _ ≤ mm * (2 * k + 1) := Nat.mul_le_mul_right _ hi

theorem getD_term (ω : Seed M k t mm) {i : ℕ} (hi : i < mm) {l : ℕ} (hl : l < k) :
    (seedNums ω).getD (4 + (i * (2 * k + 1) + 2 * l)) 0 = ((ω.2.1.1 ⟨i, hi⟩).1 ⟨l, hl⟩).val ∧
      (seedNums ω).getD (4 + (i * (2 * k + 1) + (2 * l + 1))) 0 = ((ω.2.1.1 ⟨i, hi⟩).2 ⟨l, hl⟩).toNat := by
  have hT := length_flatMap_fin (c := 2) (termNums ω ⟨i, hi⟩) (fun _ => rfl)
  rw [getD_row ω hi (by omega), getD_row ω hi (by omega), rowNums, List.getD_append _ _ _ _ (by rw [hT]; omega),
    List.getD_append _ _ _ _ (by rw [hT]; omega), show 2 * l = l * 2 + 0 by ring,
    show l * 2 + 0 + 1 = l * 2 + 1 by ring, getD_flatMap_fin (c := 2) (termNums ω ⟨i, hi⟩) (fun _ => rfl) hl (by norm_num),
    getD_flatMap_fin (c := 2) (termNums ω ⟨i, hi⟩) (fun _ => rfl) hl (by norm_num)]
  simp [termNums]

theorem getD_rhs (ω : Seed M k t mm) {i : ℕ} (hi : i < mm) :
    (seedNums ω).getD (4 + (i * (2 * k + 1) + 2 * k)) 0 = (ω.2.1.2 ⟨i, hi⟩).toNat := by
  have hT := length_flatMap_fin (c := 2) (termNums ω ⟨i, hi⟩) (fun _ => rfl)
  rw [getD_row ω hi (by omega), rowNums, List.getD_append_right _ _ _ _ (by rw [hT]; omega), hT]
  simp [show 2 * k - k * 2 = 0 by omega]

theorem getD_fix (ω : Seed M k t mm) {j : ℕ} (hj : j < M) :
    (seedNums ω).getD (4 + (mm * (2 * k + 1) + 2 * j)) 0 = (if (ω.2.2 ⟨j, hj⟩).1.val = 0 then 0 else 1) ∧
      (seedNums ω).getD (4 + (mm * (2 * k + 1) + (2 * j + 1))) 0 = (ω.2.2 ⟨j, hj⟩).2.toNat := by
  rw [getD_body, getD_body, List.getD_append_right _ _ _ _ (by rw [length_flatMap_fin _ (length_rowNums ω)]; omega),
    List.getD_append_right _ _ _ _ (by rw [length_flatMap_fin _ (length_rowNums ω)]; omega),
    length_flatMap_fin _ (length_rowNums ω), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
    show 2 * j = j * 2 + 0 by ring, show j * 2 + 0 + 1 = j * 2 + 1 by ring,
    getD_flatMap_fin (c := 2) (fixNums ω) (fun _ => rfl) hj (by norm_num),
    getD_flatMap_fin (c := 2) (fixNums ω) (fun _ => rfl) hj (by norm_num)]
  simp [fixNums]

end Code

/-! ### Reading the seed -/

/-- The number in block p of the seed part s. -/
def dn (s : List Bool) (p : ℕ) : ℕ := nm (ones s) (rest s) p

def dk (s : List Bool) : ℕ := dn s 0
def dm1 (s : List Bool) : ℕ := dn s 1
def dmm (s : List Bool) : ℕ := dn s 2
def dM (s : List Bool) : ℕ := dn s 3

/-- The checks read from s. -/
def dRows (s : List Bool) : List (List (ℕ × Bool) × Bool) :=
  (List.range (dmm s)).map fun i =>
    ((List.range (dk s)).map fun l => (dn s (4 + (i * (2 * dk s + 1) + 2 * l)),
      decide (dn s (4 + (i * (2 * dk s + 1) + (2 * l + 1))) = 1)),
     decide (dn s (4 + (i * (2 * dk s + 1) + 2 * dk s)) = 1))

/-- The fixings read from s. -/
def dFixes (s : List Bool) : List (ℕ × Bool) :=
  (List.range (dM s)).filterMap fun j =>
    if dn s (4 + (dmm s * (2 * dk s + 1) + 2 * j)) = 0 then
      some (j, decide (dn s (4 + (dmm s * (2 * dk s + 1) + (2 * j + 1))) = 1))
    else none

section Decode

variable {M k t mm : ℕ}

theorem dn_seedCode (ω : Seed M k t mm) (p : ℕ) : dn (seedCode ω) p = (seedNums ω).getD p 0 := by
  rw [dn, seedCode, Read.ones_unary_append, Read.rest_unary_append, nm_flatMap _ _ (le_seedW ω)]

theorem toNat_eq_one (b : Bool) : decide (b.toNat = 1) = b := by cases b <;> rfl

/-- **The code of a seed is read back.** -/
theorem decode_seedCode (ω : Seed M k t mm) :
    dk (seedCode ω) = k ∧ dm1 (seedCode ω) = ω.1.val ∧ dmm (seedCode ω) = mm ∧ dM (seedCode ω) = M ∧
      dRows (seedCode ω) = rowsOf ω ∧ dFixes (seedCode ω) = fixesOf ω := by
  obtain ⟨h0, h1, h2, h3⟩ := getD_hdr ω
  have ek : dk (seedCode ω) = k := by rw [dk, dn_seedCode, h0]
  have emm : dmm (seedCode ω) = mm := by rw [dmm, dn_seedCode, h2]
  have eM : dM (seedCode ω) = M := by rw [dM, dn_seedCode, h3]
  refine ⟨ek, by rw [dm1, dn_seedCode, h1], emm, eM, ?_, ?_⟩
  · rw [dRows, ek, emm]
    refine List.ext_getElem (by simp [rowsOf]) fun i hi1 hi2 => ?_
    have hi : i < mm := by simpa using hi1
    simp only [List.getElem_map, List.getElem_range, rowsOf, List.getElem_ofFn]
    refine Prod.ext ?_ ?_
    · refine List.ext_getElem (by simp [rowL]) fun l hl1 hl2 => ?_
      have hl : l < k := by simpa using hl1
      obtain ⟨e1, e2⟩ := getD_term ω hi hl
      simp only [List.getElem_map, List.getElem_range, rowL, List.getElem_ofFn, dn_seedCode, e1, e2,
        toNat_eq_one]
    · simp only [dn_seedCode, getD_rhs ω hi, toNat_eq_one]
  · rw [dFixes, ek, emm, eM, fixesOf]
    have hr : (List.finRange M).map Fin.val = List.range M :=
      List.ext_getElem (by simp) fun i h1 h2 => by simp
    rw [← hr, List.filterMap_map]
    refine List.filterMap_congr fun j _ => ?_
    obtain ⟨e1, e2⟩ := getD_fix ω j.2
    simp only [Function.comp_apply, dn_seedCode, e1, e2, toNat_eq_one, Fin.eta]
    by_cases hj : (ω.2.2 j).1.val = 0 <;> simp [hj]

end Decode

/-! ### The front end -/

/-- The seed part of the input: what follows the matrix. -/
def sI (x : List Bool) : List Bool := (gH x).2.drop (nH x * nH x)

/-- The number of variables. -/
def NII (x : List Bool) : ℕ := NS x + dmm (sI x) * dk (sI x)

def formI (x : List Bool) : Fml :=
  (hcS (nH x) (EH x) ++ isoF (zC (EH x) (nH x)) (NS x) (dk (sI x)) (dm1 (sI x)) (dRows (sI x)) (dFixes (sI x))).dedup

/-- The front end: the compact code of the formula, 3 slots per clause. -/
def preI (x : List Bool) : List Bool :=
  encK (List.replicate 3 ()) (List.replicate (Nat.log2 (2 * NII x) + 1) ()) (formI x)

/-! ### It is polynomial-time -/

section Poly

variable {α : Type} [Enc α]

@[fun_prop] theorem dn_polyT {s : α → List Bool} {p : α → ℕ} (hs : PolyT s) (hp : PolyT p) :
    PolyT fun a => dn (s a) (p a) := by
  unfold dn nm ones rest; fun_prop

theorem dn_unary {s : α → List Bool} {p : α → ℕ} (hs : PolyT s) (hp : PolyT p) : Unary fun a => dn (s a) (p a) := by
  have h : PolyT fun a => (((rest (s a)).drop (p a * ones (s a))).take (ones (s a))).takeWhile id := by
    unfold ones rest; fun_prop
  exact Unary.of_length h

theorem pos_polyT {a b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => 4 + (a x * (2 * b x + 1) + c x) := by fun_prop

theorem dnb_polyT {s : α → List Bool} {p : α → ℕ} (hs : PolyT s) (hp : PolyT p) :
    PolyT fun a => decide (dn (s a) (p a) = 1) := by
  have := dn_polyT hs hp; fun_prop

theorem dnz_polyT {s : α → List Bool} {p : α → ℕ} (hs : PolyT s) (hp : PolyT p) :
    PolyT fun a => decide (dn (s a) (p a) = 0) := by
  have := dn_polyT hs hp; fun_prop

theorem zC_polyT {E : α → List (ℕ × ℕ)} {n : α → ℕ} (hE : PolyT E) (hn : PolyT n) :
    PolyT fun a => zC (E a) (n a) := by
  unfold zC; fun_prop

theorem dRows_polyT {s : α → List Bool} (hs : PolyT s) : PolyT fun a => dRows (s a) := by
  have hmm : Unary fun a => dmm (s a) := dn_unary hs (PolyT.const 2)
  have hs1 : PolyT fun p : α × ℕ => s p.1 := hs.comp PolyT.id'.fst
  have hs2 : PolyT fun q : (α × ℕ) × ℕ => s q.1.1 := hs.comp PolyT.id'.fst.fst
  have hk1 : PolyT fun p : α × ℕ => dk (s p.1) := dn_polyT hs1 (PolyT.const 0)
  have hk2 : PolyT fun q : (α × ℕ) × ℕ => dk (s q.1.1) := dn_polyT hs2 (PolyT.const 0)
  have hi2 : PolyT fun q : (α × ℕ) × ℕ => q.1.2 := PolyT.id'.fst.snd
  have hl2 : PolyT fun q : (α × ℕ) × ℕ => q.2 := PolyT.id'.snd
  have ht : PolyT fun q : (α × ℕ) × ℕ => (dn (s q.1.1) (4 + (q.1.2 * (2 * dk (s q.1.1) + 1) + 2 * q.2)),
      decide (dn (s q.1.1) (4 + (q.1.2 * (2 * dk (s q.1.1) + 1) + (2 * q.2 + 1))) = 1)) :=
    PolyT.prodMk (dn_polyT hs2 (pos_polyT hi2 hk2 (by fun_prop)))
      (dnb_polyT hs2 (pos_polyT hi2 hk2 (by fun_prop)))
  have hrow : PolyT fun p : α × ℕ =>
      (((List.range (dk (s p.1))).map fun l => (dn (s p.1) (4 + (p.2 * (2 * dk (s p.1) + 1) + 2 * l)),
        decide (dn (s p.1) (4 + (p.2 * (2 * dk (s p.1) + 1) + (2 * l + 1))) = 1))),
       decide (dn (s p.1) (4 + (p.2 * (2 * dk (s p.1) + 1) + 2 * dk (s p.1))) = 1)) :=
    PolyT.prodMk (PolyT.map ht (PolyT.range (dn_unary hs1 (PolyT.const 0))))
      (dnb_polyT hs1 (pos_polyT PolyT.id'.snd hk1 (by fun_prop)))
  exact PolyT.map hrow (PolyT.range hmm)

theorem dFixes_polyT {s : α → List Bool} (hs : PolyT s) : PolyT fun a => dFixes (s a) := by
  have hM : Unary fun a => dM (s a) := dn_unary hs (PolyT.const 3)
  have hs1 : PolyT fun p : α × ℕ => s p.1 := hs.comp PolyT.id'.fst
  have hk1 : PolyT fun p : α × ℕ => dk (s p.1) := dn_polyT hs1 (PolyT.const 0)
  have hm1 : PolyT fun p : α × ℕ => dmm (s p.1) := dn_polyT hs1 (PolyT.const 2)
  have hj : PolyT fun p : α × ℕ => p.2 := PolyT.id'.snd
  have h0 : PolyT fun p : α × ℕ => decide (dn (s p.1) (4 + (dmm (s p.1) * (2 * dk (s p.1) + 1) + 2 * p.2)) = 0) :=
    dnz_polyT hs1 (pos_polyT hm1 hk1 (by fun_prop))
  have h1 : PolyT fun p : α × ℕ => (some (p.2, decide (dn (s p.1) (4 + (dmm (s p.1) * (2 * dk (s p.1) + 1) +
      (2 * p.2 + 1))) = 1)) : Option (ℕ × Bool)) :=
    PolyT.some' (PolyT.prodMk hj (dnb_polyT hs1 (pos_polyT hm1 hk1 (by fun_prop))))
  have hf : PolyT fun p : α × ℕ => if dn (s p.1) (4 + (dmm (s p.1) * (2 * dk (s p.1) + 1) + 2 * p.2)) = 0 then
      some (p.2, decide (dn (s p.1) (4 + (dmm (s p.1) * (2 * dk (s p.1) + 1) + (2 * p.2 + 1))) = 1)) else none :=
    PolyT.ite' h0 h1 (PolyT.const none)
  exact PolyT.filterMap hf (PolyT.range hM)

theorem xstep_eq (p x a : ℕ) (c : Bool) : xstep p x a c =
    bif c then [[(a, false), (p, true), (x, true)], [(a, false), (p, false), (x, false)],
      [(a, true), (p, false), (x, true)], [(a, true), (p, true), (x, false)]]
    else [[(a, false), (p, true)], [(a, true), (p, false)]] := by
  cases c <;> rfl

theorem xstep_polyT {p x a : α → ℕ} {c : α → Bool} (hp : PolyT p) (hx : PolyT x) (ha : PolyT a) (hc : PolyT c) :
    PolyT fun z => xstep (p z) (x z) (a z) (c z) := by
  have h : PolyT fun z => bif c z then [[(a z, false), (p z, true), (x z, true)], [(a z, false), (p z, false), (x z, false)],
      [(a z, true), (p z, false), (x z, true)], [(a z, true), (p z, true), (x z, false)]]
    else [[(a z, false), (p z, true)], [(a z, true), (p z, false)]] := by fun_prop
  exact h.congr fun z => (xstep_eq _ _ _ _).symm

theorem rowF_polyT {z B k i : α → ℕ} {L : α → List (ℕ × Bool)} (hz : PolyT z) (hB : PolyT B) (hk : Unary k)
    (hi : PolyT i) (hL : PolyT L) : PolyT fun a => rowF (z a) (B a) (k a) (i a) (L a) := by
  have hk' := hk.poly
  have hx : PolyT fun p : α × ℕ => xstep (if p.2 = 0 then z p.1 else B p.1 + i p.1 * k p.1 + (p.2 - 1))
      ((L p.1).getD p.2 (0, false)).1 (B p.1 + i p.1 * k p.1 + p.2) ((L p.1).getD p.2 (0, false)).2 :=
    xstep_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rowF
  exact PolyT.flatMap hx (PolyT.range hk)

theorem isoF_polyT {z B k m₁ : α → ℕ} {rows : α → List (List (ℕ × Bool) × Bool)} {fixes : α → List (ℕ × Bool)}
    (hk : Unary k) (hz : PolyT z) (hB : PolyT B) (hm₁ : PolyT m₁) (hrows : PolyT rows) (hfixes : PolyT fixes) :
    PolyT fun a => isoF (z a) (B a) (k a) (m₁ a) (rows a) (fixes a) := by
  have hk' := hk.poly
  have hl : Unary fun a => (rows a).length := Unary.of_length hrows
  have hmin : Unary fun a => min (m₁ a) (rows a).length :=
    Unary.of_le hl (by have := hl.poly; fun_prop) fun a => min_le_right _ _
  have h1 : PolyT fun a => (List.range (rows a).length).flatMap fun i => rowF (z a) (B a) (k a) i ((rows a).getD i ([], false)).1 :=
    PolyT.flatMap (rowF_polyT (by fun_prop) (by fun_prop) (hk.comp (by fun_prop)) (by fun_prop) (by fun_prop))
      (PolyT.range hl)
  have hr : PolyT fun a => List.range (min (m₁ a) (rows a).length) := PolyT.range hmin
  have h2 : PolyT fun a => (List.range (min (m₁ a) (rows a).length)).map fun i =>
      [(B a + i * k a + (k a - 1), ((rows a).getD i ([], false)).2)] := by fun_prop
  have h3 : PolyT fun a => (fixes a).map fun q => [q] := by fun_prop
  unfold isoF
  exact PolyT.append (PolyT.append h1 h2) h3

end Poly

theorem preI_polyT : PolyT preI := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hm : Unary fun x => (EH x).length := Unary.of_length hE
  have hNS : Unary NS := (hm.add hn).add (((Unary.const 4).mul hm).add (Unary.const 2))
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hk : Unary fun x => dk (sI x) := dn_unary hs (PolyT.const 0)
  have hmm : Unary fun x => dmm (sI x) := dn_unary hs (PolyT.const 2)
  have hN : Unary NII := hNS.add (hmm.mul hk)
  have hK : PolyT fun _ : List Bool => List.replicate 3 () := Unary.const 3
  have hw : Unary fun x => Nat.log2 (2 * NII x) + 1 :=
    Unary.of_le (((Unary.const 2).mul hN).add (Unary.const 1)) (log2_polyT hN.poly)
      fun x => by have := Nat.log2_le_self (2 * NII x); omega
  have hz : PolyT fun x => zC (EH x) (nH x) := zC_polyT hE hn.poly
  have hm1 : PolyT fun x => dm1 (sI x) := dn_polyT hs (PolyT.const 1)
  have hR : PolyT fun x => dRows (sI x) := dRows_polyT hs
  have hX : PolyT fun x => dFixes (sI x) := dFixes_polyT hs
  have hI : PolyT fun x => isoF (zC (EH x) (nH x)) (NS x) (dk (sI x)) (dm1 (sI x)) (dRows (sI x)) (dFixes (sI x)) :=
    isoF_polyT hk hz hNS.poly hm1 hR hX
  have hF : PolyT formI := PolyT.dedup (PolyT.append (hcS_polyT hn hE) hI)
  exact encK_polyT hK hw hF

/-! ### What the front end reads from the code of G and a seed -/

/-- The edge list does not see what follows the matrix. -/
theorem edges_append {n : ℕ} (G : SimpleGraph (Fin n)) (s : List Bool) :
    edges n (matrix G ++ s) = edges n (matrix G) := by
  unfold edges
  refine List.filter_congr fun p hp => ?_
  obtain ⟨h1, h2⟩ := List.mem_product.1 hp
  rw [List.mem_range] at h1 h2
  have hlt : p.1 * n + p.2 < (matrix G).length := by
    rw [stMatrixLength n G]
    calc p.1 * n + p.2 < p.1 * n + n := by omega
      _ = (p.1 + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n h1
  simp only [adjB, List.getD_append _ _ _ _ hlt]

theorem read_code {n : ℕ} (G : SimpleGraph (Fin n)) (s : List Bool) :
    nH (code G ++ s) = n ∧ EH (code G ++ s) = edges n (matrix G) ∧ sI (code G ++ s) = s := by
  have hg : gH (code G ++ s) = (List.replicate n (), matrix G ++ s) := by
    rw [gH, read1, code, List.append_assoc, Read.ones_unary_append, Read.rest_unary_append]
  have hn : nH (code G ++ s) = n := by rw [nH, hg, List.length_replicate]
  refine ⟨hn, ?_, ?_⟩
  · simp only [EH, hn, hg]; exact edges_append G s
  · simp only [sI, hn, hg]; exact List.drop_left' (stMatrixLength n G)

/-- **The front end writes the formula of G and ω.** -/
theorem formI_code {n : ℕ} (G : SimpleGraph (Fin n)) {k t mm : ℕ} (ω : Seed (edges n (matrix G)).length k t mm) :
    formI (code G ++ seedCode ω) = (hcI n (edges n (matrix G)) ω).dedup ∧
      NII (code G ++ seedCode ω) = NI n (edges n (matrix G)).length mm k := by
  obtain ⟨hn, hE, hs⟩ := read_code G (seedCode ω)
  obtain ⟨ek, em1, emm, -, eR, eF⟩ := decode_seedCode ω
  refine ⟨?_, ?_⟩
  · rw [formI, NS, hn, hE, hs, ek, em1, eR, eF]; rfl
  · rw [NII, NS, hn, hE, hs, ek, emm]; rfl

/-! ### The facts on the formula -/

theorem ik_lt {i l k mm : ℕ} (hi : i < mm) (hl : l < k) : i * k + l < mm * k :=
  calc i * k + l < i * k + k := by omega
    _ = (i + 1) * k := by ring
    _ ≤ mm * k := Nat.mul_le_mul_right k hi

theorem mem_xstep {p x a : ℕ} {c : Bool} {C : List (ℕ × Bool)} (h : C ∈ xstep p x a c) :
    C.length ≤ 3 ∧ ∀ l ∈ C, l.1 = p ∨ l.1 = x ∨ l.1 = a := by
  cases c <;> simp only [xstep, List.mem_cons, List.not_mem_nil, or_false] at h
  · rcases h with rfl | rfl <;> simp
  · rcases h with rfl | rfl | rfl | rfl <;> simp

theorem length_xstep_le (p x a : ℕ) (c : Bool) : (xstep p x a c).length ≤ 4 := by
  cases c <;> simp [xstep]

/-- The clauses of the checks and fixings have at most three literals, and their variables are below
N₀ + mm·k. -/
theorem isoF_clause {M k t mm N₀ z m₁ : ℕ} (hM : M ≤ N₀) (hz : z < N₀) (hk : 1 ≤ k) (ω : Seed M k t mm)
    {C : List (ℕ × Bool)} (hC : C ∈ isoF z N₀ k m₁ (rowsOf ω) (fixesOf ω)) :
    C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < N₀ + mm * k := by
  have hidx : ∀ i < mm, ∀ l, (((rowsOf ω).getD i ([], false)).1.getD l (0, false)).1 < N₀ := by
    intro i hi l
    refine getD_prop (P := fun q : ℕ × Bool => q.1 < N₀) (by show 0 < N₀; omega) (fun q hq => ?_) l
    rw [getD_rowsOf ω hi] at hq
    dsimp only at hq
    rw [rowL, List.mem_ofFn] at hq
    obtain ⟨l', rfl⟩ := hq
    exact lt_of_lt_of_le ((ω.2.1.1 ⟨i, hi⟩).1 l').2 hM
  simp only [isoF, List.mem_append] at hC
  rcases hC with (hC | hC) | hC
  · obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
    rw [List.mem_range, length_rowsOf] at hi
    unfold rowF at hC
    obtain ⟨l, hl, hC⟩ := List.mem_flatMap.1 hC
    rw [List.mem_range] at hl
    obtain ⟨h1, h2⟩ := mem_xstep hC
    refine ⟨h1, fun q hq => ?_⟩
    have := ik_lt hi hl
    have := hidx i hi l
    rcases h2 q hq with h | h | h
    · rw [h]; split_ifs <;> omega
    · omega
    · omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hC
    rw [List.mem_range, length_rowsOf] at hi
    have hi' : i < mm := lt_of_lt_of_le hi (min_le_right _ _)
    refine ⟨by simp, fun q hq => ?_⟩
    rw [List.mem_singleton] at hq; subst hq
    have := ik_lt hi' (show k - 1 < k by omega); simp only; omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hC
    obtain ⟨j, -, rfl⟩ := (mem_fixesOf ω q).1 hq
    refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton] at hl; subst hl
    have := j.2; simp only; omega

theorem hcI_clause {n : ℕ} (hn : 0 < n) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {k t mm : ℕ}
    (hk : 1 ≤ k) (ω : Seed E.length k t mm) {C : List (ℕ × Bool)} (hC : C ∈ hcI n E ω) :
    C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < NI n E.length mm k := by
  rcases List.mem_append.1 hC with hC | hC
  · obtain ⟨h1, h2⟩ := hcS_clause hn hE hC
    exact ⟨h1, fun l hl => by have := h2 l hl; unfold NI; omega⟩
  · exact isoF_clause (by omega) (by unfold zC; omega) hk ω hC

/-- Every variable occurs in the formula of a seed. -/
theorem occurs_hcI {n : ℕ} (E : List (ℕ × ℕ)) {k t mm : ℕ} (hk : 1 ≤ k) (ω : Seed E.length k t mm) :
    ∀ i < NI n E.length mm k, ∃ C ∈ hcI n E ω, ∃ b, (i, b) ∈ C := by
  intro i hi
  by_cases h0 : i < E.length + n + (4 * E.length + 2)
  · exact ⟨_, List.mem_append_left _ (mem_hcS_taut E h0), true, by simp⟩
  · obtain ⟨r, rfl⟩ : ∃ r, i = E.length + n + (4 * E.length + 2) + r := ⟨i - (E.length + n + (4 * E.length + 2)), by omega⟩
    have hr : r < mm * k := by unfold NI at hi; omega
    have hk0 : 0 < k := hk
    have hq : r / k < mm := (Nat.div_lt_iff_lt_mul hk0).2 hr
    have hl : r % k < k := Nat.mod_lt _ hk0
    have e : r / k * k + r % k = r := by rw [mul_comm]; exact Nat.div_add_mod _ _
    set c := (((rowsOf ω).getD (r / k) ([], false)).1.getD (r % k) (0, false)).2
    obtain ⟨C, hC, hb⟩ : ∃ C ∈ xstep (if r % k = 0 then zC E n else E.length + n + (4 * E.length + 2) + r / k * k + (r % k - 1))
        (((rowsOf ω).getD (r / k) ([], false)).1.getD (r % k) (0, false)).1
        (E.length + n + (4 * E.length + 2) + r / k * k + r % k) c,
        (E.length + n + (4 * E.length + 2) + r / k * k + r % k, false) ∈ C := by
      cases c <;> exact ⟨_, List.mem_cons_self .., List.mem_cons_self ..⟩
    refine ⟨C, List.mem_append_right _ ?_, false, ?_⟩
    · simp only [isoF, List.mem_append]
      refine Or.inl (Or.inl (List.mem_flatMap.2 ⟨r / k, List.mem_range.2 (by rw [length_rowsOf]; exact hq), ?_⟩))
      exact List.mem_flatMap.2 ⟨r % k, List.mem_range.2 hl, hC⟩
    · rw [add_assoc, e] at hb; exact hb

theorem allOccur_of {N : ℕ} {ψ : Fml} {φ : Sat3.CNF N} (hφ : toN φ = ψ.dedup)
    (h : ∀ i < N, ∃ C ∈ ψ, ∃ b, (i, b) ∈ C) : SatM.AllOccur φ := by
  intro i
  obtain ⟨C, hC, b, hb⟩ := h i.val i.2
  rw [← List.mem_dedup, ← hφ, mem_toN] at hC
  obtain ⟨D, hD, hDe⟩ := hC
  have hl : (i.val, b) ∈ D.map (fun l => (l.1.val, l.2)) := by rw [hDe]; exact hb
  obtain ⟨l', hl', e⟩ := List.mem_map.1 hl
  exact ⟨D, hD, l', hl', Fin.ext (congrArg Prod.fst e)⟩

theorem two_le_length_of {N : ℕ} {ψ : Fml} {φ : Sat3.CNF N} (hφ : toN φ = ψ.dedup)
    (h0 : [((0 : ℕ), true), (0, false)] ∈ ψ) (h1 : [((1 : ℕ), true), (1, false)] ∈ ψ) : 2 ≤ φ.length := by
  have hl : φ.length = ψ.dedup.length := by rw [← hφ, toN, List.length_map]
  rw [hl]
  rw [← List.mem_dedup] at h0 h1
  have hne : [((0 : ℕ), true), (0, false)] ≠ [(1, true), (1, false)] := by simp
  have hsub : ({[((0 : ℕ), true), (0, false)], [(1, true), (1, false)]} : Finset (List (ℕ × Bool))) ⊆
      ψ.dedup.toFinset := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rw [List.mem_toFinset]; rcases hC with rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne, List.toFinset_card_of_nodup (List.nodup_dedup _)] at this
  exact this

theorem isKCNF_of {N : ℕ} {ψ : Fml} {φ : Sat3.CNF N} (hφ : toN φ = ψ.dedup) (h : ∀ C ∈ ψ, C.length ≤ 3) :
    SatK.IsKCNF 3 φ := by
  refine ⟨fun D hD => ?_, ?_⟩
  · have hm : D.map (fun l => (l.1.val, l.2)) ∈ toN φ := mem_toN.2 ⟨D, hD, rfl⟩
    rw [hφ, List.mem_dedup] at hm
    simpa using h _ hm
  · have h : (toN φ).Nodup := by rw [hφ]; exact List.nodup_dedup _
    exact List.Nodup.of_map _ h

theorem numSat_of {N : ℕ} {ψ : Fml} {φ : Sat3.CNF N} (hφ : toN φ = ψ.dedup) : SatK.numSat φ = cntN N ψ := by
  rw [← stCntToN, hφ]
  unfold cntN
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_dedup]

/-! ### The lengths -/

theorem length_isoF_le (z B k m₁ : ℕ) (rows : List (List (ℕ × Bool) × Bool)) (fixes : List (ℕ × Bool)) :
    (isoF z B k m₁ rows fixes).length ≤ rows.length * (k * 4) + rows.length + fixes.length := by
  have h1 : ((List.range rows.length).flatMap fun i => rowF z B k i (rows.getD i ([], false)).1).length ≤
      (List.range rows.length).length * (k * 4) :=
    length_flatMap_le _ _ _ fun i _ => by
      unfold rowF
      have := length_flatMap_le (List.range k) (fun l => xstep (if l = 0 then z else B + i * k + (l - 1))
        ((rows.getD i ([], false)).1.getD l (0, false)).1 (B + i * k + l) ((rows.getD i ([], false)).1.getD l (0, false)).2)
        4 (fun l _ => length_xstep_le _ _ _ _)
      rwa [List.length_range] at this
  rw [List.length_range] at h1
  simp only [isoF, List.length_append, List.length_map, List.length_range]
  have := min_le_right m₁ rows.length
  omega

theorem length_fixesOf_le {M k t mm : ℕ} (ω : Seed M k t mm) : (fixesOf ω).length ≤ M := by
  unfold fixesOf
  exact (List.length_filterMap_le _ _).trans (by simp)

theorem length_seedCode {M k t mm : ℕ} (ω : Seed M k t mm) :
    (seedCode ω).length = (M + k + mm + 1) + 1 + (4 + mm * (2 * k + 1) + M * 2) * (M + k + mm + 1) := by
  have hL : (seedNums ω).length = 4 + mm * (2 * k + 1) + M * 2 := by
    rw [seedNums, List.length_append, List.length_append, length_flatMap_fin _ (length_rowNums ω),
      length_flatMap_fin (c := 2) (fixNums ω) (fun _ => rfl)]
    simp; ring
  rw [seedCode, List.length_append, List.length_flatMap, ← hL]
  have : (seedNums ω).map (fun a => (ublk (M + k + mm + 1) a).length) =
      List.replicate (seedNums ω).length (M + k + mm + 1) := by
    refine List.eq_replicate_iff.2 ⟨by simp, fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact length_ublk (le_seedW ω a ha)
  rw [this, List.sum_replicate, smul_eq_mul]
  simp [unary]

/-! ### The machine -/

open Classical in
/-- **The machine.** One Turing machine and one constant c: for every graph G on n ≥ 4 vertices with
m edges, all k ≥ 1, t, mm ≥ 1 and every seed ω of `Seed m k t mm`, given the code of G followed by
the code of ω, it outputs whether the formula `hcI` of G and ω has an odd number of satisfying
assignments, within c·2^{9c·N·r(N)} steps, N = 5m + n + 2 + mm·k, r(N) = lg lg(N+4)/√lg(N+4). -/
theorem hcI_tm : ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k t mm : ℕ) (ω : Seed (edges n (matrix G)).length k t mm),
      4 ≤ n → 1 ≤ k → 1 ≤ mm →
      Wrap.Outputs M (code G ++ seedCode ω)
        [decide (cntN (NI n (edges n (matrix G)).length mm k) (hcI n (edges n (matrix G)) ω) % 2 = 1)]
        (SatM.boundNK (SatK.rN 1 (1 / 2)) c 3 (NI n (edges n (matrix G)).length mm k)) := by
  obtain ⟨M₀, C, hfin, hM⟩ := compact
  obtain ⟨M, q, hfinM, hW⟩ := Wrap.everyMachineCanBeWrapped M₀ hfin preI postH preI_polyT postH_polyT
  obtain ⟨c, hc⟩ := wrapped_time_le_rateK q C C 1000 3
  refine ⟨M, c, hfinM, fun n G k t mm ω hn hk hmm => ?_⟩
  have hE := edges_bound n (matrix G)
  obtain ⟨hF, hN⟩ := formI_code G ω
  obtain ⟨φ, hφ⟩ := GraphProblems.exists_toN (N := NI n (edges n (matrix G)).length mm k)
    (ψ := (hcI n (edges n (matrix G)) ω).dedup)
    (fun C hC l hl => (hcI_clause (by omega) hE hk ω (List.mem_dedup.1 hC)).2 l hl)
  have hocc := VariableBound.Rename.allOccurStmt _ φ (allOccur_of hφ (occurs_hcI _ hk ω))
  have hpre : preI (code G ++ seedCode ω) = MainTheoremForms.encC 3 φ := by
    rw [preI, hF, hN, ← hφ, encK_toN]
  have ht0 : [((0 : ℕ), true), (0, false)] ∈ hcI n (edges n (matrix G)) ω :=
    List.mem_append_left _ (mem_hcS_taut _ (by omega))
  have ht1 : [((1 : ℕ), true), (1, false)] ∈ hcI n (edges n (matrix G)) ω :=
    List.mem_append_left _ (mem_hcS_taut _ (by omega))
  have hrun := hM 3 (NI n (edges n (matrix G)).length mm k) φ (by omega)
    (isKCNF_of hφ fun C hC => (hcI_clause (by omega) hE hk ω hC).1) (two_le_length_of hφ ht0 ht1)
    (by rw [hocc.1]; unfold NI; omega)
  unfold MainTheoremForms.CountsOccWithinC at hrun
  rw [hocc.1, hocc.2] at hrun
  have hout := hW (code G ++ seedCode ω) _ _ (by rw [hpre]; exact hrun)
  have hbit : postH (SatK.binary (NI n (edges n (matrix G)).length mm k) (SatK.numSat φ)) =
      [decide (cntN (NI n (edges n (matrix G)).length mm k) (hcI n (edges n (matrix G)) ω) % 2 = 1)] := by
    rw [postH, SatK.binary, List.range_succ_eq_map, List.map_cons, List.headD_cons, Nat.testBit_zero, numSat_of hφ]
  rw [hbit] at hout
  refine Wrap.Outputs.mono hout ?_
  -- the polynomial parts, in S = N + 2
  obtain ⟨S, hS⟩ : ∃ S, S = NI n (edges n (matrix G)).length mm k + 2 := ⟨_, rfl⟩
  have hNI : NI n (edges n (matrix G)).length mm k = (edges n (matrix G)).length + n +
      (4 * (edges n (matrix G)).length + 2) + mm * k := rfl
  have hk_le : k ≤ mm * k := Nat.le_mul_of_pos_left k hmm
  have hmm_le : mm ≤ mm * k := Nat.le_mul_of_pos_right mm hk
  have hw : Nat.log2 (2 * NI n (edges n (matrix G)).length mm k) + 1 ≤ 2 * S := by
    have := Nat.log2_le_self (2 * NI n (edges n (matrix G)).length mm k); omega
  have q1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) S
  have q2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : φ.length ≤ 26 * S ^ 2 := by
    have h1 : φ.length = (hcI n (edges n (matrix G)) ω).dedup.length := by rw [← hφ, toN, List.length_map]
    have h2 := (List.dedup_sublist (hcI n (edges n (matrix G)) ω)).length_le
    have h3 := length_hcS_le n (edges n (matrix G))
    have h4 := length_isoF_le (zC (edges n (matrix G)) n)
      ((edges n (matrix G)).length + n + (4 * (edges n (matrix G)).length + 2)) k ω.1.val (rowsOf ω) (fixesOf ω)
    have h5 := length_fixesOf_le ω
    rw [length_rowsOf, show mm * (k * 4) = 4 * (mm * k) by ring] at h4
    have h6 : (hcI n (edges n (matrix G)) ω).length = (hcS n (edges n (matrix G))).length +
        (isoF (zC (edges n (matrix G)) n) ((edges n (matrix G)).length + n + (4 * (edges n (matrix G)).length + 2)) k
          ω.1.val (rowsOf ω) (fixesOf ω)).length := List.length_append
    have h7 : ((edges n (matrix G)).length + n + 2) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hL : (MainTheoremForms.encC 3 φ).length ≤ 1000 * (NI n (edges n (matrix G)).length mm k + 2) ^ 3 := by
    rw [Wrap.length_encC, ← hS]
    have e : 26 * S ^ 2 * (3 * (2 * S)) = 156 * S ^ 3 := by ring
    calc 3 + (Nat.log2 (2 * NI n (edges n (matrix G)).length mm k) + 1) + 2 +
          φ.length * (3 * (Nat.log2 (2 * NI n (edges n (matrix G)).length mm k) + 1))
        ≤ 3 + 2 * S + 2 + 26 * S ^ 2 * (3 * (2 * S)) := by gcongr
      _ ≤ 1000 * S ^ 3 := by omega
  have hX : (code G ++ seedCode ω).length ≤ 1000 * (NI n (edges n (matrix G)).length mm k + 2) ^ 3 := by
    rw [List.length_append, length_code_eq, length_seedCode, ← hS]
    have hA : 4 + mm * (2 * k + 1) + (edges n (matrix G)).length * 2 ≤ 5 * S := by
      have : mm * (2 * k + 1) = 2 * (mm * k) + mm := by ring
      omega
    have hB : (edges n (matrix G)).length + k + mm + 1 ≤ 3 * S := by omega
    have hAB := Nat.mul_le_mul hA hB
    have e : 5 * S * (3 * S) = 15 * S ^ 2 := by ring
    have hnn : n * n ≤ S ^ 2 := by
      calc n * n ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
        _ = S ^ 2 := by ring
    omega
  exact hc 3 (NI n (edges n (matrix G)).length mm k) φ.length (NI n (edges n (matrix G)).length mm k) _ _
    (by omega) (by omega) (by omega) (by omega) hL hX

/-! ### Hamiltonian cycle with one-sided error in time 2^{o(n)} -/

open Classical in
/-- **Hamiltonian Cycle with one-sided error in time 2^{o(n)}, for O(n) edges.** One Turing machine:
for every D, δ > 0 and ε > 0 there are k, t and n₀ such that for every graph G on n ≥ n₀ vertices with
at most D·n edges, run on the code of G followed by the code of a seed ω of `Seed m k t (3m + 3)`
(m the number of edges), it halts within 2^{εn} steps with one bit out(ω); if G has no Hamiltonian
cycle, out(ω) = 0 for every seed; if G has one, out(ω) = 1 for at least a 2^{−δn} fraction of the
seeds. -/
theorem ham_randomized : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (D : ℕ) (δ ε : ℝ), 0 < δ → 0 < ε → ∃ k t n₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n →
      G.edgeFinset.card ≤ D * n →
      ∃ out : Seed (edges n (matrix G)).length k t (3 * (edges n (matrix G)).length + 3) → Bool,
        (∀ ω, Wrap.Outputs M (code G ++ seedCode ω) [out ω] ⌊(2 : ℝ) ^ (ε * n)⌋₊) ∧
        (numHamCycles G = 0 → ∀ ω, out ω = false) ∧
        (0 < numHamCycles G →
          (Fintype.card (Seed (edges n (matrix G)).length k t (3 * (edges n (matrix G)).length + 3)) : ℝ) ≤
            2 ^ (δ * n) * (Finset.univ.filter fun ω => out ω = true).card) := by
  obtain ⟨M, c, hfin, hM⟩ := hcI_tm
  refine ⟨M, hfin, fun D δ ε hδ hε => ?_⟩
  obtain ⟨k, t, hk, -, n₁, hn₁⟩ := iso_decide (δ / (D + 1)) (by positivity)
  obtain ⟨n₂, hn₂⟩ := boundS_le c 3 (θ := 1 / 4) (by norm_num) (by norm_num) hε
  obtain ⟨A, hA⟩ : ∃ A, A = 9 * D * k + 9 * k + 9 * D + 9 := ⟨_, rfl⟩
  refine ⟨k, t, n₁ + n₂ + 2 ^ (A ^ 4) + 4, fun n G hn hmG => ?_⟩
  have hp := Nat.two_pow_pos (A ^ 4)
  have hmD : (edges n (matrix G)).length ≤ D * n := (length_edges_le_card G).trans hmG
  refine ⟨fun ω => decide (cntN (NI n (edges n (matrix G)).length (3 * (edges n (matrix G)).length + 3) k)
    (hcI n (edges n (matrix G)) ω) % 2 = 1), fun ω => ?_, fun h0 ω => ?_, fun hpos => ?_⟩
  · refine Wrap.Outputs.mono (hM n G k t _ ω (by omega) hk (by omega)) (Nat.floor_le_floor ?_)
    -- N ≤ A·n ≤ n·(lg n)^{1/4}
    have hNA : NI n (edges n (matrix G)).length (3 * (edges n (matrix G)).length + 3) k ≤ A * n := by
      have h1 : (edges n (matrix G)).length * k ≤ D * n * k := Nat.mul_le_mul_right k hmD
      have h2 : k ≤ k * n := Nat.le_mul_of_pos_right k (by omega)
      have e1 : NI n (edges n (matrix G)).length (3 * (edges n (matrix G)).length + 3) k =
          5 * (edges n (matrix G)).length + n + 2 + 3 * ((edges n (matrix G)).length * k) + 3 * k := by
        unfold NI; ring
      have e2 : A * n = 9 * (D * n * k) + 9 * (k * n) + 9 * (D * n) + 9 * n := by rw [hA]; ring
      omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hL : (A : ℝ) ≤ Real.logb 2 n ^ (1 / 4 : ℝ) := by
      have h1 : ((A ^ 4 : ℕ) : ℝ) ≤ Real.logb 2 n := by
        rw [Real.le_logb_iff_rpow_le one_lt_two hn0, Real.rpow_natCast]
        exact_mod_cast (show 2 ^ (A ^ 4) ≤ n by omega)
      calc (A : ℝ) = (((A ^ 4 : ℕ) : ℝ)) ^ (1 / 4 : ℝ) := by
            push_cast
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
        _ ≤ Real.logb 2 n ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    refine hn₂ n _ (by omega) (by unfold NI; omega) ?_
    have e : (1 / 2 - 1 / 4 : ℝ) = 1 / 4 := by norm_num
    rw [e]
    have h1 : (NI n (edges n (matrix G)).length (3 * (edges n (matrix G)).length + 3) k : ℝ) ≤ A * n := by
      exact_mod_cast hNA
    have h2 : (A : ℝ) * n ≤ Real.logb 2 n ^ (1 / 4 : ℝ) * n := mul_le_mul_of_nonneg_right hL hn0.le
    have h3 : (0 : ℝ) ≤ Real.logb 2 n ^ (1 / 4 : ℝ) * n := by
      have : (0 : ℝ) ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast (show 1 ≤ n by omega))
      positivity
    nlinarith
  · have := (hn₁ n G (by omega)).1 h0 ω
    simp [this]
  · have h := (hn₁ n G (by omega)).2 hpos
    refine h.trans (mul_le_mul ?_ (le_of_eq ?_) (by positivity) (by positivity))
    · refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      have hm : ((edges n (matrix G)).length : ℝ) ≤ D * n := by exact_mod_cast hmD
      have hD : (0 : ℝ) < D + 1 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hD]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    · congr 2
      ext ω
      simp

end EthCor.HamITM
