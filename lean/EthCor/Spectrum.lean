module

public import EthCor.CnfTM
public import Wrap.Defs
import FromPrinted.Sets
import GraphProblems.Read
import CountKSat.InOut
import Mathlib.Tactic

/-! # The Max-SAT spectrum of a sparse formula in time C·2^{δn}

For a CNF φ on n variables, `spectrum φ t` is the number of assignments that satisfy exactly t of
its clauses. On 2n + m variables (m = number of clauses) the formula `specF` has the pair clauses of
`EthCor.CnfTree.pairF` (x_{2u+1} = ¬x_{2u}) and, for the j-th clause C, y_j ↔ C with y_j = x_{2n+j}
and the literal (u, b) of C on x_{2u}. Its satisfying assignments are the assignments of φ, with
exactly n + (number of satisfied clauses) true variables (`cntS_specF`). Anthropic's machine
`FromPrinted.Consequences.SIZED` for the satisfying assignments with s true variables then gives
`maxsat_spectrum`: for every width r, density D and δ > 0, one Turing machine computes, from t in
unary and the code of φ, the number `spectrum φ t`, within C·2^{δn} steps, for every φ of width at
most r with at most D·n clauses. Max-Cut, Max-k-SAT and the Ising model with ±1 couplings on
graphs with O(n) edges are special cases. -/

@[expose] public section

namespace EthCor.Spectrum

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems EthCor.CnfTree EthCor.CnfTM Turing Finset

/-! ### The numbers -/

/-- The number of clauses of φ that the assignment a satisfies. -/
def numSatClauses {n : ℕ} (φ : Sat3.CNF n) (a : Fin n → Bool) : ℕ := φ.countP fun C => decide (∃ l ∈ C, a l.1 = l.2)

/-- The number of assignments that satisfy exactly t clauses of φ. -/
def spectrum {n : ℕ} (φ : Sat3.CNF n) (t : ℕ) : ℕ := (univ.filter fun a : Fin n → Bool => numSatClauses φ a = t).card

/-! ### The formula -/

/-- The value of a clause under f. -/
def satC (f : ℕ → Bool) (C : List (ℕ × Bool)) : Bool := C.any fun l => f l.1 == l.2

/-- The literal (u, b) on the variable 2u. -/
def xl (l : ℕ × Bool) : ℕ × Bool := (2 * l.1, l.2)

/-- y ↔ C for y = x_{2n+j}: ¬y ∨ C, and ¬l ∨ y for every literal l of C. -/
def yC (n j : ℕ) (C : List (ℕ × Bool)) : Fml :=
  ((2 * n + j, false) :: C.map xl) :: C.map fun l => [(2 * l.1, !l.2), (2 * n + j, true)]

/-- The pair clauses and y_j ↔ C_j for every clause C_j of ψ. -/
def specF (n : ℕ) (ψ : Fml) : Fml := pairF n ++ (List.range ψ.length).flatMap fun j => yC n j (ψ.getD j [])

theorem satC_congr {f g : ℕ → Bool} {C : List (ℕ × Bool)} (h : ∀ l ∈ C, f l.1 = g l.1) : satC f C = satC g C := by
  rw [Bool.eq_iff_iff]
  simp only [satC, List.any_eq_true, beq_iff_eq]
  exact ⟨fun ⟨l, hl, e⟩ => ⟨l, hl, by rw [← h l hl]; exact e⟩, fun ⟨l, hl, e⟩ => ⟨l, hl, by rw [h l hl]; exact e⟩⟩

theorem sat_pairF' {n : ℕ} (f : ℕ → Bool) :
    (∀ C ∈ pairF n, ∃ l ∈ C, f l.1 = l.2) ↔ ∀ u, u < n → f (2 * u + 1) = !f (2 * u) := by
  constructor
  · intro h u hu
    obtain ⟨l1, hl1, e1⟩ := h _ (mem_pairF.2 ⟨u, hu, Or.inl rfl⟩)
    obtain ⟨l2, hl2, e2⟩ := h _ (mem_pairF.2 ⟨u, hu, Or.inr rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1 hl2
    rcases hl1 with rfl | rfl <;> rcases hl2 with rfl | rfl <;> simp_all
  · intro h C hC
    obtain ⟨u, hu, rfl | rfl⟩ := mem_pairF.1 hC
    · cases hb : f (2 * u)
      · exact ⟨(2 * u + 1, true), by simp, show f (2 * u + 1) = true by rw [h u hu, hb]; rfl⟩
      · exact ⟨(2 * u, true), by simp, hb⟩
    · cases hb : f (2 * u)
      · exact ⟨(2 * u, false), by simp, hb⟩
      · exact ⟨(2 * u + 1, false), by simp, show f (2 * u + 1) = false by rw [h u hu, hb]; rfl⟩

/-- The clauses of y ↔ C hold exactly if y is the value of C. -/
theorem sat_yC (f : ℕ → Bool) (n j : ℕ) (C : List (ℕ × Bool)) :
    (∀ D ∈ yC n j C, ∃ l ∈ D, f l.1 = l.2) ↔ f (2 * n + j) = satC (fun u => f (2 * u)) C := by
  have hbig : (∃ l ∈ (2 * n + j, false) :: C.map xl, f l.1 = l.2) ↔
      f (2 * n + j) = false ∨ ∃ l ∈ C, f (2 * l.1) = l.2 := by
    simp only [List.mem_cons, exists_eq_or_imp]
    refine or_congr Iff.rfl ⟨fun ⟨q, hq, e⟩ => ?_, fun ⟨l, hl, e⟩ => ⟨xl l, List.mem_map_of_mem hl, e⟩⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hq
    exact ⟨l, hl, e⟩
  have hsmall : (∀ D ∈ C.map (fun l => [(2 * l.1, !l.2), (2 * n + j, true)]), ∃ l ∈ D, f l.1 = l.2) ↔
      ∀ l ∈ C, f (2 * l.1) = !l.2 ∨ f (2 * n + j) = true := by
    have key : ∀ l : ℕ × Bool, (∃ q ∈ [(2 * l.1, !l.2), (2 * n + j, true)], f q.1 = q.2) ↔
        f (2 * l.1) = !l.2 ∨ f (2 * n + j) = true := by
      intro l; simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [List.forall_mem_map]
    exact ⟨fun h l hl => (key l).1 (h l hl), fun h l hl => (key l).2 (h l hl)⟩
  have hs : satC (fun u => f (2 * u)) C = true ↔ ∃ l ∈ C, f (2 * l.1) = l.2 := by simp [satC]
  rw [yC, List.forall_mem_cons, hbig, hsmall]
  by_cases hE : ∃ l ∈ C, f (2 * l.1) = l.2
  · rw [hs.2 hE]
    obtain ⟨l, hl, e⟩ := hE
    constructor
    · rintro ⟨-, h⟩
      rcases h l hl with h | h
      · rw [e] at h; simp at h
      · exact h
    · intro hy
      exact ⟨Or.inr ⟨l, hl, e⟩, fun _ _ => Or.inr hy⟩
  · have hs' : satC (fun u => f (2 * u)) C = false := by
      cases h : satC (fun u => f (2 * u)) C
      · rfl
      · exact absurd (hs.1 h) hE
    rw [hs']
    simp only [not_exists, not_and] at hE
    constructor
    · rintro ⟨h | h, -⟩
      · exact h
      · obtain ⟨l, hl, e⟩ := h; exact absurd e (hE l hl)
    · intro hy
      refine ⟨Or.inl hy, fun l hl => Or.inl ?_⟩
      have := hE l hl
      cases h1 : f (2 * l.1) <;> cases h2 : l.2 <;> simp_all

theorem sat_specF (f : ℕ → Bool) (n : ℕ) (ψ : Fml) :
    (∀ D ∈ specF n ψ, ∃ l ∈ D, f l.1 = l.2) ↔
      (∀ D ∈ pairF n, ∃ l ∈ D, f l.1 = l.2) ∧ ∀ j < ψ.length, f (2 * n + j) = satC (fun u => f (2 * u)) (ψ.getD j []) := by
  rw [specF, List.forall_mem_append]
  refine and_congr Iff.rfl ⟨fun h j hj => (sat_yC f n j _).1 fun D hD => h D (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, hD⟩),
    fun h D hD => ?_⟩
  obtain ⟨j, hj, hD⟩ := List.mem_flatMap.1 hD
  exact (sat_yC f n j _).2 (h j (List.mem_range.1 hj)) D hD

theorem vars_getD {n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (j : ℕ) : ∀ l ∈ ψ.getD j [], l.1 < n := by
  by_cases hj : j < ψ.length
  · rw [List.getD_eq_getElem _ _ hj]; exact hψ _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; simp

/-! ### The count -/

/-- The assignment of the 2n + m variables for an assignment a of the n variables. -/
def encA (n : ℕ) (ψ : Fml) (a : Fin n → Bool) (i : Fin (2 * n + ψ.length)) : Bool :=
  if h : i.val < 2 * n then dbl a ⟨i.val, h⟩ else satC (ext a) (ψ.getD (i.val - 2 * n) [])

theorem ext_encA_lt {n : ℕ} {ψ : Fml} (a : Fin n → Bool) {i : ℕ} (hi : i < 2 * n) : ext (encA n ψ a) i = ext (dbl a) i := by
  have h1 : i < 2 * n + ψ.length := by omega
  simp [CountKSat.ext, h1, hi, encA]

theorem ext_encA_ge {n : ℕ} {ψ : Fml} (a : Fin n → Bool) {j : ℕ} (hj : j < ψ.length) :
    ext (encA n ψ a) (2 * n + j) = satC (ext a) (ψ.getD j []) := by
  have h1 : 2 * n + j < 2 * n + ψ.length := by omega
  simp [CountKSat.ext, h1, encA]

theorem sat_encA {n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (a : Fin n → Bool) :
    ∀ D ∈ specF n ψ, ∃ l ∈ D, ext (encA n ψ a) l.1 = l.2 := by
  refine (sat_specF _ n ψ).2 ⟨(sat_pairF' _).2 fun u hu => ?_, fun j hj => ?_⟩
  · rw [ext_encA_lt a (by omega : 2 * u + 1 < 2 * n), ext_encA_lt a (by omega : 2 * u < 2 * n), ext_dbl_odd a hu,
      ext_dbl_even a hu]
  · rw [ext_encA_ge a hj]
    refine satC_congr fun l hl => ?_
    have hl' := vars_getD hψ j l hl
    show ext a l.1 = ext (encA n ψ a) (2 * l.1)
    rw [ext_encA_lt a (by omega : 2 * l.1 < 2 * n), ext_dbl_even a hl']
    simp [CountKSat.ext, hl']

theorem sum_getD (p : List (ℕ × Bool) → Bool) : ∀ l : Fml,
    (∑ j : Fin l.length, if p (l.getD j []) = true then 1 else 0) = l.countP p
  | [] => by simp
  | C :: l => by
    have h := Fin.sum_univ_succ (fun j : Fin (l.length + 1) => if p ((C :: l).getD j []) = true then 1 else 0)
    refine h.trans ?_
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ, List.countP_cons]
    rw [sum_getD p l]; ring

theorem card_encA {n : ℕ} (ψ : Fml) (a : Fin n → Bool) :
    (univ.filter fun i => encA n ψ a i = true).card = n + ψ.countP (satC (ext a)) := by
  rw [Finset.card_filter, Fin.sum_univ_add]
  have h1 : ∀ i : Fin (2 * n), encA n ψ a (Fin.castAdd ψ.length i) = dbl a i := fun i => by
    simp [encA, i.2]
  have h2 : ∀ j : Fin ψ.length, encA n ψ a (Fin.natAdd (2 * n) j) = satC (ext a) (ψ.getD j []) := fun j => by
    simp [encA]
  simp only [h1, h2]
  have hc := card_dbl a
  rw [Finset.card_filter] at hc
  rw [hc, sum_getD]

theorem eq_encA {n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (b : Fin (2 * n + ψ.length) → Bool)
    (hb : ∀ D ∈ specF n ψ, ∃ l ∈ D, ext b l.1 = l.2) :
    encA n ψ (fun u => b ⟨2 * u.val, by omega⟩) = b := by
  obtain ⟨hp, hy⟩ := (sat_specF _ n ψ).1 hb
  have hp' := (sat_pairF' _).1 hp
  have ha : ∀ u, u < n → ext (fun u : Fin n => b ⟨2 * u.val, by omega⟩) u = ext b (2 * u) := fun u hu => by
    simp [CountKSat.ext, hu, show 2 * u < 2 * n + ψ.length by omega]
  funext i
  have hi := i.2
  have e : ext b i.val = b i := by simp [CountKSat.ext, hi]
  unfold encA
  split_ifs with h
  · simp only [dbl]
    split_ifs with hpar
    · exact congrArg b (Fin.ext (show 2 * (i.val / 2) = i.val by omega))
    · have := hp' (i.val / 2) (by omega)
      rw [show 2 * (i.val / 2) + 1 = i.val by omega, e] at this
      have e2 : ext b (2 * (i.val / 2)) = b ⟨2 * (i.val / 2), by omega⟩ := by
        simp [CountKSat.ext, show 2 * (i.val / 2) < 2 * n + ψ.length by omega]
      rw [this, e2]
  · have hj : i.val - 2 * n < ψ.length := by omega
    have := hy (i.val - 2 * n) hj
    rw [show 2 * n + (i.val - 2 * n) = i.val by omega, e] at this
    rw [this]
    exact satC_congr fun l hl => ha l.1 (vars_getD hψ _ l hl)

theorem countP_toN {n : ℕ} (φ : Sat3.CNF n) (a : Fin n → Bool) :
    (Decode.toN φ).countP (satC (ext a)) = numSatClauses φ a := by
  unfold numSatClauses Decode.toN
  rw [List.countP_map]
  refine List.countP_congr fun C _ => ?_
  simp [satC, CountKSat.ext]

/-- **The count**: the satisfying assignments of `specF` with n + t true variables are as many as the
assignments of φ that satisfy exactly t clauses. -/
theorem cntS_specF {n : ℕ} (φ : Sat3.CNF n) (t : ℕ) :
    cntS (2 * n + (Decode.toN φ).length) (n + t) (specF n (Decode.toN φ)) = spectrum φ t := by
  have hψ : ∀ C ∈ Decode.toN φ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN hC).2
  unfold cntS spectrum
  symm
  refine Finset.card_bij (fun a _ => encA n (Decode.toN φ) a) (fun a ha => ?_) (fun a _ a' _ h => ?_) (fun b hb => ?_)
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢
    refine ⟨sat_encA hψ a, ?_⟩
    rw [card_encA, countP_toN, ha]
  · funext u
    have := congrFun h ⟨2 * u.val, by omega⟩
    simpa [encA, dbl] using this
  · simp only [mem_filter, mem_univ, true_and] at hb
    obtain ⟨hs, hc⟩ := hb
    have he := eq_encA hψ b hs
    refine ⟨fun u => b ⟨2 * u.val, by omega⟩, ?_, he⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [← he, card_encA, countP_toN] at hc
    omega

/-! ### Sizes -/

theorem shaped_specF {n r : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (hr : ∀ C ∈ ψ, C.length ≤ r) :
    Shaped (r + 2) (2 * n + ψ.length) (specF n ψ) := by
  intro D hD
  rcases List.mem_append.1 hD with hD | hD
  · obtain ⟨u, hu, rfl | rfl⟩ := mem_pairF.1 hD <;>
      exact ⟨by simp, fun l hl => by simp at hl; rcases hl with rfl | rfl <;> simp <;> omega⟩
  · obtain ⟨j, hj, hD⟩ := List.mem_flatMap.1 hD
    have hj' := List.mem_range.1 hj
    have hv := vars_getD hψ j
    have hlen : (ψ.getD j []).length ≤ r := by
      rw [List.getD_eq_getElem _ _ hj']; exact hr _ (List.getElem_mem hj')
    simp only [yC, List.mem_cons, List.mem_map] at hD
    rcases hD with rfl | ⟨l, hl, rfl⟩
    · refine ⟨by simp only [List.length_cons, List.length_map]; omega, fun q hq => ?_⟩
      simp only [List.mem_cons, List.mem_map] at hq
      rcases hq with rfl | ⟨l, hl, rfl⟩
      · simp; omega
      · have := hv l hl; simp [xl]; omega
    · refine ⟨by simp, fun q hq => ?_⟩
      have := hv l hl
      simp at hq; rcases hq with rfl | rfl <;> simp <;> omega

theorem length_flatMap_le' {β γ : Type} (l : List β) (f : β → List γ) (c : ℕ) (h : ∀ x ∈ l, (f x).length ≤ c) :
    (l.flatMap f).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    omega

theorem length_specF_le {n r : ℕ} {ψ : Fml} (hr : ∀ C ∈ ψ, C.length ≤ r) :
    (specF n ψ).length ≤ 2 * n + ψ.length * (r + 1) := by
  rw [specF, List.length_append, length_pairF]
  have h := length_flatMap_le' (List.range ψ.length) (fun j => yC n j (ψ.getD j [])) (r + 1) fun j hj => by
    have h := List.mem_range.1 hj
    rw [List.getD_eq_getElem _ _ h]
    simpa [yC] using hr _ (List.getElem_mem h)
  rw [List.length_range] at h
  omega

theorem length_input_le {D r n t : ℕ} {φ : Sat3.CNF n} (hr : ∀ C ∈ φ, C.length ≤ r) (hm : φ.length ≤ D * n)
    (ht : t ≤ φ.length) : (unary t ++ SatFree.enc φ).length + 1 ≤ (D * (2 * r + 3) + 6) * (n + 2) ^ 2 := by
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hC : ∀ C ∈ φ, (SatFree.encClause C).length ≤ (2 * r + 2) * X := by
    intro C hC
    have e : (SatFree.encClause C).length = 2 + C.length * (Nat.log2 (2 * n) + 2) := by
      simp [SatFree.encClause, SatFree.encLit, List.length_flatMap]; ring
    have hW : Nat.log2 (2 * n) + 2 ≤ 2 * X := by have := Nat.log2_le_self (2 * n); omega
    rw [e]
    have e1 : C.length * (Nat.log2 (2 * n) + 2) ≤ r * (2 * X) := Nat.mul_le_mul (hr C hC) hW
    have e2 : (2 * r + 2) * X = r * (2 * X) + 2 * X := by ring
    omega
  have hsum := length_flatMap_le' φ SatFree.encClause _ hC
  have e : (SatFree.enc φ).length = n + 1 + ((φ.flatMap SatFree.encClause).length + 1) := by
    simp [SatFree.enc]; ring
  have eu : (unary t).length = t + 1 := by simp [unary]
  rw [List.length_append, eu, e]
  have p0 : φ.length * ((2 * r + 2) * X) ≤ D * X * ((2 * r + 2) * X) :=
    Nat.mul_le_mul_right _ (hm.trans (Nat.mul_le_mul_left _ (by omega)))
  have p1 : D * X * ((2 * r + 2) * X) = D * (2 * r + 2) * X ^ 2 := by ring
  have p2 : D * n ≤ D * X ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
  have p3 : n + 6 ≤ 6 * X ^ 2 := by nlinarith
  have p4 : (D * (2 * r + 3) + 6) * X ^ 2 = D * (2 * r + 2) * X ^ 2 + D * X ^ 2 + 6 * X ^ 2 := by ring
  rw [← hX]
  omega

/-! ### The machine -/

section Poly

variable {α : Type} [Enc α]

theorem specF_polyT {n : α → ℕ} {ψ : α → Fml} (hn : Unary n) (hψ : PolyT ψ) : PolyT fun a => specF (n a) (ψ a) := by
  have h1 := pairF_polyT hn
  have hn' := hn.poly
  have hr : PolyT fun a => List.range (ψ a).length := PolyT.range (Unary.of_length hψ)
  have hy : PolyT fun p : α × ℕ => yC (n p.1) p.2 ((ψ p.1).getD p.2 []) := by unfold yC xl; fun_prop
  unfold specF
  exact PolyT.append h1 (PolyT.flatMap hy hr)

end Poly

/-- Read t in unary and the code of φ; write (2n + m in unary, n + t, `specF`). -/
def preS (x : List Bool) : List Unit × ℕ × Fml :=
  (List.replicate (2 * (FreeCode.readFree (rest x)).1.length + (FreeCode.readFree (rest x)).2.length) (),
    (FreeCode.readFree (rest x)).1.length + ones x, specF (FreeCode.readFree (rest x)).1.length (FreeCode.readFree (rest x)).2)

theorem preS_polyT : PolyT preS := by
  have hr : PolyT fun x : List Bool => FreeCode.readFree (rest x) := by
    have := FreeCode.readFree_polyT; unfold rest; fun_prop
  have hn : Unary fun x : List Bool => (FreeCode.readFree (rest x)).1.length := Unary.of_length hr.fst
  have hm : Unary fun x : List Bool => (FreeCode.readFree (rest x)).2.length := Unary.of_length hr.snd
  have ho : Unary ones := ones_unary PolyT.id'
  have h1 : PolyT fun x : List Bool =>
      List.replicate (2 * (FreeCode.readFree (rest x)).1.length + (FreeCode.readFree (rest x)).2.length) () :=
    ((Unary.const 2).mul hn).add hm
  have h2 : PolyT fun x : List Bool => (FreeCode.readFree (rest x)).1.length + ones x := by
    have := hn.poly; have := ho.poly; fun_prop
  have h3 := specF_polyT hn hr.snd
  unfold preS
  fun_prop

theorem read_spec {n : ℕ} (t : ℕ) (φ : Sat3.CNF n) :
    preS (unary t ++ SatFree.enc φ) = (List.replicate (2 * n + (Decode.toN φ).length) (), n + t, specF n (Decode.toN φ)) := by
  have hR : FreeCode.readFree (SatFree.enc φ) = (List.replicate n (), Decode.toN φ) := FreeCode.reads_readFree n φ
  simp only [preS, Read.rest_unary_append, Read.ones_unary_append, hR, List.length_replicate]

/-- Prepare, count with `SIZED`, write the number in binary. -/
def specM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn preS (FromPrinted.Consequences.SIZED w ℓ τ)) Nat.bits

@[instance_reducible] def isPolyT_specM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] : IsPolyT (specM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) preS_polyT
  IsPolyT.mapOut (M := Stepped.mapIn preS (FromPrinted.Consequences.SIZED w ℓ τ)) bits_polyT

/-! ### The theorem -/

/-- **The Max-SAT spectrum of sparse formulas in time C·2^{δn}.** For every width r, density D and
δ > 0, one Turing machine with finite alphabets, given t in unary and the code of a CNF φ on n
variables with clauses of at most r literals and at most D·n clauses, t ≤ number of clauses,
outputs in binary the number of assignments that satisfy exactly t clauses of φ, within
⌊C·2^{δn}⌋ steps. -/
theorem maxsat_spectrum (r D : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n t : ℕ) (φ : Sat3.CNF n), (∀ C ∈ φ, C.length ≤ r) → φ.length ≤ D * n → t ≤ φ.length →
      Wrap.Outputs M (unary t ++ SatFree.enc φ) (Nat.bits (spectrum φ t)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts (r + 2) (show 0 < δ / (2 * ((D : ℝ) + 2)) by positivity)
  have := isPolyT_specM (r + 2) ℓ τ
  obtain ⟨A, hA⟩ : ∃ A, A = D * (r + 2) + 6 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = c * A ^ c + c + 1 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × Sat3.CNF n // (∀ C ∈ p.2, C.length ≤ r) ∧ p.2.length ≤ D * n ∧ p.1 ≤ p.2.length}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (specM (r + 2) ℓ τ).Runs (unary x.2.1.1 ++ SatFree.enc x.2.1.2) T (K * (x.1 + 2) ^ K)
      (Nat.bits (spectrum x.2.1.2 x.2.1.1)) ∧ (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (specM (r + 2) ℓ τ) (ι := ι) (fun x => unary x.2.1.1 ++ SatFree.enc x.2.1.2)
      (fun x => Nat.bits (spectrum x.2.1.2 x.2.1.1)) (fun x => x.1) hδ K (D * (2 * r + 3) + 6) 2
      (fun x => length_input_le x.2.2.1 x.2.2.2.1 x.2.2.2.2) hrun
    exact ⟨N, C', hfin, fun n t φ hr hm ht => hN ⟨n, (t, φ), hr, hm, ht⟩⟩
  rintro ⟨n, ⟨t, φ⟩, hr, hm, ht⟩
  dsimp only at hr hm ht ⊢
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = Decode.toN φ := ⟨_, rfl⟩
  have hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN (hψdef ▸ hC)).2
  have hψr : ∀ C ∈ ψ, C.length ≤ r := by
    intro C hC
    rw [hψdef, Decode.toN] at hC
    obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    simpa using hr C' hC'
  have hψm : ψ.length = φ.length := by rw [hψdef, Decode.toN, List.length_map]
  obtain ⟨T, hT, hTle⟩ := hc (2 * n + ψ.length) (n + t) (specF n ψ) (by omega) (shaped_specF hψ hψr)
  have hpre := read_spec t φ
  rw [← hψdef] at hpre
  rw [← hpre] at hT
  have hcnt := cntS_specF φ t
  rw [← hψdef] at hcnt
  rw [hcnt] at hT
  refine ⟨T, (Stepped.mapOut_runs (Stepped.mapIn_runs hT)).mono le_rfl ?_, ?_⟩
  · have hl := length_specF_le (n := n) hψr
    have hNA : 2 * n + ψ.length + (specF n ψ).length + 2 ≤ A * (n + 2) := by
      have e1 : ψ.length * (r + 1) ≤ D * n * (r + 1) := Nat.mul_le_mul_right _ (hψm ▸ hm)
      have e2 : D * n * (r + 1) + D * n = D * n * (r + 2) := by ring
      have e3 : D * n * (r + 2) ≤ D * (r + 2) * (n + 2) := by
        calc D * n * (r + 2) = D * (r + 2) * n := by ring
          _ ≤ D * (r + 2) * (n + 2) := Nat.mul_le_mul_left _ (by omega)
      have e4 : A * (n + 2) = D * (r + 2) * (n + 2) + 6 * (n + 2) := by rw [hA]; ring
      have e5 : ψ.length ≤ D * n := hψm ▸ hm
      omega
    calc c * (2 * n + ψ.length + (specF n ψ).length + 2) ^ c ≤ c * (A * (n + 2)) ^ c :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNA _)
      _ = c * A ^ c * (n + 2) ^ c := by rw [mul_pow, mul_assoc]
      _ ≤ K * (n + 2) ^ K := absorb (by omega) (by rw [hK]; omega) (by rw [hK]; omega)
  · have hN : ((2 * n + ψ.length : ℕ) : ℝ) ≤ ((D : ℝ) + 2) * n := by
      have : 2 * n + ψ.length ≤ (D + 2) * n := by rw [hψm, add_mul]; omega
      exact_mod_cast this
    have e : δ / (2 * ((D : ℝ) + 2)) * ((2 * n + ψ.length : ℕ) : ℝ) ≤ δ / 2 * n := by
      calc δ / (2 * ((D : ℝ) + 2)) * ((2 * n + ψ.length : ℕ) : ℝ) ≤ δ / (2 * ((D : ℝ) + 2)) * (((D : ℝ) + 2) * n) :=
            mul_le_mul_of_nonneg_left hN (by positivity)
        _ = δ / 2 * n := by field_simp
    calc (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / (2 * ((D : ℝ) + 2)) * ((2 * n + ψ.length : ℕ) : ℝ)) := hTle
      _ ≤ c * (2 : ℝ) ^ (δ / 2 * n) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two e) (Nat.cast_nonneg _)
      _ ≤ K * (2 : ℝ) ^ (δ / 2 * n) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show c ≤ K by omega)) (by positivity)

end EthCor.Spectrum
