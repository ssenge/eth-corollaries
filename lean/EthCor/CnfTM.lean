module

public import EthCor.CnfTree
public import FromPrinted.GraphDefs
public import FreeCode.ReaderCert
public import KSatFreeCodeStatement
public import GraphProblems.Host
public import GraphProblems.Cert
public import CountKSat.Walk
import FromPrinted.Sets
import CountKSat.InOut
import Mathlib.Tactic

/-! # CNF of any width with at most D·n clauses: counting in time c·2^{δn}

The machine `cnfM w ℓ τ` reads the code `SatFree.enc φ` (Anthropic's code of a CNF of any width),
walks the tree of `EthCor.CnfTree.shortens` from `rootX`, counts at each leaf with
`FromPrinted.Consequences.SIZED w ℓ τ` (Anthropic's machine for the satisfying assignments with
exactly s true variables, width w), and writes the sum in binary. `cnf_counts`: for every D and δ > 0
one Turing machine counts the satisfying assignments of every CNF φ on n variables with at most D·n
clauses, none with a repeated literal, within C·2^{δn} steps. -/

@[expose] public section

namespace EthCor.CnfTM

open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems EthCor.CnfTree Turing

/-! ### The root is polynomial-time -/

section Poly

variable {α : Type} [Enc α]

@[fun_prop] theorem lv_polyT {f : α → ℕ × Bool} (hf : PolyT f) : PolyT fun a => lv (f a) := by unfold lv; fun_prop

theorem pairF_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun a => pairF (n a) := by
  have hr : PolyT fun a => List.range (n a) := PolyT.range hn
  have := hn.poly
  unfold pairF; fun_prop

theorem rootX_polyT : PolyT rootX := by
  have hu : Unary fun a : List Unit × Fml => a.1.length := Unary.of_length (by fun_prop)
  have h1 : PolyT fun a : List Unit × Fml => List.replicate (2 * a.1.length) () := (Unary.const 2).mul hu
  have h2 := pairF_polyT hu
  unfold rootX; fun_prop

end Poly

/-! ### The machine -/

/-- Read the code, walk the tree, count at the leaves, write the sum in binary. -/
def cnfM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (walkSum (stepD w) (fun x => rootX (FreeCode.readFree x))
    (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED w ℓ τ))) Nat.bits

@[instance_reducible] def isPolyT_cnfM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] : IsPolyT (cnfM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) stCertDom.2.2
  haveI := isPolyT_walkSum (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED w ℓ τ)) (stCertDom.1 w)
    (rootX_polyT.comp FreeCode.readFree_polyT)
  IsPolyT.mapOut (M := walkSum (stepD w) (fun x => rootX (FreeCode.readFree x))
    (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED w ℓ τ))) bits_polyT

/-! ### Sizes and lengths -/

/-- A node of the tree on 2n variables has size at most A·(n+2)³. -/
theorem size_node_le {D w n : ℕ} {x : DNode} (h1 : x.1 = (List.replicate (2 * n) (), n)) (h2 : x.2.1.length ≤ D * n)
    (h3 : ∀ D' ∈ x.2.1, D'.length ≤ 2 * n ∧ ∀ u ∈ D', u < 2 * n) (h4 : x.2.2.length ≤ (D + 4) * n)
    (h5 : Shaped w (2 * n) x.2.2) : size x ≤ (6 * D + (D + 4) * (3 * w + 2) + 7) * (n + 2) ^ 3 := by
  have s1 : size (List.replicate (2 * n) ()) ≤ 2 * n * 2 + 1 := SplitCount.size_unary _
  have s2 : size n ≤ n + 1 := SplitCount.size_nat_le Nat.lt_two_pow_self
  have s3 : size x.2.1 ≤ D * n * (2 * n * (2 * n + 1 + 1) + 1 + 1) + 1 :=
    SplitCount.size_list_le h2 fun D' hD' => SplitCount.size_list_le (h3 D' hD').1 fun u hu =>
      SplitCount.size_nat_le (((h3 D' hD').2 u hu).trans Nat.lt_two_pow_self)
  have s4 : size x.2.2 ≤ (D + 4) * n * (w * (2 * n + 2 + 1) + 1 + 1) + 1 := SplitCount.size_fml_le h4 h5
  have sx : size x = size (List.replicate (2 * n) ()) + size n + (size x.2.1 + size x.2.2) := by
    rw [size_prod, size_prod, h1]
    rfl
  rw [sx]
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hnX : n ≤ X := by omega
  have i1 : 2 * n * (2 * n + 1 + 1) + 1 + 1 ≤ 6 * X ^ 2 := by rw [hX]; nlinarith
  have i2 : w * (2 * n + 2 + 1) + 1 + 1 ≤ (3 * w + 2) * X := by rw [hX]; nlinarith
  have e1 : D * n * (2 * n * (2 * n + 1 + 1) + 1 + 1) ≤ 6 * D * X ^ 3 := by
    calc D * n * (2 * n * (2 * n + 1 + 1) + 1 + 1) ≤ D * X * (6 * X ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left D hnX) i1
      _ = 6 * D * X ^ 3 := by ring
  have e2 : (D + 4) * n * (w * (2 * n + 2 + 1) + 1 + 1) ≤ (D + 4) * (3 * w + 2) * X ^ 3 := by
    calc (D + 4) * n * (w * (2 * n + 2 + 1) + 1 + 1) ≤ (D + 4) * X * ((3 * w + 2) * X) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hnX) i2
      _ = (D + 4) * (3 * w + 2) * X ^ 2 := by ring
      _ ≤ (D + 4) * (3 * w + 2) * X ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have e3 : 7 * X ≤ 7 * X ^ 3 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) X)
  have e4 : (6 * D + (D + 4) * (3 * w + 2) + 7) * X ^ 3 = 6 * D * X ^ 3 + (D + 4) * (3 * w + 2) * X ^ 3 + 7 * X ^ 3 := by ring
  rw [← hX]
  omega

/-- The code of a CNF with at most D·n clauses, none with a repeated literal, has length below
(4D + 4)·(n+2)³. -/
theorem length_enc_le {D n : ℕ} {φ : Sat3.CNF n} (hm : φ.length ≤ D * n) (hnd : ∀ C ∈ φ, C.Nodup) :
    (SatFree.enc φ).length + 1 ≤ (4 * D + 4) * (n + 2) ^ 3 := by
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hW : Nat.log2 (2 * n) + 1 ≤ 2 * n + 1 := by have := Nat.log2_le_self (2 * n); omega
  have hC : ∀ C ∈ φ, (SatFree.encClause C).length ≤ 4 * X ^ 2 := by
    intro C hC
    have hlen : C.length ≤ 2 * n := by
      have := (hnd C hC).length_le_card
      simpa [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm] using this
    have e : (SatFree.encClause C).length = 2 + C.length * (Nat.log2 (2 * n) + 2) := by
      simp [SatFree.encClause, SatFree.encLit, List.length_flatMap]; ring
    rw [e]
    calc 2 + C.length * (Nat.log2 (2 * n) + 2) ≤ 2 + 2 * n * (2 * n + 2) := by gcongr; omega
      _ ≤ 4 * X ^ 2 := by rw [hX]; nlinarith
  have hsum : (φ.flatMap SatFree.encClause).length ≤ D * X * (4 * X ^ 2) := by
    rw [List.length_flatMap]
    calc (φ.map fun C => (SatFree.encClause C).length).sum ≤ φ.length * (4 * X ^ 2) := by
          have := List.sum_le_card_nsmul (φ.map fun C => (SatFree.encClause C).length) (4 * X ^ 2) (by
            intro y hy
            obtain ⟨C, hC', rfl⟩ := List.mem_map.1 hy
            exact hC C hC')
          simpa using this
      _ ≤ D * X * (4 * X ^ 2) := Nat.mul_le_mul_right _ (hm.trans (Nat.mul_le_mul_left _ (by omega)))
  have e : (SatFree.enc φ).length = n + 1 + ((φ.flatMap SatFree.encClause).length + 1) := by
    simp [SatFree.enc]; ring
  rw [e, ← hX]
  have h3 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
  have h1 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  have e2 : D * X * (4 * X ^ 2) = 4 * D * X ^ 3 := by ring
  have e3 : (4 * D + 4) * X ^ 3 = 4 * D * X ^ 3 + 4 * X ^ 3 := by ring
  omega

/-- A ≤ K and e ≤ K give A·X^e ≤ K·X^K, for X ≥ 1. -/
theorem absorb {A e K X : ℕ} (hX : 1 ≤ X) (hA : A ≤ K) (he : e ≤ K) : A * X ^ e ≤ K * X ^ K :=
  Nat.mul_le_mul hA (Nat.pow_le_pow_right hX he)

/-! ### The theorem -/

/-- **CNF with at most D·n clauses, of any width, counted in time C·2^{δn}.** For every D and every
δ > 0 one Turing machine with finite alphabets, started on the code of a CNF φ on n variables with at
most D·n clauses, none of which repeats a literal, halts within ⌊C·2^{δn}⌋ steps with the number of
satisfying assignments of φ in binary. -/
theorem cnf_counts (D : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (φ : Sat3.CNF n), φ.length ≤ D * n → (∀ C ∈ φ, C.Nodup) →
      Nonempty (TM2OutputsInTime M.tm ((SatFree.enc φ).map M.inputAlphabet.invFun)
        (some ((Nat.bits (SatK.numSat φ)).map M.outputAlphabet.invFun)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊) := by
  obtain ⟨w, hw2, hsh⟩ := shortens D (show 0 < δ / 4 by positivity)
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts w (show 0 < δ / 8 by positivity)
  have := isPolyT_cnfM w ℓ τ
  -- the constants
  obtain ⟨A, hA⟩ : ∃ A, A = 6 * D + (D + 4) * (3 * w + 2) + 7 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = (D + 3) * (A + 2) + c * (2 * D + 6) ^ c + c + 12 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {φ : Sat3.CNF n // φ.length ≤ D * n ∧ ∀ C ∈ φ, C.Nodup}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (cnfM w ℓ τ).Runs (SatFree.enc x.2.1) T (K * (x.1 + 2) ^ K)
      (Nat.bits (SatK.numSat x.2.1)) ∧ (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (cnfM w ℓ τ) (ι := ι) (fun x => SatFree.enc x.2.1)
      (fun x => Nat.bits (SatK.numSat x.2.1)) (fun x => x.1) hδ K (4 * D + 4) 3
      (fun x => length_enc_le x.2.2.1 x.2.2.2) hrun
    exact ⟨N, C', hfin, fun n φ hm hnd => hN ⟨n, φ, hm, hnd⟩⟩
  rintro ⟨n, φ, hm, hnd⟩
  simp only
  -- the formula with numbers as variables
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = Decode.toN φ := ⟨_, rfl⟩
  have hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN (hψdef ▸ hC)).2
  have hψm : ψ.length ≤ D * n := by rw [hψdef, Decode.toN, List.length_map]; exact hm
  obtain ⟨t1, t2, t3, t4⟩ := hsh n ψ hψ hψm
  have hR : FreeCode.readFree (SatFree.enc φ) = (List.replicate n (), ψ) := by rw [hψdef]; exact FreeCode.reads_readFree n φ
  rw [← hR] at t1 t2 t3 t4
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 4 * n) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  -- the leaves
  have hleaf : ∀ x ∈ leaves (stepD w) ((D + 2) * n) (rootX (FreeCode.readFree (SatFree.enc φ))),
      (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED w ℓ τ)).Runs x ⌊(c : ℝ) * E⌋₊ (c * (2 * D + 6) ^ c * X ^ c)
        (cntS (2 * n) n (leafD x).2.2) := by
    intro x hx
    obtain ⟨-, h1, h2, h3⟩ := t2 x hx
    obtain ⟨T, hr, hTle⟩ := hc (2 * n) n (leafD x).2.2 (by omega) h2
    have e : leafD x = (List.replicate (2 * n) (), n, (leafD x).2.2) := by simp [leafD, h1]
    rw [← e] at hr
    refine (Stepped.mapIn_runs hr).mono (Nat.le_floor ?_) ?_
    · have e8 : δ / 8 * ((2 * n : ℕ) : ℝ) = δ / 4 * n := by push_cast; ring
      rw [e8] at hTle; rw [hE]; exact hTle
    · have : (2 * D + 6) * X = (2 * D + 4) * n + 2 * n + (4 * D + 12) := by rw [hX]; ring
      calc c * (2 * n + (leafD x).2.2.length + 2) ^ c ≤ c * ((2 * D + 6) * X) ^ c :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)
        _ = c * (2 * D + 6) ^ c * X ^ c := by rw [mul_pow, mul_assoc]
  -- the stack
  have hstack : ∀ i, size ((round (stepD w))^[i] ([rootX (FreeCode.readFree (SatFree.enc φ))], [])).1 ≤
      ((D + 2) * n + 1) * (A * X ^ 3 + 1) + 1 := by
    intro i
    obtain ⟨s1, s2⟩ := t4 i
    exact SplitCount.size_list_le s1 fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := s2 x hx
      rw [hA, hX]; exact size_node_le h1 h2 h3 h4 h5
  have hlt : ((leaves (stepD w) ((D + 2) * n) (rootX (FreeCode.readFree (SatFree.enc φ)))).map
      fun x => cntS (2 * n) n (leafD x).2.2).sum < 2 ^ (n + 1) := by
    rw [← t3]
    exact lt_of_le_of_lt (SplitCount.cntN_le n ψ) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have wr := walkSum_runs (stepD w) (root := fun x => rootX (FreeCode.readFree x))
    (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED w ℓ τ)) ((D + 2) * n) (SatFree.enc φ)
    (fun x hx => (t2 x hx).1) (fun x => cntS (2 * n) n (leafD x).2.2) ⌊(c : ℝ) * E⌋₊ _ _ (n + 1) hleaf hstack hlt
  rw [← t3, hψdef, stCntToN n φ] at wr
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (leaves (stepD w) ((D + 2) * n) (rootX (FreeCode.readFree (SatFree.enc φ)))).length := ⟨_, rfl⟩
  rw [← hL] at wr t1
  refine ⟨_, (Stepped.mapOut_runs wr).mono le_rfl ?_, ?_⟩
  · -- the space
    rw [← hX]
    have hc4 : c ≤ c + 4 := by omega
    have p1 : ((D + 2) * n + 1) * (A * X ^ 3 + 1) + 1 ≤ (D + 3) * (A + 2) * X ^ (c + 4) := by
      calc ((D + 2) * n + 1) * (A * X ^ 3 + 1) + 1 ≤ ((D + 3) * X) * ((A + 1) * X ^ 3) + X ^ 4 := by
            have h3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
            have h4 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ hX1
            gcongr
            · nlinarith
            · nlinarith
        _ = (D + 3) * (A + 1) * X ^ 4 + X ^ 4 := by ring
        _ ≤ (D + 3) * (A + 2) * X ^ 4 := by
            have e1 : (D + 3) * (A + 2) * X ^ 4 = (D + 3) * (A + 1) * X ^ 4 + (D + 3) * X ^ 4 := by ring
            have e2 : X ^ 4 ≤ (D + 3) * X ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
            omega
        _ ≤ (D + 3) * (A + 2) * X ^ (c + 4) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
    have p2 : c * (2 * D + 6) ^ c * X ^ c ≤ c * (2 * D + 6) ^ c * X ^ (c + 4) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 hc4)
    have p3 : n + 1 + 1 + 3 ≤ 8 * X ^ (c + 4) := by
      have : X ≤ X ^ (c + 4) := Nat.le_self_pow (by omega) X
      omega
    have p4 : ((D + 3) * (A + 2) + c * (2 * D + 6) ^ c + 8) * X ^ (c + 4) ≤ K * X ^ K :=
      absorb hX1 (by omega) (by omega)
    have e5 : ((D + 3) * (A + 2) + c * (2 * D + 6) ^ c + 8) * X ^ (c + 4) =
        (D + 3) * (A + 2) * X ^ (c + 4) + c * (2 * D + 6) ^ c * X ^ (c + 4) + 8 * X ^ (c + 4) := by ring
    omega
  · -- the time
    have hfl : ((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (c : ℝ) * E := Nat.floor_le (by positivity)
    have hLE : (L : ℝ) ≤ E := hE ▸ t1
    have hEE : E * E = (2 : ℝ) ^ (δ / 2 * n) := by
      rw [hE, ← Real.rpow_add two_pos]; congr 1; ring
    have hE0 : 0 ≤ E := by linarith
    have hcK : (c : ℝ) + 2 ≤ (K : ℝ) := by
      have : c + 2 ≤ K := by omega
      exact_mod_cast this
    calc ((L * (⌊(c : ℝ) * E⌋₊ + 2) : ℕ) : ℝ) = (L : ℝ) * (((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) + 2) := by push_cast; ring
      _ ≤ E * ((c : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE0
      _ = ((c : ℝ) + 2) * (E * E) := by ring
      _ = ((c : ℝ) + 2) * (2 : ℝ) ^ (δ / 2 * n) := by rw [hEE]
      _ ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * n) := mul_le_mul_of_nonneg_right hcK (by positivity)

/-- **Deciding** CNF-SAT with at most D·n clauses of any width within C·2^{δn} steps: the output is
the binary number of satisfying assignments, which is not the empty word exactly if φ is
satisfiable. -/
theorem numSat_ne_zero_iff {n : ℕ} (φ : Sat3.CNF n) : SatK.numSat φ ≠ 0 ↔ Sat3.Satisfiable φ := by
  unfold SatK.numSat Sat3.Satisfiable
  rw [Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
  simp [Finset.Nonempty]

end EthCor.CnfTM
