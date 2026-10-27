import EthCor.ColorFormula
import EthCor.TimeArith
import GraphProblems.Cert
import GraphProblems.Engine
import Wrap.Main
import Wrap.FrontEnd
import CountKSat.InOut
import NamesInOrder.General
import CountedRoute.Main
import VariableBound.Paper.Rename.Math
import ToTuring.Lib.Nat1

/-! # Counting k-colorings with one call to the machine of the Main Theorem

The input is k in unary followed by the code of G. The front end `preC` writes the compact code of
the binary coloring formula `colB` (width 2⌈log₂ k⌉ on n⌈log₂ k⌉ + 4 variables); the machine of
`MainTheoremForms.MainTheoremCompact` counts it; `bitsTrim` turns its (n·b+5)-bit output into
`Nat.bits`. `Wrap.everyMachineCanBeWrapped` puts the three together on one Turing machine
(`colorings_uniform`). -/

namespace EthCor

open Groundwork Groundwork.Prog Groundwork.Decode CountKSat GraphProblems Turing

/-! ### The front end -/

/-- The compact code with the width K and the number w of bits of a slot given in unary. -/
def encK (K w : List Unit) (F : Fml) : List Bool :=
  K.map (fun _ => true) ++ false :: (w.map (fun _ => true) ++ false :: F.flatMap fun C =>
    (List.range K.length).flatMap fun j => (List.range w.length).map (Wrap.slotNat C[j]?).testBit)

def kOf (x : List Bool) : ℕ := ones x
def gOf (x : List Bool) : List Unit × List Bool := read1 (rest x)
def formOf (x : List Bool) : Fml := (colB (kOf x) (gOf x).1.length (gOf x).2).dedup

/-- The front end. -/
def preC (x : List Bool) : List Bool :=
  encK (List.replicate (2 * nb (kOf x)) ()) (List.replicate (Nat.log2 (2 * ((gOf x).1.length * nb (kOf x) + 4)) + 1) ())
    (formOf x)

theorem read_input {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) :
    kOf (unary k ++ code G) = k ∧ gOf (unary k ++ code G) = (List.replicate n (), matrix G) := by
  refine ⟨Read.ones_unary_append k _, ?_⟩
  rw [gOf, Read.rest_unary_append]; exact stRead1 n G

theorem encK_toN (K : ℕ) {N : ℕ} (ψ : Sat3.CNF N) :
    encK (List.replicate K ()) (List.replicate (Nat.log2 (2 * N) + 1) ()) (toN ψ) = MainTheoremForms.encC K ψ := by
  simp only [encK, MainTheoremForms.encC, toN, List.map_replicate, List.length_replicate, List.flatMap_map,
    List.getElem?_map, Wrap.slotNat_map]

/-! ### The front end is polynomial-time -/

section Poly

variable {α : Type} [Enc α]

theorem nb_le (k : ℕ) : nb k ≤ 2 * k := by
  have := Nat.log2_le_self (2 * (k - 1)); unfold nb; omega

@[fun_prop] theorem nb_polyT {k : α → ℕ} (hk : PolyT k) : PolyT fun a => nb (k a) := by unfold nb; fun_prop

theorem nb_unary {k : α → ℕ} (hk : Unary k) : Unary fun a => nb (k a) :=
  Unary.of_le ((Unary.const 2).mul hk) (nb_polyT hk.poly) fun a => nb_le (k a)

theorem forbid_polyT {b v c : α → ℕ} (hb : Unary b) (hv : PolyT v) (hc : PolyT c) :
    PolyT fun a => forbid (b a) (v a) (c a) := by
  have := hb.poly
  have r : PolyT fun a => List.range (b a) := PolyT.range hb
  unfold forbid; fun_prop

theorem colB_polyT {k n : α → ℕ} {m : α → List Bool} (hk : Unary k) (hn : Unary n) (hm : PolyT m) :
    PolyT fun a => colB (k a) (n a) (m a) := by
  have hk' := hk.poly
  have hn' := hn.poly
  have hb := nb_unary hk
  have hb' := hb.poly
  have hA : PolyT fun a => (List.range (n a)).flatMap fun v =>
      ((List.range (2 * k a)).filter fun c => decide (k a ≤ c) && decide (Nat.log2 c < nb (k a))).map
        fun c => forbid (nb (k a)) v c := by
    have hf : PolyT fun q : (α × ℕ) × ℕ => forbid (nb (k q.1.1)) q.1.2 q.2 :=
      forbid_polyT (hb.comp (by fun_prop)) (by fun_prop) (by fun_prop)
    have hd : PolyT fun q : (α × ℕ) × ℕ => decide (k q.1.1 ≤ q.2) && decide (Nat.log2 q.2 < nb (k q.1.1)) := by
      fun_prop
    have r : PolyT fun p : α × ℕ => List.range (2 * k p.1) := PolyT.range (((Unary.const 2).mul hk).comp (by fun_prop))
    exact PolyT.flatMap (PolyT.map hf (PolyT.filter hd r)) (PolyT.range hn)
  have hB : PolyT fun a => ((GraphProblems.pairs (n a)).filter fun p => adjB (n a) (m a) p.1 p.2).flatMap fun p =>
      (List.range (k a)).map fun c => forbid (nb (k a)) p.1 c ++ forbid (nb (k a)) p.2 c := by
    have hf : PolyT fun q : (α × (ℕ × ℕ)) × ℕ => forbid (nb (k q.1.1)) q.1.2.1 q.2 ++ forbid (nb (k q.1.1)) q.1.2.2 q.2 :=
      PolyT.append (forbid_polyT (hb.comp (by fun_prop)) (by fun_prop) (by fun_prop))
        (forbid_polyT (hb.comp (by fun_prop)) (by fun_prop) (by fun_prop))
    have r : PolyT fun p : α × (ℕ × ℕ) => List.range (k p.1) := PolyT.range (hk.comp (by fun_prop))
    have hd : PolyT fun q : α × (ℕ × ℕ) => adjB (n q.1) (m q.1) q.2.1 q.2.2 := by fun_prop
    exact PolyT.flatMap (PolyT.map hf r) (PolyT.filter hd (pairs_polyT hn))
  have hC : PolyT fun a => (List.range (n a * nb (k a))).map fun i => [(i, true), (i, false)] :=
    PolyT.map (by fun_prop) (PolyT.range (hn.mul hb))
  have hD : PolyT fun a => (List.range 4).map fun i => [(n a * nb (k a) + i, true)] :=
    PolyT.map (by fun_prop) (PolyT.range (Unary.const 4))
  unfold colB
  exact PolyT.append (PolyT.append (PolyT.append hA hB) hC) hD

theorem encK_polyT {K w : α → List Unit} {F : α → Fml} (hK : PolyT K) (hw : PolyT w) (hF : PolyT F) :
    PolyT fun x => encK (K x) (w x) (F x) := by
  have hrK : PolyT fun p : (α × List (ℕ × Bool)) => List.range (K p.1).length :=
    PolyT.range ((Unary.of_length hK).comp PolyT.id'.fst)
  have hrw : PolyT fun p : ((α × List (ℕ × Bool)) × ℕ) => List.range (w p.1.1).length :=
    PolyT.range ((Unary.of_length hw).comp PolyT.id'.fst.fst)
  have hs : PolyT fun p : (((α × List (ℕ × Bool)) × ℕ) × ℕ) => (Wrap.slotNat p.1.1.2[p.1.2]?).testBit p.2 :=
    PolyT.testBit (Wrap.slotNat_polyT (by fun_prop)) (by fun_prop)
  unfold encK
  fun_prop

theorem preC_polyT : PolyT preC := by
  have hk : Unary kOf := ones_unary PolyT.id'
  have hg : PolyT gOf := by unfold gOf; have := stCertRead.1; fun_prop
  have hn : Unary fun x => (gOf x).1.length := Unary.of_length hg.fst
  have hb := nb_unary hk
  have hK : PolyT fun x => List.replicate (2 * nb (kOf x)) () := (Unary.const 2).mul hb
  have hw : Unary fun x => Nat.log2 (2 * ((gOf x).1.length * nb (kOf x) + 4)) + 1 :=
    Unary.of_le (((Unary.const 2).mul ((hn.mul hb).add (Unary.const 4))).add (Unary.const 1))
      (by have := hb.poly; have := hn.poly; fun_prop)
      fun x => by have := Nat.log2_le_self (2 * ((gOf x).1.length * nb (kOf x) + 4)); omega
  have hF : PolyT formOf := PolyT.dedup (colB_polyT hk hn hg.snd)
  exact encK_polyT hK hw hF

end Poly

/-! ### Reading the count off the output -/

theorem testBit_bval (w : List Bool) (i : ℕ) : (Groundwork.PolyT.bval w).testBit i = w.getD i false := by
  induction w generalizing i with
  | nil => simp [Groundwork.PolyT.bval_nil]
  | cons b w ih =>
    change (Nat.bit b (Groundwork.PolyT.bval w)).testBit i = _
    cases i with
    | zero => simp
    | succ i => rw [Nat.testBit_bit_succ, ih]; simp

theorem bitsTrim_binary {V c : ℕ} (hc : c < 2 ^ (V + 1)) : Groundwork.PolyT.bitsTrim (SatK.binary V c) = Nat.bits c := by
  rw [← Groundwork.PolyT.bits_bval]
  congr 1
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_bval, SatK.binary]
  by_cases hi : i < V + 1
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [List.getD_eq_getElem?_getD, hi]

/-! ### The facts on the formula -/

theorem colB_var_lt (k n : ℕ) (m : List Bool) : ∀ C ∈ colB k n m, ∀ l ∈ C, l.1 < n * nb k + 4 := by
  intro C hC l hl
  simp only [colB, forbid, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hC
  rcases hC with ((⟨v, hv, c, -, rfl⟩ | ⟨p, ⟨hp, -⟩, c, -, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    exact idx_lt' hv (List.mem_range.1 hj)
  · have hp' := GraphProblems.Color.mem_pairs.1 hp
    rcases List.mem_append.1 hl with hl | hl <;> obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    · exact idx_lt' hp'.1 (List.mem_range.1 hj)
    · exact idx_lt' hp'.2 (List.mem_range.1 hj)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp only <;> omega
  · rw [List.mem_singleton] at hl; subst hl; simp only; omega

theorem colB_width {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (m : List Bool) : ∀ C ∈ colB k n m, C.length ≤ 2 * nb k := by
  have hb := one_le_nb hk
  intro C hC
  simp only [colB, forbid, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hC
  rcases hC with ((⟨v, hv, c, -, rfl⟩ | ⟨p, -, c, -, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · simp; omega
  · simp; omega
  · simp; omega
  · simp; omega

theorem mem_colB_taut (k n : ℕ) (m : List Bool) {i : ℕ} (hi : i < n * nb k) : [(i, true), (i, false)] ∈ colB k n m := by
  simp only [colB, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨i, hi, rfl⟩)

theorem mem_colB_unit (k n : ℕ) (m : List Bool) {i : ℕ} (hi : i < 4) : [(n * nb k + i, true)] ∈ colB k n m := by
  simp only [colB, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr ⟨i, hi, rfl⟩

theorem mem_toN {N : ℕ} {φ : Sat3.CNF N} {C : List (ℕ × Bool)} :
    C ∈ toN φ ↔ ∃ D ∈ φ, D.map (fun l => (l.1.val, l.2)) = C := by
  simp [toN]

/-- Every variable occurs. -/
theorem allOccur_of {k n : ℕ} {m : List Bool} {φ : Sat3.CNF (n * nb k + 4)} (hφ : toN φ = (colB k n m).dedup) :
    SatM.AllOccur φ := by
  intro i
  have hC : ∃ C ∈ colB k n m, ∃ l ∈ C, l.1 = i.val := by
    by_cases hi : i.val < n * nb k
    · exact ⟨_, mem_colB_taut k n m hi, (i.val, true), by simp, rfl⟩
    · exact ⟨_, mem_colB_unit k n m (show i.val - n * nb k < 4 by have := i.2; omega), _, List.mem_singleton.2 rfl,
        by simp only; omega⟩
  obtain ⟨C, hC, l, hl, hli⟩ := hC
  rw [← List.mem_dedup, ← hφ, mem_toN] at hC
  obtain ⟨D, hD, rfl⟩ := hC
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
  exact ⟨D, hD, l', hl', Fin.ext hli⟩

theorem two_le_length {k n : ℕ} {m : List Bool} {φ : Sat3.CNF (n * nb k + 4)} (hφ : toN φ = (colB k n m).dedup) :
    2 ≤ φ.length := by
  have hl : φ.length = (colB k n m).dedup.length := by rw [← hφ, toN, List.length_map]
  rw [hl]
  have h0 := mem_colB_unit k n m (show 0 < 4 by omega)
  have h1 := mem_colB_unit k n m (show 1 < 4 by omega)
  rw [← List.mem_dedup] at h0 h1
  have hne : [(n * nb k + 0, true)] ≠ [(n * nb k + 1, true)] := by simp
  have hsub : ({[(n * nb k + 0, true)], [(n * nb k + 1, true)]} : Finset (List (ℕ × Bool))) ⊆ (colB k n m).dedup.toFinset := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rw [List.mem_toFinset]; rcases hC with rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne, List.toFinset_card_of_nodup (List.nodup_dedup _)] at this
  exact this

theorem isKCNF_of {k n : ℕ} (hk : 2 ≤ k) {m : List Bool} {φ : Sat3.CNF (n * nb k + 4)} (hφ : toN φ = (colB k n m).dedup) :
    SatK.IsKCNF (2 * nb k) φ := by
  refine ⟨fun D hD => ?_, ?_⟩
  · have hm : D.map (fun l => (l.1.val, l.2)) ∈ toN φ := mem_toN.2 ⟨D, hD, rfl⟩
    rw [hφ, List.mem_dedup] at hm
    simpa using colB_width hk n m _ hm
  · have h : (toN φ).Nodup := by rw [hφ]; exact List.nodup_dedup _
    exact List.Nodup.of_map _ h

theorem numSat_of {k n : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) {φ : Sat3.CNF (n * nb k + 4)}
    (hφ : toN φ = (colB k n (matrix G)).dedup) : SatK.numSat φ = numColorings G k := by
  rw [← stCntToN, hφ, ← cntN_colB hk stAdj G]
  unfold cntN
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_dedup]

/-! ### The length bounds -/

theorem length_flatMap_le {β γ : Type} (l : List β) (f : β → List γ) (c : ℕ) (h : ∀ x ∈ l, (f x).length ≤ c) :
    (l.flatMap f).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    omega

theorem length_colB_le (k n : ℕ) (m : List Bool) :
    (colB k n m).length ≤ n * (2 * k) + n * n * k + n * nb k + 4 := by
  simp only [colB, List.length_append]
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) ?_
  · refine (length_flatMap_le _ _ (2 * k) fun v _ => ?_).trans (by simp)
    rw [List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
  · refine (length_flatMap_le _ _ k fun p _ => by simp).trans ?_
    exact Nat.mul_le_mul_right k ((List.length_filter_le _ _).trans (by simp [GraphProblems.pairs, List.length_product]))
  · simp
  · simp

/-! ### The theorem -/

/-- The Main Theorem on the compact code, from Anthropic's proof. -/
theorem compact : MainTheoremForms.MainTheoremCompact :=
  NamesInOrder.generalFormFollowsAsPropositions CountedRoute.mainTheoremHolds

theorem length_input_le {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) : (unary k ++ code G).length = k + 1 + (n + 1 + n * n) := by
  simp [unary, code, stMatrixLength n G]; omega

/-- **Counting k-colorings, uniformly in k.** One Turing machine and one constant c: for all
2 ≤ k ≤ n and every graph G on n vertices, given k in unary and G, it outputs the number of proper
k-colorings of G within c·2^{c·(2b)²·(n·b)·r(n·b)} steps, b = ⌈log₂ k⌉, r(N) = lg lg(N+4)/√lg(N+4). -/
theorem colorings_uniform : ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), 2 ≤ k → k ≤ n →
      Wrap.Outputs M (unary k ++ code G) (Nat.bits (numColorings G k))
        (SatM.boundNK (SatK.rN 1 (1 / 2)) c (2 * nb k) (n * nb k)) := by
  obtain ⟨M₀, C, hfin, hM⟩ := compact
  obtain ⟨M, q, hfinM, hW⟩ := Wrap.everyMachineCanBeWrapped M₀ hfin preC Groundwork.PolyT.bitsTrim preC_polyT (Groundwork.PolyT.bitsTrim' PolyT.id')
  obtain ⟨c, hc⟩ := wrapped_time_le_rateK q C C 1000 6
  refine ⟨M, c, hfinM, fun n k G hk hkn => ?_⟩
  have hb := one_le_nb hk
  obtain ⟨hkx, hgx⟩ := read_input k G
  obtain ⟨φ, hφ⟩ := GraphProblems.exists_toN (N := n * nb k + 4) (ψ := (colB k n (matrix G)).dedup)
    (fun C hC l hl => colB_var_lt k n (matrix G) C (List.mem_dedup.1 hC) l hl)
  have hocc := VariableBound.Rename.allOccurStmt _ φ (allOccur_of hφ)
  have hpre : preC (unary k ++ code G) = MainTheoremForms.encC (2 * nb k) φ := by
    rw [preC, formOf, hkx, hgx]
    simp only [List.length_replicate]
    rw [← hφ, encK_toN]
  have hrun := hM (2 * nb k) (n * nb k + 4) φ (by omega) (isKCNF_of hk hφ) (two_le_length hφ) (by rw [hocc.1]; omega)
  have hcnt : SatK.numSat φ = numColorings G k := numSat_of hk G hφ
  have hlt : numColorings G k < 2 ^ (n * nb k + 4 + 1) := by
    have h1 : SatK.numSat φ ≤ 2 ^ (n * nb k + 4) := (Finset.card_filter_le _ _).trans (by simp)
    have h2 : 2 ^ (n * nb k + 4) < 2 ^ (n * nb k + 4 + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  unfold MainTheoremForms.CountsOccWithinC at hrun
  rw [hocc.1, hocc.2, hcnt] at hrun
  have hout := hW (unary k ++ code G) _ _ (by rw [hpre]; exact hrun)
  rw [bitsTrim_binary hlt] at hout
  refine Wrap.Outputs.mono hout ?_
  -- the polynomial parts
  obtain ⟨s, hs⟩ : ∃ s, s = n * nb k + 2 := ⟨_, rfl⟩
  have hN1 : 1 ≤ n * nb k := Nat.mul_pos (by omega) hb
  have hns : n ≤ n * nb k := Nat.le_mul_of_pos_right n hb
  have hbs : nb k ≤ n * nb k := Nat.le_mul_of_pos_left (nb k) (by omega)
  have hw : Nat.log2 (2 * (n * nb k + 4)) + 1 ≤ 7 * s := by
    have := Nat.log2_le_self (2 * (n * nb k + 4)); omega
  have hs2 : 2 ≤ s := by omega
  have hm : φ.length ≤ 8 * s ^ 3 := by
    have h1 : φ.length = (colB k n (matrix G)).dedup.length := by rw [← hφ, toN, List.length_map]
    have h2 := (List.dedup_sublist (colB k n (matrix G))).length_le
    have h3 := length_colB_le k n (matrix G)
    have hks : k ≤ s := by omega
    have hn' : n ≤ s := by omega
    have hb' : nb k ≤ s := by omega
    have p1 : n * (2 * k) ≤ 2 * s ^ 2 := by
      calc n * (2 * k) ≤ s * (2 * s) := Nat.mul_le_mul hn' (by omega)
        _ = 2 * s ^ 2 := by ring
    have p2 : n * n * k ≤ s ^ 3 := by
      calc n * n * k ≤ s * s * s := Nat.mul_le_mul (Nat.mul_le_mul hn' hn') hks
        _ = s ^ 3 := by ring
    have p3 : n * nb k ≤ s ^ 2 := by
      calc n * nb k ≤ s * s := Nat.mul_le_mul hn' hb'
        _ = s ^ 2 := by ring
    have p4 : 4 ≤ s ^ 2 := by
      calc 4 = 2 * 2 := rfl
        _ ≤ s * s := Nat.mul_le_mul hs2 hs2
        _ = s ^ 2 := by ring
    have p5 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have q0 : 1 ≤ s ^ 6 := Nat.one_le_pow _ _ (by omega)
  have q1 : s ≤ s ^ 6 := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q2 : s ^ 2 ≤ s ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : s ^ 5 ≤ s ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hL : (MainTheoremForms.encC (2 * nb k) φ).length ≤ 1000 * (n * nb k + 2) ^ 6 := by
    rw [Wrap.length_encC, ← hs]
    have hb2 : 2 * nb k ≤ 2 * s := by omega
    have e : 8 * s ^ 3 * (2 * s * (7 * s)) = 112 * s ^ 5 := by ring
    calc 2 * nb k + (Nat.log2 (2 * (n * nb k + 4)) + 1) + 2 + φ.length * (2 * nb k * (Nat.log2 (2 * (n * nb k + 4)) + 1))
        ≤ 2 * s + 7 * s + 2 + 8 * s ^ 3 * (2 * s * (7 * s)) := by gcongr
      _ ≤ 1000 * s ^ 6 := by omega
  have hX : (unary k ++ code G).length ≤ 1000 * (n * nb k + 2) ^ 6 := by
    rw [length_input_le, ← hs]
    have e : s * s = s ^ 2 := by ring
    calc k + 1 + (n + 1 + n * n) ≤ s + 1 + (s + 1 + s * s) := by gcongr <;> omega
      _ ≤ 1000 * s ^ 6 := by omega
  exact hc (2 * nb k) (n * nb k) φ.length (n * nb k + 4) _ _ (by omega) hN1 (by omega) le_rfl hL hX

end EthCor
