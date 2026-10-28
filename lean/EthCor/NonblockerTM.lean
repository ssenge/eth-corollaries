import EthCor.Nonblocker
import EthCor.VcTM
import FromPrinted.Dom

/-! # Nonblocker in time C·(n+2)^C·2^{εk}

The input is the code of G followed by k in unary. The front end `preN` lists the vertices with a
neighbour (n′ of them). If 2k ≤ n′ the answer is yes (Ore), if n′ < k it is no; in these cases the
front end writes a fixed graph whose count has the right sign. Otherwise n′ < 2k, and it writes the
code of `core G` with s = n′ − k. Anthropic's machine `DOMcount` counts the dominating sets of size s
of the graph it is given within c·2^{(ε/2)·n′} ≤ c·2^{εk} steps, and `postN` says whether the count is
positive (`nb_answer`). The FPT host `tm_fpt` makes one Turing machine of it (`nb_fpt`). -/

namespace EthCor.NbTM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset EthCor.Nb

/-! ### The front end -/

def nX (x : List Bool) : ℕ := GraphProblems.ones x
def mX (x : List Bool) : List Bool := (rest x).take (nX x * nX x)
def kX (x : List Bool) : ℕ := GraphProblems.ones ((rest x).drop (nX x * nX x))
def jX (x : List Bool) : List ℕ := niL (nX x) (mX x)

/-- The front end: a graph and a size for the dominating-set counter. -/
def preN (x : List Bool) : List Bool :=
  if 2 * kX x ≤ (jX x).length then [false, false]
  else if (jX x).length < kX x then [true, false, false, false]
  else unary (jX x).length ++ (unary ((jX x).length - kX x) ++ subM (nX x) (mX x) (jX x))

def postN (N : ℕ) : List Bool := [decide (0 < N)]

/-- The front end, Anthropic's counter of dominating sets of a given size, the sign of the count. -/
def nbM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn preN (FromPrinted.Consequences.DOMcount w ℓ τ)) postN

/-! ### Polynomial time -/

section Poly

variable {α : Type} [Enc α]

theorem unary_polyT {k : α → ℕ} (hk : Unary k) : PolyT fun a => unary (k a) := by
  have h : PolyT fun a => (List.replicate (k a) ()).map (fun _ => true) ++ [false] :=
    PolyT.append (PolyT.map (by fun_prop) hk) (PolyT.const [false])
  exact h.congr fun a => by simp [unary]

theorem niL_polyT {n : α → ℕ} {m : α → List Bool} (hn : Unary n) (hm : PolyT m) :
    PolyT fun a => niL (n a) (m a) := by
  have hn' := hn.poly
  have hd : PolyT fun q : α × ℕ => (List.range (n q.1)).any fun u => adjB (n q.1) (m q.1) q.2 u :=
    PolyT.any (by fun_prop) (PolyT.range (hn.comp (by fun_prop)))
  unfold niL
  exact PolyT.filter hd (PolyT.range hn)

theorem subM_polyT {n : α → ℕ} {m : α → List Bool} {J : α → List ℕ} (hn : PolyT n) (hm : PolyT m)
    (hJ : PolyT J) : PolyT fun a => subM (n a) (m a) (J a) := by
  have hf : PolyT fun q : α × ℕ => (J q.1).map fun v => adjB (n q.1) (m q.1) q.2 v :=
    PolyT.map (by fun_prop) (by fun_prop)
  unfold subM
  exact PolyT.flatMap hf hJ

theorem dec2_polyT {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) : PolyT fun a => decide (2 * f a ≤ g a) := by
  fun_prop

theorem declt_polyT {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) : PolyT fun a => decide (g a < f a) := by
  fun_prop

end Poly

theorem preN_polyT : PolyT preN := by
  have hn : Unary nX := ones_unary PolyT.id'
  have hn' := hn.poly
  have hm : PolyT mX := by unfold mX; fun_prop
  have hk : PolyT kX := by unfold kX; fun_prop
  have hJ : PolyT jX := niL_polyT hn hm
  have hL : Unary fun x => (jX x).length := Unary.of_length hJ
  have hL' := hL.poly
  have hs : Unary fun x => (jX x).length - kX x := Unary.of_le hL (by fun_prop) fun x => Nat.sub_le _ _
  have h3 : PolyT fun x => unary (jX x).length ++ (unary ((jX x).length - kX x) ++ subM (nX x) (mX x) (jX x)) :=
    PolyT.append (unary_polyT hL) (PolyT.append (unary_polyT hs) (subM_polyT hn' hm hJ))
  have c1 : PolyT fun x => decide (2 * kX x ≤ (jX x).length) := dec2_polyT hk hL'
  have c2 : PolyT fun x => decide ((jX x).length < kX x) := declt_polyT hk hL'
  have hite := PolyT.ite' (c := fun x => (jX x).length < kX x) (f := fun _ => [true, false, false, false])
    (g := fun x => unary (jX x).length ++ (unary ((jX x).length - kX x) ++ subM (nX x) (mX x) (jX x)))
    c2 (PolyT.const _) h3
  exact PolyT.ite' (c := fun x => 2 * kX x ≤ (jX x).length) (f := fun _ => [false, false]) c1 (PolyT.const _) hite

theorem postN_polyT : PolyT postN := by unfold postN; fun_prop

@[instance_reducible] def isPolyT_nbM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.DOMcount w ℓ τ)] :
    IsPolyT (nbM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.DOMcount w ℓ τ) preN_polyT
  IsPolyT.mapOut (M := Stepped.mapIn preN (FromPrinted.Consequences.DOMcount w ℓ τ)) postN_polyT

/-! ### What the front end reads and writes -/

theorem read_nb {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    nX (code G ++ unary k) = n ∧ mX (code G ++ unary k) = matrix G ∧ kX (code G ++ unary k) = k := by
  have e : code G ++ unary k = unary n ++ (matrix G ++ unary k) := by rw [code, List.append_assoc]
  have h1 : nX (code G ++ unary k) = n := by rw [nX, e]; exact Read.ones_unary_append n _
  have h2 : rest (code G ++ unary k) = matrix G ++ unary k := by rw [e]; exact Read.rest_unary_append n _
  refine ⟨h1, ?_, ?_⟩
  · rw [mX, h1, h2]; exact List.take_left' (stMatrixLength n G)
  · rw [kX, h1, h2, List.drop_left' (stMatrixLength n G)]; simpa using Read.ones_unary_append k []

theorem codeWith_bot0 : codeWith (⊥ : SimpleGraph (Fin 0)) 0 = [false, false] := by
  simp [codeWith, unary, matrix]

theorem codeWith_bot1 : codeWith (⊥ : SimpleGraph (Fin 1)) 0 = [true, false, false, false] := by
  simp [codeWith, unary, matrix]
  rfl

theorem numDom_bot0 : 0 < numDominatingSets (⊥ : SimpleGraph (Fin 0)) 0 :=
  (numDom_pos_iff _ le_rfl).2 ⟨∅, fun v => v.elim0, le_rfl⟩

theorem numDom_bot1 : ¬ 0 < numDominatingSets (⊥ : SimpleGraph (Fin 1)) 0 := by
  rw [numDom_pos_iff _ (Nat.zero_le 1)]
  rintro ⟨D, hD, hc⟩
  rw [Nat.le_zero, card_eq_zero] at hc
  subst hc
  rcases hD 0 with h | ⟨u, hu, -⟩
  · exact absurd h (Finset.notMem_empty _)
  · exact absurd hu (Finset.notMem_empty _)

theorem length_input {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    (code G ++ unary k).length = n + 1 + n * n + (k + 1) := by
  simp [code, unary, stMatrixLength n G]; omega

/-! ### The theorem -/

open Classical in
/-- **Nonblocker in 2^{εk}·poly(n).** For every ε > 0 there are C and one Turing machine with finite
alphabets: given a graph G on n vertices and k ≤ n in unary, it outputs whether G has a dominating set
with at most n − k vertices (equivalently, a set of k vertices whose complement dominates), within
⌊C·(n+2)^C·2^{εk}⌋ steps. -/
theorem nb_fpt {ε : ℝ} (hε : 0 < ε) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), k ≤ n →
      Wrap.Outputs M (code G ++ unary k) [decide (∃ D : Finset (Fin n), IsDominating G D ∧ D.card + k ≤ n)]
        ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ (ε * k)⌋₊ := by
  obtain ⟨w, ℓ, τ, c, -, ⟨hI⟩, hc⟩ := FromPrinted.Consequences.stDominatingCounted (ε / 2) (by positivity)
  have := isPolyT_nbM w ℓ τ
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) // p.1 ≤ n}
  suffices hrun : ∀ x : ι, ∃ T S : ℕ, (nbM w ℓ τ).Runs (code x.2.1.2 ++ unary x.2.1.1) T S
      [decide (∃ D : Finset (Fin x.1), IsDominating x.2.1.2 D ∧ D.card + x.2.1.1 ≤ x.1)] ∧
      (code x.2.1.2 ++ unary x.2.1.1).length + S + 1 ≤ (c + 2) * (x.1 + 2) ^ (c + 2) ∧
      (T : ℝ) ≤ c * (2 : ℝ) ^ (ε * x.2.1.1) by
    obtain ⟨N, C, hfin, hN⟩ := EthCor.VcTM.tm_fpt (nbM w ℓ τ) (ι := ι) (fun x => code x.2.1.2 ++ unary x.2.1.1)
      (fun x => [decide (∃ D : Finset (Fin x.1), IsDominating x.2.1.2 D ∧ D.card + x.2.1.1 ≤ x.1)])
      (fun x => x.1) (fun x => x.2.1.1) hε.le c (c + 2) (c + 2) hrun
    exact ⟨N, C, hfin, fun n k G hk => hN ⟨n, (k, G), hk⟩⟩
  rintro ⟨n, ⟨k, G⟩, hk⟩
  dsimp only at hk ⊢
  obtain ⟨hn, hm, hkx⟩ := read_nb G k
  have hans := nb_answer G k
  have hNn : (niL n (matrix G)).length ≤ n := by have := card_iso_add G; omega
  -- one run of the counter
  have key : ∀ {N' s : ℕ} (H : SimpleGraph (Fin N')), s ≤ N' → N' ≤ n → N' ≤ 2 * k →
      preN (code G ++ unary k) = codeWith H s →
      (0 < numDominatingSets H s ↔ ∃ D : Finset (Fin n), IsDominating G D ∧ D.card + k ≤ n) →
      ∃ T S : ℕ, (nbM w ℓ τ).Runs (code G ++ unary k) T S
        [decide (∃ D : Finset (Fin n), IsDominating G D ∧ D.card + k ≤ n)] ∧
        (code G ++ unary k).length + S + 1 ≤ (c + 2) * (n + 2) ^ (c + 2) ∧
        (T : ℝ) ≤ c * (2 : ℝ) ^ (ε * k) := by
    intro N' s H hs hN' hN2 hpre hiff
    obtain ⟨T, hr, hT⟩ := hc N' H s hs
    have hr2 : (FromPrinted.Consequences.DOMcount w ℓ τ).Runs (preN (code G ++ unary k)) T (c * (N' + 2) ^ c)
        (numDominatingSets H s) := by rw [hpre]; exact hr
    have wo := Stepped.mapOut_runs (f := postN) (Stepped.mapIn_runs (f := preN) hr2)
    have hval : postN (numDominatingSets H s) = [decide (∃ D : Finset (Fin n), IsDominating G D ∧ D.card + k ≤ n)] := by
      rw [postN]
      congr 1
      exact decide_eq_decide.2 hiff
    rw [hval] at wo
    refine ⟨T, _, wo, ?_, ?_⟩
    · rw [length_input]
      obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
      have hX1 : 1 ≤ X := by omega
      have e1 : X ^ 2 = n * n + 4 * n + 4 := by rw [hX]; ring
      have e2 : c * (N' + 2) ^ c ≤ c * X ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      have e3 : X ^ 2 ≤ X ^ (c + 2) := Nat.pow_le_pow_right hX1 (by omega)
      have e4 : c * X ^ c ≤ c * X ^ (c + 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
      have e5 : (c + 2) * X ^ (c + 2) = c * X ^ (c + 2) + 2 * X ^ (c + 2) := by ring
      rw [← hX, e5]
      omega
    · refine hT.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (Nat.cast_nonneg c))
      have : (N' : ℝ) ≤ 2 * k := by exact_mod_cast hN2
      nlinarith
  -- the three cases
  have hpre := preN.eq_1 (code G ++ unary k)
  rw [jX, hn, hm, hkx] at hpre
  by_cases h1 : 2 * k ≤ (niL n (matrix G)).length
  · rw [if_pos h1, ← codeWith_bot0] at hpre
    exact key ⊥ le_rfl (Nat.zero_le n) (Nat.zero_le _) hpre ⟨fun _ => hans.2 (Or.inl h1), fun _ => numDom_bot0⟩
  · rw [if_neg h1] at hpre
    by_cases h2 : (niL n (matrix G)).length < k
    · rw [if_pos h2, ← codeWith_bot1] at hpre
      refine key ⊥ (Nat.zero_le 1) (by omega) (by omega) hpre ⟨fun h => absurd h numDom_bot1, fun h => ?_⟩
      rcases hans.1 h with h' | ⟨h', -⟩ <;> omega
    · rw [if_neg h2, ← matrix_core G] at hpre
      refine key (core G) (Nat.sub_le _ _) hNn (by omega) hpre ⟨fun h => hans.2 (Or.inr ⟨by omega, h⟩), fun h => ?_⟩
      rcases hans.1 h with h' | ⟨-, h'⟩
      · omega
      · exact h'

end EthCor.NbTM
