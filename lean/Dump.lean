import EthCor

/-! # Dump: the Lean front ends on given input words

Reads lines `name arg bits` from stdin and prints, for each, what the Lean front end of the
algorithm `name` writes for the counter on the input word `bits` (a string of 0 and 1), as JSON.
`arg` is the number of colors q for `potts`, the degree d for `vc` and the width w for `cnf`, `cds`
and `cdr`, and is ignored otherwise. Triples (1^N, s, F) are printed as [N, s, F], formulas as
lists of clauses of [variable, 0/1]. The Python tests (`python/tests/test_lean_agreement.py`)
compare these outputs with the Python reference implementation. Run with `lake env lean --run Dump.lean`. -/

open Groundwork CountKSat GraphProblems

namespace Dump

def jb (b : Bool) : String := if b then "1" else "0"
def jlist {α : Type} (f : α → String) (l : List α) : String := "[" ++ ",".intercalate (l.map f) ++ "]"
def jlit (l : ℕ × Bool) : String := "[" ++ toString l.1 ++ "," ++ jb l.2 ++ "]"
def jfml (F : Groundwork.Prog.Fml) : String := jlist (jlist jlit) F
def jword (w : List Bool) : String := jlist jb w
def jtrip (t : List Unit × ℕ × Groundwork.Prog.Fml) : String :=
  "[" ++ toString t.1.length ++ "," ++ toString t.2.1 ++ "," ++ jfml t.2.2 ++ "]"

def parseBits (s : String) : List Bool := s.toList.map (· == '1')

def run (name : String) (arg : ℕ) (x : List Bool) : String :=
  match name with
  | "col" => jfml (EthCor.formOf x)
  | "hom" => jfml (EthCor.Hom.formHom x)
  | "spec" => jtrip (EthCor.Spectrum.preS x)
  | "potts" => jtrip (EthCor.PottsTM.preP arg x)
  | "perm" => jtrip (EthCor.PermTM.leafP x)
  | "sperm" => jtrip (EthCor.SPermTM.leafS x)
  | "hcF" => jfml (EthCor.HamTM.formH x)
  | "hcS" => jfml (EthCor.HamSTM.formS x)
  | "hcI" => jfml (EthCor.HamITM.formI x)
  | "conn" => jtrip (EthCor.ConnTM.preC x)
  | "cvc" => jtrip (EthCor.ConnTM.preV x)
  | "ci" => jtrip (EthCor.ConnITM.preR x)
  | "nb" => jword (EthCor.NbTM.preN x)
  | "vc" => jlist jtrip ((Sparsify.leaves (EthCor.Vc.stepV arg) 1000 (EthCor.VcTM.rootV x)).map
      (EthCor.Vc.leafV arg))
  | "cnf" => jlist jtrip ((Sparsify.leaves (stepD arg) 1000
      (EthCor.CnfTree.rootX (FreeCode.readFree x))).map leafD)
  | "grow" => jlist (fun y => "[" ++ toString y.1.1.length ++ "," ++ jfml (EthCor.GrowTM.leafF y) ++ "]")
      (Sparsify.leaves EthCor.GrowTree.stepW 1000 (EthCor.CnfTree.rootX (FreeCode.readFree x)))
  | "cds" => jlist jtrip ((Sparsify.leaves (stepD arg) 1000 (EthCor.CdsTM.rootC x)).map leafD)
  | "cdr" => jlist jtrip ((Sparsify.leaves (stepD arg) 1000 (EthCor.CdsITM.rootR x)).map leafD)
  | "pos" => jlist jtrip ((Sparsify.leaves (stepD arg) 1000 (EthCor.PosTM.rootP x)).map leafD)
  | "posr" => jlist jtrip ((Sparsify.leaves (stepD arg) 1000 (EthCor.PosTM.rootQ x)).map leafD)
  | "for" => jtrip (EthCor.ForestTM.preF x)
  | "fi" => jtrip (EthCor.ForestITM.preQ x)
  | _ => "\"unknown\""

end Dump

partial def loop (h : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  match (line.trimAscii.toString.splitOn " ") with
  | [name, arg, bits] => IO.println (Dump.run name arg.toNat! (Dump.parseBits bits))
  | _ => IO.println "\"bad input\""
  loop h

def main : IO Unit := do
  loop (← IO.getStdin)
