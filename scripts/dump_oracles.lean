/-
  scripts/dump_oracles.lean — oracle dumper for scripts/audit_prose.py.
  Writes all_names.txt (every env constant) and euclids_decls.tsv
  (EuclidsPath decls: name<TAB>kind<TAB>tainted<TAB>has_sorry), the two oracle
  files the prose↔Lean auditor reads. The two generated files are build
  artifacts (not committed). Run from the repo root after `lake build`:
      lake env lean scripts/dump_oracles.lean
      python scripts/audit_prose.py --data . --root .
-/
import EuclidsPath
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let consts := env.constants.toList
  let allNames := String.intercalate "\n" (consts.map (fun (n, _) => n.toString))
  IO.FS.writeFile "all_names.txt" allNames
  let mut lines : Array String := #[]
  for (n, ci) in consts do
    if n.toString.startsWith "EuclidsPath" && !n.isInternal && (ci.isThm || ci.isDef) then
      let ax ← collectAxioms n
      let sry := if ax.contains ``sorryAx then "1" else "0"
      let mut tnt := "0"
      for a in ax do
        if a != ``sorryAx && !standard.contains a then tnt := "1"
      let kind := if ci.isThm then "theorem" else "def"
      lines := lines.push (n.toString ++ "\t" ++ kind ++ "\t" ++ tnt ++ "\t" ++ sry)
  IO.FS.writeFile "euclids_decls.tsv" (String.intercalate "\n" lines.toList)
  logInfo s!"oracles written: {consts.length} names, {lines.size} EuclidsPath decls"
