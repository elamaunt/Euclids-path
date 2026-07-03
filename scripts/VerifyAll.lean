/-
  scripts/VerifyAll.lean — reproducible axiom/sorry verifier for the whole repository.

  Run from the repository root:

      lake env lean scripts/VerifyAll.lean

  It enumerates every non-internal `EuclidsPath*` theorem/def in the built
  environment, collects the axioms each one depends on, and reports:

    * total number of declarations checked;
    * declarations tainted by `sorryAx` (an unfinished proof);
    * declarations tainted by a NON-STANDARD axiom (anything beyond Lean's
      `propext`, `Classical.choice`, `Quot.sound`).

  It then SELF-ASSERTS the two eternal honesty invariants and fails with a
  non-zero exit code (elaboration error) if either is violated:

    (1) the ONLY non-standard axiom anywhere is `step00FirstCause`;
    (2) the ONLY `sorryAx`-tainted declaration is `twin_prime_conjecture`.

  The taint COUNT itself is printed but NOT asserted — it legitimately grows as
  content is added; only the two invariants above must hold forever.
-/
import EuclidsPath
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total := 0
  let mut sorryTainted : Array Name := #[]
  let mut axTainted : Array (Name × Name) := #[]        -- (declaration, non-standard axiom)
  let mut axNames : Array Name := #[]                   -- distinct non-standard axioms
  for (n, ci) in env.constants.toList do
    if n.toString.startsWith "EuclidsPath" && !n.isInternal && (ci.isThm || ci.isDef) then
      total := total + 1
      let ax ← collectAxioms n
      if ax.contains ``sorryAx then sorryTainted := sorryTainted.push n
      for a in ax do
        if a != ``sorryAx && !standard.contains a then
          axTainted := axTainted.push (n, a)
          if !axNames.contains a then axNames := axNames.push a
  -- Human-readable report
  logInfo m!"Проверено деклараций: {total}"
  logInfo m!"Заражены sorryAx: {sorryTainted.size}"
  for i in sorryTainted.qsort (·.toString < ·.toString) do
    logInfo m!"  SORRY-TAINTED: {i}"
  logInfo m!"Заражены НЕСТАНДАРТНЫМИ аксиомами: {axTainted.size}"
  for (n, a) in axTainted.qsort (fun x y => x.1.toString < y.1.toString) do
    logInfo m!"  AXIOM-TAINTED: {n} ← {a}"
  -- Self-asserted invariants (fail the run on violation)
  if axNames.size != 1 then
    throwError "ИНВАРИАНТ НАРУШЕН: ожидалась ровно ОДНА нестандартная аксиома, найдено {axNames.size}: {axNames}"
  if !axNames[0]!.toString.endsWith "step00FirstCause" then
    throwError "ИНВАРИАНТ НАРУШЕН: нестандартная аксиома не step00FirstCause: {axNames[0]!}"
  if sorryTainted.size != 1 || !sorryTainted[0]!.toString.endsWith "twin_prime_conjecture" then
    throwError "ИНВАРИАНТ НАРУШЕН: sorryAx-заражена не только twin_prime_conjecture: {sorryTainted}"
  logInfo m!"✔ ИНВАРИАНТЫ ОК: единственная нестандартная аксиома = {axNames[0]!}; sorryAx = {sorryTainted[0]!}"
