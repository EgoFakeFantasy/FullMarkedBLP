import FullMarkedBLP
import Lean

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    if (`FullMarkedBLP).isPrefixOf name && info.isTheorem then
      count := count + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless permitted.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
        unless used.contains ax do
          used := used.push ax
      logInfo m!"{name}: {axioms}"
  logInfo m!"Kernel audit passed: {count} theorem constants; axioms: {used}"

