import Tltt
open Tltt

def main : IO Unit := do
  IO.println "Hello, world!"
  let a :=
    4 +
      3
  IO.println s!"{a}"
  return ()
