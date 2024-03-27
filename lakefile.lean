import Lake
open Lake DSL

package «tltt» {
  -- add package configuration options here
}

lean_lib «Tltt» {
  -- add library configuration options here
}

@[default_target]
lean_exe «tltt» {
  root := `Main
}
