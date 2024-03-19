import Lake
open Lake DSL

package «2ltt» {
  -- add package configuration options here
}

lean_lib [anonymous] {
  -- add library configuration options here
}

@[default_target]
lean_exe «2ltt» {
  root := `Main
}
