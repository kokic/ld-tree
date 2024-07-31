import Lake
open Lake DSL

package «ld-tree» where
  -- add package configuration options here

lean_lib «LdTree» where
  -- add library configuration options here

@[default_target]
lean_exe «ld-tree» where
  root := `Main
