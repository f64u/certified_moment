import Lake
open Lake DSL

package «typed_assembly» where
  -- add package configuration options here

lean_lib «TypedAssembly» where
  -- add library configuration options here

@[default_target]
lean_exe «typed_assembly» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true


require std from git
  "https://github.com/leanprover/std4/" @ "v4.2.0" 

