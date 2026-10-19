import Lake
open Lake DSL

package lratcheck where

@[default_target]
lean_exe lratcheck where
  root := `Main
  moreLinkArgs := #["-Wl,--stack,1073741824"]
