import Lake
open Lake DSL

package «ConnectivitySwitching» where
  srcDir := "."

@[default_target]
lean_lib «ConnectivitySwitching» where
  roots := #[`ConnectivitySwitching]
