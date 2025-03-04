import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso.git"@"v4.16.0"
require flean from git "https://github.com/josephmckinsey/Flean.git"@"main"

@[default_target]
lean_lib FleanBlogPost where
  roots := #[`FleanBlogPost]

package "FleanBlogPost" where
  -- building the C code cost much more than the optimizations save
  moreLeancArgs := #["-O0"]
  -- work around clang emitting invalid linker optimization hints that lld rejects
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-Wl,-ignore_optimization_hints"]
    else #[]

@[default_target]
lean_exe "generate-post" where
  --extraDepTargets := #[`FleanBlogPost]
  root := `Main
