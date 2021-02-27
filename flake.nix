{
  description = "LeanProto";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  inputs.nix.url = github:NixOS/nix;
  inputs.leanrulewrapper.url = "/home/zygi/lean/leannixwrapper/leanRuleWrapper.nix";
  inputs.leanrulewrapper.flake = false;

  inputs.lean.url = "/home/zygi/lean/lean4";
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.leanproto-native.url = "/home/zygi/lean/leanprotoProj/leanproto-native";
  inputs.assrt-command.url = "/home/zygi/lean/lean4-assert-command";

  outputs = { self, lean, flake-utils, leanproto-native, assrt-command, nixpkgs, leanrulewrapper, nix}: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = lean.packages.${system};
      pkg = leanPkgs.buildLeanPackage {
        name = "LeanProto";  # must match the name of the top-level .lean file
        src = ./.;
        deps = [leanproto-native.packages.${system} assrt-command.packages.${system}];
        pluginDeps = [leanproto-native.packages.${system}.plugin];
      };
    in {
      packages = pkg // {
        inherit (leanPkgs) lean;
      # } // (builtins.trace leanrulewrapper {}) ;
      } // ((import leanrulewrapper) { inherit pkg system nixpkgs nix; });

      defaultPackage = pkg.modRoot;
    });
}

